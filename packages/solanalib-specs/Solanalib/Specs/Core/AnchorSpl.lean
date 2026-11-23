/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorConstruct
public import Solanalib.Specs.Core.AnchorContext
public import Solanalib.Specs.Core.TokenState
public import Solanalib.Specs.Core.TokenInstructionConstructors
public import Solanalib.Specs.Core.CpiRequest
public import Solanalib.Specs.Core.AccountInfoDataAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSpl

/-- The legacy wrapper and interface wrapper are distinct source types even
though their decoded mint fields use the shared mathematical vocabulary. -/
structure Mint where
  value : Token.Mint
  deriving DecidableEq, Repr

structure InterfaceMint where
  value : Token.Mint
  deriving DecidableEq, Repr

def mintDeref (mint : Mint) : Token.Mint := mint.value
def interfaceMintDeref (mint : InterfaceMint) : Token.Mint := mint.value

def sampleMint : Token.Mint := ⟨none, 40, 6, true, none⟩

/-- The short unchecked byte slice in `token::accessor::amount` can panic even
though acquiring its data guard is checked. -/
inductive AmountPanic where
  | sliceBounds
  deriving DecidableEq, Repr

abbrev AmountOutcome :=
  Outcome AccountInfo.State (Except AnchorAccount.Error Nat) AmountPanic AmountPanic

/-- Read exactly bytes 64 through 71 in little-endian order. This accessor does
not check the account owner, full token-account length, or initialized state. -/
def amount (before : AccountInfo.State) (args : AccountInfo.Args) : Option AmountOutcome :=
  let (borrowed, during) := AccountInfo.tryBorrowData before args
  match borrowed with
  | .error failure => some (.returned (.error (AnchorAccount.programError failure)) during)
  | .ok guard =>
    match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      match Token.readNat bytes 64 8 with
      | some value =>
        match Borrow.release during guard with
        | (.ok (), after) => some (.returned (.ok value) after)
        | (.error _, _) => none
      | none =>
        if args.profile.aborts then some (.terminated .sliceBounds)
        else match Borrow.release during guard with
          | (.ok (), after) => some (.unwound .sliceBounds after)
          | (.error _, _) => none

/-- The source-local continuation reads bytes 64..72 and releases the acquired
guard on return or unwind. An abort has no resulting state or invented cleanup. -/
def amountReadOutcome (profile : AccountInfo.Profile) (during : AccountInfo.State)
    (guard : Borrow.Guard) (bytes : _root_.Solanalib.Runtime.Bytes) : AmountOutcome :=
  match Token.readNat bytes 64 8 with
  | some value => .returned (.ok value) (Borrow.release during guard).2
  | none =>
    if profile.aborts then .terminated .sliceBounds
    else .unwound .sliceBounds (Borrow.release during guard).2

/-- An actual acquired guard can be released; no global invariant or extra
cleanup-success hypothesis is needed for this callback-free local read. -/
theorem amount_release {before during : AccountInfo.State} {args : AccountInfo.Args}
    {guard : Borrow.Guard}
    (acquired : AccountInfo.tryBorrowData before args = (.ok guard, during)) :
    Borrow.release during guard =
      (.ok (), { during with slots := during.slots.set guard.id none }) :=
  Borrow.release_after_acquire (AccountInfo.GuardCallback.tryBorrow_acquire acquired)

/-- Once the actual current data is available, every local read branch has its
exact return, unwind or terminal outcome, including successful guard cleanup. -/
theorem amount_read {before during : AccountInfo.State} {args : AccountInfo.Args}
    {guard : Borrow.Guard} {bytes : _root_.Solanalib.Runtime.Bytes}
    (acquired : AccountInfo.tryBorrowData before args = (.ok guard, during))
    (current : Borrow.current during guard = .ok (.whole, .data bytes)) :
    amount before args = some (amountReadOutcome args.profile during guard bytes) := by
  have released := amount_release acquired
  cases read : Token.readNat bytes 64 8 with
  | none =>
    by_cases aborts : args.profile.aborts = true <;>
      simp [amount, amountReadOutcome, acquired, current, read, aborts, released]
  | some value => simp [amount, amountReadOutcome, acquired, current, read, released]

/-- The reached data-cell premise supplies the typed read and thereby the
complete local continuation. Borrow failures remain separate earlier outcomes. -/
theorem amount_after_borrow {before during : AccountInfo.State} {args : AccountInfo.Args}
    {guard : Borrow.Guard}
    (ready : AccountInfo.DataBorrow.Ready .shared before args.info.data)
    (acquired : AccountInfo.tryBorrowData before args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      amount before args = some (amountReadOutcome args.profile during guard bytes) := by
  obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current ready acquired
  exact ⟨bytes, current, amount_read acquired current⟩

/-- Every admitted local observation has an actual finite outcome. A missing
handle or borrow conflict returns its checked error; a short slice still panics. -/
theorem amount_progress {before : AccountInfo.State} {args : AccountInfo.Args}
    (ready : AccountInfo.DataBorrow.Ready .shared before args.info.data) :
    ∃ outcome, amount before args = some outcome := by
  cases acquired : AccountInfo.tryBorrowData before args with
  | mk result during =>
    cases result with
    | error failure =>
      exact ⟨.returned (.error (AnchorAccount.programError failure)) during, by simp [amount,
        acquired]⟩
    | ok guard =>
      obtain ⟨bytes, _, continued⟩ := amount_after_borrow ready acquired
      exact ⟨amountReadOutcome args.profile during guard bytes, continued⟩

def amountContract :
    Solanalib.Contracts.Model AccountInfo.State AccountInfo.Args
      (Except AnchorAccount.Error Nat) AmountPanic AmountPanic where
  requires := fun before args => AccountInfo.DataBorrow.Ready .shared before args.info.data
  post := fun state args outcome => amount state args = some outcome

def amountRun (state : AccountInfo.State) (args : AccountInfo.Args) (outcome : AmountOutcome) :
  Prop :=
  amount state args = some outcome

theorem amount_reference : amountContract.Holds amountRun := by
  intro _ _ _ _ step
  exact step

def amountSampleBytes : _root_.Solanalib.Runtime.Bytes := List.replicate 64 0 ++ [42, 0, 0, 0, 0,
  0, 0, 0]

def amountSampleState : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data amountSampleBytes, AccountInfo.sampleProfile.policy⟩], []⟩

theorem amount_execution : amountContract.HasExecution amountRun := by
  refine ⟨amountSampleState, AccountInfo.sampleArgs,
    .returned (.ok 42)
      (Borrow.release (AccountInfo.tryBorrowData amountSampleState AccountInfo.sampleArgs).2 ⟨0,
        0⟩).2,
    trivial, ?_⟩
  rfl

/-- Source order of the three AccountInfo arguments supplied by Anchor SPL. -/
structure TransferAccounts where
  source : AccountInfo.Value
  destination : AccountInfo.Value
  authority : AccountInfo.Value
  deriving DecidableEq, Repr

abbrev TransferContext := AnchorContext.Value TransferAccounts AccountInfo.Value

structure TransferArgs where
  context : TransferContext
  amount : UInt64

/-- the source of Anchor SPL uses the fixed legacy token ID and an empty multisig
signer list. `ctx.program_id` and remaining accounts are not consulted. -/
def transferBuilderArgs (args : TransferArgs) : Token.Instruction.TransferArgs where
  programId := Token.legacyProgramId
  source := args.context.accounts.source.key
  destination := args.context.accounts.destination.key
  authority := args.context.accounts.authority.key
  signers := []
  amount := args.amount.toNat

def transferInstruction (args : TransferArgs) : _root_.Solanalib.Runtime.CpiInstruction :=
  Token.Instruction.authorityInstruction (transferBuilderArgs args).toAuthorityArgs
    (Token.Instruction.transferData args.amount.toNat)

/-- The shared mathematical token builder succeeds at this fixed program ID;
this discharges its value-level admission check without an assumed success. -/
theorem transfer_builder (args : TransferArgs) :
    Token.Instruction.transfer (transferBuilderArgs args) = .ok (transferInstruction args) := by
  simp [Token.Instruction.transfer, Token.Instruction.checkProgram,
    Token.Instruction.ProgramSet.accepts, transferBuilderArgs, transferInstruction,
    Functor.map, Except.map]

def transferRequest (args : TransferArgs) : CpiRequest.Request AccountInfo.Value where
  instruction := transferInstruction args
  accounts := [args.context.accounts.source, args.context.accounts.destination,
    args.context.accounts.authority]
  signers := args.context.signerSeeds

/-- Actual invocation is the only opaque boundary. Its ordinary error,
state changes, unwind and terminal outcome are all supplied by this relation. -/
structure TransferIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  invoke : CpiRequest.Invocation State AccountInfo.Value ProgramError.Value Unwind Terminal

def transfer (index : TransferIndex) :
    Callback.Run index.State TransferArgs (Except AnchorAccount.Error Unit)
      index.Unwind index.Terminal :=
  fun before args outcome => Callback.map (Except.mapError AnchorAccount.programError)
    (fun state (_ : Unit) => index.invoke state (transferRequest args)) before () outcome

def transferFamily : Family where
  Index := TransferIndex
  State := fun i => i.State
  Args := fun _ => TransferArgs
  Value := fun _ => Except AnchorAccount.Error Unit
  Unwind := fun i => i.Unwind
  Terminal := fun i => i.Terminal
  contract := fun i => { requires := fun _ _ => True, post := transfer i }

def transferRun : FamilyRun transferFamily := transfer

theorem transfer_reference : FamilyReference transferFamily transferRun := by
  intro _ _ _ _ _ step
  exact step

def transferSample : TransferIndex :=
  ⟨Nat, String, String,
    fun before _ outcome => outcome = .returned (.error .insufficientFunds) (before + 5)⟩

def transferSampleArgs : TransferArgs :=
  ⟨⟨⟨AccountInfo.sampleInfo, AccountInfo.sampleInfo, AccountInfo.sampleInfo⟩,
    [], .zero, [[], [[1, 2], []]]⟩, 42⟩

/-- A failing opaque provider is an inhabited reference too; no rollback or
success is assumed to make the wrapper family nonvacuous. -/
theorem transfer_execution :
    FamilyHasExecution transferFamily transferRun transferSample := by
  exact ⟨(0 : Nat), transferSampleArgs,
    .returned (.error (AnchorAccount.programError .insufficientFunds)) (5 : Nat), trivial,
    .returned (.error .insufficientFunds) (5 : Nat), rfl, rfl⟩

end Solanalib.Specs.Core.AnchorSpl
