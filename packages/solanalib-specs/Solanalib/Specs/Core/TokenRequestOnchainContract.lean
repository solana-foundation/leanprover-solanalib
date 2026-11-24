/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestOnchain
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Onchain

/-- Ambient client state and the reason types of the external invocation remain
parameters of the shared preparation-and-invocation contract. -/
structure Types where
  /-- Ambient storage and dependency effects alongside the shared borrow world. -/
  Extra : Type
  /-- Reasons for finite unwinding exits. -/
  Unwind : Type
  /-- Reasons for finite terminal exits, which expose no post-state. -/
  Terminal : Type

/-- Value-observation preparation arguments and the selected opaque provider. -/
structure Call (types : Types) where
  /-- The ordinary checked-transfer arguments. -/
  args : Args
  /-- Every finite exit of the selected opaque invocation interpretation. -/
  invoke : CpiRequest.Invocation (State × types.Extra) Account Error types.Unwind types.Terminal

/-- Embed provider exits without changing their account or ambient effects. -/
def providerOutcome {Extra Unwind Terminal : Type}
    (outcome : Outcome (State × Extra) (Except Error Unit) Unwind Terminal) :
    Outcome (State × Extra) (Except Error Unit) (Panic ⊕ Unwind) (Panic ⊕ Terminal) :=
  match outcome with
  | .returned value after => .returned value after
  | .unwound reason after => .unwound (.inr reason) after
  | .terminated reason => .terminated (.inr reason)

/-- Only successful local preparation reaches the supplied CPI provider.
Local errors retain the complete post-cleanup borrow world; invocation exits
retain the actual state of the provider. No fee, transfer or rollback guarantee is assumed. -/
def run (types : Types) (before : State × types.Extra) (call : Call types)
    (outcome : Outcome (State × types.Extra) (Except Error Unit)
      (Panic ⊕ types.Unwind) (Panic ⊕ types.Terminal)) : Prop :=
  match prepare before.1 call.args with
  | (.success prepared, after) =>
    ∃ result, call.invoke (after, before.2) (prepared.request call.args.signers) result ∧
      providerOutcome result = outcome
  | (.error error, after) => outcome = .returned (.error error) (after, before.2)
  | (.panic reason, after) =>
    if call.args.profile.aborts then outcome = .terminated (.inl reason)
    else outcome = .unwound (.inl reason) (after, before.2)
  | (.malformed, _) => False

/-- The supporting value-level preparation family; allocation/Rc exits are
omitted. Its local read/release admission prevents erased preparation paths
without assuming any exit or success of the opaque invocation provider. -/
def invokeTransferCheckedFamily : Family where
  Index := Types
  State := fun types => State × types.Extra
  Args := Call
  Value := fun _ => Except Error Unit
  Unwind := fun types => Panic ⊕ types.Unwind
  Terminal := fun types => Panic ⊕ types.Terminal
  contract := fun types => {
    requires := fun before call => PreparationReady before.1 call.args
    post := run types }

/-- The supporting value-level reference, separate from the operational family. -/
def invokeTransferCheckedRun : FamilyRun invokeTransferCheckedFamily := run

theorem invokeTransferCheckedReference :
    FamilyReference invokeTransferCheckedFamily invokeTransferCheckedRun := by
  intro _ _ _ _ _ result
  exact result

/-- Admission retains every actual provider exit after the exact prepared
request. Ordinary preparation errors and either local panic strategy also
have their actual continuation, including the real cleanup state on unwind. -/
theorem run_retains {types : Types} {before : State × types.Extra} {call : Call types}
    (ready : PreparationReady before.1 call.args) :
    match prepare before.1 call.args with
    | (.success prepared, after) =>
      ∀ result, call.invoke (after, before.2) (prepared.request call.args.signers) result →
        run types before call (providerOutcome result)
    | (.error error, after) => run types before call (.returned (.error error) (after, before.2))
    | (.panic reason, after) =>
      if call.args.profile.aborts then run types before call (.terminated (.inl reason))
      else run types before call (.unwound (.inl reason) (after, before.2))
    | (.malformed, _) => False := by
  have localStep := prepare_not_malformed ready
  cases prepared : prepare before.1 call.args with
  | mk result after =>
    cases result with
    | success value =>
      intro result invoked
      simp only [run, prepared]
      exact ⟨result, invoked, rfl⟩
    | error error => simp [run, prepared]
    | panic reason =>
      cases strategy : call.args.profile.aborts <;> simp [strategy, run, prepared]
    | malformed => simp [prepared] at localStep

/-- Once local read/release admission holds, preparation cannot be the reason
for an empty wrapper relation. A finite wrapper exit exists exactly when the
provider has an exit at any actually reached successful preparation. This
does not assert termination of an arbitrary provider. -/
theorem run_hasOutcome_iff {types : Types} {before : State × types.Extra} {call : Call types}
    (ready : PreparationReady before.1 call.args) :
    (∃ outcome, run types before call outcome) ↔
      ∀ prepared after, prepare before.1 call.args = (.success prepared, after) →
        ∃ result, call.invoke (after, before.2) (prepared.request call.args.signers) result := by
  constructor
  · rintro ⟨outcome, executed⟩ prepared after success
    obtain ⟨result, invoked, _⟩ := (show ∃ result,
      call.invoke (after, before.2) (prepared.request call.args.signers) result ∧
        providerOutcome result = outcome from by simpa only [run, success] using executed)
    exact ⟨result, invoked⟩
  · intro provider
    have localStep := prepare_not_malformed ready
    cases prepared : prepare before.1 call.args with
    | mk result after =>
      cases result with
      | success value =>
        obtain ⟨result, invoked⟩ := provider value after prepared
        have retained := run_retains ready
        rw [prepared] at retained
        exact ⟨providerOutcome result, retained result invoked⟩
      | error error =>
        exact ⟨.returned (.error error) (after, before.2), by simp [run, prepared]⟩
      | panic reason =>
        cases strategy : call.args.profile.aborts with
        | false =>
          exact ⟨.unwound (.inl reason) (after, before.2), by simp [run, prepared, strategy]⟩
        | true => exact ⟨.terminated (.inl reason), by simp [run, prepared, strategy]⟩
      | malformed => simp [prepared] at localStep

/-- A valid initialized mint without extensions. This is only a mathematical
wire fixture; no assessment source or Rust executable is used. -/
def witnessMintBytes : Bytes := List.replicate 45 0 ++ [1] ++ List.replicate 36 0

/-- An initialized bare-mint world for the closed mathematical witness. -/
def witnessState : State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data witnessMintBytes, AccountInfo.sampleProfile.policy⟩], []⟩

/-- The shared account value used in each role of the aliasing witness. -/
def witnessInfo : Account := AccountInfo.sampleInfo

/-- Aliasing all four roles is allowed by request preparation. Whether this
instruction is executable is wholly left to the invocation provider. -/
def witnessArgs : Args where
  profile := AccountInfo.sampleProfile
  crypto := Address.witnessCrypto
  tokenProgramId := token2022ProgramId
  source := witnessInfo
  mint := witnessInfo
  destination := witnessInfo
  authority := witnessInfo
  additional := []
  amount := 1
  decimals := 0
  signers := [[], [[], [7]]]

/-- The exact checked-transfer request produced by the value-level witness. -/
def witnessPrepared : Prepared where
  instruction := Instruction.transferCheckedInstruction {
    programId := token2022ProgramId
    source := .zero
    mint := .zero
    destination := .zero
    authority := .zero
    signers := []
    amount := 1
    decimals := 0 }
  accounts := [witnessInfo, witnessInfo, witnessInfo, witnessInfo]

/-- The witness borrow world after the temporary mint guard is released. -/
def witnessAfter : State := { witnessState with slots := [none] }

theorem witnessInfo_valid : AccountInfo.Valid AccountInfo.sampleProfile witnessState witnessInfo :=
  by
  refine ⟨by decide, ?_, by decide, ⟨40, rfl⟩, ⟨witnessMintBytes, rfl, by decide⟩⟩
  constructor
  · intro id slot found
    simp [Borrow.State.lookupSlot, witnessState] at found
  · intro handle cell found
    simp only [Borrow.State.exclusiveCount, Borrow.State.sharedCount, Borrow.State.count,
      witnessState, List.countP_nil]
    exact ⟨by decide, by decide, Nat.zero_le _⟩

/-- Preparation really succeeds and releases its mint guard before CPI. -/
theorem witness_prepares :
    prepare witnessState witnessArgs = (.success witnessPrepared, witnessAfter) := by
  decide +kernel

/-- The closed aliasing witness satisfies the reached mint-data read and
actual guard cleanup requirements, without whole-argument validity. -/
theorem witness_ready : PreparationReady witnessState witnessArgs := by
  with_unfolding_all repeat' constructor

/-- Closed ambient/unwind/terminal types for the mathematical witness. -/
def sampleTypes : Types := ⟨Nat, Nat, Nat⟩

/-- The witness provider returns an ordinary error after changing ambient state.
A model execution error does not imply state preservation. -/
def witnessProvider : CpiRequest.Invocation (State × Nat) Account Error Nat Nat :=
  fun before request outcome =>
    outcome = .returned (.error .InsufficientFunds)
      (before.1, before.2 + request.accounts.length)

/-- The closed checked-transfer call with its explicit sample provider. -/
def witnessCall : Call sampleTypes := ⟨witnessArgs, witnessProvider⟩

theorem invokeTransferCheckedSatisfiable :
    FamilySatisfiable invokeTransferCheckedFamily sampleTypes :=
  ⟨(witnessState, (0 : Nat)), witnessCall, witness_ready⟩

theorem invokeTransferCheckedHasExecution :
    FamilyHasExecution invokeTransferCheckedFamily invokeTransferCheckedRun sampleTypes := by
  refine ⟨(witnessState, (0 : Nat)), witnessCall,
    .returned (.error .InsufficientFunds) (witnessAfter, (4 : Nat)), witness_ready, ?_⟩
  change run sampleTypes (witnessState, (0 : Nat)) witnessCall _
  unfold run
  change (match prepare witnessState witnessArgs with
    | (.success prepared, after) => _
    | (.error error, after) => _
    | (.panic reason, after) => _
    | (.malformed, _) => False)
  rw [witness_prepares]
  exact ⟨.returned (.error .InsufficientFunds) (witnessAfter, (4 : Nat)), rfl, rfl⟩

end Solanalib.Specs.Core.Token.Onchain
