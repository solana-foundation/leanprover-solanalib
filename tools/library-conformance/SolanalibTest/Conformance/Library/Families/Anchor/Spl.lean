/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Construct
import SolanalibTest.Conformance.Library.Families.Anchor.Errors
import Solanalib.Specs.AnchorSpl.Token

/-!
# anchor-spl 1.0.2: `Mint` dereference, `accessor::amount`, `token::transfer`

* The two `Mint` dereferences are field projections (`returnsOf`, by `rfl`), with a trivial
  ambient state; the wrapper is decoded natively from the 82 mint bytes of the record and its
  fields are the arguments.
* `accessor::amount`: the observation model is the executable `AnchorSpl.amount`; the primary
  model (`AnchorSplAmountOwned.run`) is decided at its registered sample index
  `AnchorOwnedSamples.amount` (reference heap).
* `token::transfer` (observation model `AnchorSpl.transfer`): the opaque invocation is
  instantiated by the `RefCell` pre-check of solana-invoke over the borrow state of the record,
  then the scripted `sol_invoke_signed_rust` reply of the shim, appending the request to a CPI
  log; the return code becomes the `ProgramError` through the registered
  `ProgramError.V3_0_1.fromStatus`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor.Spl

open Solanalib.Contracts.Model Solanalib.Specs.Core SolanalibTest.Conformance.Library.Runtime
open SolanalibTest.Conformance.Library.Families.Anchor.Errors (both outcomeJson renderOpt emptyJson)
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (pgraph_ite Heap BoxId StringId
  Failure)

/-! ## Mint dereference -/

def asMint (j : Json) : Result Token.Mint := do
  pure ⟨← asOption asPubkey (← field j "mint_authority"), ← natField j "supply",
    UInt8.ofNat (← asUInt 8 (← field j "decimals")), ← boolField j "is_initialized",
    ← asOption asPubkey (← field j "freeze_authority")⟩

def mintJson (m : Token.Mint) : Json := Json.mkObj [("mint_authority", optionJson pubkeyJson
  m.mintAuthority),
  ("supply", toJson m.supply), ("decimals", toJson m.decimals.toNat), ("is_initialized", toJson
    m.isInitialized),
  ("freeze_authority", optionJson pubkeyJson m.freezeAuthority)]

def unitIndex : AnchorAccount.ProjectionIndex := ⟨Unit, Unit⟩

def mintDerefChecker : Checker := ofModel
  ("<anchor_spl::token::Mint as core::ops::deref::Deref>::deref") ([])
  "Solanalib.Specs.AnchorSpl.token.Mint.deref_run"
  fun c => do
    let m ← asMint (← field c.args "mint")
    decideReturns (State := Unit) (Value := Token.Mint)
      (Solanalib.Specs.AnchorSpl.token.Mint.deref_run unitIndex)
      (fun before args => (AnchorSpl.mintDeref args, before)) rfl () ⟨m⟩ asMint (fun _ => pure ())
        mintJson
      (fun _ => .null) c.outcome

def interfaceMintDerefChecker : Checker := ofModel
  ("<anchor_spl::token_interface::Mint as core::ops::deref::Deref>::deref") ([])
  "Solanalib.Specs.AnchorSpl.token_interface.Mint.deref_run"
  fun c => do
    let m ← asMint (← field c.args "mint")
    decideReturns (State := Unit) (Value := Token.Mint)
      (Solanalib.Specs.AnchorSpl.token_interface.Mint.deref_run unitIndex)
      (fun before args => (AnchorSpl.interfaceMintDeref args, before)) rfl () ⟨m⟩ asMint (fun _ =>
        pure ()) mintJson
      (fun _ => .null) c.outcome

/-! ## accessor::amount -/

abbrev AmountObs := Outcome WorldObs (Except (Option ErrorValue) Nat) AnchorSpl.AmountPanic Unit

/-- `amount` slices `bytes[64..72]`: the one slice-bounds message Rust gives
for data of this length (`sliceFailMessage`). -/
def asAmountPanic (dataLength : Nat) (r : String) : Option AnchorSpl.AmountPanic :=
  if r = sliceFailMessage 64 72 dataLength then some .sliceBounds else none

def asAmountObs (dataLength : Nat) (j : Json) : Result (Option AmountObs) :=
  parseOutcome (asExcept (fun e => do pure (some (← asErrorValue e))) (fun v => v.getNat?))
    asWorldObs
    (asAmountPanic dataLength) noReason j

def amountObsJson : Option AmountObs → Json
  | none => "<no outcome>"
  | some (.returned v s) => returnedJson (match v with
      | .ok n => okJson (toJson n)
      | .error e => errJson (optionJson errorValueJson e)) (worldObsJson s)
  | some (.unwound _ s) => Json.mkObj [("exit", "unwound"), ("reason", "slice bounds"), (
    "state",
    worldObsJson s)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def projectAmount {S E T : Type} (input : LoaderInput) (cells : S → AccountInfo.State)
    (err : S → E → Option ErrorValue) : Outcome S (Except E Nat) AnchorSpl.AmountPanic T → AmountObs
  | .returned v s => .returned (match v with
      | .ok n => .ok n
      | .error e => .error (err s e)) (observeWorld input (inputOwners input) (cells s))
  | .unwound r s => .unwound r (observeWorld input (inputOwners input) (cells s))
  | .terminated _ => .terminated ()

abbrev AW := AnchorAccount.World Heap
abbrev AErr := AnchorErrorOwned.Error BoxId
abbrev AOut := Outcome AW (Except AErr Nat) AnchorSpl.AmountPanic (AnchorSpl.AmountPanic ⊕ Failure)

def amountTypes := AnchorOwnedSamples.amount

def ownedFn : OpsFn AW StringId BoxId Failure := RefFn.fn.focus Owned.Focus.snd

theorem ownedGraph : OpsGraph amountTypes.errors ownedFn := RefFn.graph.focus Owned.Focus.snd

def programFn (before : AW) (failure : ProgramError.Value) :
    Option (Outcome AW AErr AnchorSpl.AmountPanic (AnchorSpl.AmountPanic ⊕ Failure)) :=
  (OwnedFn.fromProgramFn ownedFn before failure).map fun
    | .returned v s => .returned v s
    | .unwound e _ => nomatch e
    | .terminated r => .terminated (.inr r)

def liftP : Outcome AW AErr Empty Failure →
    Option (Outcome AW AErr AnchorSpl.AmountPanic (AnchorSpl.AmountPanic ⊕ Failure))
  | .returned v s => some (.returned v s)
  | .unwound e _ => nomatch e
  | .terminated r => some (.terminated (.inr r))

theorem program_graph (before : AW) (failure : ProgramError.Value) :
    PGraph (AnchorSplAmountOwned.program amountTypes failure before ()) (programFn before failure)
      := by
  have e : programFn before failure = (OwnedFn.fromProgramFn ownedFn before failure).bind liftP :=
    by
    unfold programFn
    cases OwnedFn.fromProgramFn ownedFn before failure with
    | none => rfl
    | some p => cases p with
      | returned v s => rfl
      | unwound e _ => exact nomatch e
      | terminated r => rfl
  rw [e]
  apply PGraph.congr (PGraph.exists_step (OwnedFn.fromProgram_graph ownedGraph before failure)
    fun produced => PGraph.ofOption (liftP produced))
  intro o
  apply exists_congr; intro p
  apply and_congr_right; intro _
  cases p with
  | returned v s => exact ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩
  | unwound e _ => exact nomatch e
  | terminated r => exact ⟨fun h => by rw [h]; rfl, fun h => (Option.some.inj h).symm⟩

def amountFn (before : AW) (args : AccountInfo.Args) : Option AOut :=
  match AccountInfo.tryBorrowData before.1 args with
  | (.error failure, during) => (programFn (during, before.2) failure).map (Outcome.map
    Except.error)
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      match Token.readNat bytes 64 8 with
      | some value =>
        match Borrow.release during guard with
        | (.ok (), after) => some (.returned (.ok value) (after, before.2))
        | (.error _, _) => none
      | none =>
        if args.profile.aborts then some (.terminated (.inl .sliceBounds))
        else match Borrow.release during guard with
          | (.ok (), after) => some (.unwound .sliceBounds (after, before.2))
          | (.error _, _) => none

theorem amount_graph (before : AW) (args : AccountInfo.Args) :
    PGraph (Solanalib.Specs.AnchorSpl.token.accessor.amount_run amountTypes before args) (amountFn
      before args) := by
  show PGraph (AnchorSplAmountOwned.run amountTypes before args) _
  unfold AnchorSplAmountOwned.run amountFn
  rcases AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · exact PGraph.map _ (program_graph _ _)
  · dsimp only
    rcases Borrow.current during guard with e | ⟨view, content⟩
    · exact PGraph.false
    · rcases content with x | bytes
      · exact PGraph.false
      · dsimp only
        rcases Token.readNat bytes 64 8 with _ | value
        · apply pgraph_ite _ (PGraph.eq_left _)
          rcases Borrow.release during guard with ⟨r, after⟩
          rcases r with e | u
          · exact PGraph.false
          · exact PGraph.eq_left _
        · rcases Borrow.release during guard with ⟨r, after⟩
          rcases r with e | u
          · exact PGraph.false
          · exact PGraph.eq_left _

def heap0 : Heap := ⟨[], [], Owned.budget, []⟩

def amountChecker : Checker := ofModels ("anchor_spl::token::accessor::amount") ([])
  ("Solanalib.Specs.AnchorSpl.token.accessor.amount_run (index amount_sample) " ++
    "+ Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_run")
  ["Solanalib.Specs.AnchorSpl.token.accessor.amount_run",
    "Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_run"]
  fun c => do
    let (input, world) ← asWorld c.state
    let info ← infoAt input (← natField c.args "account")
    let args : AccountInfo.Args := ⟨profile, info⟩
    let recorded ← asAmountObs (dataLength world info.data) c.outcome
    let owned := decideProjected (O := AOut)
      (Solanalib.Specs.AnchorSpl.token.accessor.amount_run amountTypes (world, heap0) args) _
      (amount_graph (world, heap0) args)
      (projectAmount input Prod.fst (fun s e => AnchorErrorOwned.current amountTypes.errors s e))
        recorded amountObsJson
    let observation := decideProjected (O := AnchorSpl.AmountOutcome)
      (Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_run world args) _
      (PGraph.ofOption (AnchorSpl.amount world args)) (projectAmount input id (fun _ e => some e))
        recorded amountObsJson
    return [owned, observation]

/-! ## token::transfer -/

/-- A recorded CPI request (`sol_invoke_signed_rust`). -/
structure ReqObs where
  instruction : Solanalib.Runtime.CpiInstruction
  accounts : List AccountInfo.Value
  signers : List (List Solanalib.Runtime.Bytes)
  deriving DecidableEq

def reqObs (r : CpiRequest.Request AccountInfo.Value) : ReqObs := ⟨r.instruction, r.accounts,
  r.signers⟩

def asReq (r : Request) : Result ReqObs := do
  let call ← field r.fields "call"
  let ix ← field call "instruction"
  let metas ← (← asArray (← field ix "accounts")).mapM fun m => do
    pure (⟨← keyField m "pubkey", if ← boolField m "is_signer" then 1 else 0,
      if ← boolField m "is_writable" then 1 else 0⟩ : Solanalib.Runtime.CpiMeta)
  pure ⟨⟨← keyField ix "program_id", metas, ← asBytes (← field ix "data")⟩,
    ← asList asInfo (← field call "account_infos"), ← asList (asList asBytes) (← field call
      "signers_seeds")⟩

def asCpiLog (state : Json) : Result (List ReqObs) := do
  let s ← syscallsOf state
  s.log.mapM fun r => do
    unless r.syscall = "sol_invoke_signed_rust" do throw s!"unexpected syscall {r.syscall}"
    asReq r

def reqJson (r : ReqObs) : Json := Json.mkObj [
  ("program_id", pubkeyJson r.instruction.programId),
  ("accounts", listJson (fun (m : Solanalib.Runtime.CpiMeta) => Json.mkObj [("pubkey", pubkeyJson
    m.key),
    ("signer", toJson m.signerByte), ("writable", toJson m.writableByte)]) r.instruction.metas),
  ("data", bytesJson r.instruction.data), ("account_infos", listJson infoJson r.accounts),
  ("signers_seeds", listJson (listJson bytesJson) r.signers)]

/-- The invocation instance: the `invoke_signed` of solana-invoke 0.5.0 first probes
the `RefCell`s of the account info matching each instruction meta (the first
one with its key): both cells mutably for a writable meta, shared otherwise;
a failure returns `AccountBorrowFailed` without the syscall. The borrow state
is that of the record (held across the call; nothing in `transfer` changes it before
the invocation). Then the scripted reply of the shim: the request is appended to
the CPI log and its return code is the result. -/
structure Invocation where
  ret : Nat
  world : AccountInfo.State

def cellFree (s : AccountInfo.State) (h : Borrow.Handle) : Bool :=
  s.exclusiveCount h = 0 && s.sharedCount h = 0

def cellShareable (s : AccountInfo.State) (h : Borrow.Handle) : Bool := s.exclusiveCount h = 0

def precheck (world : AccountInfo.State) (req : CpiRequest.Request AccountInfo.Value) : Bool :=
  req.instruction.metas.all fun m =>
    match req.accounts.find? (fun i => decide (i.key = m.key)) with
    | none => true
    | some info =>
      if m.writableByte ≠ 0 then cellFree world info.lamports && cellFree world info.data
      else cellShareable world info.lamports && cellShareable world info.data

def replyOf (ret : Nat) : Except ProgramError.Value Unit :=
  if ret = 0 then .ok () else .error (ProgramError.V3_0_1.fromStatus (UInt64.ofNat ret))

def invokeFn (inv : Invocation) (log : List ReqObs) (req : CpiRequest.Request AccountInfo.Value) :
    Outcome (List ReqObs) (Except ProgramError.Value Unit) String String :=
  if precheck inv.world req then .returned (replyOf inv.ret) (log ++ [reqObs req])
  else .returned (.error .accountBorrowFailed) log

def transferIndex (inv : Invocation) : AnchorSpl.TransferIndex :=
  ⟨List ReqObs, String, String, Callback.ofFunction (invokeFn inv)⟩

/-- The CPI log and the unconsumed scripted replies. -/
abbrev TObs := Outcome (List ReqObs × List Reply) (Except AnchorAccount.Error Unit) String String

def asCpiState (j : Json) : Result (List ReqObs × List Reply) := do
  pure (← asCpiLog j, (← syscallsOf j).replies)

def replyJson (r : Reply) : Json := Json.mkObj [("syscall", Json.str r.syscall), ("return", toJson
  r.ret)]

/-- Each call of the instance consumes the next reply; the rest are left exactly. -/
def withReplies (replies : List Reply) : Outcome (List ReqObs) (Except AnchorAccount.Error Unit)
  String String → TObs
  | .returned v log => .returned v (log, replies.drop log.length)
  | .unwound r log => .unwound r (log, replies.drop log.length)
  | .terminated r => .terminated r

def asTransferArgs (c : Case) : Result AnchorSpl.TransferArgs := do
  let input ← loaderInput (← field c.state "input")
  let ctx ← field c.args "context"
  let a ← field ctx "accounts"
  pure ⟨⟨⟨← infoAt input (← natField a "from"), ← infoAt input (← natField a "to"),
      ← infoAt input (← natField a "authority")⟩, [], ← keyField ctx "program_id",
      ← asList (asList asBytes) (← field ctx "signer_seeds")⟩, ← asU64 (← field c.args
        "amount")⟩

def transferChecker : Checker := ofModel ("anchor_spl::token::transfer") ([])
  "Solanalib.Specs.AnchorSpl.token.transfer_observation_run"
  fun c => do
    let args ← asTransferArgs c
    let (_, world) ← asWorld c.state
    let script ← syscallsOf c.state
    let ret ← match script.replies with
      | [r] => pure r.ret
      | _ => throw "one scripted invocation reply expected"
    let inv : Invocation := ⟨ret, world⟩
    let recorded ← parseOutcome (asExcept (fun e => asErrorValue e) asUnit) asCpiState (fun r =>
      some r)
      (fun r => some r) c.outcome
    let rel := Solanalib.Specs.AnchorSpl.token.transfer_observation_run (transferIndex inv) [] args
    pure (decideProjected (O := Outcome (List ReqObs) (Except AnchorAccount.Error Unit) String
      String) rel _
      (PGraph.map (Except.mapError AnchorAccount.programError) (PGraph.ofFunction (invokeFn inv) []
        _))
      (withReplies script.replies) recorded
      (renderOpt (outcomeJson (fun (s : List ReqObs × List Reply) => Json.mkObj [("calls", listJson
        reqJson s.1),
        ("replies_left", listJson replyJson s.2)]) (exceptJson errorValueJson (fun _ => .null))
          Json.str Json.str)))

/-- The Mint dereferences have a trivial ambient state: their frame is that
no syscall happens. -/
def checkers : List Checker :=
  ([mintDerefChecker, interfaceMintDerefChecker, amountChecker].map (withFrame [(
    "no syscalls",
    noSyscalls)])) ++
    [withFrame [("accounts unchanged", accountsUnchanged)] transferChecker]

end SolanalibTest.Conformance.Library.Families.Anchor.Spl
