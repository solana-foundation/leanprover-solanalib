/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.AccountInfo
import SolanalibTest.Conformance.Library.Families.SdkAccounts.State
import Solanalib.Specs.SolanaAccountInfo.Operations

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AccountInfoSdk
open SolanalibTest.Conformance.Library.Families.AccountsV1

def tryLenComputed (state : AccountInfo.State) (args : AccountInfo.Args) :
    Option (Outcome AccountInfo.State (Except ProgramError.Value Nat) Empty Empty) :=
  (tryDataLen state args).map fun (value, after) => .returned value after

theorem tryLen_evaluated (state : AccountInfo.State) (args : AccountInfo.Args)
    (out : Outcome AccountInfo.State (Except ProgramError.Value Nat) Empty Empty) :
    tryDataLenReference state args out ↔ tryLenComputed state args = some out := by
  cases out with
  | unwound reason _ | terminated reason => exact nomatch reason
  | returned value after =>
    cases step : tryDataLen state args with
    | none => simp [tryDataLenReference, tryLenComputed, step]
    | some result => cases result; simp [tryDataLenReference, tryLenComputed, step]

def tryLenCheck
    (contract : Solanalib.Contracts.Model AccountInfo.State AccountInfo.Args (Except
      ProgramError.Value Nat))
    (sameRequires : ∀ s a, contract.requires s a = AccountInfo.ObservationReady .dataLen s a.info)
    (relation : AccountInfo.State → AccountInfo.Args → Outcome AccountInfo.State (Except
      ProgramError.Value Nat) Empty Empty → Prop)
    (same : relation = tryDataLenReference) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state.borrow b.args) := by rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state.borrow b.args) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded (asExcept programErrorOf (·.getNat?)) nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty) (fun r v _ => decide (r = v))
    (borrowFits b) noMatch noMatch recorded
  return admits (relation b.state.borrow b.args) (tryLenComputed b.state.borrow b.args)
    (fun out => by rw [same]; exact tryLen_evaluated b.state.borrow b.args out) fits
    (Info.renderOutcome (exceptJson programErrorJson (fun (v : Nat) => v)) Info.stateJson)

def borrowReady (lamports : Bool) (state : AccountInfo.State) (args : AccountInfo.Args) : Prop :=
  if lamports then LamportsBorrowReady state args.info else AccountInfo.DataBorrowReady state
    args.info

instance borrowReadyDecidable (lamports : Bool) (state : AccountInfo.State) (args :
  AccountInfo.Args) :
    Decidable (borrowReady lamports state args) := by
  unfold borrowReady
  split <;> infer_instance

def borrowCheck (lamports : Bool)
    (contract : Solanalib.Contracts.Model AccountInfo.State AccountInfo.Args (Except
      ProgramError.Value Borrow.Guard))
    (sameRequires : ∀ s a, contract.requires s a = borrowReady lamports s a)
    (relation : AccountInfo.State → AccountInfo.Args → Outcome AccountInfo.State (Except
      ProgramError.Value Borrow.Guard) Empty Empty → Prop)
    (model : AccountInfo.State → AccountInfo.Args → Except ProgramError.Value Borrow.Guard ×
      AccountInfo.State)
    (same : relation = returnsOf model) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state.borrow b.args) := by rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state.borrow b.args) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded (asExcept programErrorOf (fun j => natField j "guard")) nativeOf
    c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty)
    (fun r v _ => match r, v with
      | .ok id, .ok guard => id == guard.id
      | .error error, .error expected => decide (error = expected)
      | _, _ => false)
    (borrowFits b) noMatch noMatch recorded
  return admits (relation b.state.borrow b.args) _
    (fun out => by rw [same]; exact returnsOf_graph model b.state.borrow b.args out) fits
    (Info.renderOutcome (exceptJson programErrorJson
      (fun guard => Json.mkObj [("guard", guard.id), ("generation", guard.generation)]))
        Info.stateJson)

def assignCheck
    (contract : Solanalib.Contracts.Model State (AccountInfo.Value × Solanalib.Runtime.Pubkey) Unit)
    (sameRequires : ∀ s a, contract.requires s a = (a.1.ownerRef.id < s.owners.length))
    (model : State → AccountInfo.Value × Solanalib.Runtime.Pubkey → Unit × State)
    (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  let args := (b.args.info, ← pubkeyOf (← field c.args "new_owner"))
  have : Decidable (contract.requires b.state args) := by rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state args) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded asUnit nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty) (fun _ _ _ => true)
    (fun n s => stateFits b.native n s b.native.base.rc) noMatch noMatch recorded
  return admits (returnsOf model b.state args) _ (returnsOf_graph model b.state args) fits
    (Info.renderOutcome (fun _ => Json.null) stateJson)

/-- Enumerating both finite resize outcomes retains termination only at an
actually reached zeroing boundary. No ghost after-state is fabricated. -/
def resizeOutcomes (state : State) (args : ResizeArgs) :
    List (Outcome State (Except ProgramError.Value Unit) Empty ResizeTerminal) :=
  match prepareResize state args with
  | .malformed => []
  | .finished value after => [.returned value after]
  | .zero guard oldLen increase during =>
    [.returned (.ok ()) (completeZero during guard oldLen increase), .terminated .zeroing]

theorem resize_evaluated (state : State) (args : ResizeArgs)
    (out : Outcome State (Except ProgramError.Value Unit) Empty ResizeTerminal) :
    resizeReference state args out ↔ out ∈ resizeOutcomes state args := by
  unfold resizeReference resizeOutcomes
  cases prepareResize state args <;> simp

theorem admitsMany_iff {O : Type} (relation : O → Prop) (computed : List O)
    (graph : ∀ out, relation out ↔ out ∈ computed) (fits : O → Bool) :
    (∃ out, relation out ∧ fits out = true) ↔ ∃ out ∈ computed, fits out = true := by
  simp only [graph]

def admitsMany {O : Type} (relation : O → Prop) (computed : List O)
    (graph : ∀ out, relation out ↔ out ∈ computed) (fits : O → Bool)
    (render : O → Json) : Verdict :=
  have : Decidable (∃ out, relation out ∧ fits out = true) :=
    decidable_of_iff _ (admitsMany_iff relation computed graph fits).symm
  ⟨decide (∃ out, relation out ∧ fits out = true), Json.arr (computed.map render).toArray⟩

def reallocArgsOf (before : Before) (j : Json) : Result ResizeArgs := do
  return ⟨before.args.info, ← asUInt 64 (← field j "new_len"), ← boolField j "zero_init"⟩

def resizeArgsOf (before : Before) (j : Json) : Result (AccountInfo.Value × Nat) := do
  unless ← boolField j "zero_init" do throw "resize fixes zero initialization to true"
  return (before.args.info, ← asUInt 64 (← field j "new_len"))

def resizeCheck {A : Type} (argsOf : Before → Json → Result A) (project : A → ResizeArgs)
    (contract : Solanalib.Contracts.Model State A (Except ProgramError.Value Unit) Empty
      ResizeTerminal)
    (sameRequires : ∀ s a, contract.requires s a = ResizeReady s (project a))
    (relation : State → A → Outcome State (Except ProgramError.Value Unit) Empty ResizeTerminal →
      Prop)
    (same : ∀ s a, relation s a = resizeReference s (project a))
    (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  let args ← argsOf b c.args
  have : Decidable (contract.requires b.state args) := by rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state args) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded (asExcept programErrorOf asUnit) nativeOf c.outcome
  let terminalFits : Bool ← match recorded with
    | .terminated _ => do
      let detail ← field c.outcome "detail"
      let status ← natField detail "status"
      let byte ← natField detail "byte"
      let length ← natField detail "length"
      pure (match prepareResize b.state (project args) with
        | .zero _ _ expected _ => status == 91 && byte == 0 && length == expected
        | _ => false)
    | _ => pure true
  let fits := matchOutcome (U := Empty) (fun r v _ => decide (r = v))
    (fun n s => stateFits b.native n s b.native.base.rc (expectedMemsets b.state (project args)))
    noMatch (fun reason (_ : ResizeTerminal) => reason == "zeroing" && terminalFits) recorded
  return admitsMany (relation b.state args) (resizeOutcomes b.state (project args))
    (fun out => by rw [same]; exact resize_evaluated b.state (project args) out) fits
    (fun out => match out with
      | .returned value state => returnedJson (exceptJson programErrorJson (fun _ => Json.null)
        value) (stateJson state)
      | .unwound reason _ => nomatch reason
      | .terminated .zeroing => Json.mkObj [("exit", "terminated"), ("reason", "zeroing")])

def asRefCheck
    (contract : Solanalib.Contracts.Model AccountInfo.State Reference Reference)
    (sameRequires : ∀ s a, contract.requires s a = True)
    (model : AccountInfo.State → Reference → Reference × AccountInfo.State)
    (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state.borrow b.reference) := by
    rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state.borrow b.reference) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded (fun j => natField j "reference") nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty)
    (fun r v _ => r == v.id) (borrowFits b) noMatch noMatch recorded
  return admits (returnsOf model b.state.borrow b.reference) _
    (returnsOf_graph model b.state.borrow b.reference) fits
    (Info.renderOutcome (fun reference => Json.mkObj [("reference", reference.id)]) Info.stateJson)


def emptyComputed (state : AccountInfo.State) (args : AccountInfo.Args) :
    Option (Outcome AccountInfo.State Bool AccountInfo.Panic AccountInfo.Panic) :=
  match AccountInfo.observe .dataLen state args.info with
  | (.value value, after) => some (.returned (value == 0) after)
  | (.borrowFailed, after) =>
    some (if args.profile.aborts then .terminated .borrowFailed else .unwound .borrowFailed after)
  | (.malformed, _) => none

theorem empty_evaluated (state : AccountInfo.State) (args : AccountInfo.Args)
    (out : Outcome AccountInfo.State Bool AccountInfo.Panic AccountInfo.Panic) :
    dataIsEmptyReference state args out ↔ emptyComputed state args = some out := by
  unfold dataIsEmptyReference emptyComputed
  rcases AccountInfo.observe .dataLen state args.info with ⟨result, after⟩
  cases result with
  | value value => simp [eq_comm]
  | borrowFailed => cases args.profile.aborts <;> simp [eq_comm]
  | malformed => simp

def emptyCheck
    (contract : Solanalib.Contracts.Model AccountInfo.State AccountInfo.Args Bool AccountInfo.Panic
      AccountInfo.Panic)
    (sameRequires : ∀ s a, contract.requires s a = AccountInfo.ObservationReady .dataLen s a.info)
    (relation : AccountInfo.State → AccountInfo.Args → Outcome AccountInfo.State Bool
      AccountInfo.Panic AccountInfo.Panic → Prop)
    (same : relation = dataIsEmptyReference) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state.borrow b.args) := by rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state.borrow b.args) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded (·.getBool?) nativeOf c.outcome
  let fits := matchOutcome (fun r (v : Bool) _ => r == v) (borrowFits b) Info.panicOf Info.panicOf
    recorded
  return admits (relation b.state.borrow b.args) (emptyComputed b.state.borrow b.args)
    (fun out => by rw [same]; exact empty_evaluated b.state.borrow b.args out) fits
    (Info.renderOutcome (fun (v : Bool) => v) Info.stateJson)


end SolanalibTest.Conformance.Library.Families.SdkAccounts

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AccountInfoSdk
open SolanalibTest.Conformance.Library.Families.AccountsV1

def getterCheck (observation : AccountInfo.Observation)
    (contract : Solanalib.Contracts.Model AccountInfo.State AccountInfo.Args Nat AccountInfo.Panic
      AccountInfo.Panic)
    (sameRequires : ∀ s a, contract.requires s a = AccountInfo.ObservationReady observation s
      a.info)
    (relation : AccountInfo.State → AccountInfo.Args → Outcome AccountInfo.State Nat
      AccountInfo.Panic AccountInfo.Panic → Prop)
    (same : relation = AccountInfo.observeReference observation) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state.borrow b.args) := by rw [sameRequires]; infer_instance
  unless decide (contract.requires b.state.borrow b.args) do
    throw "the input is outside the registered precondition"
  validateBefore b
  let recorded ← parseRecorded (·.getNat?) nativeOf c.outcome
  let fits := matchOutcome (fun r (v : Nat) _ => r == v) (borrowFits b) Info.panicOf Info.panicOf
    recorded
  return admits (relation b.state.borrow b.args) (Info.observeComputed observation b.state.borrow
    b.args)
    (fun out => by rw [same]; exact Info.observe_evaluated observation b.state.borrow b.args out)
      fits
    (Info.renderOutcome (fun (v : Nat) => v) Info.stateJson)

def cloneCheck
    (relation : (AccountInfo.State × List Nat) → AccountInfo.Value →
      Outcome (AccountInfo.State × List Nat) AccountInfo.Value Empty Empty → Prop)
    (same : relation = Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_reference
      Info.cloneIndex)
    (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  validateBefore b
  let recorded ← parseRecorded Info.infoOf nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty) (fun r v (_ : AccountInfo.State × List Nat) =>
    decide (r = v))
    (fun n (s : AccountInfo.State × List Nat) => stateFits b.native n { b.state with borrow := s.1
      } s.2)
    noMatch noMatch recorded
  return admits (relation (b.state.borrow, b.native.base.rc) b.args.info) _
    (fun out => by
      rw [same]; exact Info.clone_evaluated (b.state.borrow, b.native.base.rc) b.args.info out) fits
    (Info.renderOutcome Info.infoJson (fun s => Json.mkObj [("borrow", Info.stateJson s.1), (
      "rc",
      toJson s.2)]))

end SolanalibTest.Conformance.Library.Families.SdkAccounts
