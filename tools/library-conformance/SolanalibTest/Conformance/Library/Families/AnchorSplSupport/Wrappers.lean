/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Values
import Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-!
Exact-source projected-wrapper conformance. The evaluator is the proved finite
graph of the registered mathematical run. It records a typed opaque invocation;
it never evaluates an invocation implementation. Native Rc multiplicity is
compared with the ordered clone/drop events of the same run, including duplicates.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport
open Solanalib.Specs.Core.AnchorSplSupport.Execution
open Solanalib.Specs.Core.AnchorSplSupport.Conformance

def script (json : Json) : Result Script := do
  match ← json.getStr? with
  | "ok" => pure .ok
  | "custom" => pure .custom
  | "borsh" => pure .borsh
  | "unwind" => pure .unwind
  | _ => throw "unknown whole-signature script"

private def numbers : List Nat := [1, 2, 3, 4, 5, 6, 7, 40, 41, 50]

/-- Each native fixture retains one outer owner; the passed values contribute
one Rc occurrence each. Equal remaining accounts are counted twice. -/
def passedOwners (operation : Operation) (custodian : Bool) : List AccountInfo.Value :=
  let args := nativeArgs operation custodian
  operation.owners args.context.accounts ++ [Sample.info 40, Sample.info 40, Sample.info 41] ++
    operation.profile.programOwners args.context.program ++
    match operation with
    | .withdraw => if custodian then [Sample.info 6] else []
    | _ => []

def initialCount (operation : Operation) (custodian : Bool) (cell : Borrow.Handle) : Int :=
  1 + ((passedOwners operation custodian).countP fun info =>
    info.lamports == cell || info.data == cell)

def countEvents (events : List Reference.Event) (cell : Borrow.Handle) (initial : Int) : Int :=
  events.foldl (fun count event => match event with
    | .cloneRc _ changed => if changed == cell then count + 1 else count
    | .dropRc _ changed => if changed == cell then count - 1 else count
    | _ => count) initial

def countsJson (operation : Operation) (custodian : Bool) (events : List Reference.Event) : Json :=
  Json.arr (numbers.map fun number => Json.mkObj [
    ("account", toJson number),
    ("lamports", toJson (countEvents events ⟨2 * number⟩ (initialCount operation custodian ⟨2 *
      number⟩))),
    ("data", toJson (countEvents events ⟨2 * number + 1⟩ (initialCount operation custodian ⟨2 *
      number + 1⟩)))]).toArray

def beforeJson (operation : Operation) (custodian : Bool) : Json :=
  Json.mkObj [("counts", countsJson operation custodian []), ("effect", toJson (0 : Nat))]

private def keyNumber (key : Solanalib.Runtime.Pubkey) : Nat := (key.bytes.getLastD 0).toNat

def infoJson (operation : Operation) (custodian : Bool) (events : List Reference.Event)
    (info : AccountInfo.Value) : Json := Json.mkObj [
  ("key", bytesJson info.key.bytes), ("owner", bytesJson info.owner.bytes),
  ("signer", Json.bool info.isSigner), ("writable", Json.bool info.isWritable),
  ("executable", Json.bool info.executable), ("abi_word", toJson info.unused.toNat),
  ("lamports_alias", toJson (keyNumber info.key)), ("data_alias", toJson (keyNumber info.key)),
  ("lamports_count", toJson (countEvents events info.lamports (initialCount operation custodian
    info.lamports))),
  ("data_count", toJson (countEvents events info.data (initialCount operation custodian
    info.data)))]

def instructionJson (instruction : Instruction.Value) : Json := Json.mkObj [
  ("program_id", bytesJson instruction.programId.bytes),
  ("metas", Json.arr (instruction.metas.map fun entry => Json.mkObj [
    ("key", bytesJson entry.key.bytes), ("signer", Json.bool (entry.signerByte != 0)),
    ("writable", Json.bool (entry.writableByte != 0))]).toArray),
  ("data", bytesJson instruction.data)]

def signersJson (signers : List (List Solanalib.Runtime.Bytes)) : Json :=
  Json.arr (signers.map fun signer => Json.arr (signer.map bytesJson).toArray).toArray

def requestJson (operation : Operation) (custodian : Bool) (events : List Reference.Event)
    (request : CpiRequest.Request AccountInfo.Value) : Json := Json.mkObj [
  ("instruction", instructionJson request.instruction),
  ("accounts", Json.arr (request.accounts.map (infoJson operation custodian events)).toArray),
  ("signers", signersJson request.signers)]

/-- Counts at invocation are derived from the event prefix at that call, not
from counts after cleanup. The source request is taken from the actual event. -/
def callsJson (operation : Operation) (custodian : Bool) (events : List Reference.Event) : Json :=
  Json.arr (events.foldl (fun (prior, calls) event =>
    (prior ++ [event], match event with
      | .invoke request => calls.push (requestJson operation custodian prior request)
      | _ => calls)) ([], #[])).2

def afterJson (operation : Operation) (custodian : Bool) (after : Reference.State) : Json :=
  Json.mkObj [("counts", countsJson operation custodian after.events),
    ("effect", toJson after.effect), ("calls", callsJson operation custodian after.events)]

def programJson (state : Reference.State) : ProgramErrorOwned.Value Nat → Json
  | .custom code => Json.mkObj [("kind", "custom"), ("value", toJson code.toNat)]
  | .borshIoError resource => Json.mkObj [("kind", "borsh"),
      ("value", (Reference.errors.currentString state resource).map Json.str |>.getD Json.null)]
  | _ => Json.str "unrecorded error variant"

def errorJson (profile : Profile) (state : Reference.State) (error : Error Reference.resources
  profile) : Json :=
  match AnchorErrorOperations.currentPayload profile.storage Reference.errors state error with
  | some (.program value) =>
      if value.origin.isNone && value.compared.isNone then
        Json.mkObj [("tag", "error"), ("program", programJson state value.error)]
      else Json.str "unexpected diagnostics"
  | _ => Json.str "missing current program-error payload"

def outcomeJson (operation : Operation) (custodian : Bool) :
    Outcome Reference.State (Except (Error Reference.resources operation.profile) Unit) String
      String → Json
  | .returned result after => returnedJson (match result with
      | .ok () => Json.mkObj [("tag", "ok")]
      | .error error => errorJson operation.profile after error) (afterJson operation custodian
        after)
  | .unwound reason after => Json.mkObj [
      ("exit", "unwound"), ("reason", reason), ("state", afterJson operation custodian after)]
  | .terminated reason => Json.mkObj [("exit", "terminated"), ("reason", reason)]

/-- Existential observation of a real finite native-model outcome. No state
component is supplied by the recorded output to force a desired execution. -/
def observed {S V U T : Type} (relation : Outcome S V U T → Prop)
    (render : Outcome S V U T → String) (recorded : String) : Prop :=
  ∃ outcome, relation outcome ∧ render outcome = recorded

theorem observed_iff {S V U T : Type} (relation : Outcome S V U T → Prop)
    (computed : Option (Outcome S V U T)) (graph : PGraph relation computed)
    (render : Outcome S V U T → String) (recorded : String) :
    observed relation render recorded ↔ computed.map render = some recorded := by
  constructor
  · rintro ⟨outcome, executed, rfl⟩
    simp [(graph outcome).mp executed]
  · intro same
    cases actual : computed with
    | none => simp [actual] at same
    | some outcome =>
      refine ⟨outcome, (graph outcome).mpr actual, ?_⟩
      simpa only [actual, Option.map_some, Option.some.injEq] using same

def operationName : Operation → String
  | .associated _ .create => "associated_create"
  | .associated _ .idempotent => "associated_idempotent"
  | .memo => "memo"
  | .metadata => "metadata"
  | .deactivate => "deactivate"
  | .withdraw => "withdraw"

/-- Every recorded script and custodian choice has the checked source-prefix
domain at the exact native fixture. This is not a universal admission theorem
for arbitrary vector stores or providers. -/
theorem wrapper_requires (operation : Operation)
    (contract : Solanalib.Contracts.Model Reference.State (Args Reference.resources operation)
      (Except (Error Reference.resources operation.profile) Unit) String String)
    (contract_eq : contract = (family operation).contract
      ⟨Reference.resources, Reference.invoke⟩)
    (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires contract (Sample.initial reply.reply)
      (nativeArgs operation custodian) := by
  rw [contract_eq]
  exact Reference.ready_of_checked operation _ _ (native_checked operation reply custodian)

/-- Decide the registered run and its real input domain at the fixed recorder
fixtures. Opaque errors and unwinds retain their actual finite after-state. -/
def wrapperChecker (operation : Operation) (function contractName runName : String)
    (contract : Solanalib.Contracts.Model Reference.State (Args Reference.resources operation)
      (Except (Error Reference.resources operation.profile) Unit) String String)
    (contract_eq : contract = (family operation).contract
      ⟨Reference.resources, Reference.invoke⟩)
    (relation : Run Reference.resources (Args Reference.resources operation)
      (Except (Error Reference.resources operation.profile) Unit))
    (evaluated : relation = run ⟨Reference.resources, Reference.invoke⟩ operation) : Checker where
  function := function
  generics := []
  reference := runName
  decides := [contractName, runName]
  decidesRequires := [contractName, runName]
  check := fun c => do
    let reply ← script (← field c.args "script")
    let custodian ← (← field c.args "custodian").getBool?
    unless (← field c.args "operation").getStr? == .ok (operationName operation) do
      throw "fixture operation disagrees with selected source"
    if operation.profile == .modern && reply == .borsh then
      throw "the modern ProgramError has no owned BorshIoError variant"
    let args := nativeArgs operation custodian
    unless (← field c.args "signers") == signersJson args.context.signerSeeds do
      throw "fixture signer seeds disagree with native setup"
    unless c.state == beforeJson operation custodian do
      throw "input Rc ownership disagrees with native setup"
    let before := Sample.initial reply.reply
    let computed := runFn Reference.functions operation before args
    have graph : PGraph (relation before args) computed := by
      rw [evaluated]
      exact run_graph Reference.functions Reference.graphs operation before args
    have required := wrapper_requires operation contract contract_eq reply custodian
    let _ : Decidable (Solanalib.Contracts.Model.requires contract before args) := isTrue required
    let _ : Decidable (observed (relation before args) (fun outcome => (outcomeJson operation
      custodian outcome).compress) c.outcome.compress) :=
      decidable_of_iff (computed.map (fun outcome => (outcomeJson operation custodian
        outcome).compress) = some c.outcome.compress)
        (observed_iff (relation before args) computed graph (fun outcome => (outcomeJson operation
          custodian outcome).compress) c.outcome.compress).symm
    pure ⟨decide (Solanalib.Contracts.Model.requires contract before args) &&
      decide (observed (relation before args) (fun outcome => (outcomeJson operation custodian
        outcome).compress) c.outcome.compress),
      (computed.map (outcomeJson operation custodian)).getD (Json.str "no finite model \
        outcome")⟩

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport
