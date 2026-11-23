/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.OwnedGraph
import SolanalibTest.Conformance.Library.Families.Anchor.World
import Solanalib.Specs.AnchorLang.error

/-!
# anchor-lang 1.0.2 error construction (`anchor_lang.error`)

Each record of `From<AnchorError>`, `with_pubkeys` and `with_values` is
decided against both registered models of the function: the primary owned
model at an index whose String/Box provider is the registered reference heap
`AnchorErrorOwned.Reference.ops` (resource identities and liveness observed
through the tracking allocator of the driver), and the value-level
`_observation` model. `with_values` takes two scripted operands
(`Operand`): their `Display` either returns a text or panics, and their
`Drop` may panic; the operands log both, so the order of conversions and
destructors is observed. The scripted callbacks below are the same scripts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor.Errors

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Anchor.Owned
open AnchorErrorOwned.Reference (StringId BoxId Failure)

abbrev Heap := AnchorErrorOwned.Reference.State

/-! ## Shared parsing and verdicts -/

/-- Combine the verdicts of the primary and the observation model. -/
def both (owned observation : Verdict) : Verdict :=
  ⟨owned.admitted && observation.admitted,
    Json.mkObj [("model", owned.expected), ("observation_model", observation.expected)]⟩

def renderOpt {α : Type} (render : α → Json) : Option α → Json
  | none => Json.str "<no outcome>"
  | some a => render a

def outcomeJson {S V U T : Type} (state : S → Json) (value : V → Json) (unwind : U → Json)
    (terminal : T → Json) : Outcome S V U T → Json
  | .returned v s => returnedJson (value v) (state s)
  | .unwound r s => Json.mkObj [("exit", "unwound"), ("reason", unwind r), ("state", state s)]
  | .terminated r => Json.mkObj [("exit", "terminated"), ("reason", terminal r)]

def emptyJson : Empty → Json := fun e => nomatch e

/-- Decide a relation registered as `returnsOf model` (by `rfl`) on an optional outcome. -/
def decideRet {S A V : Type} [DecidableEq S] [DecidableEq V]
    (relation : S → A → Outcome S V Empty Empty → Prop) (model : S → A → V × S)
    (evaluated : relation = returnsOf model) (before : S) (args : A)
    (recorded : Option (Outcome S V Empty Empty)) (render : Outcome S V Empty Empty → Json) :
      Verdict :=
  let computed : Outcome S V Empty Empty := .returned (model before args).1 (model before args).2
  match recorded with
  | some o =>
    have : Decidable (relation before args o) := by
      rw [evaluated]; exact instDecidableReturnsOf model before args o
    ⟨decide (relation before args o), render computed⟩
  | none => ⟨false, render computed⟩

/-- Project an owned-error outcome to its observation. -/
def projectError {U T : Type} (nStrings nBoxes : Nat) :
    Outcome Heap (AnchorErrorOwned.Error BoxId) U T → Outcome HeapObs ErrorObs U T
  | .returned e s => .returned (observeError nStrings nBoxes s e) (observeHeap nStrings nBoxes s)
  | .unwound r s => .unwound r (observeHeap nStrings nBoxes s)
  | .terminated t => .terminated t

def failureJson : Failure → Json
  | .allocation .name => "allocation name"
  | .allocation .message => "allocation message"
  | .allocation .box => "allocation box"

def heapOutcomeJson : Outcome HeapObs ErrorObs Empty Failure → Json :=
  outcomeJson heapObsJson errorObsJson emptyJson failureJson

def valueOutcomeJson : Outcome Unit ErrorValue Empty Empty → Json :=
  outcomeJson (fun _ => .null) errorValueJson emptyJson emptyJson

/-- The outcome of the observation model is the observed value of the recorded result. -/
def valueOutcome {U T : Type} : Outcome HeapObs ErrorObs U T → Option (Outcome Unit ErrorValue
  Empty Empty)
  | .returned r _ => r.value.map fun v => .returned v ()
  | _ => none

def boxArg (j : Json) : Result (AnchorErrorOwned.Error BoxId) := do pure ⟨⟨← j.getNat?⟩⟩

def inputCounts (heap : Heap) : Nat × Nat := (heap.strings.length, heap.boxes.length)

/-! ## `From<AnchorError>` -/

def fromAnchorRel := Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_run
  Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_sample

theorem fromAnchor_graph (heap : Heap) (payload : AnchorErrorOwned.AnchorPayload StringId) :
    PGraph (fromAnchorRel heap payload) (OwnedFn.fromAnchorFn RefFn.fn heap payload) :=
  OwnedFn.fromAnchor_graph RefFn.graph heap payload

def fromAnchorChecker : Checker := ofModels
  ("<anchor_lang::error::Error as \
    core::convert::From<anchor_lang::error::AnchorError>>::from") ([])
  ("Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_run (index \
    from_anchor_error_sample) " ++
    "+ Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_observation_run (State := \
      Unit)")
  ["Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_run",
    "Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_observation_run"]
  fun c => do
    let heap ← asHeap c.state
    let (ns, nb) := inputCounts heap
    let payload ← match ← asPayload (← field c.args "error") with
      | .anchor p => pure p
      | .program _ => throw "From<AnchorError> takes an AnchorError"
    let recorded ← parseOutcome asErrorObs asHeapObs noReason noReason c.outcome
    let owned := decideProjected (fromAnchorRel heap payload) _ (fromAnchor_graph heap payload)
      (projectError (U := Empty) (T := Failure) ns nb) recorded (renderOpt heapOutcomeJson)
    let value ← resolve heap (.anchor payload)
    let anchorValue ← match value with
      | .anchor v => pure v
      | .program _ => throw "unreachable"
    let observation := decideRet (S := Unit) (V := ErrorValue)
      (Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_observation_run Unit)
      AnchorError.fromAnchorReference rfl () anchorValue (recorded.bind valueOutcome)
        valueOutcomeJson
    return [owned, observation]

/-! ## `with_pubkeys` -/

def withPubkeysRel := Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_run
  Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_sample

theorem withPubkeys_graph (heap : Heap) (args : AnchorErrorOwned.Error BoxId ×
  Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey) :
    PGraph (withPubkeysRel heap args) (OwnedFn.withPubkeysFn RefFn.fn
      AnchorErrorOwned.Reference.ops heap args) :=
  OwnedFn.withPubkeys_graph RefFn.graph heap args

def withPubkeysChecker : Checker := ofModels ("anchor_lang::error::Error::with_pubkeys") ([])
  ("Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_run (index with_pubkeys_sample) " ++
    "+ Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_observation_run (State := Unit)")
  ["Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_run",
    "Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_observation_run"]
  fun c => do
    let heap ← asHeap c.state
    let (ns, nb) := inputCounts heap
    let error ← boxArg (← field c.args "error")
    let left ← keyField c.args "left"
    let right ← keyField c.args "right"
    let recorded ← parseOutcome asErrorObs asHeapObs noReason noReason c.outcome
    let owned := decideProjected (withPubkeysRel heap (error, left, right)) _
      (withPubkeys_graph heap (error, left, right)) (projectError (U := Empty) (T := Failure) ns
        nb) recorded (renderOpt heapOutcomeJson)
    let value ← match heap.boxes[error.resource.index]? with
      | some (some p) => resolve heap p
      | _ => throw "with_pubkeys receiver is not an input Box"
    let observation := decideRet (S := Unit) (V := ErrorValue)
      (Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_observation_run Unit)
      AnchorError.withPubkeysReference rfl () ⟨value, left, right⟩ (recorded.bind valueOutcome)
      valueOutcomeJson
    return [owned, observation]

/-! ## `with_values` with scripted operands -/

/-- A scripted `impl ToString` operand: `Display` writes `text` or, if it is
`none`, panics with `"display <tag>"`; `Drop` panics with `"drop <tag>"` iff
`dropPanics`. Both are logged. -/
structure Operand where
  tag : String
  text : Option String
  dropPanics : Bool
  deriving DecidableEq

inductive OpEvent where
  | display (tag : String)
  | drop (tag : String)
  deriving DecidableEq

def asOperand (j : Json) : Result Operand := do
  pure ⟨← strField j "tag", ← asOption (fun x => x.getStr?) (← field j "text"), ← boolField j
    "drop_panics"⟩

def asOpEvent (j : Json) : Result OpEvent := do
  let (k, v) ← asTagged j
  match k with
  | "display" => pure (.display (← v.getStr?))
  | "drop" => pure (.drop (← v.getStr?))
  | other => throw s!"unknown operand event {other}"

def opEventJson : OpEvent → Json
  | .display t => tagged "display" t
  | .drop t => tagged "drop" t

def displayReason (op : Operand) : String := "display " ++ op.tag
def dropReason (op : Operand) : String := "drop " ++ op.tag

/-! ### Observation model -/

abbrev Log := List OpEvent

def display (log : Log) (op : Operand) : Outcome Log String String Unit :=
  match op.text with
  | some t => .returned t (log ++ [.display op.tag])
  | none => .unwound (displayReason op) (log ++ [.display op.tag])

/-- Dropping the operand tuple: the second field is still dropped while the
a panic in the first field unwinds; a panic during that unwind aborts. -/
def dropTuple (log : Log) (l r : Operand) : Outcome Log Unit String Unit :=
  let after := log ++ [.drop l.tag, .drop r.tag]
  if l.dropPanics then (if r.dropPanics then .terminated () else .unwound (dropReason l) after)
  else if r.dropPanics then .unwound (dropReason r) after else .returned () after

/-- The same drops while a conversion panic unwinds: any destructor panic aborts. -/
def dropTupleUnwinding (log : Log) (l r : Operand) : Outcome Log Unit Empty Unit :=
  if l.dropPanics || r.dropPanics then .terminated () else .returned () (log ++ [.drop l.tag, .drop
    r.tag])

def obsCallbacks : AnchorError.ValuesCallbacks Log ProgramError.Value Operand Operand String Unit
  where
  left := Callback.ofFunction display
  right := Callback.ofFunction display
  normalCleanup := Callback.ofFunction fun log args => dropTuple log args.values.left
    args.values.right
  unwindCleanup := Callback.ofFunction fun log args => dropTupleUnwinding log args.values.left
    args.values.right

def obsIndex : Solanalib.Specs.AnchorLang.error.Error.with_values_observation_family.Index :=
  ⟨Log, Operand, Operand, String, Unit, obsCallbacks⟩

/-- The `ValuesRun` reference relation, computed for function callbacks. -/
def valuesFn {S PE L R U T : Type}
    (left : S → L → Outcome S String U T) (right : S → R → Outcome S String U T)
    (normal : S → AnchorError.NormalCleanupArgs PE L R → Outcome S Unit U T)
    (unwind : S → AnchorError.UnwindCleanupArgs PE L R U → Outcome S Unit Empty T)
    (before : S) (args : AnchorError.ValuesArgs PE L R) : Outcome S (AnchorError.Value PE) U T :=
  match left before args.left with
  | .returned lt middle =>
    match right middle args.right with
    | .returned rt actual =>
      match normal actual ⟨args, lt, rt⟩ with
      | .returned () after => .returned (args.error.replaceCompared (.values lt rt)) after
      | .unwound r after => .unwound r after
      | .terminated t => .terminated t
    | .unwound r actual =>
      match unwind actual ⟨args, r, some lt⟩ with
      | .returned () after => .unwound r after
      | .unwound e _ => nomatch e
      | .terminated t => .terminated t
    | .terminated t => .terminated t
  | .unwound r actual =>
    match unwind actual ⟨args, r, none⟩ with
    | .returned () after => .unwound r after
    | .unwound e _ => nomatch e
    | .terminated t => .terminated t
  | .terminated t => .terminated t

theorem valuesRun_graph {S PE L R U T : Type}
    (left : S → L → Outcome S String U T) (right : S → R → Outcome S String U T)
    (normal : S → AnchorError.NormalCleanupArgs PE L R → Outcome S Unit U T)
    (unwind : S → AnchorError.UnwindCleanupArgs PE L R U → Outcome S Unit Empty T)
    (before : S) (args : AnchorError.ValuesArgs PE L R) :
    PGraph (AnchorError.ValuesRun ⟨Callback.ofFunction left, Callback.ofFunction right,
        Callback.ofFunction normal, Callback.ofFunction unwind⟩ before args)
      (some (valuesFn left right normal unwind before args)) := by
  intro o
  constructor
  · intro run
    cases run with
    | returned hl hr hc =>
      simp only [Callback.ofFunction] at hl hr hc
      simp only [valuesFn, hl, hr, hc]
    | cleanupUnwound hl hr hc =>
      simp only [Callback.ofFunction] at hl hr hc
      simp only [valuesFn, hl, hr, hc]
    | cleanupTerminated hl hr hc =>
      simp only [Callback.ofFunction] at hl hr hc
      simp only [valuesFn, hl, hr, hc]
    | leftUnwound hl hc =>
      simp only [Callback.ofFunction] at hl hc
      simp only [valuesFn, hl, hc]
    | leftCleanupTerminated hl hc =>
      simp only [Callback.ofFunction] at hl hc
      simp only [valuesFn, hl, hc]
    | leftTerminated hl =>
      simp only [Callback.ofFunction] at hl
      simp only [valuesFn, hl]
    | rightUnwound hl hr hc =>
      simp only [Callback.ofFunction] at hl hr hc
      simp only [valuesFn, hl, hr, hc]
    | rightCleanupTerminated hl hr hc =>
      simp only [Callback.ofFunction] at hl hr hc
      simp only [valuesFn, hl, hr, hc]
    | rightTerminated hl hr =>
      simp only [Callback.ofFunction] at hl hr
      simp only [valuesFn, hl, hr]
  · intro h
    have h' : valuesFn left right normal unwind before args = o := Option.some.inj h
    subst h'
    cases hl : left before args.left with
    | returned lt middle =>
      cases hr : right middle args.right with
      | returned rt actual =>
        cases hc : normal actual ⟨args, lt, rt⟩ with
        | returned u after =>
          cases u; simp only [valuesFn, hl, hr, hc]; apply AnchorError.ValuesRun.returned <;>
            assumption
        | unwound r after =>
          simp only [valuesFn, hl, hr, hc]; apply AnchorError.ValuesRun.cleanupUnwound <;>
            assumption
        | terminated t =>
          simp only [valuesFn, hl, hr, hc]; apply AnchorError.ValuesRun.cleanupTerminated <;>
            assumption
      | unwound r actual =>
        cases hc : unwind actual ⟨args, r, some lt⟩ with
        | returned u after =>
          cases u; simp only [valuesFn, hl, hr, hc]; apply AnchorError.ValuesRun.rightUnwound <;>
            assumption
        | unwound e _ => exact nomatch e
        | terminated t =>
          simp only [valuesFn, hl, hr, hc]; apply AnchorError.ValuesRun.rightCleanupTerminated <;>
            assumption
      | terminated t =>
        simp only [valuesFn, hl, hr]; apply AnchorError.ValuesRun.rightTerminated <;> assumption
    | unwound r actual =>
      cases hc : unwind actual ⟨args, r, none⟩ with
      | returned u after =>
        cases u; simp only [valuesFn, hl, hc]; apply AnchorError.ValuesRun.leftUnwound <;>
          assumption
      | unwound e _ => exact nomatch e
      | terminated t =>
        simp only [valuesFn, hl, hc]; apply AnchorError.ValuesRun.leftCleanupTerminated <;>
          assumption
    | terminated t =>
      simp only [valuesFn, hl]; apply AnchorError.ValuesRun.leftTerminated; assumption

/-! ### Primary owned model -/

abbrev World := Heap × Log

def ownedOps : AnchorErrorOwned.Ops World StringId BoxId Failure :=
  AnchorErrorOwned.Reference.ops.focus Owned.Focus.fst

def ownedFn : OpsFn World StringId BoxId Failure := RefFn.fn.focus Owned.Focus.fst

theorem ownedGraph : OpsGraph ownedOps ownedFn := RefFn.graph.focus Owned.Focus.fst

/-- `to_string` allocates the returned String in the heap. -/
def displayOwned (state : World) (op : Operand) : Outcome World StringId String Failure :=
  let log := state.2 ++ [.display op.tag]
  match op.text with
  | some t =>
    match AnchorErrorOwned.Reference.allocateString true state.1 t with
    | .returned id heap => .returned id (heap, log)
    | .unwound e _ => nomatch e
    | .terminated f => .terminated f
  | none => .unwound (displayReason op) (state.1, log)

def dropOwned (state : World) (op : Operand) : Outcome World Unit String Failure :=
  let after := (state.1, state.2 ++ [.drop op.tag])
  if op.dropPanics then .unwound (dropReason op) after else .returned () after

def ownedCallbacks : AnchorErrorOwned.ValuesCallbacks World StringId Operand Operand String Failure
  where
  left := Callback.ofFunction displayOwned
  right := Callback.ofFunction displayOwned
  dropLeft := Callback.ofFunction dropOwned
  dropRight := Callback.ofFunction dropOwned
  double := fun _ _ _ _ => False

def ownedIndex : Solanalib.Specs.AnchorLang.error.Error.with_values_contract.Index where
  base := ⟨World, StringId, BoxId, Failure, ownedOps⟩
  Left := Operand
  Right := Operand
  Unwind := String
  callbacks := ownedCallbacks

def noDoubleFn : World → String → String → Option Failure := fun _ _ _ => none

theorem double_graph : ∀ s r r', PGraph (ownedCallbacks.double s r r') (noDoubleFn s r r') :=
  fun _ _ _ => PGraph.false

open AnchorErrorOwned in
def replaceValuesFn (before : World) (args : Error BoxId × StringId × StringId) :
    Option (Outcome World (Error BoxId) Empty Failure) :=
  (ownedOps.currentBox before args.1.resource).bind fun payload =>
    (OwnedFn.dropStringsFn ownedFn (comparedStrings payload.compared) before).bind
      (PGraph.bindK fun _ afterDrops =>
        (ownedOps.currentBox afterDrops args.1.resource).bind fun actual =>
          (ownedOps.writeBox afterDrops args.1.resource (actual.withValues args.2.1 args.2.2)).bind
            fun after => some (.returned args.1 after))

open AnchorErrorOwned in
theorem replaceValues_graph (before : World) (args : Error BoxId × StringId × StringId) :
    PGraph (replaceValues ownedOps before args) (replaceValuesFn before args) := by
  obtain ⟨error, left, right⟩ := args
  apply PGraph.exists_step (PGraph.ofOption _)
  intro payload
  apply PGraph.bind (OwnedFn.dropStrings_graph ownedGraph _ before)
  intro _ afterDrops
  apply PGraph.exists_step (PGraph.ofOption _)
  intro actual
  apply PGraph.exists_step (PGraph.ofOption _)
  intro after
  exact PGraph.eq_left _

open AnchorErrorOwned in
def bodyFn (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) (before : World) :
    Option (Outcome World (Error BoxId) String Failure) :=
  (some (displayOwned before args.left)).bind (PGraph.bindK fun left middle =>
    ((some (displayOwned middle args.right)).bind
      (PGraph.onUnwindFn noDoubleFn [fun s => (ownedFn.dropString s left).map OwnedFn.liftO])).bind
      (PGraph.bindK fun right actual =>
        (replaceValuesFn actual (args.error, left, right)).map OwnedFn.liftO))

open AnchorErrorOwned in
theorem body_graph (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) (before : World) :
    PGraph (valuesBody ownedOps ownedCallbacks args before ()) (bodyFn args before) := by
  apply PGraph.bind (PGraph.ofFunction displayOwned before args.left)
  intro left middle
  apply PGraph.bind
  · exact PGraph.protect double_graph
      (PGraph.DropsGraph.cons (fun s => OwnedFn.lift_graph (ownedGraph.dropString s left))
        PGraph.DropsGraph.nil)
      (PGraph.ofFunction displayOwned middle args.right)
  · intro right actual
    exact OwnedFn.lift_graph (replaceValues_graph actual _)

open AnchorErrorOwned in
/-- The protected scope (release on every unwind). -/
def protectedFn (before : World) (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) :
    Option (Outcome World (Error BoxId) String Failure) :=
  ((bodyFn args before).bind (PGraph.cleanupFn noDoubleFn
      [fun s => some (dropOwned s args.left), fun s => some (dropOwned s args.right)])).bind
    (PGraph.onUnwindFn noDoubleFn [fun s => (OwnedFn.dropErrorFn ownedFn ownedOps args.error s).map
      OwnedFn.liftO])

open AnchorErrorOwned in
/-- The rust-lang/rust#47949 alternative: a normal body, then an unwinding
operand cleanup that leaves the receiver live. -/
def leakFn (before : World) (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) :
    Option (Outcome World (Error BoxId) String Failure) :=
  (bodyFn args before).bind fun pending => match pending with
    | .returned value returned =>
      (PGraph.cleanupFn noDoubleFn [fun s => some (dropOwned s args.left), fun s => some (dropOwned
        s args.right)]
        (.returned value returned)).bind fun cleaned => match cleaned with
        | .unwound reason after => some (.unwound reason after)
        | _ => none
    | _ => none

/-- Both alternatives (the second only on the return-place path). -/
def withValuesOutcomes (before : World) (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) :
    List (Outcome World (AnchorErrorOwned.Error BoxId) String Failure) :=
  (ownedOps.currentBox before args.error.resource).toList.flatMap fun _ =>
    (protectedFn before args).toList ++ (leakFn before args).toList

def withValuesRel := Solanalib.Specs.AnchorLang.error.Error.with_values_run ownedIndex

open AnchorErrorOwned in
theorem locals_graph (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) :
    PGraph.DropsGraph
      [fun state result => ownedCallbacks.dropLeft state args.left result,
       fun state result => ownedCallbacks.dropRight state args.right result]
      [fun s => some (dropOwned s args.left), fun s => some (dropOwned s args.right)] :=
  PGraph.DropsGraph.cons (d := fun state result => ownedCallbacks.dropLeft state args.left result)
    (fun s => PGraph.ofFunction dropOwned s args.left)
    (PGraph.DropsGraph.cons (d := fun state result => ownedCallbacks.dropRight state args.right
      result)
      (fun s => PGraph.ofFunction dropOwned s args.right) PGraph.DropsGraph.nil)

open AnchorErrorOwned in
theorem leak_graph (before : World) (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) :
    PGraph (fun final => ∃ value returned,
        valuesBody ownedOps ownedCallbacks args before () (.returned value returned) ∧
        ∃ reason after, Owned.cleanup ownedCallbacks.double
            [fun state result => ownedCallbacks.dropLeft state args.left result,
             fun state result => ownedCallbacks.dropRight state args.right result]
            (.returned value returned) (.unwound reason after) ∧
          final = .unwound reason after)
      (leakFn before args) := by
  intro o
  unfold leakFn
  constructor
  · rintro ⟨value, returned, called, reason, after, cleaned, rfl⟩
    rw [(body_graph args before _).mp called]
    show (PGraph.cleanupFn noDoubleFn _ (.returned value returned)).bind _ = _
    rw [(PGraph.cleanup double_graph _ _ (locals_graph args) _ _).mp cleaned]
    rfl
  · intro h
    cases hb : bodyFn args before with
    | none => rw [hb] at h; cases h
    | some pending =>
      rw [hb] at h
      cases pending with
      | unwound _ _ | terminated _ => cases h
      | returned value returned =>
        cases hc : PGraph.cleanupFn noDoubleFn
            [fun s => some (dropOwned s args.left), fun s => some (dropOwned s args.right)]
            (.returned value returned) with
        | none => simp only [hc, Option.bind] at h; cases h
        | some cleaned =>
          simp only [hc, Option.bind] at h
          cases cleaned with
          | returned _ _ | terminated _ => cases h
          | unwound reason after =>
            cases h
            exact ⟨value, returned, (body_graph args before _).mpr hb, reason, after,
              (PGraph.cleanup double_graph _ _ (locals_graph args) _ _).mpr hc, rfl⟩

open AnchorErrorOwned in
theorem withValues_graph (before : World) (args : AnchorErrorOwned.ValuesArgs BoxId Operand
  Operand) :
    LGraph (withValuesRel before args) (withValuesOutcomes before args) := by
  apply LGraph.exists_step (PGraph.ofOption _)
  intro payload
  apply LGraph.or
  · exact LGraph.ofPGraph (PGraph.protect double_graph
      (PGraph.DropsGraph.cons (d := AnchorErrorOwned.dropErrorLift ownedOps args.error)
        (fun s => OwnedFn.lift_graph (OwnedFn.dropError_graph ownedGraph args.error s))
          PGraph.DropsGraph.nil)
      (PGraph.scope double_graph (locals_graph args) (body_graph args before)))
  · exact LGraph.ofPGraph (leak_graph before args)

/-! ### Checker -/

def projectWorld (nStrings nBoxes : Nat) :
    Outcome World (AnchorErrorOwned.Error BoxId) String Failure → Outcome (HeapObs × Log) ErrorObs
      String Failure
  | .returned e s => .returned (observeError nStrings nBoxes s.1 e) (observeHeap nStrings nBoxes
    s.1, s.2)
  | .unwound r s => .unwound r (observeHeap nStrings nBoxes s.1, s.2)
  | .terminated t => .terminated t

def asWorldObs (j : Json) : Result (HeapObs × Log) := do
  pure (← asHeapObs j, ← asList asOpEvent (← field j "log"))

def worldObsJson (o : HeapObs × Log) : Json :=
  Json.mkObj [("heap", heapObsJson o.1), ("log", listJson opEventJson o.2)]

def ownedOutcomeJson : Outcome (HeapObs × Log) ErrorObs String Failure → Json :=
  outcomeJson worldObsJson errorObsJson (fun r => Json.str r) failureJson

def obsOutcomeJson : Outcome Log ErrorValue String Unit → Json :=
  outcomeJson (listJson opEventJson) errorValueJson (fun r => Json.str r) (fun _ => "abort")

def observationOutcome :
    Outcome (HeapObs × Log) ErrorObs String Failure → Option (Outcome Log ErrorValue String Unit)
  | .returned r s => r.value.map fun v => .returned v s.2
  | .unwound r s => some (.unwound r s.2)
  | .terminated _ => none

def withValuesChecker : Checker := ofModels ("anchor_lang::error::Error::with_values")
  ([("impl ToString (0)", "conformance_anchor::errors::Operand"),
    ("impl ToString (1)", "conformance_anchor::errors::Operand")])
  ("Solanalib.Specs.AnchorLang.error.Error.with_values_run (scripted operands, reference \
    heap) " ++
    "+ Solanalib.Specs.AnchorLang.error.Error.with_values_observation_run (scripted \
      operands)")
  ["Solanalib.Specs.AnchorLang.error.Error.with_values_run",
    "Solanalib.Specs.AnchorLang.error.Error.with_values_observation_run"]
  fun c => do
    let heap ← asHeap c.state
    let log ← asList asOpEvent (← field c.state "log")
    let (ns, nb) := inputCounts heap
    let error ← boxArg (← field c.args "error")
    let left ← asOperand (← field c.args "left")
    let right ← asOperand (← field c.args "right")
    let recorded ← parseOutcome asErrorObs asWorldObs (fun r => some r) noReason c.outcome
    let args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand := ⟨error, left, right⟩
    let owned := decideProjectedList (withValuesRel (heap, log) args) _ (withValues_graph (heap,
      log) args)
      (projectWorld ns nb) recorded (fun os => listJson ownedOutcomeJson os)
    let value ← match heap.boxes[error.resource.index]? with
      | some (some p) => resolve heap p
      | _ => throw "with_values receiver is not an input Box"
    let obsArgs : AnchorError.ValuesArgs ProgramError.Value Operand Operand := ⟨value, left, right⟩
    let obsRel := Solanalib.Specs.AnchorLang.error.Error.with_values_observation_run obsIndex log
      obsArgs
    let observation := decideProjected (O := Outcome Log ErrorValue String Unit)
      (P := Outcome Log ErrorValue String Unit) obsRel _
      (valuesRun_graph display display (fun l a => dropTuple l a.values.left a.values.right)
        (fun l a => dropTupleUnwinding l a.values.left a.values.right) log obsArgs)
      id (recorded.bind observationOutcome) (renderOpt obsOutcomeJson)
    return [owned, observation]

def checkers : List Checker :=
  [fromAnchorChecker, withPubkeysChecker, withValuesChecker].map (withFrame [("no syscalls",
    noSyscalls)])

end SolanalibTest.Conformance.Library.Families.Anchor.Errors
