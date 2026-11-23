/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.Borrow

/-!
# Shared deciders of family `AccountsV1`

The native state of an account record is a projection of the model state:
ghost components with no native counterpart (guard generations, owner-reference
epochs, entry lengths, the tombstones of released guards) are supplied by the
state before the call and forgotten in the state after it. A record is
therefore admitted when the registered relation admits **some** outcome that
the recorded native outcome matches (`fits`). For a reference whose graph is
a computed `Option` outcome (`graph`), this existential is decided by
evaluating the reference once (`admits_iff_graph`); every checker of the
family decides it through that lemma at the registered relation.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.AccountsV1

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Whether the computed outcome, if any, is matched. -/
def fitsSome {O : Type} (fits : O → Bool) : Option O → Bool
  | some c => fits c
  | none => false

/-- A relation whose admitted outcomes are exactly the computed one, if any:
the existential over outcomes matched by a record is the match of the
computed outcome. -/
theorem admits_iff_graph {O : Type} (relation : O → Prop) (computed : Option O)
    (graph : ∀ o, relation o ↔ computed = some o) (fits : O → Bool) :
    (∃ o, relation o ∧ fits o = true) ↔ fitsSome fits computed = true := by
  revert graph
  cases computed with
  | none => intro graph; simp [graph, fitsSome]
  | some c =>
    intro graph
    constructor
    · rintro ⟨o, ho, hm⟩
      rw [graph] at ho
      cases ho
      exact hm
    · intro hm
      exact ⟨c, (graph c).mpr rfl, hm⟩

/-- The decision of `∃ o, relation o ∧ fits o = true` obtained from the graph lemma of the
relation. -/
def admitsDecidable {O : Type} (relation : O → Prop) (computed : Option O)
    (graph : ∀ o, relation o ↔ computed = some o) (fits : O → Bool) :
    Decidable (∃ o, relation o ∧ fits o = true) :=
  decidable_of_iff _ (admits_iff_graph relation computed graph fits).symm

/-- The verdict on a record: the registered relation admits an outcome the
record matches. `expected` renders the computed outcome for the report. -/
def admits {O : Type} (relation : O → Prop) (computed : Option O)
    (graph : ∀ o, relation o ↔ computed = some o) (fits : O → Bool)
    (render : O → Json) : Verdict :=
  ⟨@decide (∃ o, relation o ∧ fits o = true) (admitsDecidable relation computed graph fits),
    match computed with | some c => render c | none => Json.str "no outcome"⟩

/-- The graph of a total reference, as a computed outcome. -/
theorem returnsOf_graph {S A V U T : Type} (run : S → A → V × S) (before : S) (args : A)
    (o : Outcome S V U T) :
    returnsOf run before args o ↔
      some (Outcome.returned (run before args).1 (run before args).2) = some o := by
  rw [returnsOf_iff, Option.some.injEq]

/-! ## Recorded outcomes -/

/-- A recorded outcome, with the value and state still in their native form. -/
inductive Recorded (RV RS : Type) where
  | returned (value : RV) (state : RS)
  | unwound (reason : String) (state : RS)
  | terminated (reason : String)

def parseRecorded {RV RS : Type} (value : Json → Result RV) (state : Json → Result RS) (j : Json) :
    Result (Recorded RV RS) := do
  match ← (← field j "exit").getStr? with
  | "returned" => return .returned (← value (← field j "result")) (← state (← field j
    "state"))
  | "unwound" => return .unwound (← (← field j "reason").getStr?) (← state (← field j
    "state"))
  | "terminated" => return .terminated (← (← field j "reason").getStr?)
  | other => throw s!"unknown exit {other}"

/-- A model outcome matches a recorded one when exits agree and value, reason
and state match; the state after a return and after an unwind may be compared
differently (`unwoundState`). -/
def matchOutcomeBy {S V U T RV RS : Type} (value : RV → V → S → Bool) (returnedState : RS → S →
  Bool)
    (unwoundState : RS → S → Bool) (unwind : String → U → Bool) (terminal : String → T → Bool) :
    Recorded RV RS → Outcome S V U T → Bool
  | .returned rv rs, .returned v s => value rv v s && returnedState rs s
  | .unwound rr rs, .unwound r s => unwind rr r && unwoundState rs s
  | .terminated rr, .terminated r => terminal rr r
  | _, _ => false

/-- `matchOutcomeBy` with one state comparison for both exits. -/
def matchOutcome {S V U T RV RS : Type} (value : RV → V → S → Bool) (state : RS → S → Bool)
    (unwind : String → U → Bool) (terminal : String → T → Bool) :
    Recorded RV RS → Outcome S V U T → Bool :=
  matchOutcomeBy value state state unwind terminal

def noMatch {α : Type} (_ : String) (_ : α) : Bool := false

/-! ## Native values -/

def natField (j : Json) (k : String) : Result Nat := do (← field j k).getNat?
def boolField (j : Json) (k : String) : Result Bool := do (← field j k).getBool?
def strField (j : Json) (k : String) : Result String := do (← field j k).getStr?
def arrField (j : Json) (k : String) : Result (List Json) := do return (← (← field j
  k).getArr?).toList

def pubkeyOf (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

def modeOf (s : String) : Result Borrow.Mode :=
  match s with
  | "shared" => pure .shared
  | "exclusive" => pure .exclusive
  | other => throw s!"unknown borrow mode {other}"

def modeJson : Borrow.Mode → Json
  | .shared => "shared"
  | .exclusive => "exclusive"

/-- A live guard object of the driver: its identity, the cell its lease is on,
its mode and its current target. -/
structure GuardEntry (View : Type) where
  id : Nat
  cell : Nat
  mode : Borrow.Mode
  view : View

/-- `{"id": i, …}` or, for consecutive identities with one target, `{"ids": [a, b], …}`. -/
def guardEntries {View : Type} (view : Json → Result View) (j : Json) : Result (List (GuardEntry
  View)) := do
  let cell ← natField j "cell"
  let mode ← modeOf (← strField j "mode")
  let v ← view (← field j "view")
  let ids ← match j.getObjVal? "id" with
    | .ok i => pure [← i.getNat?]
    | .error _ => do
      match ← arrField j "ids" with
      | [a, b] => do
        let a ← a.getNat?
        let b ← b.getNat?
        unless a ≤ b do throw "guard range out of order"
        pure (List.range' a (b + 1 - a))
      | _ => throw "guard range must have two ends"
  return ids.map fun id => ⟨id, cell, mode, v⟩

/-- The guard objects of a state; an identity names at most one object. -/
def guardsOf {View : Type} (view : Json → Result View) (j : Json) : Result (List (GuardEntry View))
  := do
  let entries ← arrField j "guards"
  let guards := (← entries.mapM (guardEntries view)).flatten
  unless (guards.map (·.id)).Nodup do throw "a guard identity is listed twice"
  return guards

/-- The slots of the state before: `slots` identities, live where a guard
object holds them (with its recorded generation), released otherwise. -/
def slotsOf {View : Type} (guards : List (GuardEntry View)) (count : Nat) (generations : List Nat) :
    Result (List (Option (Borrow.Slot View))) := do
  for g in guards do
    unless g.id < count do throw s!"guard {g.id} outside the {count} slots"
  return (List.range count).map fun i =>
    (guards.find? (·.id == i)).map fun g => ⟨⟨g.cell⟩, g.mode, generations.getD i 0, g.view⟩

/-- The identities of the live slots of a model state. -/
def liveIds {C View : Type} (s : Borrow.State C View) : List Nat :=
  (List.range s.slots.length).filter fun i => (s.lookupSlot i).isSome

/-- The recorded guard objects are live model slots with the same lease and
target, and every live model slot is held by a recorded object or is in
`consumed`: the guards the checked call takes without returning an object while
the model keeps their lease (the argument of an unwinding `Ref::map`). The
checker derives `consumed` from the call and its exit, never from the record;
such a lease then shows only in the borrow state of the cell. -/
def guardsMatch {C View : Type} [DecidableEq View] (guards : List (GuardEntry View)) (consumed :
  List Nat)
    (s : Borrow.State C View) : Bool :=
  guards.all (fun g => match s.lookupSlot g.id with
    | some slot => decide (slot.cell = ⟨g.cell⟩ ∧ slot.mode = g.mode ∧ slot.view = g.view)
    | none => false) &&
  (liveIds s).all fun i => guards.any (·.id == i) || consumed.contains i

def guardJson {View : Type} (view : View → Json) (id : Nat) (slot : Borrow.Slot View) : Json :=
  Json.mkObj [("id", id), ("cell", slot.cell.cell), ("mode", modeJson slot.mode), ("view", view
    slot.view)]

def liveSlotsJson {C View : Type} (view : View → Json) (s : Borrow.State C View) : Json :=
  Json.arr ((liveIds s).filterMap fun i => (s.lookupSlot i).map (guardJson view i)).toArray

end SolanalibTest.Conformance.Library.Families.AccountsV1
