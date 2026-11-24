/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Errors
import SolanalibTest.Conformance.Library.Families.Anchor.Decide

/-!
# Preconditions of the owned error models

* `From<AnchorError>` (`from_anchor_error_sample`): `BoxingLaws ∧ Payload.Ready`.
* `with_pubkeys` (`with_pubkeys_sample`): `ComparisonLaws ∧ Ready ∧ ComparisonStoreReady`.
* `with_values` (the scripted index): `ComparisonLaws ∧ Ready ∧ CallReady`.

The laws and the store readiness hold for the reference heap (`Reference.ops_laws`,
`Ops.focus_laws`, `ComparisonStoreReady.of_available`); `CallReady` follows
from `Ready` for the scripted operands (`callReady_of_ready`: a conversion
allocates a fresh String and leaves every other resource unchanged, an operand
drop changes no resource). So each `requires` is equivalent to `Ready`
(`Payload.Ready`: distinct live Strings), which `readyB` decides.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace SolanalibTest.Conformance.Library.Families.Anchor.RequiresErrors

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorErrorOwned
open SolanalibTest.Conformance.Library.Families.Anchor.Errors
open AnchorErrorOwned.Reference (StringId BoxId)

/-! ## `Payload.Ready` and `Ready` -/

def payloadReadyB {S Str Box T : Type} [DecidableEq Str] (ops : Ops S Str Box T) (state : S)
    (payload : Payload Str) : Bool :=
  decide payload.strings.Nodup && payload.strings.all fun r => (ops.currentString state r).isSome

theorem payloadReadyB_iff {S Str Box T : Type} [DecidableEq Str] (ops : Ops S Str Box T) (state : S)
    (payload : Payload Str) : payloadReadyB ops state payload = true ↔ payload.Ready ops state := by
  unfold payloadReadyB Payload.Ready
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Option.isSome_iff_exists]

def readyB {S Str Box T : Type} [DecidableEq Str] (ops : Ops S Str Box T) (state : S) (error :
  Error Box) : Bool :=
  match ops.currentBox state error.resource with
  | some payload => payloadReadyB ops state payload
  | none => false

theorem readyB_iff {S Str Box T : Type} [DecidableEq Str] (ops : Ops S Str Box T) (state : S)
  (error : Error Box) :
    readyB ops state error = true ↔ Ready ops state error := by
  unfold readyB Ready
  cases h : ops.currentBox state error.resource with
  | none => simp
  | some payload =>
    rw [payloadReadyB_iff]
    exact ⟨fun r => ⟨payload, rfl, r⟩, fun ⟨p, e, r⟩ => by cases e; exact r⟩

/-! ## Laws of the reference heap -/

theorem boxing : Reference.ops.BoxingLaws :=
  ⟨Reference.ops_laws.box.current, Reference.ops_laws.box.fresh, Reference.ops_laws.box_strings⟩

theorem comparison : Reference.ops.ComparisonLaws :=
  ⟨Reference.ops_laws.stringDrop.other, Reference.ops_laws.drop_boxes,
    Reference.ops_laws.store.current,
    Reference.ops_laws.store_strings⟩

theorem ownedLaws : ownedOps.Laws := Reference.ops.focus_laws Reference.ops_laws Owned.Focus.fst

theorem ownedComparison : ownedOps.ComparisonLaws :=
  ⟨ownedLaws.stringDrop.other, ownedLaws.drop_boxes, ownedLaws.store.current,
    ownedLaws.store_strings⟩

/-! ## `From<AnchorError>` and `with_pubkeys` -/

theorem fromAnchor_requires_iff (heap : Heap) (payload : AnchorPayload StringId) :
    (Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_contract.contract
        Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_sample).requires heap payload ↔
      payloadReadyB Reference.ops heap (.anchor payload) = true := by
  rw [payloadReadyB_iff]
  exact ⟨fun h => h.2, fun h => ⟨boxing, h⟩⟩

theorem withPubkeys_requires_iff (heap : Heap) (args : Error BoxId × Solanalib.Runtime.Pubkey ×
  Solanalib.Runtime.Pubkey) :
    (Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_contract.contract
        Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_sample).requires heap args ↔
      readyB Reference.ops heap args.1 = true := by
  rw [readyB_iff]
  exact ⟨fun h => h.2.1, fun h => ⟨comparison, h,
    ComparisonStoreReady.of_available Reference.ops Reference.ops_laws.drop_boxes
      Reference.ops_laws.store.available _ _ _⟩⟩

/-! ## `with_values`: the scripted operands satisfy every callback frame -/

theorem currentString_append (heap : Heap) (text : String) (r : StringId) (h : r.index <
  heap.strings.length) :
    Reference.currentString ⟨heap.strings ++ [some text], heap.boxes, heap.remaining - 1,
      heap.events ++ [.message ⟨heap.strings.length⟩ text]⟩ r =
      Reference.currentString heap r := by
  simp [Reference.currentString, List.getElem?_append_left h]

theorem index_lt_of_live {heap : Heap} {r : StringId} {text : String}
    (h : Reference.currentString heap r = some text) : r.index < heap.strings.length := by
  unfold Reference.currentString at h
  rcases Nat.lt_or_ge r.index heap.strings.length with lt | ge
  · exact lt
  · rw [List.getElem?_eq_none ge] at h
    cases h

/-- Every exit of a conversion frames the held error and live Strings. -/
theorem display_frame (state : World) (op : Operand) (error : Error BoxId) (strings : List StringId)
    (live : ∀ r ∈ strings, ∃ text, ownedOps.currentString state r = some text) :
    StringFrame ownedOps error strings state (displayOwned state op) := by
  unfold displayOwned
  cases ht : op.text with
  | none =>
    exact ⟨rfl, fun _ _ => rfl⟩
  | some t =>
    dsimp only
    unfold Reference.allocateString
    by_cases zero : state.1.remaining = 0
    · simp only [zero, ↓reduceIte]
      trivial
    · simp only [zero, ↓reduceIte, Reference.stringResult]
      refine ⟨⟨rfl, ?_⟩, ⟨t, ?_⟩, ?_⟩
      · intro r member
        obtain ⟨text, present⟩ := live r member
        exact currentString_append state.1 t r (index_lt_of_live present)
      · show (Owned.Focus.fst.get _ : Heap).strings[state.1.strings.length]?.join = some t
        simp [Owned.Focus.fst]
      · intro member
        obtain ⟨text, present⟩ := live _ member
        have := index_lt_of_live (r := ⟨state.1.strings.length⟩) present
        exact Nat.lt_irrefl _ this

theorem drop_frame (state : World) (op : Operand) (error : Error BoxId) (strings : List StringId) :
    DropFrame ownedOps error strings state (dropOwned state op) := by
  unfold dropOwned
  by_cases p : op.dropPanics
  · simp only [p, ↓reduceIte]; exact ⟨rfl, fun _ _ => rfl⟩
  · simp only [p, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, fun _ _ => rfl⟩

theorem admissible (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) (initial : World) :
    ownedCallbacks.Admissible ownedOps args initial where
  left := by
    intro payload outcome _ ready run
    have e : displayOwned initial args.left = outcome := run
    rw [← e]
    exact display_frame initial args.left args.error payload.strings ready.2
  right := by
    intro payload retained afterLeft outcome _ ready first run
    have e1 : displayOwned initial args.left = .returned retained afterLeft := first
    have frame := display_frame initial args.left args.error payload.strings ready.2
    rw [e1] at frame
    obtain ⟨⟨_, held⟩, newLive, _⟩ := frame
    have e2 : displayOwned afterLeft args.right = outcome := run
    rw [← e2]
    apply display_frame
    intro r member
    rcases List.mem_cons.mp member with same | member
    · subst same; exact newLive
    · obtain ⟨text, present⟩ := ready.2 r member
      exact ⟨text, (held r member).trans present⟩
  dropLeft := by
    intro before payload outcome _ _ _ run
    have e : dropOwned before args.left = outcome := run
    rw [← e]
    exact drop_frame before args.left args.error payload.strings
  dropRight := by
    intro before payload outcome _ _ _ run
    have e : dropOwned before args.right = outcome := run
    rw [← e]
    exact drop_frame before args.right args.error payload.strings

theorem callReady_of_ready (args : AnchorErrorOwned.ValuesArgs BoxId Operand Operand) (initial :
  World)
    (ready : Ready ownedOps initial args.error) : ownedCallbacks.CallReady ownedOps args initial :=
  ValuesCallbacks.CallReady.of_admissible ready (admissible args initial) ownedLaws.drop_boxes
    ownedLaws.store.available

theorem withValues_requires_iff (before : World) (args : AnchorErrorOwned.ValuesArgs BoxId Operand
  Operand) :
    (Solanalib.Specs.AnchorLang.error.Error.with_values_contract.contract ownedIndex).requires
      before args ↔
      readyB ownedOps before args.error = true := by
  rw [readyB_iff]
  exact ⟨fun h => h.2.1, fun h => ⟨ownedComparison, h, callReady_of_ready args before h⟩⟩

end SolanalibTest.Conformance.Library.Families.Anchor.RequiresErrors
