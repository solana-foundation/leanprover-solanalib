/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorrowLifecycle
public import Solanalib.Specs.Core

/-!
Closed mathematical controls for identified guards and finite callbacks. The
fixtures are fresh pure cell worlds, with no pointer, Rust permission, or source
execution interpretation. Callback controls change the held mutable contents,
another identified cell, and captured auxiliary state before returning an error
or unwinding. Shared callbacks also change captured state and another cell.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Borrow

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borrow

/-- Two possible checked projections for the concrete data model. -/
inductive View where
  /-- The complete current list. -/
  | whole
  /-- The current list after its first element, checked for nonemptiness. -/
  | tail
  deriving DecidableEq, Repr

/-- Current-view interpretation, evaluated against the current cell contents. -/
def project (view : View) (contents : List Nat) : Except String (List Nat) :=
  match view with
  | .whole => .ok contents
  | .tail => match contents with
    | [] => .error "empty data"
    | _ :: rest => .ok rest

/-- A two-cell world with independently bounded policies and no live leases. -/
def initial : State (List Nat) View :=
  ⟨[⟨[7, 8], ⟨2⟩⟩, ⟨[11], Policy.accountView⟩], []⟩

/-- The identified data cell. -/
def dataCell : Handle := ⟨0⟩

/-- A separate cell reachable by a captured callback handle. -/
def capturedCell : Handle := ⟨1⟩

/-- The first acquired guard token. -/
def original : Guard := ⟨0, 0⟩

/-- The transferred token retains the same lease id and advances generation. -/
def moved : Guard := ⟨0, 1⟩

/-- Current state after actual mathematical exclusive acquisition. -/
def exclusive : State (List Nat) View := (acquire initial dataCell .exclusive .whole).2

/-- Current state after actual mathematical shared acquisition. -/
def shared : State (List Nat) View := (acquire initial dataCell .shared .whole).2

/-- Mutable callback effects update both the held contents and captured cell. -/
def mutated : State (List Nat) View :=
  (replaceCell (replaceCell exclusive dataCell [41, 8]).2 capturedCell [13]).2

/-- Shared callback effects preserve the held data but change the captured cell. -/
def captured : State (List Nat) View := (replaceCell shared capturedCell [13]).2

/-- A concrete finite callback state includes captured auxiliary data. -/
abbrev W := World (List Nat) View Nat

/-- The mutation footprint preserves a shared view and preserves mutable length. -/
def footprint : Footprint (List Nat) View := fun mode _ before after =>
  match mode with
  | .shared => before = after
  | .exclusive => before.length = after.length

/-- A singleton finite callback relation, used with explicit frame proofs below. -/
def emits (produced : Outcome W (Except String View) String String) :
    MapCallback (List Nat) View Nat String String String :=
  fun _ _ _ outcome => outcome = produced

/-- The initial world is a satisfiable, nonempty protocol state. -/
theorem initial_valid : initial.Valid := State.valid_empty_slots _

/-- Exclusive acquisition preserves the complete invariant. -/
theorem exclusive_valid : exclusive.Valid := acquire_valid initial_valid _ _ _

/-- Shared acquisition preserves the complete invariant. -/
theorem shared_valid : shared.Valid := acquire_valid initial_valid _ _ _

/-- The original guard refers to the actual exclusive slot. -/
theorem exclusive_live : exclusive.resolve original = some ⟨dataCell, .exclusive, 0, .whole⟩ := rfl

/-- The shared guard refers to the same identified data cell. -/
theorem shared_live : shared.resolve original = some ⟨dataCell, .shared, 0, .whole⟩ := rfl

/-- The callback mutation has a real admissible frame, including its captured-cell effects. -/
theorem mutated_frame : CallbackFrame footprint exclusive mutated original := by
  apply CallbackFrame.of_slots
  · exact replaceCell_valid (replaceCell_valid exclusive_valid dataCell [41, 8]) capturedCell [13]
  · simp [mutated, replaceCell_slots]
  · intro handle
    simp only [mutated, replaceCell_policy]
  · intro slot old next live oldFound nextFound
    rw [exclusive_live] at live
    cases live
    change some ⟨[7, 8], ⟨2⟩⟩ = some old at oldFound
    cases oldFound
    change some ⟨[41, 8], ⟨2⟩⟩ = some next at nextFound
    cases nextFound
    rfl

/-- Shared access does not erase effects on captured cells or auxiliary state. -/
theorem captured_frame : CallbackFrame footprint shared captured original := by
  apply CallbackFrame.of_slots
  · exact replaceCell_valid shared_valid capturedCell [13]
  · exact replaceCell_slots shared capturedCell [13]
  · intro handle
    exact replaceCell_policy shared capturedCell handle [13]
  · intro slot old next live oldFound nextFound
    rw [shared_live] at live
    cases live
    change some ⟨[7, 8], ⟨2⟩⟩ = some old at oldFound
    cases oldFound
    change some ⟨[7, 8], ⟨2⟩⟩ = some next at nextFound
    cases nextFound
    rfl

/-- A callback that changes the protected shared contents fails the explicit frame. -/
theorem shared_held_mutation_rejected :
    ¬CallbackFrame footprint shared (replaceCell shared dataCell [41, 8]).2 original := by
  intro frame
  have forbidden := frame.changes ⟨dataCell, .shared, 0, .whole⟩ ⟨[7, 8], ⟨2⟩⟩
    ⟨[41, 8], ⟨2⟩⟩ shared_live rfl rfl
  change ([7, 8] : List Nat) = [41, 8] at forbidden
  cases forbidden

/-- A callback cannot consume the held guard of its caller before mapping completes. -/
theorem callback_guard_release_rejected :
    ¬CallbackFrame footprint exclusive (release exclusive original).2 original := by
  intro frame
  have impossible := frame.resolve exclusive_live
  change none = some (⟨dataCell, .exclusive, 0, .whole⟩ : Slot View) at impossible
  cases impossible

/-- Two aliases consume the same shared quota; saturation and exclusive conflict differ. -/
theorem alias_shared_bound :
    (acquire initial dataCell .shared .whole).1 = .ok original ∧
    (acquire shared dataCell.alias .shared .whole).1 = .ok ⟨1, 0⟩ ∧
    (acquire (acquire shared dataCell.alias .shared .whole).2 dataCell .shared .whole).1 =
      .error .sharedLimit ∧
    (acquire shared dataCell.alias .exclusive .whole) = (.error .conflict, shared) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Exclusive acquisition blocks both acquisition modes through an alias. -/
theorem exclusive_blocks_alias :
    acquire exclusive dataCell.alias .shared .whole = (.error .conflict, exclusive) ∧
    acquire exclusive dataCell.alias .exclusive .whole = (.error .conflict, exclusive) :=
  ⟨rfl, rfl⟩

/-- Independent identified cells have independent exclusive leases. -/
theorem separate_cells_independent :
    (acquire exclusive capturedCell .exclusive .whole).1 = .ok ⟨1, 0⟩ ∧
    (acquire exclusive capturedCell .exclusive .whole).2.lease dataCell = .exclusive ∧
    (acquire exclusive capturedCell .exclusive .whole).2.lease capturedCell = .exclusive :=
  ⟨rfl, rfl, rfl⟩

/-- Inserting a fresh cell preserves a live guard and gives the new cell no lease. -/
theorem insertion_preserves_existing_guard :
    current (exclusive.insert Policy.accountView [99]).2 original = .ok (.whole, [7, 8]) ∧
    (exclusive.insert Policy.accountView [99]).2.lease ⟨2⟩ = .free ∧
    (exclusive.insert Policy.accountView [99]).2.Valid :=
  ⟨rfl, rfl, State.insert_valid exclusive_valid _ _⟩

/-- Releasing one shared alias leaves the other live until its own release. -/
theorem shared_release_counts :
    (release (acquire shared dataCell.alias .shared .whole).2 original).2.lease dataCell =
      .shared 1 ∧
    current (release (acquire shared dataCell.alias .shared .whole).2 original).2 ⟨1, 0⟩ =
      .ok (.whole, [7, 8]) ∧
    (release (release (acquire shared dataCell.alias .shared .whole).2 original).2 ⟨1, 0⟩).2.lease
      dataCell = .free := ⟨rfl, rfl, rfl⟩

/-- A live shared guard cannot perform the exclusive-write operation. -/
theorem shared_write_rejected : write shared original [99] = (.error .wrongMode, shared) := rfl

/-- Missing handles and unissued guard tokens are checked errors with unchanged state. -/
theorem invalid_inputs_rejected :
    acquire initial ⟨2⟩ .shared .whole = (.error .missingCell, initial) ∧
    release initial original = (.error .invalidGuard, initial) ∧
    current initial original = .error .invalidGuard := ⟨rfl, rfl, rfl⟩

/-- A live guard observes new contents before release; no copy-back is needed. -/
theorem write_visible_immediately :
    current (write exclusive original [41, 8]).2 original = .ok (.whole, [41, 8]) ∧
    ((write exclusive original [41, 8]).2.lookupCell dataCell).map Cell.value = some [41, 8] :=
  ⟨rfl, rfl⟩

/-- A real finite `try_map` error preserves target, captured-cell and auxiliary effects. -/
theorem failed_map_executes :
    tryMap .release (emits (.returned (.error "rejected") (mutated, 99)))
      (exclusive, 17) original
      (.returned (.ok (.error ("rejected", moved))) ((transfer mutated original .whole).2, 99)) :=
        by
  simp only [tryMap, exclusive_live]
  change ∃ produced,
    emits (.returned (.error "rejected") (mutated, 99)) (exclusive, 17) dataCell .whole produced ∧
    _ = finishTryMap .release original .whole produced
  refine ⟨.returned (.error "rejected") (mutated, 99), rfl, ?_⟩
  exact (finishTryMap_error .release original .whole "rejected" (mutated, 99)
    (mutated_frame.resolve exclusive_live)).symm

/-- Error returns the same underlying lease/view with a fresh token, not a stale snapshot. -/
theorem failed_map_preserves_effects :
    current (transfer mutated original .whole).2 moved = .ok (.whole, [41, 8]) ∧
    ((transfer mutated original .whole).2.lookupCell capturedCell).map Cell.value = some [13] ∧
    (transfer mutated original .whole).2.lease dataCell = .exclusive ∧
    current (transfer mutated original .whole).2 original = .error .invalidGuard :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A transferred guard may be released once; its current contents survive both checks. -/
theorem failed_map_guard_release :
    (release (transfer mutated original .whole).2 moved).1 = .ok () ∧
    (release (transfer mutated original .whole).2 moved).2.lease dataCell = .free ∧
    ((release (transfer mutated original .whole).2 moved).2.lookupCell dataCell).map Cell.value =
      some [41, 8] ∧
    (release (release (transfer mutated original .whole).2 moved).2 moved).1 =
      .error .invalidGuard := ⟨rfl, rfl, rfl, rfl⟩

/-- Successful mapping changes the recorded projection while retaining the cell lease. -/
theorem successful_map_executes :
    tryMap .release (emits (.returned (.ok .tail) (mutated, 99)))
      (exclusive, 17) original
      (.returned (.ok (.ok moved)) ((transfer mutated original .tail).2, 99)) := by
  simp only [tryMap, exclusive_live]
  change ∃ produced,
    emits (.returned (.ok .tail) (mutated, 99)) (exclusive, 17) dataCell .whole produced ∧
    _ = finishTryMap .release original .whole produced
  refine ⟨.returned (.ok .tail) (mutated, 99), rfl, ?_⟩
  exact (finishTryMap_ok .release original .whole .tail (mutated, 99)
    (mutated_frame.resolve exclusive_live)).symm

/-- Dereference applies the mapped descriptor to current contents. -/
theorem successful_map_dereference :
    (deref project (transfer mutated original .tail).2 moved).1 = .ok (.ok [8]) ∧
    (transfer mutated original .tail).2.lease dataCell = .exclusive := ⟨rfl, rfl⟩

/-- A shared mapping can alter captured state and another cell while preserving its held view. -/
theorem shared_map_captured_effects :
    tryMap .release (emits (.returned (.ok .tail) (captured, 99)))
      (shared, 17) original
      (.returned (.ok (.ok moved)) ((transfer captured original .tail).2, 99)) ∧
    ((transfer captured original .tail).2.lookupCell capturedCell).map Cell.value = some [13] ∧
    (deref project (transfer captured original .tail).2 moved).1 = .ok (.ok [8]) := by
  refine ⟨?_, rfl, rfl⟩
  simp only [tryMap, shared_live]
  change ∃ produced,
    emits (.returned (.ok .tail) (captured, 99)) (shared, 17) dataCell .whole produced ∧
    _ = finishTryMap .release original .whole produced
  refine ⟨.returned (.ok .tail) (captured, 99), rfl, ?_⟩
  exact (finishTryMap_ok .release original .whole .tail (captured, 99)
    (captured_frame.resolve shared_live)).symm

/-- Unwind with source-bound release retains all callback mutations and frees the lease. -/
theorem unwind_release_effects :
    tryMap .release (emits (.unwound "panic" (mutated, 99))) (exclusive, 17) original
      (.unwound "panic" ((release mutated original).2, 99)) ∧
    (release mutated original).2.lease dataCell = .free ∧
    ((release mutated original).2.lookupCell dataCell).map Cell.value = some [41, 8] := by
  refine ⟨?_, rfl, rfl⟩
  simp only [tryMap, exclusive_live]
  exact ⟨.unwound "panic" (mutated, 99), rfl, rfl⟩

/-- Manually suppressed cleanup instead retains the lease but still consumes the input token. -/
theorem unwind_retained_lease :
    tryMap .retainLease (emits (.unwound "panic" (mutated, 99))) (exclusive, 17) original
      (.unwound "panic" ((transfer mutated original .whole).2, 99)) ∧
    (transfer mutated original .whole).2.lease dataCell = .exclusive ∧
    current (transfer mutated original .whole).2 original = .error .invalidGuard := by
  refine ⟨?_, rfl, rfl⟩
  simp only [tryMap, exclusive_live]
  exact ⟨.unwound "panic" (mutated, 99), rfl, rfl⟩

/-- A terminal callback has a finite terminal outcome and no invented final world. -/
theorem terminal_callback :
    tryMap .release (emits (.terminated "abort")) (exclusive, 17) original
      (.terminated "abort") := by
  simp only [tryMap, exclusive_live]
  exact ⟨.terminated "abort", rfl, rfl⟩

/-- A new acquisition never reuses the stable id of the dropped guard or revives it. -/
theorem retired_after_reacquisition :
    (acquire (release exclusive original).2 dataCell .exclusive .whole).1 = .ok ⟨1, 0⟩ ∧
    current (acquire (release exclusive original).2 dataCell .exclusive .whole).2 original =
      .error .invalidGuard := ⟨rfl, rfl⟩

/-- AccountView and target-sized RefCell policies remain distinct explicit parameters. -/
theorem policy_bounds :
    Policy.accountView.sharedLimit = 254 ∧
    (Policy.refCell 64).sharedLimit = 2^63 - 1 ∧
    (Policy.refCell 32).sharedLimit = 2^31 - 1 := by decide

/-- A zero-shared policy rejects its first shared acquisition while permitting exclusivity. -/
theorem zero_shared_policy :
    (acquire (⟨[⟨[7], ⟨0⟩⟩], []⟩ : State (List Nat) View) dataCell .shared .whole).1 =
      .error .sharedLimit ∧
    (acquire (⟨[⟨[7], ⟨0⟩⟩], []⟩ : State (List Nat) View) dataCell .exclusive .whole).1 =
      .ok original := ⟨rfl, rfl⟩

/-- The protocol has a concrete valid nonempty state and a successful live acquisition. -/
theorem nonvacuous_acquisition :
    ∃ before after : State (List Nat) View, ∃ guard : Guard,
      before.Valid ∧ acquire before dataCell .exclusive .whole = (.ok guard, after) ∧
      current after guard = .ok (.whole, [7, 8]) :=
  ⟨initial, exclusive, original, initial_valid, rfl, rfl⟩

namespace Admission

/-- The actual cell of the acquired guard exists independently of callback admission. -/
theorem exclusive_present : exclusive.lookupCell dataCell = some ⟨[7, 8], ⟨2⟩⟩ := rfl

/-- An adversarial callback consumes the guard of the caller and then reports an error. -/
def badOutcome : Outcome W (Except String View) String String :=
  .returned (.error "callback error") ((release exclusive original).2, 99)

/-- This callback has exactly the inadmissible outcome, rather than no finite exit. -/
def badCallback : MapCallback (List Nat) View Nat String String String := emits badOutcome

/-- The adversarial callback has a real finite execution at the live input. -/
theorem bad_callback_executes :
    badCallback (exclusive, 17) dataCell .whole badOutcome := rfl

/-- Universal admission rejects consumption of the actual held guard. -/
theorem bad_callback_not_admitted :
    ¬MapCallback.Admissible footprint badCallback (exclusive, 17) original := by
  intro admitted
  exact callback_guard_release_rejected
    (admitted _ _ exclusive_live exclusive_present badOutcome bad_callback_executes)

/-- The inadmissible exit is retained as the exact checked transfer failure,
including its actual released store and captured-state update. -/
theorem bad_exit_retained :
    tryMap .release badCallback (exclusive, 17) original
      (.returned (.error .invalidGuard) ((release exclusive original).2, 99)) :=
  tryMap_of_callback .release (callback := badCallback) (before := (exclusive, 17))
    (guard := original) (produced := badOutcome) exclusive_live exclusive_present
    bad_callback_executes

/-- An impossible postcondition at a concrete valid input, without callback admission. -/
def impossibleContract : Solanalib.Contracts.Model W Guard (TryMapResult String) String String where
  requires before guard := before = (exclusive, 17) ∧ guard = original
  post _ _ _ := False

/-- The vacuity regression uses a satisfiable input, not an impossible precondition. -/
theorem impossible_precondition_satisfiable : impossibleContract.Satisfiable :=
  ⟨(exclusive, 17), original, rfl, rfl⟩

/-- A frame-breaking callback has an execution that refutes the impossible postcondition. -/
theorem impossible_post_not_holds :
    ¬impossibleContract.Holds (tryMap .release badCallback) := by
  intro holds
  exact holds (exclusive, 17) original _ ⟨rfl, rfl⟩ bad_exit_retained

/-- A soundness contract explicitly requires admission of every callback exit. -/
def admittedContract (callback : MapCallback (List Nat) View Nat String String String) :
    Solanalib.Contracts.Model W Guard (TryMapResult String) String String where
  requires before guard := before.1.Valid ∧
    MapCallback.Admissible footprint callback before guard
  post before _ outcome := ValidExit outcome ∧ HistoryExit before.1 outcome

/-- Validity and token-history correctness consume universal admission from the
contract precondition rather than extracting it from the operational relation. -/
theorem admittedContract_holds (callback : MapCallback (List Nat) View Nat String String String) :
    (admittedContract callback).Holds (tryMap .release callback) := by
  intro before guard outcome ready step
  exact ⟨tryMap_valid ready.1 ready.2 step, tryMap_history ready.2 step⟩

/-- The soundness precondition excludes the actual frame-breaking callback input. -/
theorem bad_input_not_ready :
    ¬(admittedContract badCallback).requires (exclusive, 17) original := by
  intro ready
  exact bad_callback_not_admitted ready.2

/-- One nondeterministic callback can return success, return an error, unwind,
or terminate. Every state-bearing alternative keeps its actual mutations. -/
def allExits : MapCallback (List Nat) View Nat String String String :=
  fun _ _ _ outcome =>
    outcome = .returned (.ok .tail) (mutated, 99) ∨
    outcome = .returned (.error "rejected") (mutated, 99) ∨
    outcome = .unwound "panic" (mutated, 99) ∨
    outcome = .terminated "abort"

/-- Admission checks every alternative, including ordinary errors and unwinds. -/
theorem all_exits_admitted :
    MapCallback.Admissible footprint allExits (exclusive, 17) original := by
  intro slot cell live present produced called
  rcases called with rfl | rfl | rfl | rfl
  · exact mutated_frame
  · exact mutated_frame
  · exact mutated_frame
  · trivial

/-- Every one of the four alternatives of the admitted callback remains a mapping
execution with the exact result, cleanup policy and actual final world. -/
theorem all_exits_retained :
    tryMap .release allExits (exclusive, 17) original
      (.returned (.ok (.ok moved)) ((transfer mutated original .tail).2, 99)) ∧
    tryMap .release allExits (exclusive, 17) original
      (.returned (.ok (.error ("rejected", moved))) ((transfer mutated original .whole).2, 99)) ∧
    tryMap .release allExits (exclusive, 17) original
      (.unwound "panic" ((release mutated original).2, 99)) ∧
    tryMap .release allExits (exclusive, 17) original (.terminated "abort") := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tryMap_of_callback .release (callback := allExits) (before := (exclusive, 17))
      (guard := original) (produced := .returned (.ok .tail) (mutated, 99))
      exclusive_live exclusive_present
      (show allExits (exclusive, 17) dataCell .whole
        (.returned (.ok .tail) (mutated, 99)) from Or.inl rfl)
  · exact tryMap_of_callback .release (callback := allExits) (before := (exclusive, 17))
      (guard := original) (produced := .returned (.error "rejected") (mutated, 99))
      exclusive_live exclusive_present
      (show allExits (exclusive, 17) dataCell .whole
        (.returned (.error "rejected") (mutated, 99)) from Or.inr (Or.inl rfl))
  · exact tryMap_of_callback .release (callback := allExits) (before := (exclusive, 17))
      (guard := original) (produced := .unwound "panic" (mutated, 99))
      exclusive_live exclusive_present
      (show allExits (exclusive, 17) dataCell .whole
        (.unwound "panic" (mutated, 99)) from Or.inr (Or.inr (Or.inl rfl)))
  · exact tryMap_of_callback .release (callback := allExits) (before := (exclusive, 17))
      (guard := original) (produced := .terminated "abort") exclusive_live exclusive_present
      (show allExits (exclusive, 17) dataCell .whole
        (.terminated "abort") from Or.inr (Or.inr (Or.inr rfl)))

/-- The admitted contract has a real permitted execution, in addition to its
universal partial-correctness proof. No empty relation supplies this witness. -/
theorem admitted_contract_has_execution :
    (admittedContract allExits).HasExecution (tryMap .release allExits) :=
  ⟨(exclusive, 17), original, _, ⟨exclusive_valid, all_exits_admitted⟩,
    all_exits_retained.1⟩

/-- Its satisfiable precondition follows from the same permitted live execution. -/
theorem admitted_contract_satisfiable : (admittedContract allExits).Satisfiable :=
  admitted_contract_has_execution.satisfiable

/-- An allowed terminal alternative does not justify discarding a different,
state-bearing alternative that consumes the guard of the caller. -/
def mixedExits : MapCallback (List Nat) View Nat String String String :=
  fun _ _ _ outcome => outcome = badOutcome ∨ outcome = .terminated "abort"

/-- Universal admission rejects the mixed callback even though one exit is terminal. -/
theorem mixed_callback_not_admitted :
    ¬MapCallback.Admissible footprint mixedExits (exclusive, 17) original := by
  intro admitted
  exact callback_guard_release_rejected
    (admitted _ _ exclusive_live exclusive_present badOutcome (Or.inl rfl))

/-- The mixed callback retains both its checked failure and its terminal exit;
the relation does not select just the alternative satisfying the frame. -/
theorem mixed_exits_retained :
    tryMap .release mixedExits (exclusive, 17) original
      (.returned (.error .invalidGuard) ((release exclusive original).2, 99)) ∧
    tryMap .release mixedExits (exclusive, 17) original (.terminated "abort") := by
  constructor
  · exact tryMap_of_callback .release (callback := mixedExits) (before := (exclusive, 17))
      (guard := original) (produced := badOutcome) exclusive_live exclusive_present
      (show mixedExits (exclusive, 17) dataCell .whole badOutcome from Or.inl rfl)
  · exact tryMap_of_callback .release (callback := mixedExits) (before := (exclusive, 17))
      (guard := original) (produced := .terminated "abort") exclusive_live exclusive_present
      (show mixedExits (exclusive, 17) dataCell .whole (.terminated "abort") from Or.inr rfl)

/-- A callback with no finite outcome can represent divergence. -/
def noExits : MapCallback (List Nat) View Nat String String String := fun _ _ _ _ => False

/-- Frame admission alone deliberately asserts no callback progress. Absence
of outcomes here comes from the callback itself, not from the frame test of the mapping. -/
theorem no_progress_assumed :
    MapCallback.Admissible footprint noExits (exclusive, 17) original ∧
    ¬∃ outcome, tryMap .release noExits (exclusive, 17) original outcome := by
  constructor
  · intro slot cell live present produced called
    exact False.elim called
  · intro execution
    obtain ⟨produced, called⟩ :=
      (tryMap_hasOutcome_iff .release noExits exclusive_live exclusive_present).mp execution
    exact called

end Admission

end SolanalibTest.Specs.Core.Borrow
