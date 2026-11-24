/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV2.Map

/-!
# solana-account-view 2.0.0: deciding the registered preconditions

The checkers decide the registered `requires` of every model whose
precondition is not `True` and that the parser does not already establish:

* `Ref::release`, `RefMut::release`: the guard resolves to a live slot
  (`release_requires_iff`);
* `Ref::try_map`, `RefMut::try_map` at `mapProfile` with a scripted callback:
  the guard is live, its cell exists, its mode is the mode of the family, and
  `CallbackSafe` holds (`tryMap_requires_iff`). With a function-defined
  callback, `CallbackSafe` is a statement about the one callback outcome: the
  callback frame (`Borrow.CallbackFrame` under `sliceFootprint`) and the validity of the exit
  (`CallbackValid`: a well-formed pool and, on return, a valid target);
* the `try_borrow`/`try_borrow_mut` observations: `State.Valid` of the
  observed account (`obsValid_iff`).

Each predicate is reformulated with bounded quantifiers over the finite cell and
slot lists, which are decidable, and proved equivalent to the registered one.
A record outside a precondition fails.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.AccountsV2

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! ## Presence of the cell of a handle (`HasAccount`) -/

instance (s : PoolState) (h : Handle) : Decidable (s.HasAccount h) :=
  decidable_of_iff _ (Option.isSome_iff_exists (x := s.lookupCell h))

/-! ## Pool validity (`Borrow.State.Valid`, `PoolWellFormed`) -/

/-- A slot entry names an existing cell. -/
def slotInRange (cells : Nat) : Option Slot → Prop
  | none => True
  | some slot => slot.cell.cell < cells

instance (n : Nat) (e : Option Slot) : Decidable (slotInRange n e) := by
  cases e <;> unfold slotInRange <;> infer_instance

/-- The lease bounds of cell `i`. -/
def leaseBounds (s : PoolState) (i : Nat) (cell : Borrow.Cell Account) : Prop :=
  s.exclusiveCount ⟨i⟩ ≤ 1 ∧ (s.exclusiveCount ⟨i⟩ = 1 → s.sharedCount ⟨i⟩ = 0) ∧
    s.sharedCount ⟨i⟩ ≤ cell.policy.sharedLimit

def ValidB (s : PoolState) : Prop :=
  (∀ e ∈ s.slots, slotInRange s.cells.length e) ∧
    ∀ i (h : i < s.cells.length), leaseBounds s i s.cells[i]

instance (s : PoolState) : Decidable (ValidB s) := by unfold ValidB leaseBounds; infer_instance

theorem valid_iff (s : PoolState) : s.Valid ↔ ValidB s := by
  constructor
  · rintro ⟨slots, cells⟩
    refine ⟨?_, ?_⟩
    · intro e member
      cases e with
      | none => trivial
      | some slot =>
        obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
        have live : s.lookupSlot id = some slot := by simp [Borrow.State.lookupSlot, found]
        obtain ⟨cell, present⟩ := slots id slot live
        simp only [Borrow.State.lookupCell, List.getElem?_eq_some_iff] at present
        exact present.1
    · intro i h
      exact cells ⟨i⟩ s.cells[i] (by simp [Borrow.State.lookupCell, h])
  · rintro ⟨slots, cells⟩
    refine ⟨?_, ?_⟩
    · intro id slot live
      simp only [Borrow.State.lookupSlot, Option.bind_eq_some_iff] at live
      obtain ⟨entry, found, rfl⟩ := live
      have inRange := slots _ (List.mem_of_getElem? found)
      exact ⟨_, List.getElem?_eq_getElem inRange⟩
    · intro handle cell present
      simp only [Borrow.State.lookupCell, List.getElem?_eq_some_iff] at present
      obtain ⟨h, rfl⟩ := present
      exact cells handle.cell h

instance (s : PoolState) : Decidable s.Valid := decidable_of_iff _ (valid_iff s).symm

instance (a : Account) : Decidable a.Valid := by unfold AccountView.Account.Valid; infer_instance

instance (s : PoolState) : Decidable (AccountView.PoolWellFormed s) := by
  unfold AccountView.PoolWellFormed; infer_instance

/-! ## Callback frames -/

instance (a b : Option Slot) : Decidable (Borrow.SlotHistory a b) := by
  unfold Borrow.SlotHistory; split <;> infer_instance

def HistoryB (b a : PoolState) : Prop :=
  b.slots.length ≤ a.slots.length ∧
    ∀ id, id < b.slots.length → Borrow.SlotHistory (b.lookupSlot id) (a.lookupSlot id)

instance (b a : PoolState) : Decidable (HistoryB b a) := by unfold HistoryB; infer_instance

theorem history_iff (b a : PoolState) : Borrow.History b a ↔ HistoryB b a :=
  ⟨fun h => ⟨h.frontier, h.entries⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Cell `i` of `b` still exists in `a` with the same policy. -/
def cellKept (a : PoolState) (old : Borrow.Cell Account) (i : Nat) : Prop :=
  match a.cells[i]? with
  | some next => next.policy = old.policy
  | none => False

instance (a : PoolState) (old : Borrow.Cell Account) (i : Nat) : Decidable (cellKept a old i) := by
  unfold cellKept; split <;> infer_instance

instance (mode : Mode) (view : Slice) (old next : Account) :
    Decidable (AccountView.sliceFootprint mode view old next) := by
  unfold AccountView.sliceFootprint; infer_instance

/-- The footprint condition at the cell of the held guard. -/
def changesB (b a : PoolState) (guard : Guard) : Prop :=
  match b.resolve guard with
  | none => True
  | some slot => match b.lookupCell slot.cell, a.lookupCell slot.cell with
    | some old, some next => AccountView.sliceFootprint slot.mode slot.view old.value next.value
    | _, _ => True

instance (b a : PoolState) (guard : Guard) : Decidable (changesB b a guard) := by
  unfold changesB; split
  · infer_instance
  · split <;> infer_instance

def FrameB (b a : PoolState) (guard : Guard) : Prop :=
  ValidB a ∧ HistoryB b a ∧ (∀ i (h : i < b.cells.length), cellKept a b.cells[i] i) ∧
    a.resolve guard = b.resolve guard ∧ changesB b a guard

instance (b a : PoolState) (guard : Guard) : Decidable (FrameB b a guard) := by
  unfold FrameB; infer_instance

theorem frame_iff (b a : PoolState) (guard : Guard) :
    Borrow.CallbackFrame AccountView.sliceFootprint b a guard ↔ FrameB b a guard := by
  constructor
  · intro f
    refine ⟨(valid_iff a).mp f.valid, (history_iff b a).mp f.history, ?_, f.held, ?_⟩
    · intro i h
      obtain ⟨next, found, policy⟩ := f.cells ⟨i⟩ b.cells[i] (by simp [Borrow.State.lookupCell, h])
      simp only [Borrow.State.lookupCell] at found
      simp [cellKept, found, policy]
    · unfold changesB
      split
      · trivial
      · rename_i slot live
        split
        · rename_i old next present now
          exact f.changes slot old next live present now
        · trivial
  · rintro ⟨valid, history, kept, held, changes⟩
    refine ⟨(valid_iff a).mpr valid, (history_iff b a).mpr history, ?_, held, ?_⟩
    · intro handle old present
      simp only [Borrow.State.lookupCell, List.getElem?_eq_some_iff] at present
      obtain ⟨h, rfl⟩ := present
      have k := kept handle.cell h
      unfold cellKept at k
      split at k
      · rename_i next found
        exact ⟨next, found, k⟩
      · exact k.elim
    · intro slot old next live present now
      unfold changesB at changes
      rw [live] at changes
      simp only [present, now] at changes
      exact changes

/-! ## Release: a live guard -/

theorem release_requires_iff (mode : Mode) (before : World) (guard : Guard) :
    ((AccountView.releaseFamily mode).contract AccountView.sliceProfile).requires before guard ↔
      (before.1.resolve guard).isSome = true :=
  Option.isSome_iff_exists.symm

/-! ## `try_map`: `CallbackSafe` at a scripted callback -/

/-- A target of the byte-range profile is valid in its account. -/
def viewValidB (s : PoolState) (handle : Handle) (view : Slice) : Prop :=
  match s.cells[handle.cell]? with
  | some cell => view.offset + view.length ≤ cell.value.dataLen
  | none => False

instance (s : PoolState) (handle : Handle) (view : Slice) : Decidable (viewValidB s handle view) :=
  by
  unfold viewValidB; split <;> infer_instance

theorem viewValid_iff (w : World) (handle : Handle) (view : Slice) :
    AccountView.sliceProfile.ViewValid w handle view ↔ viewValidB w.1 handle view := by
  show (∃ cell, w.1.cells[handle.cell]? = some cell ∧ view.offset + view.length ≤
    cell.value.dataLen) ↔ _
  unfold viewValidB
  split
  · rename_i cell found
    constructor
    · rintro ⟨c, f, v⟩
      rw [found] at f
      cases f
      exact v
    · exact fun v => ⟨cell, found, v⟩
  · rename_i none_found
    constructor
    · rintro ⟨c, f, _⟩
      rw [none_found] at f
      cases f
    · exact False.elim

/-- The admission and validity of the callback at one outcome, decidably. -/
def safeB (before : World) (guard : Guard) (handle : Handle) (original : Slice)
    (produced : Outcome World (Except Nat Slice) String Empty) : Prop :=
  match produced with
  | .returned result after =>
    FrameB before.1 after.1 guard ∧ AccountView.PoolWellFormed after.1 ∧
      viewValidB after.1 handle (match result with | .ok mapped => mapped | .error _ => original)
  | .unwound _ after => FrameB before.1 after.1 guard ∧ AccountView.PoolWellFormed after.1
  | .terminated _ => True

instance (before : World) (guard : Guard) (handle : Handle) (original : Slice)
    (produced : Outcome World (Except Nat Slice) String Empty) :
    Decidable (safeB before guard handle original produced) := by
  unfold safeB; split <;> infer_instance

theorem safe_iff (before : World) (guard : Guard) (handle : Handle) (original : Slice)
    (produced : Outcome World (Except Nat Slice) String Empty) :
    (Borrow.CallbackAdmissible (Aux := Unit) AccountView.sliceFootprint before.1 guard produced ∧
      mapProfile.CallbackValid handle original produced) ↔
      safeB before guard handle original produced := by
  cases produced with
  | returned result after =>
    cases result with
    | ok mapped => exact and_congr (frame_iff _ _ _) (and_congr Iff.rfl (viewValid_iff after handle
      mapped))
    | error e => exact and_congr (frame_iff _ _ _) (and_congr Iff.rfl (viewValid_iff after handle
      original))
  | unwound reason after =>
    exact and_congr (frame_iff _ _ _) Iff.rfl
  | terminated reason => exact ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩

/-- The `try_map` precondition at a scripted callback, decidably. -/
def tryMapReadyB (mode : Mode) (script : Script) (before : World) (guard : Guard) : Prop :=
  match before.1.resolve guard with
  | none => False
  | some slot => match before.1.lookupCell slot.cell with
    | none => False
    | some _ => slot.mode = mode ∧
        safeB before guard slot.cell slot.view (runScript script before slot.cell slot.view)

instance (mode : Mode) (script : Script) (before : World) (guard : Guard) :
    Decidable (tryMapReadyB mode script before guard) := by
  unfold tryMapReadyB; split
  · infer_instance
  · split <;> infer_instance

theorem tryMap_requires_iff (mode : Mode) (script : Script) (before : World) (guard : Guard) :
    (AccountView.genericTryMapContract mapProfile mode).requires before ⟨guard, scriptCallback
      script⟩ ↔
      tryMapReadyB mode script before guard := by
  show ((∃ slot cell, before.1.resolve guard = some slot ∧ before.1.lookupCell slot.cell = some
    cell ∧
      slot.mode = mode) ∧ mapProfile.CallbackSafe before ⟨guard, scriptCallback script⟩) ↔ _
  unfold tryMapReadyB AccountView.TryMapProfile.CallbackSafe
  split
  · rename_i dead
    constructor
    · rintro ⟨⟨slot, cell, live, _⟩, _⟩
      change before.1.resolve guard = some slot at live
      rw [dead] at live
      cases live
    · exact False.elim
  · rename_i slot live
    split
    · rename_i missing
      constructor
      · rintro ⟨⟨slot', cell, live', present, _⟩, _⟩
        change before.1.resolve guard = some slot' at live'
        rw [live] at live'
        cases live'
        rw [missing] at present
        cases present
      · exact False.elim
    · rename_i cell present
      constructor
      · rintro ⟨⟨slot', cell', live', _, mode'⟩, safe⟩
        change before.1.resolve guard = some slot' at live'
        rw [live] at live'
        cases live'
        refine ⟨mode', (safe_iff _ _ _ _ _).mp ?_⟩
        exact safe slot cell live present _ rfl
      · rintro ⟨mode', safe⟩
        refine ⟨⟨slot, cell, live, present, mode'⟩, ?_⟩
        intro slot' cell' live' present' produced called
        change before.1.resolve guard = some slot' at live'
        rw [live] at live'
        cases live'
        have same : runScript script before slot.cell slot.view = produced := called
        subst same
        exact (safe_iff _ _ _ _ _).mpr safe

/-! ## Observation acquisitions: `State.Valid` -/

/-- The byte availability required by a lease. -/
def bytesReady (data : Option Solanalib.Runtime.Bytes) (length : Nat) : Prop :=
  match data with
  | some bytes => bytes.length = length
  | none => False

instance (data : Option Solanalib.Runtime.Bytes) (length : Nat) : Decidable (bytesReady data
  length) := by
  unfold bytesReady; split <;> infer_instance

def obsValidB (s : ObsState) : Prop :=
  s.account.lamports < Solanalib.Runtime.U64_LIMIT ∧ s.account.dataLen <
    Solanalib.Runtime.U64_LIMIT ∧
    match s.account.lease with
    | .free => bytesReady s.account.data s.account.dataLen
    | .shared count => 0 < count ∧ count ≤ 254 ∧ bytesReady s.account.data s.account.dataLen
    | .exclusive => s.account.data = none

instance (s : ObsState) : Decidable (obsValidB s) := by
  unfold obsValidB; split <;> infer_instance

theorem bytesReady_iff (data : Option Solanalib.Runtime.Bytes) (length : Nat) :
    (∃ bytes, data = some bytes ∧ bytes.length = length) ↔ bytesReady data length := by
  cases data <;> simp [bytesReady]

theorem obsValid_iff (s : ObsState) : s.Valid ↔ obsValidB s := by
  unfold AccountViewObservation.State.Valid obsValidB
  cases s.account.lease <;> simp only [bytesReady_iff]

end SolanalibTest.Conformance.Library.Families.AccountsV2
