/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAccountView
public import Solanalib.Specs.Core.AccountViewMapLaws
public import Solanalib.Specs.Core.AccountViewRevisionLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountView.Lifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView

/-- A nonempty account with reserved suffix bytes and read-only metadata. -/
def account : Account :=
  ⟨⟨.zero, true, false, false⟩, .zero, 17, 3, 3, [1, 2, 3, 99, 88], 0, 0⟩

/-- A one-account pool with a nonempty logical prefix and retained backing suffix. -/
def state : State := ⟨[⟨account, Borrow.Policy.accountView⟩], []⟩
/-- The identity of the fixture account, shared by all its aliases. -/
def handle : Handle := ⟨0⟩
/-- The first issued guard token in the fixture pool. -/
def guard : Guard := ⟨0, 0⟩

/-- The example satisfies the full pool invariant, not only a projected lease. -/
theorem state_ready : Ready state handle := by
  refine ⟨⟨Borrow.State.valid_empty_slots _, ?_⟩, _, rfl⟩
  intro cell member
  have same : cell = ⟨account, Borrow.Policy.accountView⟩ := List.mem_singleton.mp member
  subst cell
  exact ⟨rfl, by unfold Account.Valid; decide⟩

/-- Source scalar models refer to the same identified account. -/
theorem observations :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_model state handle = (17, state) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.data_len_model state handle = (3, state) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_signer_model state handle = (true, state)
      ∧
    (Solanalib.Specs.SolanaAccountView.AccountView.Pool.address_model state handle).1.account =
      handle := by decide

/-- A local setter does not add an SDK writable-metadata check. Existing aliases
observe the new working balance; runtime conservation remains a separate check. -/
theorem read_only_metadata_allows_local_set :
    let after := (Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_model state
      (handle, 41)).2
    (after.account handle.alias).lamports = 41 ∧
    (after.account handle).metadata.writable = false := by decide

/-- The actual mathematical result of the setter meets the versioned contract. -/
theorem setter_contract :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_contract.ensures state (handle,
      41) ()
      (Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_model state (handle, 41)).2
        :=
  Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_reference state (handle, 41)
    state_ready.2

/-- The pool after one successful shared acquisition. -/
def sharedState : State := (Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model
  state handle).2
/-- The pool after one successful exclusive acquisition. -/
def exclusiveState : State :=
  (Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_mut_model state handle).2

theorem shared_step :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model state handle = (.ok guard,
      sharedState) := rfl

theorem exclusive_step :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_mut_model state handle = (.ok
      guard, exclusiveState) := rfl

theorem exclusive_ready : GuardReady exclusiveState .exclusive guard :=
  acquire_guardReady state_ready.1 exclusive_step

/-- Both checked modes reject an incompatible live lease without changing state. -/
theorem borrow_conflicts :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_mut_model sharedState handle =
      (.error .accountBorrowFailed, sharedState) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model exclusiveState handle =
      (.error .accountBorrowFailed, exclusiveState) := ⟨rfl, rfl⟩

/-- Typed mutable dereference instantiates the common reference family at the
ordinary byte profile, retaining the existing guard and world. -/
theorem mutable_reference_contract :
    (Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_contract.contract sliceProfile).ensures
      (exclusiveState, ()) guard ⟨guard, true⟩ (exclusiveState, ()) := by
  apply (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_reference
    sliceProfile)
    (exclusiveState, ()) guard (.returned ⟨guard, true⟩ (exclusiveState, ()))
  · trivial
  · rfl

/-- The exclusive pool after an immediate three-byte replacement. -/
def writtenState : State := (writeReference exclusiveState ⟨guard, true⟩ [9, 8, 7]).2

/-- A write is visible immediately, while the exclusive guard remains live. -/
theorem write_is_immediate :
    guardRead writtenState guard = .ok [9, 8, 7] ∧
    writtenState.lease handle = .exclusive := ⟨rfl, rfl⟩

theorem written_ready : GuardReady writtenState .exclusive guard := by
  apply writeReference_guardReady exclusive_ready
  intro slot live
  have same : slot = ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩ := by
    have expected : exclusiveState.resolve guard = some ⟨handle, .exclusive, 0, ⟨0, 3⟩⟩ := rfl
    rw [expected] at live
    cases live
    rfl
  subst slot
  rfl

/-- The pool after destroying the exclusive guard. -/
def releasedState : State := (Borrow.release writtenState guard).2

/-- Release consumes the token once and leaves already-written bytes intact. -/
theorem release_consumes_without_copyback :
    guardRead releasedState guard = .error .invalidGuard ∧
    Borrow.release releasedState guard = (.error .invalidGuard, releasedState) ∧
    (releasedState.account handle).bytes = [9, 8, 7] ∧
    releasedState.lease handle = .free := ⟨rfl, rfl, rfl, rfl⟩

/-- The versioned destructor family applies after the mutable write. -/
theorem release_contract :
    (Solanalib.Specs.SolanaAccountView.RefMut.release_contract.contract sliceProfile).ensures
      (writtenState, ()) guard () (releasedState, ()) := by
  apply (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.release_reference sliceProfile)
    (writtenState, ()) guard (.returned () (releasedState, ()))
  · exact ⟨_, rfl⟩
  · rfl

/-- A later acquisition uses a fresh id, so it cannot revive the old token. -/
theorem reacquire_no_old_token :
    (Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model releasedState handle).1 =
      .ok ⟨1, 0⟩ ∧
    guardRead (Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model releasedState
      handle).2 guard =
      .error .invalidGuard := ⟨rfl, rfl⟩

/-- The free pool after the v1 close operation. -/
def closedWithResizeDeltaState : State :=
  (Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_model state handle).2

/-- Local close can zero a nonzero working balance; it erases the logical header,
not the allocated bytes. This is not a runtime-conservation success statement. -/
theorem close_with_resize_delta_preserves_backing :
    (Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_model state
      handle).1 = .ok () ∧
    (closedWithResizeDeltaState.account handle).lamports = 0 ∧
    (closedWithResizeDeltaState.account handle).dataLen = 0 ∧
    (closedWithResizeDeltaState.account handle).backing = [1, 2, 3, 99, 88] := ⟨rfl, rfl, rfl, rfl⟩

/-- Every live data lease blocks local close before any header update. -/
theorem close_with_resize_delta_borrow_failure :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_model sharedState
      handle = (.error .accountBorrowFailed, sharedState) := rfl

/-- The byte-only compatibility layer agrees at acquisition but cannot be used
to justify the later mapping or destruction of this guard. -/
theorem acquisition_core_projection :
    (acquisitionBytes state handle
      (Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model state handle).1,
      observe sharedState handle) =
      AccountViewObservation.reference.tryBorrow (observe state handle) () :=
  shared_acquisition_projection (cell := ⟨account, Borrow.Policy.accountView⟩) rfl rfl

/-- V1 clone preserves the existing identity and creates no independent cell. -/
theorem clone_alias :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.clone_model state handle = (handle, state)
      := rfl

/-- The pool after shrinking its logical data while retaining the backing. -/
def shrunk : State := (Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model state
  (handle, 1)).2

/-- Shrinking changes the signed delta and visible length without erasing backing. -/
theorem shrink_keeps_backing :
    (shrunk.account handle).dataLen = 1 ∧
    (shrunk.account handle).resizeDelta = -2 ∧
    (shrunk.account handle).backing = [1, 2, 3, 99, 88] := by decide

/-- A following growth zeroes re-exposed data and preserves the reserved suffix. -/
theorem regrow_zeroes_exposed_bytes :
    let after := (Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model shrunk (handle,
      4)).2
    (after.account handle).bytes = [1, 0, 0, 0] ∧
    (after.account handle).backing = [1, 0, 0, 0, 88] ∧
    (after.account handle).resizeDelta = 1 := by decide

/-- The accumulated signed growth check rejects an excessive allocation request. -/
theorem growth_limit_fails :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model state (handle, 10244) =
      (.error .invalidRealloc, state) := rfl

/-- Borrow conflict precedes the signed conversion failure in the v1 source. -/
theorem resize_conflict_precedes_conversion :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model sharedState (handle, I32_MAX +
      1) =
      (.error .accountBorrowFailed, sharedState) := rfl

/-- Even an unchanged requested length does not bypass the first borrow check. -/
theorem resize_unchanged_still_checks_borrow :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model sharedState (handle, 3) =
      (.error .accountBorrowFailed, sharedState) := rfl

/-- A mathematical account outside the balance of the source and signed-counter
representation invariants. Its identity and backing bytes are still present. -/
def unboundedState : State :=
  ⟨[⟨{ account with lamports := Solanalib.Runtime.U64_LIMIT, resizeDelta := 9 },
    Borrow.Policy.accountView⟩], []⟩

/-- The branch contract retains this actual close result without claiming that
the starting balance or signed counter represents a valid Rust account. -/
theorem close_contract_without_resize_invariant :
    let after := (Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_model
      unboundedState handle).2
    ¬ (unboundedState.account handle).ResizeValid ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_contract.ensures
      unboundedState handle
      (.ok ()) after ∧
    (after.account handle).lamports = 0 ∧
    (after.account handle).resizeDelta = 6 ∧
    (after.account handle).backing = [1, 2, 3, 99, 88] := by
  refine ⟨by unfold Account.ResizeValid Account.Valid; decide, ?_, rfl, rfl, rfl⟩
  exact Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_reference
    unboundedState handle
    ⟨⟨_, rfl⟩, fun _ _ => by decide⟩

/-- Capacity is needed for the stronger backing-length theorem, not the branch
contract: this mathematical growth still has its actual cell-update result. -/
theorem resize_contract_without_capacity :
    let after := (Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model state (handle,
      6)).2
    ¬ 6 ≤ (state.account handle).backing.length ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.ensures state (handle, 6)
      (.ok ()) after ∧
    (after.account handle).dataLen = 6 ∧
    (after.account handle).backing = [1, 2, 3, 0, 0, 0] ∧
    Ready after handle ∧ (after.account handle).ResizeValid := by
  refine ⟨by decide, ?_, rfl, rfl, ?_, ?_⟩
  · exact Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_reference state (handle, 6)
      ⟨state_ready.2, by decide⟩
  · exact resize_ready state_ready
  · exact resize_preserves_signed_domain state_ready.2
      (by unfold Account.ResizeValid Account.Valid; decide)

/-- An unrelated malformed balance/counter does not hide the signed-conversion
error or its unchanged state from the versioned branch contract. -/
theorem resize_failure_without_resize_invariant :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_model unboundedState (handle, I32_MAX
      + 1) =
      (.error .invalidRealloc, unboundedState) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.ensures unboundedState
      (handle, I32_MAX + 1) (.error .invalidRealloc) unboundedState := by
  refine ⟨rfl, ?_⟩
  exact Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_reference unboundedState
    (handle, I32_MAX + 1) ⟨⟨_, rfl⟩, by decide⟩

/-- A header the loader cannot create: its signed counter is five below `i32::MAX`. -/
def nearMaxState : State :=
  ⟨[⟨{ account with resizeDelta := I32_MAX - 5 }, Borrow.Policy.accountView⟩], []⟩

/-- A header the loader cannot create: its signed counter is one above `i32::MIN`. -/
def nearMinState : State :=
  ⟨[⟨{ account with resizeDelta := -((I32_MAX : Int) + 1) + 1 }, Borrow.Policy.accountView⟩], []⟩

/-- Growing by six from a counter near `i32::MAX` overflows the `i32`
addition of the source, so the resize contract does not admit it; growth on a counter that
fits, and shrinking there, remain admitted. -/
theorem resize_overflow_outside_contract :
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.requires nearMaxState
      (handle, 9) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.requires nearMaxState
      (handle, 1) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.requires unboundedState
      (handle, 9) := by
  refine ⟨fun ready => absurd ready.2 (by decide), ⟨⟨_, rfl⟩, by decide⟩, ⟨⟨_, rfl⟩, by decide⟩⟩

/-- Shrinking from a counter near `i32::MIN` overflows the same addition, and
v1 the `resize_delta - data_len` of the close overflows there; a borrowed account
reaches neither computation, so its borrow failure stays admitted. -/
theorem close_overflow_outside_contract :
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.requires nearMinState
      (handle, 0) ∧
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_contract.requires
      nearMinState handle ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_contract.requires
      { nearMinState with slots := sharedState.slots } handle := by
  refine ⟨fun ready => absurd ready.2 (by decide), fun ready => absurd ready.2 (by decide),
    ⟨⟨_, rfl⟩, by decide⟩⟩

/-- Every loader-consistent header is inside both contracts. -/
theorem loader_header_inside_contracts {pool : State} {cell : Handle}
    (present : pool.HasAccount cell) (valid : (pool.account cell).ResizeValid) (newLength : Nat) :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.resize_contract.requires pool (cell,
      newLength) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_with_resize_delta_contract.requires
      pool cell :=
  ⟨⟨present, resizeArithmetic_of_resizeValid valid newLength⟩,
    ⟨present, closeArithmetic_of_resizeValid valid .v1⟩⟩

/-- The unsafe owner reference needs its own epoch validity; no data lease supplies it. -/
theorem close_invalidates_owner_reference :
    ¬ (Solanalib.Specs.SolanaAccountView.AccountView.Pool.owner_model state handle).1.Valid
      closedWithResizeDeltaState := by
  apply owner_invalidated_by_close rfl
  · exact ⟨state_ready.2, rfl⟩
  · rfl

end SolanalibTest.Specs.SolanaAccountView.Lifecycle

namespace SolanalibTest.Specs.SolanaAccountView.Lifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView

/-- The free pool after the v2 close operation. -/
def closedHeaderState : State :=
  (Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_header_model state handle).2

/-- Local close can zero a nonzero working balance; it erases the logical header,
not the allocated bytes. This is not a runtime-conservation success statement. -/
theorem close_header_preserves_backing :
    (Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_header_model state handle).1 = .ok ()
      ∧
    (closedHeaderState.account handle).lamports = 0 ∧
    (closedHeaderState.account handle).dataLen = 0 ∧
    (closedHeaderState.account handle).backing = [1, 2, 3, 99, 88] := ⟨rfl, rfl, rfl, rfl⟩

/-- Every live data lease blocks local close before any header update. -/
theorem close_header_borrow_failure :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.close_header_model sharedState handle =
      (.error .accountBorrowFailed, sharedState) := rfl

/-- The byte-only compatibility layer agrees at acquisition but cannot be used
to justify the later mapping or destruction of this guard. -/
theorem acquisition_observation_projection :
    (acquisitionBytes state handle
      (Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model state handle).1,
      observe sharedState handle) =
      Solanalib.Specs.SolanaAccountView.AccountView.Observation.reference.tryBorrow (observe state
        handle) () :=
  shared_acquisition_projection rfl rfl

/-- V2 shared dereference of an exclusive guard returns a read-only reference;
the exclusive lease of the guard is retained for a later mutable use. -/
theorem exclusive_read_reference :
    (Solanalib.Specs.SolanaAccountView.RefMut.deref_contract.contract sliceProfile).ensures
      (exclusiveState, ()) guard ⟨guard, false⟩ (exclusiveState, ()) := by
  apply (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.deref_reference sliceProfile)
    (exclusiveState, ()) guard (.returned ⟨guard, false⟩ (exclusiveState, ()))
  · trivial
  · rfl

/-- V2 close preserves the unobserved compatibility field rather than performing
the signed delta subtraction present only in the v1 source. -/
theorem close_has_no_resize_update :
    (closedHeaderState.account handle).resizeDelta = account.resizeDelta := rfl

/-- The balance equation is mathematical for every Nat. A Rust scalar binding
must separately restrict that value to its source width. -/
theorem wide_balance_update :
    ((setLamports state (handle, Solanalib.Runtime.U64_LIMIT)).2.account handle).lamports =
      Solanalib.Runtime.U64_LIMIT ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_contract.ensures
      state (handle, Solanalib.Runtime.U64_LIMIT) () (setLamports state (handle,
        Solanalib.Runtime.U64_LIMIT)).2 :=
  ⟨rfl, Solanalib.Specs.SolanaAccountView.AccountView.Pool.set_lamports_reference
    state (handle, Solanalib.Runtime.U64_LIMIT) state_ready.2⟩

/-- Constructing a descriptor for a consumed token does not authorize a read. -/
theorem consumed_descriptor_cannot_read :
    (Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_contract.contract sliceProfile).ensures
      (releasedState, ()) guard ⟨guard, true⟩ (releasedState, ()) ∧
    (⟨guard, true⟩ : DataRef).read releasedState = .error .invalidGuard := by
  refine ⟨?_, rfl⟩
  exact (FamilyReference.at Solanalib.Specs.SolanaAccountView.RefMut.deref_mut_reference
    sliceProfile)
    (releasedState, ()) guard (.returned ⟨guard, true⟩ (releasedState, ())) trivial rfl

/-- A second destruction has an actual registry failure, so the successful
destructor contract still needs a live token. -/
theorem second_release_rejected :
    ¬ (Solanalib.Specs.SolanaAccountView.RefMut.release_contract.contract sliceProfile).requires
      (releasedState, ()) guard ∧
    Borrow.release releasedState guard = (.error .invalidGuard, releasedState) := by
  refine ⟨?_, rfl⟩
  rintro ⟨slot, live⟩
  cases live

/-- Missing handles retain the raw checked-acquisition failure. The mathematical
protocol contract does not silently restrict this branch to well-formed inputs. -/
theorem missing_account_borrow :
    let empty : State := ⟨[], []⟩
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_model empty handle =
      (.error .accountBorrowFailed, empty) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_contract.ensures
      empty handle (.error .accountBorrowFailed) empty := by
  refine ⟨rfl, ?_⟩
  exact Solanalib.Specs.SolanaAccountView.AccountView.Pool.try_borrow_reference ⟨[], []⟩ handle
    trivial

namespace Scalar

/-- No cell is available for a scalar load in this pool. -/
def emptyState : State := ⟨[], []⟩

/-- All four exposed scalar contracts reject the absent handle, while the
unchanged total references still compute their mathematical fallback values. -/
theorem missing_handle_rejected :
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_contract.requires emptyState
      handle ∧
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.data_len_contract.requires emptyState
      handle ∧
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_signer_contract.requires emptyState
      handle ∧
    ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_contract.requires emptyState
      (handle, .zero) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_model emptyState handle = (0,
      emptyState) ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_model emptyState (handle, .zero) =
      (true, emptyState) := by
  have missing : ¬ emptyState.HasAccount handle := by
    rintro ⟨cell, present⟩
    cases present
  exact ⟨missing, missing, missing, missing, rfl, rfl⟩

/-- Neither an arbitrary scalar value nor an owner comparison can satisfy the
new real-cell post when the selected handle is absent. -/
theorem missing_handle_no_real_cell_post :
    (∀ value after, ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_contract.ensures
      emptyState handle value after) ∧
    (∀ value after, ¬ Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_contract.ensures
      emptyState (handle, .zero) value after) := by
  constructor <;> intro value after post <;>
    obtain ⟨_, cell, present, _⟩ := post <;> cases present

/-- A client of the scalar contract recovers the actual current field and
unchanged state without unfolding its implementation or requiring full Ready. -/
theorem observation_from_current_cell {Value : Type} (observe : Account → Value)
    {run : State → Handle → Value × State}
    (spec : (observationContract observe).RealizedBy run)
    {before : State} {selected : Handle} {cell : Borrow.Cell Account}
    (present : before.lookupCell selected = some cell) :
    run before selected = (observe cell.value, before) := by
  obtain ⟨sameState, actual, lookup, value⟩ := spec before selected ⟨cell, present⟩
  rw [present] at lookup
  cases lookup
  exact Prod.ext value sameState

/-- The nonempty fixture satisfies each real-cell scalar post, including the
owner comparison; these are the exact exposed versioned contracts. -/
theorem current_values_satisfy_posts :
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_contract.ensures state handle 17
      state ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.data_len_contract.ensures state handle 3
      state ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_signer_contract.ensures state handle true
      state ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_contract.ensures state (handle,
      .zero) true state :=
  ⟨Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_reference state handle state_ready.2,
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.data_len_reference state handle
      state_ready.2,
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.is_signer_reference state handle
      state_ready.2,
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_reference state (handle, .zero)
      state_ready.2⟩

/-- A current scalar cell can exist even when an unrelated entry-length field
does not satisfy the complete source representation invariant. -/
def unrelatedInvalidState : State :=
  ⟨[⟨{ account with entryLen := Solanalib.Runtime.U64_LIMIT }, Borrow.Policy.accountView⟩], []⟩

/-- Scalar admission does not restore the full pool invariant. The current
balance and owner are still read from the present cell in this mathematical state. -/
theorem presence_without_full_ready :
    ¬ Ready unrelatedInvalidState handle ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_contract.requires
      unrelatedInvalidState handle ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_contract.ensures
      unrelatedInvalidState handle 17 unrelatedInvalidState ∧
    Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_contract.ensures
      unrelatedInvalidState (handle, .zero) true unrelatedInvalidState := by
  refine ⟨?_, ⟨_, rfl⟩, ?_, ?_⟩
  · intro ready
    have valid := (ready.1.2 _ (List.mem_singleton_self _)).2
    exact (Nat.lt_irrefl Solanalib.Runtime.U64_LIMIT) valid.2.2.1
  · exact Solanalib.Specs.SolanaAccountView.AccountView.Pool.lamports_reference
      unrelatedInvalidState handle ⟨_, rfl⟩
  · exact Solanalib.Specs.SolanaAccountView.AccountView.Pool.owned_by_reference
      unrelatedInvalidState (handle, .zero) ⟨_, rfl⟩

end Scalar

end SolanalibTest.Specs.SolanaAccountView.Lifecycle
