/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.SolanaAccountView.Mapping

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountView.ExternalTarget

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountView
open SolanalibTest.Specs.SolanaAccountView.Lifecycle

/-- A mathematical descriptor tag, deliberately outside every ordinary account
range. It is not a claimed physical pointer or serialized usize offset. -/
def externalTag : Nat := Solanalib.Runtime.U64_LIMIT

/-- This interpretation includes ordinary account byte targets and separate
captured storage. The access permission of the latter is supplied independently of
the held account lease. The descriptor type has no fixed memory-layout meaning. -/
def targetProfile : GuardProfile where
  View := Slice
  Aux := Solanalib.Runtime.Bytes
  valid := fun cells external handle view =>
    if view.offset = externalTag then view.length = external.length
    else ∃ cell, cells[handle.cell]? = some cell ∧ view.ValidFor cell.value
  footprint := fun _ _ before after => after = before

/-- A reference interpretation admitting ordinary slices and separately authorized external storage.
-/
def profile : TryMapProfile := ⟨targetProfile, Unit, Empty, Empty⟩
/-- A shared account guard paired with independent external bytes. -/
def before : targetProfile.World := (sharedState, ([42, 43] : Solanalib.Runtime.Bytes))
/-- The descriptor for the two-byte external target. -/
def target : Slice := ⟨externalTag, 2⟩
/-- The callback that maps the account reference to its authorized external target. -/
def args : TryMapArgs profile :=
  ⟨guard, fun _ _ _ outcome => outcome = .returned (.ok target) before⟩
/-- The world after mapping, with the original account lease still held. -/
def after : targetProfile.World :=
  ((Borrow.transfer sharedState guard target).2, ([42, 43] : Solanalib.Runtime.Bytes))

/-- Target reads use the supplied interpretation and current world of the descriptor. -/
def readTarget (cells : List (Borrow.Cell Account)) (external : Solanalib.Runtime.Bytes)
    (handle : Handle) (view : Slice) : Solanalib.Runtime.Bytes :=
  if view.offset = externalTag then external
  else (((cells[handle.cell]?).map Borrow.Cell.value).getD Account.empty).read view

theorem shared_ready : GuardReady sharedState .shared guard :=
  acquire_guardReady state_ready.1 shared_step

theorem unchanged_frame :
    Borrow.CallbackFrame targetProfile.footprint sharedState sharedState guard :=
  Borrow.CallbackFrame.refl _ _ shared_ready.1.1 _ (fun _ _ _ => rfl)

theorem callback_safe : profile.CallbackSafe before args := by
  intro slot cell _ _ produced step
  change produced = .returned (.ok target) before at step
  subst produced
  exact ⟨unchanged_frame, shared_ready.1, rfl⟩

theorem precondition :
    (Solanalib.Specs.SolanaAccountView.Ref.try_map_contract.contract profile).requires before args
      :=
  ⟨⟨_, _, rfl, rfl, rfl⟩, callback_safe⟩

/-- The shared source family supports a target outside the leased account. -/
theorem reference_runs :
    Solanalib.Specs.SolanaAccountView.Ref.try_map_model profile before args
      (.returned (.ok (nextGuard guard)) after) := by
  exact genericTryMap_of_callback profile (before := before) (args := args)
    (slot := ⟨handle, .shared, 0, ⟨0, 3⟩⟩) (cell := ⟨account, Borrow.Policy.accountView⟩)
    (produced := .returned (.ok target) before) rfl rfl callback_safe rfl

theorem mapping_contract :
    (Solanalib.Specs.SolanaAccountView.Ref.try_map_contract.contract profile).ensures before args
      (.ok (nextGuard guard)) after :=
  (FamilyReference.at Solanalib.Specs.SolanaAccountView.Ref.try_map_reference profile)
    before args _ precondition reference_runs

/-- The resulting target permission is separate from the still-held source lease. -/
theorem target_reference_ready :
    targetProfile.Ready .shared after (nextGuard guard) ∧ Borrow.Retired after.1 guard :=
  tryMap_returned_guardReady profile .shared precondition mapping_contract

theorem mapped_reads_external_storage :
    (⟨nextGuard guard, false⟩ : DataRef).project targetProfile readTarget after =
      .ok [42, 43] ∧
    after.1.lease handle = .shared 1 := ⟨rfl, rfl⟩

/-- The ordinary byte-range precondition rejects this non-account target.
Clients must use the generic target interpretation for its subsequent accesses. -/
theorem external_target_is_not_an_account_slice :
    ¬ GuardReady after.1 .shared (nextGuard guard) := by
  rintro ⟨_, slot, cell, live, present, _, range⟩
  change some ⟨handle, .shared, 1, target⟩ = some slot at live
  cases live
  change some ⟨account, Borrow.Policy.accountView⟩ = some cell at present
  cases present
  change externalTag + 2 ≤ 3 at range
  have large : 3 < externalTag := by decide
  omega

/-- Account header operations remain composable with the mapped reference.
They preserve its lease and cannot redirect its separately interpreted target. -/
theorem header_update_with_external_reference :
    let changed := ((setLamports after.1 (handle, 66)).2, after.2)
    (State.account changed.1 handle).lamports = 66 ∧
    (⟨nextGuard guard, false⟩ : DataRef).project targetProfile readTarget changed =
      .ok [42, 43] ∧
    changed.1.lease handle = .shared 1 := ⟨rfl, rfl, rfl⟩

/-- A counterexample world that has no external target bytes. -/
def missingWorld : targetProfile.World := (sharedState, ([] : Solanalib.Runtime.Bytes))
/-- A proposed mapping that lacks the permission of the returned external target. -/
def missingArgs : TryMapArgs profile :=
  ⟨guard, fun _ _ _ outcome => outcome = .returned (.ok target) missingWorld⟩

/-- A held source lease cannot authorize a returned target whose separate
storage permission is absent. The safe-callback premise rejects that execution. -/
theorem missing_target_permission_rejected :
    ¬ (Solanalib.Specs.SolanaAccountView.Ref.try_map_contract.contract profile).requires
      missingWorld missingArgs := by
  intro ready
  have invalid := ready.2 ⟨handle, .shared, 0, ⟨0, 3⟩⟩
    ⟨account, Borrow.Policy.accountView⟩ rfl rfl (.returned (.ok target) missingWorld) rfl
  have impossible : (2 : Nat) = 0 := invalid.2.2
  cases impossible

end SolanalibTest.Specs.SolanaAccountView.ExternalTarget
