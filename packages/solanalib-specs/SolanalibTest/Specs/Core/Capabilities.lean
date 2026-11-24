/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.AccountViewMapLaws
public import Solanalib.Specs.SolanaAccountView.Capabilities
public import Solanalib.Specs.Pinocchio.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Capabilities

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace Balance

open AccountViewObservation

/-- Only the two observation operations used by this sequential client. -/
def needs : Solanalib.Specs.SolanaAccountView.Capabilities.Selection :=
  (Capabilities.Selection.member Solanalib.Specs.SolanaAccountView.Capabilities.catalog
    .AccountView_Observation_set_lamports).union
  (Capabilities.Selection.member Solanalib.Specs.SolanaAccountView.Capabilities.catalog
    .AccountView_Observation_lamports)

/-- A client calls the supplied setter and then the supplied getter, using
the actual intermediate state. It unfolds neither reference implementation. -/
def writeRead (operations : Solanalib.Specs.SolanaAccountView.Capabilities.Operations) :
    Callback.Run State Nat Nat Empty Empty :=
  Callback.bind (operations .AccountView_Observation_set_lamports PUnit.unit)
    (fun _ after => operations .AccountView_Observation_lamports PUnit.unit after ())

/-- Every conforming implementation gives read-after-write and preserves the
domain for later borrows. Both requested contract fields are consumed. -/
theorem writeRead_result {operations : Solanalib.Specs.SolanaAccountView.Capabilities.Operations}
    (spec : Solanalib.Specs.SolanaAccountView.Capabilities.Spec needs operations)
    {before after : State} {value observed : Nat}
    (valid : before.Valid) (bounded : value < Solanalib.Runtime.U64_LIMIT)
    (called : writeRead operations before value (.returned observed after)) :
    observed = value ∧ after.account.lamports = observed ∧
      after = before.setLamports value ∧ after.Valid := by
  obtain ⟨intermediate, written, read⟩ := called
  cases intermediate with
  | returned result middle =>
      have changed := spec.holds .AccountView_Observation_set_lamports PUnit.unit (Or.inl rfl)
        before value (.returned result middle) bounded written
      change middle = before.setLamports value at changed
      have observedValue := spec.holds .AccountView_Observation_lamports PUnit.unit (Or.inr rfl)
        middle () (.returned observed after) trivial read
      change after = middle ∧ observed = middle.account.lamports at observedValue
      have observedEq : observed = value := observedValue.2.trans
        (congrArg (fun state : State => state.account.lamports) changed)
      rw [observedValue.1, changed]
      exact ⟨observedEq, observedEq.symm, rfl, State.setLamports_valid valid bounded⟩
  | unwound impossible _ | terminated impossible => exact nomatch impossible

/-- A concrete valid input for a nonempty execution of the conditional client. -/
def initial : State := ⟨⟨.zero, false, true, false⟩, ⟨.zero, 0, 0, 0, .free, some []⟩⟩

/-- The selected reference bundle supplies only the two assumptions of this client. -/
theorem reference_needs : Solanalib.Specs.SolanaAccountView.Capabilities.Spec needs
    Solanalib.Specs.SolanaAccountView.Capabilities.reference :=
  Solanalib.Specs.SolanaAccountView.Capabilities.reference_spec.restrict (fun _ _ _ => trivial)

/-- The closed client really performs the write and reads its updated balance. -/
theorem reference_execution :
    writeRead Solanalib.Specs.SolanaAccountView.Capabilities.reference initial 7
      (.returned 7 (initial.setLamports 7)) :=
  ⟨.returned () (initial.setLamports 7), rfl, rfl⟩

/-- Both concrete conclusions follow from the conditional client theorem:
the getter observes the updated account, and that account remains valid. -/
theorem reference_result :
    (initial.setLamports 7).account.lamports = 7 ∧
      (initial.setLamports 7).Valid := by
  have result := writeRead_result reference_needs
    (before := initial) ⟨by decide, by decide, [], rfl, rfl⟩ (by decide) reference_execution
  exact ⟨result.2.1.trans result.1, result.2.2.2⟩

/-- A wrong getter demonstrates that a capability cannot be replaced by an
unrelated successful interpretation when subsets are composed. -/
def wrongOperations : Solanalib.Specs.SolanaAccountView.Capabilities.Operations := fun key =>
  match key with
  | .AccountView_Observation_lamports => fun _ =>
      returnsOf (fun (before : State) (_ : Unit) => ((99 : Nat), before))
  | key => Solanalib.Specs.SolanaAccountView.Capabilities.reference key

/-- The same catalog and requested getter reject the incorrect return. -/
theorem wrong_getter_rejected :
    ¬ Solanalib.Specs.SolanaAccountView.Capabilities.Spec needs wrongOperations := by
  intro spec
  have wrong := spec.holds .AccountView_Observation_lamports PUnit.unit (Or.inr rfl)
    initial () (.returned (99 : Nat) initial) trivial rfl
  have impossible : (99 : Nat) = 0 := wrong.2
  contradiction

end Balance

namespace Guards

open AccountView

/-- A client needs mapping and release, including all interpreted target types. -/
def needs : Solanalib.Specs.SolanaAccountView.Capabilities.Selection :=
  (Capabilities.Selection.member Solanalib.Specs.SolanaAccountView.Capabilities.catalog
    .Ref_try_map).union
  (Capabilities.Selection.member Solanalib.Specs.SolanaAccountView.Capabilities.catalog
    .Ref_release)

/-- A normal mapping result, including Err, supplies the live replacement
token to release. Both tokens are then unusable; callback cells and auxiliary
effects remain those reached before release. -/
theorem map_then_release
    {operations : Solanalib.Specs.SolanaAccountView.Capabilities.Operations}
    (spec : Solanalib.Specs.SolanaAccountView.Capabilities.Spec needs operations)
    (profile : TryMapProfile) {before middle after : profile.target.World}
    {args : TryMapArgs profile} {result : TryMapResult profile}
    (ready : (genericTryMapContract profile .shared).requires before args)
    (mapped : operations .Ref_try_map profile before args (.returned result middle))
    (released : operations .Ref_release profile.target middle (resultGuard profile result)
      (.returned () after)) :
    after.1.cells = middle.1.cells ∧ after.2 = middle.2 ∧
      after.1.resolve args.guard = none ∧
      after.1.resolve (resultGuard profile result) = none := by
  have mapPost := spec.holds .Ref_try_map profile (Or.inl rfl)
    before args (.returned result middle) ready mapped
  obtain ⟨nextReady, oldRetired⟩ := tryMap_returned_guardReady profile .shared ready mapPost
  obtain ⟨_, slot, _, live, _, _, _⟩ := nextReady
  have releasePost := spec.holds .Ref_release profile.target (Or.inr rfl)
    middle (resultGuard profile result) (.returned () after) ⟨slot, live⟩ released
  change Borrow.release middle.1 (resultGuard profile result) = (.ok (), after.1) ∧
    after.2 = middle.2 at releasePost
  have stateEq := congrArg Prod.snd releasePost.1
  change (Borrow.release middle.1 (resultGuard profile result)).2 = after.1 at stateEq
  rw [← stateEq]
  exact ⟨Borrow.release_cells _ _, releasePost.2,
    (oldRetired.persists (Borrow.release_history _ _)).unusable,
    (Borrow.release_retired live).unusable⟩

/-- The same subset also consumes the actual unwind state from its mapping
contract, without requiring or executing release after that unwind. -/
theorem map_unwind_retains
    {operations : Solanalib.Specs.SolanaAccountView.Capabilities.Operations}
    (spec : Solanalib.Specs.SolanaAccountView.Capabilities.Spec
      (Capabilities.Selection.member Solanalib.Specs.SolanaAccountView.Capabilities.catalog
        .Ref_try_map) operations)
    (profile : TryMapProfile) {before after : profile.target.World}
    {args : TryMapArgs profile} {reason : profile.Unwind}
    (ready : (genericTryMapContract profile .shared).requires before args)
    (mapped : operations .Ref_try_map profile before args (.unwound reason after)) :
    PoolWellFormed after.1 ∧ after.1.resolve args.guard = none := by
  have post := spec.holds .Ref_try_map profile rfl before args
    (.unwound reason after) ready mapped
  have kept := tryMap_unwind_retired profile .shared post
  exact ⟨kept.1, kept.2.unusable⟩

/-- A concrete mapped-error callback changes captured state before returning. -/
abbrev errorProfile : TryMapProfile := ⟨sliceProfileWithAux Nat, Nat, Nat, Nat⟩

/-- A live shared guard and independent captured state. -/
def initial : errorProfile.target.World := (witnessGuardState .shared, (0 : Nat))

/-- This callback has an ordinary Err after a visible captured-state update. -/
def errorArgs : TryMapArgs errorProfile :=
  ⟨witnessGuard, fun (before : State × Nat) _ _ outcome =>
    outcome = .returned (.error 17) (before.1, (before.2 + 5 : Nat))⟩

/-- The error callback preserves its actual held reference and every guard. -/
theorem error_ready : (genericTryMapContract errorProfile .shared).requires initial errorArgs := by
  refine ⟨⟨_, _, rfl, rfl, rfl⟩, ?_⟩
  intro slot cell live present produced callback
  change produced = .returned (.error 17) (witnessGuardState .shared, (5 : Nat)) at callback
  subst produced
  obtain ⟨valid, currentSlot, currentCell, currentLive, currentPresent, _, range⟩ :=
    witness_guard_ready .shared
  change (witnessGuardState .shared).resolve witnessGuard = some slot at live
  change (witnessGuardState .shared).lookupCell slot.cell = some cell at present
  have sameSlot : slot = currentSlot := by rw [currentLive] at live; cases live; rfl
  subst slot
  have sameCell : cell = currentCell := by rw [currentPresent] at present; cases present; rfl
  subst cell
  exact ⟨sliceFrame_refl valid.1 _, valid, currentCell, currentPresent, range⟩

/-- Mapping retains the changed state of the callback under the replacement token. -/
def changed : errorProfile.target.World :=
  ((Borrow.transfer initial.1 witnessGuard ⟨0, 0⟩).2, (5 : Nat))

/-- Releasing that replacement token keeps the already changed state. -/
def finished : errorProfile.target.World :=
  ((Borrow.release changed.1 (nextGuard witnessGuard)).2, (5 : Nat))

/-- Both primitive calls are actual reference executions on the Err path. -/
theorem error_calls :
    Solanalib.Specs.SolanaAccountView.Capabilities.reference .Ref_try_map errorProfile
      initial errorArgs (.returned (.error (nextGuard witnessGuard, 17)) changed) ∧
    Solanalib.Specs.SolanaAccountView.Capabilities.reference .Ref_release errorProfile.target
      changed (nextGuard witnessGuard) (.returned () finished) := by
  refine ⟨?_, rfl⟩
  exact genericTryMap_of_callback errorProfile
    (before := initial) (args := errorArgs)
    (slot := ⟨witnessHandle, .shared, 0, ⟨0, 0⟩⟩)
    (cell := ⟨Account.empty, Borrow.Policy.accountView⟩)
    (produced := .returned (.error 17) (initial.1, (5 : Nat)))
    rfl rfl error_ready.2 rfl

/-- The conditional client proves cleanup on a real error execution, while
preserving the effect performed before Err. Neither token can be reused. -/
theorem error_cleanup_result :
    finished.2 = (5 : Nat) ∧ finished.1.resolve witnessGuard = none ∧
      finished.1.resolve (nextGuard witnessGuard) = none := by
  have spec : Solanalib.Specs.SolanaAccountView.Capabilities.Spec needs
      Solanalib.Specs.SolanaAccountView.Capabilities.reference :=
    Solanalib.Specs.SolanaAccountView.Capabilities.reference_spec.restrict (fun _ _ _ => trivial)
  have result := map_then_release spec errorProfile error_ready error_calls.1 error_calls.2
  exact ⟨rfl, result.2.2⟩

end Guards

namespace Selection

/-- One actual generic getter index has a stateful initialized reply. -/
def onchain : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := Nat
  Terminal := Nat
  target := .solana
  read := fun before _ outcome =>
    outcome = .returned ⟨0, some Sysvar.zeroClock⟩ (before + 3) ∨
    outcome = .unwound 9 (before + 5) ∨ outcome = .terminated 11

/-- A different source profile remains a different index of the same family. -/
def host : Sysvar.GetterIndex Sysvar.Clock := { onchain with target := .hostStub }

/-- Selecting one family instance does not select another target profile. -/
theorem different_index_excluded :
    ¬ Capabilities.Selection.one Solanalib.Specs.Pinocchio.Capabilities.catalog
      .sysvars_clock_Clock_get onchain .sysvars_clock_Clock_get host := by
  intro selected
  unfold Capabilities.Selection.one at selected
  have same : host = onchain := by
    exact eq_of_heq (Sigma.mk.inj selected).2
  have target := congrArg Sysvar.GetterIndex.target same
  contradiction

/-- Selecting a member retains every genuine generic instantiation. -/
theorem whole_family_includes_both :
    Capabilities.Selection.member Solanalib.Specs.Pinocchio.Capabilities.catalog
      .sysvars_clock_Clock_get .sysvars_clock_Clock_get onchain ∧
    Capabilities.Selection.member Solanalib.Specs.Pinocchio.Capabilities.catalog
      .sysvars_clock_Clock_get .sysvars_clock_Clock_get host := ⟨rfl, rfl⟩

/-- A tagged combination preserves the exact member types of both versions. -/
theorem two_libraries_compose :
    Capabilities.Spec
      (Solanalib.Specs.SolanaAccountView.Capabilities.catalog.sum
        Solanalib.Specs.Pinocchio.Capabilities.catalog)
      (Capabilities.sumSelection Balance.needs
        (Capabilities.Selection.one Solanalib.Specs.Pinocchio.Capabilities.catalog
          .sysvars_clock_Clock_get onchain))
      (Capabilities.sumOperations Solanalib.Specs.SolanaAccountView.Capabilities.reference
        Solanalib.Specs.Pinocchio.Capabilities.reference) :=
  Capabilities.sumSpec Balance.reference_needs
    (Solanalib.Specs.Pinocchio.Capabilities.reference_spec.restrict (fun _ _ _ => trivial))

/-- Empty interpretations satisfy partial correctness but supply no execution.
Capability assumptions must not be advertised as a termination guarantee. -/
theorem empty_operations_do_not_supply_progress :
    let operations : Solanalib.Specs.SolanaAccountView.Capabilities.Operations :=
      fun _ _ _ _ _ => False
    Solanalib.Specs.SolanaAccountView.Capabilities.Spec Balance.needs operations ∧
      ¬ ∃ outcome, operations .AccountView_Observation_lamports PUnit.unit Balance.initial ()
        outcome := by
  refine ⟨⟨fun _ _ _ _ _ _ _ impossible => False.elim impossible⟩, ?_⟩
  rintro ⟨_, impossible⟩
  exact impossible

end Selection

end SolanalibTest.Specs.Core.Capabilities
