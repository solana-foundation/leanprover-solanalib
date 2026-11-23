/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewMap

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- The generic infallible map contract over all supplied target and exit types. -/
def mapFamily (mode : Mode) : Family where
  Index := MapProfile
  State := fun profile => profile.target.World
  Args := fun profile => TryMapArgs profile.fallible
  Value := fun _ => Guard
  Unwind := MapProfile.Unwind
  Terminal := MapProfile.Terminal
  contract := fun profile => genericMapContract profile mode

/-- The infallible source reference delegates to the same fallible protocol. -/
def mapRun (mode : Mode) : FamilyRun (mapFamily mode) :=
  fun profile before args outcome =>
    genericTryMapRun profile.fallible before args (mapOutcome profile outcome)

theorem mapFamily_reference (mode : Mode) :
    FamilyReference (mapFamily mode) (mapRun mode) := by
  intro profile before args outcome ready step
  exact genericTryMap_reference profile.fallible mode before args _ ready step

/-- A byte-range target supplies an ordinary finite mapping example. -/
def mapSample : MapProfile := ⟨sliceProfile, Empty, Empty⟩

/-- The infallible map has the same concrete successful lease transfer. -/
theorem mapFamily_execution (mode : Mode) :
    FamilyHasExecution (mapFamily mode) (mapRun mode) mapSample := by
  let before := (witnessGuardState mode, ())
  let args := identityMapArgs mapSample.fallible witnessGuard
  refine ⟨before, args, .returned (nextGuard witnessGuard)
    ((Borrow.transfer before.1 witnessGuard ⟨0, 0⟩).2, ()), ?_, ?_⟩
  · exact ⟨⟨_, _, rfl, rfl, rfl⟩, identityMap_safe Empty mode⟩
  · exact genericTryMap_of_callback mapSample.fallible
      (before := before) (args := args)
      (slot := ⟨witnessHandle, mode, 0, ⟨0, 0⟩⟩)
      (cell := ⟨Account.empty, Borrow.Policy.accountView⟩)
      (produced := .returned (.ok ⟨0, 0⟩) before)
      rfl rfl (identityMap_safe Empty mode) rfl

theorem mapFamily_satisfiable (mode : Mode) :
    FamilySatisfiable (mapFamily mode) mapSample :=
  (mapFamily_execution mode).satisfiable

end Solanalib.Specs.Core.AccountView
