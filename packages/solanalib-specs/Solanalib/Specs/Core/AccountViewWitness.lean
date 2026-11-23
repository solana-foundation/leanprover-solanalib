/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountView

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- A closed one-account world, with no live leases. -/
def witnessState : State := ⟨[⟨Account.empty, Borrow.Policy.accountView⟩], []⟩

/-- The existing account in witnessState. -/
def witnessHandle : Handle := ⟨0⟩

/-- A closed live guard token. -/
def witnessGuard : Guard := ⟨0, 0⟩

/-- One identified shared or exclusive acquisition of the empty data range. -/
def witnessGuardState (mode : Mode) : State :=
  { witnessState with slots := [some ⟨witnessHandle, mode, 0, ⟨0, 0⟩⟩] }

theorem witness_ready : Ready witnessState witnessHandle := by
  constructor
  · constructor
    · constructor
      · intro id slot live
        simp [Borrow.State.lookupSlot, witnessState] at live
      · intro handle cell present
        rcases handle with ⟨index⟩
        cases index with
        | zero =>
          simp [Borrow.State.lookupCell, witnessState] at present
          subst cell
          simp [Borrow.State.exclusiveCount, Borrow.State.sharedCount, Borrow.State.count,
            witnessState, Borrow.Policy.accountView]
        | succ index =>
          simp [Borrow.State.lookupCell, witnessState] at present
    · intro cell member
      simp only [witnessState, List.mem_singleton] at member
      subst cell
      exact ⟨rfl, Account.empty_valid_core⟩
  · exact ⟨_, rfl⟩

theorem witness_guard_ready (mode : Mode) :
    GuardReady (witnessGuardState mode) mode witnessGuard := by
  constructor
  · constructor
    · constructor
      · intro id slot live
        cases id with
        | zero =>
          simp [Borrow.State.lookupSlot, witnessGuardState] at live
          subst slot
          exact ⟨_, rfl⟩
        | succ id => simp [Borrow.State.lookupSlot, witnessGuardState] at live
      · intro handle cell present
        rcases handle with ⟨index⟩
        cases index with
        | zero =>
          simp [Borrow.State.lookupCell, witnessGuardState, witnessState] at present
          subst cell
          cases mode <;>
            decide
        | succ index =>
          simp [Borrow.State.lookupCell, witnessGuardState, witnessState] at present
    · intro cell member
      simp only [witnessGuardState, witnessState, List.mem_singleton] at member
      subst cell
      exact ⟨rfl, Account.empty_valid_core⟩
  · exact ⟨_, _, rfl, rfl, rfl, Nat.le_refl 0⟩

theorem observation_satisfiable {Value : Type} (observe : Account → Value) :
    (observationContract observe).Satisfiable :=
  ⟨witnessState, witnessHandle, witness_ready.2⟩

theorem clone_satisfiable : clone_contract.Satisfiable :=
  ⟨witnessState, witnessHandle, trivial⟩

theorem address_satisfiable : address_contract.Satisfiable :=
  ⟨witnessState, witnessHandle, trivial⟩

theorem owner_satisfiable : owner_contract.Satisfiable :=
  ⟨witnessState, witnessHandle, trivial⟩

theorem owned_by_satisfiable : owned_by_contract.Satisfiable :=
  ⟨witnessState, (witnessHandle, .zero), witness_ready.2⟩

theorem set_lamports_satisfiable : set_lamports_contract.Satisfiable :=
  ⟨witnessState, (witnessHandle, 0), witness_ready.2⟩

theorem borrow_satisfiable (mode : Mode) : (borrowContract mode).Satisfiable :=
  ⟨witnessState, witnessHandle, trivial⟩

theorem deref_satisfiable (mode : Mode) (writable : Bool) :
    (derefContract mode writable).Satisfiable :=
  ⟨witnessGuardState mode, witnessGuard, trivial⟩

theorem release_satisfiable (mode : Mode) : (releaseContract mode).Satisfiable :=
  ⟨witnessGuardState mode, witnessGuard, ⟨_, rfl⟩⟩


/-- The closed empty account admits header-only close. -/
theorem closeHeader_satisfiable : closeHeader_contract.Satisfiable :=
  ⟨witnessState, witnessHandle, fun _ => witness_ready.2⟩

end Solanalib.Specs.Core.AccountView
