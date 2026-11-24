/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiWitness
public import Solanalib.Specs.Core.OpaqueCpiSdkOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.OwnedWitness

open Solanalib.Runtime Sdk.Owned

/-- A finite one-slot owner protocol. This is a consistency instance, not an
implementation of the SDK allocator or an invocation body. -/
def clone (before : Option CpiInstruction) (instruction : CpiInstruction) :
    Outcome (Option CpiInstruction) Unit Empty Unit → Prop
  | .returned () after => before = none ∧ after = some instruction
  | .unwound reason _ => nomatch reason
  | .terminated () => True

def drop (_before : Option CpiInstruction) (_resource : Unit) :
    Outcome (Option CpiInstruction) Unit Empty Unit → Prop
  | .returned () after => after = none
  | .unwound reason _ => nomatch reason
  | .terminated () => True

def provider : Provider where
  State := Option CpiInstruction
  Resource := Unit
  Terminal := Unit
  current := fun state _ => state
  clone := clone
  drop := drop
  clone_current := by intro _ _ resource _ h; cases resource; exact h.2
  clone_fresh := by intro _ _ resource _ h; cases resource; exact h.1
  drop_current := by intro _ _ _ h; exact h

def index : Sdk.Owned.Index := ⟨Witness.index, provider⟩

def before : State index := ⟨Witness.sdkBefore, none⟩

theorem success : Run index before Witness.signedArgs (.returned (.ok ()) before) :=
  .returned (resource := ()) rfl ⟨rfl, rfl⟩ ⟨Witness.success, rfl⟩ rfl

theorem signedHasExecution :
    FamilyHasExecution signedFamily signedRun index :=
  ⟨before, Witness.signedArgs, .returned (.ok ()) before, trivial, success⟩

theorem signedSatisfiable : FamilySatisfiable signedFamily index :=
  signedHasExecution.satisfiable

theorem unsignedHasExecution :
    FamilyHasExecution unsignedFamily unsignedRun index :=
  ⟨before, Witness.unsignedArgs, .returned (.ok ()) before, trivial, success⟩

theorem unsignedSatisfiable : FamilySatisfiable unsignedFamily index :=
  unsignedHasExecution.satisfiable

/-- A cloning failure is a terminal outcome before invoking the callee. -/
theorem allocation_terminal :
    Run index before Witness.signedArgs (.terminated (.local ())) :=
  .cloneTerminal rfl trivial

/-- A cleanup failure remains terminal after a successful canonical CPI. -/
theorem cleanup_terminal :
    Run index before Witness.signedArgs (.terminated (.local ())) :=
  .dropTerminal (resource := ()) rfl ⟨rfl, rfl⟩ ⟨Witness.success, rfl⟩ trivial

end Solanalib.Specs.Core.OpaqueCpi.OwnedWitness
