/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.FieldReference
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionMeta

/-- A clone borrows an existing AccountMeta. The access interpretation retains
the source reference and observes its current value; cloning acquires no guard
and allocates no vector. Rust Boolean representation is a separate binding. -/
structure Types where
  State : Type
  Reference : Type
  access : FieldReference.Access State Reference Instruction.Meta

/-- The derived clone copies all three fields without modifying its source. -/
def run (types : Types) (before : types.State) (reference : types.Reference) :
    Outcome types.State Instruction.Meta Empty Empty → Prop :=
  fun outcome => ∃ value, types.access.current before reference = some value ∧
    outcome = .returned value before

def family : Family where
  Index := Types
  State := Types.State
  Args := Types.Reference
  Value := fun _ => Instruction.Meta
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun types => .returning
    (fun before reference => ∃ value, types.access.Reads before reference value)
    (fun before reference value after =>
      after = before ∧ types.access.Reads before reference value)

def reference : FamilyRun family := run

theorem reference_correct : FamilyReference family reference := by
  intro types before source outcome admitted execution
  obtain ⟨value, current, rfl⟩ := execution
  obtain ⟨_, live, _⟩ := admitted
  exact ⟨rfl, live, current⟩

/-- Every admitted source borrow has a normal clone with its exact current
contents. No allocator or arbitrary success relation is needed. -/
theorem returns_current (types : Types) (before : types.State)
    (source : types.Reference) (value : Instruction.Meta)
    (read : types.access.Reads before source value) :
    (family.contract types).requires before source ∧
      run types before source (.returned value before) :=
  ⟨⟨value, read⟩, ⟨value, read.2, rfl⟩⟩

def sample : Types where
  State := Instruction.Meta
  Reference := Unit
  access := ⟨fun _ _ => True, fun state _ => some state⟩

theorem sample_satisfiable : FamilySatisfiable family sample :=
  ⟨Instruction.accountMeta .zero true false, (), _, trivial, rfl⟩

theorem sample_hasExecution : FamilyHasExecution family reference sample := by
  let value := Instruction.accountMeta .zero true false
  exact ⟨value, (), .returned value value,
    ⟨value, trivial, rfl⟩, ⟨value, rfl, rfl⟩⟩

end Solanalib.Specs.Core.InstructionMeta
