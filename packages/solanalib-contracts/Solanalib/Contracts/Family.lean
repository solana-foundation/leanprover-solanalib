/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Contracts

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Contracts.Model

/-- A family of source-facing contracts. The index can carry Type-valued Rust
model parameters as well as callback and profile choices. Each instantiated
model uses ordinary Type-valued state, arguments and outcomes. This does not
restrict a generic API to one concrete state or account representation. -/
structure Family where
  /-- Source types and explicit provider or target choices. -/
  Index : Type 1
  /-- The ambient state of each instantiation. -/
  State : Index → Type
  /-- The function arguments of each instantiation. -/
  Args : Index → Type
  /-- Ordinary returned values, including any Result error. -/
  Value : Index → Type
  /-- Reasons carried by finite unwinding exits. -/
  Unwind : Index → Type
  /-- Reasons carried by terminal exits. -/
  Terminal : Index → Type
  /-- The model predicate at the exact selected instantiation. -/
  contract : (index : Index) → Solanalib.Contracts.Model (State index) (Args index)
    (Value index) (Unwind index) (Terminal index)

/-- A reference relation for every member of an indexed contract family. -/
abbrev FamilyRun (family : Family) :=
  (index : family.Index) → family.State index → family.Args index →
    Outcome (family.State index) (family.Value index)
      (family.Unwind index) (family.Terminal index) → Prop

/-- Universal partial correctness of the reference family. A closed theorem
of this proposition may quantify source types through the index without
taking an assumed proof or an arbitrary instantiation as a theorem parameter. -/
def FamilyReference (family : Family) (run : FamilyRun family) : Prop :=
  ∀ index, (family.contract index).Holds (run index)

/-- An explicitly registered instantiation has a satisfiable precondition.
Other instantiations may have uninhabited source types or stronger requirements. -/
def FamilySatisfiable (family : Family) (sample : family.Index) : Prop :=
  (family.contract sample).Satisfiable

/-- An actual permitted finite reference execution at the registered sample.
This accompanies universal reference correctness; it does not turn that
partial-correctness assertion into a termination guarantee. -/
def FamilyHasExecution (family : Family) (run : FamilyRun family)
    (sample : family.Index) : Prop :=
  (family.contract sample).HasExecution (run sample)

/-- Family reference correctness specializes to any selected source types and
profile, independently of the instantiation used for the nonvacuity witness. -/
theorem FamilyReference.at {family : Family} {run : FamilyRun family}
    (reference : FamilyReference family run) (index : family.Index) :
    (family.contract index).Holds (run index) := reference index

/-- The actual sample execution also witnesses its precondition. -/
theorem FamilyHasExecution.satisfiable {family : Family} {run : FamilyRun family}
    {sample : family.Index} (execution : FamilyHasExecution family run sample) :
    FamilySatisfiable family sample :=
  Solanalib.Contracts.Model.HasExecution.satisfiable execution

end Solanalib.Contracts.Model
