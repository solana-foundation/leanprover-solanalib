/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainConstructor
import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

/-!
# The allocated instruction constructors at the registered sample index

`InstructionAllocated.run types state plan` is the operational relation of
every versioned constructor family (`InstructionAllocated.family`). At the
registered sample index `Witness.sampleTypes` (two vector ledgers,
normal-only vector operations), it admits exactly one outcome for each input,
computed by `runF`; `run_fn` proves this. Both are the generic
`OnchainConstructor.runF`/`run_fn` at the primitive bundle of the sample ledgers
`samplePrims`. The checkers decide the registered family references through it.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.Allocated

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.InstructionAllocated

abbrev ST : Types := Witness.sampleTypes
abbrev St := Witness.State
abbrev Out (V : Type) := Outcome St V Nat Nat

/-! ## The constructor relation at the sample ledgers -/

def dbl (_ : St) (original later : Nat) : Nat := original + later

theorem double_fn : ∀ s o l t, ST.doubleUnwind s o l t ↔ t = dbl s o l :=
  fun _ _ _ _ => Iff.rfl

/-- The primitive bundle of the sample ledgers: the reference vector operations on
each half of the pair of ledgers, and the double-unwind combination of the sample. -/
def samplePrims : OnchainConstructor.ConstructorPrims ST where
  bytes := OnchainPrims.VecPrims.reference.focus Owned.Focus.fst
  metas := OnchainPrims.VecPrims.reference.focus Owned.Focus.snd
  dbl := dbl
  double_fn := double_fn

abbrev Result := Except Token.Error (Value ST)

/-- The computed outcome of the constructor relation at the sample index. -/
def runF (state : St) (plan : Plan) : Option (Out Result) :=
  OnchainConstructor.runF samplePrims state plan

/-- At the sample index, the constructor relation admits exactly `runF`. -/
theorem run_fn (state : St) (plan : Plan) (o : Out Result) :
    run ST state plan o ↔ runF state plan = some o :=
  OnchainConstructor.run_fn samplePrims state plan o

/-! ## Observation: returned instruction and heap counts

The native recording observes the returned instruction and the fresh
allocations and deallocations made during the call. In the ledger state each
`withCapacity`/`fromList` appends one slot and each drop retires one, starting
from the empty ledgers. -/

structure Heap where
  allocations : Nat
  deallocations : Nat
  deriving DecidableEq, Repr

def retired {E : Type} (l : Owned.VectorState E) : Nat := (l.filter (·.isNone)).length

def heapOf (s : St) : Heap := ⟨s.1.length + s.2.length, retired s.1 + retired s.2⟩

abbrev Observation := Except Token.Error Solanalib.Runtime.CpiInstruction × Heap

def observe? : Out Result → Option Observation
  | .returned (.ok v) s => (observe ST s v).map fun i => (.ok i, heapOf s)
  | .returned (.error e) s => some (.error e, heapOf s)
  | .unwound _ _ | .terminated _ => none

/-- The relation admits an outcome with the recorded observation exactly when
the computed outcome has it. -/
theorem admits_iff (state : St) (plan : Plan) (recorded : Observation) :
    (∃ o, run ST state plan o ∧ observe? o = some recorded) ↔
      (runF state plan).bind observe? = some recorded := by
  constructor
  · rintro ⟨o, ho, hobs⟩
    rw [(run_fn state plan o).1 ho]
    exact hobs
  · intro h
    cases hf : runF state plan with
    | none => rw [hf] at h; cases h
    | some o =>
      rw [hf, Option.bind_some] at h
      exact ⟨o, (run_fn state plan o).2 hf, h⟩

instance (state : St) (plan : Plan) (recorded : Observation) :
    Decidable (∃ o, run ST state plan o ∧ observe? o = some recorded) :=
  decidable_of_iff _ (admits_iff state plan recorded).symm

end SolanalibTest.Conformance.Library.Families.TokenInterface.Allocated
