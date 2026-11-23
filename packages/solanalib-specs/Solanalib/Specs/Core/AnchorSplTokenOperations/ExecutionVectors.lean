/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CallbackGraph
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.AnchorSplTokenOperations.Builders

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Execution

/- Functional forms of selected primitive interpretations, together with
exact graph equivalences. These reuse the established conformance vector
graph construction and canonical vector ledger; no SDK implementation is
replaced or proved. -/

structure VecFn (State Element Resource U T : Type) where
  withCapacity : State → Nat → Option (Outcome State Resource U T)
  fromList : State → List Element → Option (Outcome State Resource U T)
  push : State → Resource × Element → Option (Outcome State Unit U T)
  extend : State → Resource × List Element → Option (Outcome State Unit U T)
  drop : State → Resource → Option (Outcome State Unit U T)

structure VecGraph {State Element Resource U T : Type} (ops : Owned.VectorOps State Element
  Resource U T)
    (fn : VecFn State Element Resource U T) : Prop where
  withCapacity : ∀ s a, PGraph (ops.withCapacity s a) (fn.withCapacity s a)
  fromList : ∀ s a, PGraph (ops.fromList s a) (fn.fromList s a)
  push : ∀ s a, PGraph (ops.push s a) (fn.push s a)
  extend : ∀ s a, PGraph (ops.extend s a) (fn.extend s a)
  drop : ∀ s a, PGraph (ops.drop s a) (fn.drop s a)

def refVec {E U T : Type} : VecFn (Owned.VectorState E) E Nat U T where
  withCapacity := fun s _ => some (.returned (s.allocate []).1 (s.allocate []).2)
  fromList := fun s v => some (.returned (s.allocate v).1 (s.allocate v).2)
  push := fun s (r, v) => (s.current r).map fun values => .returned () (s.set r (some (values ++
    [v])))
  extend := fun s (r, v) => (s.current r).map fun values => .returned () (s.set r (some (values ++
    v)))
  drop := fun s r => (s.current r).map fun _ => .returned () (s.set r none)

theorem returnsOf_graph {St A V U T : Type} (f : St → A → V × St) (b : St) (a : A) :
    PGraph (returnsOf (Unwind := U) (Terminal := T) f b a) (some (.returned (f b a).1 (f b a).2))
      := by
  intro o
  cases o <;> simp [returnsOf, Prod.ext_iff]

theorem refVec_graph {E U T : Type} : VecGraph (Owned.vectorReference (Element := E) (Unwind := U)
  (Terminal := T)) refVec where
  withCapacity := fun s a => returnsOf_graph (fun (state : Owned.VectorState E) (_ : Nat) =>
    state.allocate []) s a
  fromList := fun s a => returnsOf_graph Owned.VectorState.allocate s a
  push := fun s a => PGraph.exists_eq' _ (PGraph.ofOption (s.current a.1))
  extend := fun s a => PGraph.exists_eq' _ (PGraph.ofOption (s.current a.1))
  drop := fun s a => PGraph.exists_eq' _ (PGraph.ofOption (s.current a))

def VecFn.focus {Outer Inner E R U T : Type} (fn : VecFn Inner E R U T) (part : Owned.Focus Outer
  Inner) :
    VecFn Outer E R U T where
  withCapacity := fun s a => (fn.withCapacity (part.get s) a).map (part.liftOutcome s)
  fromList := fun s a => (fn.fromList (part.get s) a).map (part.liftOutcome s)
  push := fun s a => (fn.push (part.get s) a).map (part.liftOutcome s)
  extend := fun s a => (fn.extend (part.get s) a).map (part.liftOutcome s)
  drop := fun s a => (fn.drop (part.get s) a).map (part.liftOutcome s)

theorem VecGraph.focus {Outer Inner E R U T : Type} {ops : Owned.VectorOps Inner E R U T}
    {fn : VecFn Inner E R U T} (h : VecGraph ops fn) (part : Owned.Focus Outer Inner) :
    VecGraph (ops.focus part) (fn.focus part) where
  withCapacity := fun s a => PGraph.focusLift part (h.withCapacity (part.get s) a)
  fromList := fun s a => PGraph.focusLift part (h.fromList (part.get s) a)
  push := fun s a => PGraph.focusLift part (h.push (part.get s) a)
  extend := fun s a => PGraph.focusLift part (h.extend (part.get s) a)
  drop := fun s a => PGraph.focusLift part (h.drop (part.get s) a)


end Solanalib.Specs.Core.AnchorSplTokenOperations.Execution
