/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAccountInfo

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAccountInfo.RcLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountInfoRc

/-- Cloning and then dropping the new owner performs four distinct Rc calls.
The field handles remain aliases; the provider state records the ownership work. -/
theorem clone_then_drop :
    Callback.bind (cloneCall traceOps) (fun info state => dropCall traceOps state info)
      [] AccountInfo.sampleInfo (.returned ()
        [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩, .drop .lamports ⟨0⟩, .drop .data ⟨1⟩]) := by
  refine ⟨.returned AccountInfo.sampleInfo [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩], ?_, ?_⟩
  · exact ⟨.returned () [.clone .lamports ⟨0⟩], rfl,
      .returned () [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩], rfl, rfl⟩
  · exact ⟨.returned () [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩, .drop .lamports ⟨0⟩], rfl, rfl⟩

def firstStops : Ops (List Event) String where
  cloneRc := fun _ args outcome => match args.1 with
    | .lamports => outcome = .terminated "lamports-overflow"
    | .data => False
  dropRc := fun _ _ _ => False

/-- Terminal overflow on the first Rc invokes neither the second clone nor a
cleanup provider. There is no fabricated state following termination. -/
theorem first_terminal_stops_cloning :
    cloneCall firstStops [] AccountInfo.sampleInfo (.terminated "lamports-overflow") :=
  ⟨.terminated "lamports-overflow", rfl, rfl⟩

def secondStops : Ops (List Event) String where
  cloneRc := fun state args outcome => match args.1 with
    | .lamports => outcome = .returned () (state ++ [.clone .lamports args.2])
    | .data => outcome = .terminated "data-overflow"
  dropRc := fun _ _ _ => False

/-- The normal effect of the first dependency precedes a terminal second call.
Even this partial construction has no unwind cleanup after an abort. -/
theorem second_terminal_stops_without_drop :
    cloneCall secondStops [] AccountInfo.sampleInfo (.terminated "data-overflow") :=
  ⟨.returned () [.clone .lamports ⟨0⟩], rfl, .terminated "data-overflow", rfl, rfl⟩

/-- Arbitrary successful providers cannot replace the source account value.
All pointed-current-state facts still come from the provider world. -/
theorem returned_clone_keeps_aliases {State Terminal : Type} (ops : Ops State Terminal)
    (before after : State) (info result : AccountInfo.Value)
    (run : cloneCall ops before info (.returned result after)) :
    result.lamports = info.lamports ∧ result.data = info.data ∧ result.ownerRef = info.ownerRef :=
      by
  have same := clone_identity ops run
  subst result
  exact ⟨rfl, rfl, rfl⟩

end SolanalibTest.Specs.SolanaAccountInfo.RcLifecycle
