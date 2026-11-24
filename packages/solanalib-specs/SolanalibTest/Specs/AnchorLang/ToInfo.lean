/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.construct

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.ToInfo

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The AsRef effect precedes both Rc increments in the primary model. -/
theorem as_ref_then_both_rc_clones :
    AnchorToInfo.run AnchorToInfo.sample [] ()
      (.returned AccountInfo.sampleInfo AnchorToInfo.sampleTrace) := AnchorToInfo.sample_run

def unwindingAsRef : AnchorToInfo.Types where
  State := Nat
  Input := Unit
  Unwind := String
  Terminal := String
  asRef := Callback.ofFunction fun state _ => .unwound "as-ref" (state + 1)
  rc := ⟨fun _ _ _ => False, fun _ _ _ => False⟩

/-- An unwinding AsRef preserves its changed state and never calls Rc::clone. -/
theorem as_ref_unwind_skips_clones :
    AnchorToInfo.run unwindingAsRef (4 : Nat) () (.unwound "as-ref" (5 : Nat)) :=
  ⟨.unwound "as-ref" (5 : Nat), rfl, rfl⟩

def terminalRc : AnchorToInfo.Types where
  State := Nat
  Input := Unit
  Unwind := String
  Terminal := String
  asRef := Callback.ofFunction fun state _ => .returned AccountInfo.sampleInfo (state + 1)
  rc := {
    cloneRc := fun _ argument outcome => match argument.1 with
      | .lamports => outcome = .terminated "rc-overflow"
      | .data => False
    dropRc := fun _ _ _ => False }

/-- A terminal Rc dependency after AsRef cannot become an ordinary return or
an AsRef unwind; lifting the outcome vocabulary preserves the terminal. -/
theorem rc_terminal_after_as_ref :
    AnchorToInfo.run terminalRc (4 : Nat) () (.terminated "rc-overflow") := by
  refine ⟨.returned AccountInfo.sampleInfo (5 : Nat), rfl, ?_⟩
  exact ⟨.terminated "rc-overflow", ⟨.terminated "rc-overflow", rfl, rfl⟩, rfl⟩

end SolanalibTest.Specs.AnchorLang.ToInfo
