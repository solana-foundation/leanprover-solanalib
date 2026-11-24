/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionClone
public import Solanalib.Specs.Core.InstructionBuilderSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionClone.Sample

open InstructionBuilder.Sample

def types : Types := ⟨State, Instruction.OwnedValue Nat Nat, Nat, Nat, Nat, Nat⟩

/-- A finite logical resource ledger supplies a concrete consistency witness.
It neither models allocator addresses nor proves a Rust allocation succeeds. -/
def providers : Providers types where
  access := ⟨fun _ _ => True, fun _ source => some source⟩
  metas := ⟨metaVec, Callback.ofFunction fun state source =>
    match metasAt state source with
    | some values => .returned state.metas.length (allocateMetas state values)
    | none => .unwound (404 : Nat) state⟩
  bytes := ⟨byteVec, Callback.ofFunction fun state source =>
    match bytesAt state source with
    | some values => .returned state.bytes.length (allocateBytes state values)
    | none => .unwound (404 : Nat) state⟩
  doubleUnwind := fun (_ : State) (first later terminal : Nat) => terminal = first + later + 1000

def source : Value types := ⟨.ofNat 9, (0 : Nat), (0 : Nat)⟩

def args : Args types := ⟨source, providers⟩

def before : State where
  metas := [some [Instruction.accountMeta .zero true true,
    Instruction.accountMeta .zero false false]]
  bytes := [some [9, 0, 255]]

def middle : State := allocateMetas before
  [Instruction.accountMeta .zero true true, Instruction.accountMeta .zero false false]

def after : State := allocateBytes middle [9, 0, 255]

theorem execution : FamilyHasExecution family reference types := by
  refine ⟨before, args, .returned ⟨.ofNat 9, (1 : Nat), (1 : Nat)⟩ after, ?_, ?_⟩
  · exact ⟨source, trivial, rfl⟩
  · refine ⟨source, rfl, ?_⟩
    exact copyRun_returned types providers source before middle after (1 : Nat) (1 : Nat) rfl rfl

end Solanalib.Specs.Core.InstructionClone.Sample
