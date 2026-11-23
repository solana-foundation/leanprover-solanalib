/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionSystemExtended
public import Solanalib.Specs.Core.InstructionBuilderSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionSystemExtended.Sample

open InstructionBuilder.Sample

def types : Types := ⟨State, Nat, Nat, Nat, Nat, Nat⟩
def seedTypes : SeedTypes := ⟨types, Nat⟩

def prefundSource : PrefundSource := ⟨.zero, some (.zero, 0), 32, .ofNat 9⟩

def prefundArgs : PrefundArgs types where
  source := prefundSource
  format := .bincode
  providers := providers PrefundData PrefundData.bytes

def prefundAllocated : State := allocateMetas {} [Instruction.accountMeta .zero true true]

def prefundPushed : State :=
  { prefundAllocated with metas := [some prefundSource.metas] }

def prefundAfter : State :=
  afterSerialize PrefundData.bytes .bincode prefundPushed prefundSource.data

theorem prefund_execution : FamilyHasExecution prefundFamily prefundReference types := by
  refine ⟨({} : State), prefundArgs,
    .returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ prefundAfter, trivial, ?_⟩
  refine ⟨.returned (0 : Nat) prefundAllocated, rfl, ?_⟩
  refine ⟨.returned () prefundPushed, ?_, ?_⟩
  · exact ⟨.returned () prefundPushed, rfl, rfl⟩
  · exact InstructionBuilder.run_of_serialized _ _ _ _ _ _ rfl

/-- Serialization observes the temporary string resource at the actual call
state. The sample does not collapse the source copy into a value snapshot. -/
def seedProviders : InstructionBuilder.Providers seedTypes.builder where
  metaVec := metaVec
  byteVec := byteVec
  serialize := Callback.ofFunction fun (before : State) (format, data) =>
    match bytesAt before data.seed with
    | none => .returned (.error (404 : Nat)) before
    | some seed => .returned (.ok (before.bytes.length : Nat))
      (afterSerialize (fun data : SeedData Nat =>
        seedBytes data.base seed data.lamports data.space data.owner) format before data)
  unwrapFailure := Callback.ofFunction fun (before : State) (error : Nat) =>
    .unwound (error + 100) { before with events := before.events ++ [30] }
  doubleUnwind := fun (_ : State) (first later terminal : Nat) =>
    terminal = first + later + 1000

def seedSource : SeedSource := ⟨.zero, .zero, .zero, [97, 0, 195, 169], 7, 32, .ofNat 9⟩

def seedArgs : SeedArgs seedTypes := ⟨seedSource, seedProviders, byteVec⟩

def seedAllocated : State := allocateMetas {} seedSource.metas
def seedCopied : State := allocateBytes seedAllocated seedSource.seed

def seedSerialized : State := afterSerialize
  (fun data : SeedData Nat =>
    seedBytes data.base seedSource.seed data.lamports data.space data.owner)
  .bincode seedCopied (seedData seedTypes seedSource (0 : Nat))

def seedAfter : State := retireBytes seedSerialized 0

theorem seed_execution : FamilyHasExecution seedFamily seedReference seedTypes := by
  refine ⟨({} : State), seedArgs,
    .returned ⟨.zero, (0 : Nat), (1 : Nat)⟩ seedAfter, trivial, ?_⟩
  refine ⟨.returned (0 : Nat) seedAllocated, rfl, ?_⟩
  refine ⟨.returned (0 : Nat) seedCopied, ?_, ?_⟩
  · exact ⟨.returned (0 : Nat) seedCopied, rfl, rfl⟩
  · exact seedAfterCopy_returned seedTypes seedArgs (0 : Nat) (0 : Nat) (1 : Nat)
      seedCopied seedSerialized seedAfter rfl rfl

end Solanalib.Specs.Core.InstructionSystemExtended.Sample
