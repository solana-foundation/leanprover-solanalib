/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.SystemInstruction
import Solanalib.Specs.SolanaSystemInterface.Extended
import SolanalibTest.Conformance.Library.Families.InstructionExtensions.Common
import Solanalib.Specs.SolanaSystemInterface.Seeded

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.InstructionExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core InstructionSystemExtended
open SolanalibTest.Conformance.Library.Borsh
open SolanalibTest.Conformance.Library.Families.Instructions

def seedTypes : SeedTypes := ⟨types, Nat⟩

def seedEncode : Encode (SeedData Nat) := fun state data =>
  seedBytes data.base ((bytesAt state data.seed).getD []) data.lamports data.space data.owner

def seededArgs (source : SeedSource) (failAt : Option Nat) : SeedArgs seedTypes :=
  ⟨source, providers failAt seedEncode, byteVec failAt⟩

def finishSeedFn (seed : Nat) : Out Value → Out Value
  | .returned value state => .returned value (retireByte state seed)
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => .terminated reason

theorem finishSeed_graph (source : SeedSource) (failAt : Option Nat) (seed : Nat)
    (pending final : Out Value) :
    finishSeed seedTypes (seededArgs source failAt) seed pending final ↔
      finishSeedFn seed pending = final := by
  cases pending with
  | returned value state =>
    unfold finishSeed
    refine (protect_iff _ _ _ _ _ _).trans ?_
    simp only [Owned.cleanup, Owned.VectorOps.dropAction, seededArgs, byteVec, Callback.ofFunction]
    simp only [finishSeedFn]
    constructor
    · rintro ⟨_, rfl, h⟩; exact h.symm
    · intro h; exact ⟨_, rfl, h.symm⟩
  | unwound impossible _ => exact impossible.elim
  | terminated reason => exact eq_comm

def seedAfterCopyFn (source : SeedSource) (failAt : Option Nat) (metas seed : Nat)
    (before : State) : Out Value :=
  finishSeedFn seed (buildFn failAt seedEncode Instruction.systemProgramId
    (seedData seedTypes source seed) metas before)

theorem seedAfterCopy_graph (source : SeedSource) (failAt : Option Nat) (metas seed : Nat)
    (before : State) (outcome : Out Value) :
    seedAfterCopy seedTypes (seededArgs source failAt) metas seed before outcome ↔
      seedAfterCopyFn source failAt metas seed before = outcome := by
  unfold seedAfterCopy
  change (∃ pending, InstructionBuilder.run (types.builder (SeedData Nat)) .bincode before
      ⟨Instruction.systemProgramId, seedData seedTypes source seed, metas, providers failAt
        seedEncode⟩ pending ∧
    finishSeed seedTypes (seededArgs source failAt) seed pending outcome) ↔ _
  constructor
  · rintro ⟨pending, built, finished⟩
    have builtEq := (build_graph failAt seedEncode .bincode Instruction.systemProgramId
      (seedData seedTypes source seed) metas before pending).mp built
    subst builtEq
    exact (finishSeed_graph source failAt seed _ outcome).mp finished
  · intro h
    exact ⟨_, (build_graph failAt seedEncode .bincode Instruction.systemProgramId
      (seedData seedTypes source seed) metas before _).mpr rfl,
      (finishSeed_graph source failAt seed _ outcome).mpr h⟩

def seedAfterAllocationFn (source : SeedSource) (failAt : Option Nat) (metas : Nat)
    (before : State) : Out Value :=
  Outcome.bind (byteFromList failAt before source.seed) (seedAfterCopyFn source failAt metas)

theorem seedAfterAllocation_graph (source : SeedSource) (failAt : Option Nat) (metas : Nat)
    (before : State) (outcome : Out Value) :
    seedAfterAllocation seedTypes (seededArgs source failAt) metas before outcome ↔
      seedAfterAllocationFn source failAt metas before = outcome := by
  exact bind_graph _ _ (byteFromList failAt) (seedAfterCopyFn source failAt metas)
    (fun _ _ _ => (protect_iff _ _ _ _ _ _).trans Iff.rfl)
    (seedAfterCopy_graph source failAt metas) before _ outcome

def seededFn (source : SeedSource) (failAt : Option Nat) (before : State) : Out Value :=
  Outcome.bind (metaFromList failAt before source.metas) (seedAfterAllocationFn source failAt)

theorem seeded_graph (source : SeedSource) (failAt : Option Nat)
    (before : State) (outcome : Out Value) :
    Solanalib.Specs.SolanaSystemInterface.instruction.create_account_with_seed_run seedTypes before
      (seededArgs source failAt) outcome ↔ seededFn source failAt before = outcome := by
  exact bind_graph _ _ (metaFromList failAt) (seedAfterAllocationFn source failAt)
    (fun _ _ _ => Iff.rfl) (seedAfterAllocation_graph source failAt) before _ outcome

def parseSeeded (j : Json) : Result SeedSource := do
  let seed ← asBytes (← field j "seed")
  unless (String.fromUTF8? ⟨seed.toArray⟩).isSome do throw "source seed is not a Rust str"
  pure ⟨← keyField j "from", ← keyField j "to", ← keyField j "base", seed,
    ← natField j "lamports" 64, ← natField j "space" 64, ← keyField j "owner"⟩

def seededChecker (legacy : Bool) : Checker where
  function := if legacy then "solana_program::system_instruction::create_account_with_seed"
    else "solana_system_interface::instruction::create_account_with_seed"
  generics := []
  reference := "Solanalib.Specs.SolanaSystemInterface.instruction.create_account_with_seed_\
    run"
  decides := ["Solanalib.Specs.SolanaSystemInterface.instruction.create_account_with_seed_r\
    un"]
  check := fun c => do
    asUnit c.state
    let source ← parseSeeded c.args
    let failAt ← failure c.args
    pure (decideObserved _ (seededFn source failAt {}) (seeded_graph source failAt {})
      (observed false) (some c.outcome) (outcomeJson false))


theorem program_seeded_graph (source : SeedSource) (failAt : Option Nat)
    (before : State) (outcome : Out Value) :
    Solanalib.Specs.SolanaProgram.system_instruction.create_account_with_seed_run seedTypes before
      (seededArgs source failAt) outcome ↔ seededFn source failAt before = outcome := by
  exact bind_graph _ _ (metaFromList failAt) (seedAfterAllocationFn source failAt)
    (fun _ _ _ => Iff.rfl) (seedAfterAllocation_graph source failAt) before _ outcome

def programSeededChecker : Checker where
  function := "solana_program::system_instruction::create_account_with_seed"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.system_instruction.create_account_with_seed_r\
    un"
  decides := ["Solanalib.Specs.SolanaProgram.system_instruction.create_account_with_seed_ru\
    n"]
  check := fun c => do
    asUnit c.state
    let source ← parseSeeded c.args
    let failAt ← failure c.args
    pure (decideObserved _ (seededFn source failAt {}) (program_seeded_graph source failAt {})
      (observed false) (some c.outcome) (outcomeJson false))

end SolanalibTest.Conformance.Library.Families.InstructionExtensions

namespace SolanalibTest.Conformance.Library.Families.InstructionExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core InstructionSystemExtended
open SolanalibTest.Conformance.Library.Borsh
open SolanalibTest.Conformance.Library.Families.Instructions

def prefundEncode : Encode PrefundData := fun _ data => data.bytes

def prefundArgs (source : PrefundSource) (format : InstructionBuilder.Format)
    (failAt : Option Nat) : PrefundArgs types :=
  ⟨source, format, providers failAt prefundEncode⟩

def prefundAfterFn (source : PrefundSource) (failAt : Option Nat)
    (metas : Nat) (before : State) : Out Value :=
  match source.payer with
  | none => buildFn failAt prefundEncode Instruction.systemProgramId source.data metas before
  | some (payer, _) => Outcome.bind
      (pushMeta failAt before (metas, Instruction.accountMeta payer true true))
      (fun _ after => buildFn failAt prefundEncode Instruction.systemProgramId source.data metas
        after)

def prefundFn (source : PrefundSource) (failAt : Option Nat) (before : State) : Out Value :=
  Outcome.bind (metaFromList failAt before [Instruction.accountMeta source.newAccount true true])
    (prefundAfterFn source failAt)

theorem prefundAfter_graph (source : PrefundSource) (format : InstructionBuilder.Format)
    (failAt : Option Nat) (metas : Nat) (before : State) (outcome : Out Value) :
    prefundAfterAllocation types (prefundArgs source format failAt) metas before () outcome ↔
      prefundAfterFn source failAt metas before = outcome := by
  cases hp : source.payer with
  | none =>
    simpa only [prefundAfterAllocation, prefundArgs, prefundAfterFn, hp] using
      build_graph failAt prefundEncode format Instruction.systemProgramId source.data metas before
        outcome
  | some payer =>
    dsimp only [prefundAfterAllocation, prefundArgs, prefundAfterFn]
    rw [hp]
    refine bind_graph _ _ (pushMeta failAt)
      (fun _ after => buildFn failAt prefundEncode Instruction.systemProgramId source.data metas
        after)
      (fun s a o => ?_) (fun _ s o => ?_) before _ outcome
    · exact (protect_iff _ _ _ _ _ _).trans Iff.rfl
    · exact build_graph failAt prefundEncode format Instruction.systemProgramId source.data metas s
        o

theorem prefund_graph (source : PrefundSource) (format : InstructionBuilder.Format)
    (failAt : Option Nat) (before : State) (outcome : Out Value) :
    Solanalib.Specs.SolanaSystemInterface.instruction.create_account_allow_prefund_run types before
      (prefundArgs source format failAt) outcome ↔ prefundFn source failAt before = outcome := by
  exact bind_graph _ _ (metaFromList failAt) (prefundAfterFn source failAt)
    (fun _ _ _ => Iff.rfl) (prefundAfter_graph source format failAt) before _ outcome

def parsePrefund (j : Json) : Result PrefundSource := do
  let payer ← match ← field j "payer" with
    | .null => pure none
    | obj => do
      let value ← field obj "some"
      pure (some (← keyField value "pubkey", ← natField value "lamports" 64))
  pure ⟨← keyField j "new_account", payer, ← natField j "space" 64, ← keyField j "owner"⟩

def prefundChecker (format : InstructionBuilder.Format) : Checker where
  function := "solana_system_interface::instruction::create_account_allow_prefund"
  generics := []
  reference := "Solanalib.Specs.SolanaSystemInterface.instruction.create_account_allow_pref\
    und_run"
  decides := ["Solanalib.Specs.SolanaSystemInterface.instruction.create_account_allow_prefu\
    nd_run"]
  check := fun c => do
    asUnit c.state
    let source ← parsePrefund c.args
    let failAt ← failure c.args
    pure (decideObserved _ (prefundFn source failAt {})
      (prefund_graph source format failAt {}) (observed false) (some c.outcome) (outcomeJson false))

end SolanalibTest.Conformance.Library.Families.InstructionExtensions
