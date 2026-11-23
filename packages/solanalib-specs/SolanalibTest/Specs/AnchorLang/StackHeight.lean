/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.StackHeight
public import Solanalib.Specs.AnchorLang.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.AnchorLang.StackHeight

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawRuntime
open Solanalib.Specs.AnchorLang.solana_program.instruction

theorem observes_frame_count (index : Index) (before : Solanalib.Runtime.InvState) :
    get_stack_height_run index before () (.returned ⟨before.ts.stack.length, []⟩ before) := rfl

end SolanalibTest.Specs.AnchorLang.StackHeight

@[expose] public section

namespace SolanalibTest.Specs.AnchorLang.V1_0_2StackHeight

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩]
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.1.1", "1.1.2", "1.2.0", "1.2.1", "1.2.2", "1.3.\
      0"].all
      (fun version =>
      decide (((selectedProfile "raw-runtime-anchor-lang-1.0.2").forBuild
        { build0 with version := version }).identities .solana_program_instruction_get_stack_height
          =
          [⟨"anchor-lang", version, "anchor_lang::solana_program::instruction::get_stack_he\
            ight",
            "anchor_lang::solana_program::instruction::get_stack_height"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::solana_program::instruction::get_stack_height",
            "anchor_lang::solana_program::instruction::get_stack_height"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build0).identities .solana_program_instruction_get_stack_height)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "raw-runtime-anchor-lang-1.0.2").applicability
      .solana_program_instruction_get_stack_height).length = 1 ∧
    ["0.999.999", "2.0.0", "1.3.0-rc.1"].all (fun version =>
      (((selectedProfile "raw-runtime-anchor-lang-1.0.2").forBuild { build0 with version := version
        }).identities
        .solana_program_instruction_get_stack_height).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-lang-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with target := [⟨"os", "solana"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩, ⟨"pointer_width",
        "64"⟩]
        },
      { build0 with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "unsupported-target-valu\
        e"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"os", "solana"⟩, ⟨"os", "solana"⟩] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"os", "unsupported-target-value"⟩] } ] :
        List Versioning.Build).all
      (fun build => (((selectedProfile "raw-runtime-anchor-lang-1.0.2").forBuild build).identities
        .solana_program_instruction_get_stack_height).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.V1_0_2StackHeight
