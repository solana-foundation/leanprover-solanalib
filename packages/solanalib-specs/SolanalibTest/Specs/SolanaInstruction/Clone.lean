/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaInstruction.AccountMetaGeneric
public import Solanalib.Specs.SolanaInstruction.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaInstruction.Clone

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem metadata_current_read_preserves_all_fields :
    Solanalib.Specs.SolanaInstruction.AccountMeta.clone_run InstructionMeta.sample
      (Instruction.accountMeta (.ofNat 17) false true) ()
      (.returned (Instruction.accountMeta (.ofNat 17) false true)
        (Instruction.accountMeta (.ofNat 17) false true)) :=
  ⟨_, rfl, rfl⟩

def expired : InstructionMeta.Types where
  State := Unit
  Reference := Unit
  access := ⟨fun _ _ => False, fun _ _ => some (Instruction.accountMeta .zero true true)⟩

theorem expired_reference_not_admitted :
    ¬ (Solanalib.Specs.SolanaInstruction.AccountMeta.clone_contract.contract expired).requires ()
      () := by
  rintro ⟨_, impossible, _⟩
  exact impossible

def selectedBuild : Versioning.Build where
  package := "solana-instruction"
  version := "2.3.3"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

theorem compatible_clone_identities :
    ["2.3.3", "2.3.4", "2.9.0"].all (fun version => decide
      ((Solanalib.Specs.SolanaInstruction.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .AccountMeta_clone =
        [⟨"solana-instruction", version, "core::clone::Clone::clone",
          "<solana_instruction::account_meta::AccountMeta as core::clone::Clone>::clone"⟩])) = true
            := by
  decide +kernel

theorem outside_clone_range_rejected :
    ["2.3.2", "3.0.0", "3.4.0", "2.3.4-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaInstruction.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .AccountMeta_clone = [])) = true := by
  decide +kernel

theorem clone_range_does_not_narrow_existing_constructors :
    let selected := Solanalib.Specs.SolanaInstruction.Capabilities.catalog.forBuild
      { selectedBuild with version := "3.4.0" }
    selected.identities .AccountMeta_new ≠ [] ∧ selected.identities .AccountMeta_new_readonly ≠ []
      := by
  decide +kernel

theorem forked_clone_rejected :
    (Solanalib.Specs.SolanaInstruction.Capabilities.catalog.forBuild
      { selectedBuild with
        version := "2.3.4"
        source := ⟨"git", "https://example.invalid/instruction", "fork"⟩ }).identities
          .AccountMeta_clone = [] := by decide +kernel

end SolanalibTest.Specs.SolanaInstruction.Clone
