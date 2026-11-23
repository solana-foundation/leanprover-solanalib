/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken
public import Solanalib.Specs.SplToken.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SplToken

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Authority and both supplied signer occurrences deliberately alias. -/
def authority : AuthorityArgs := ⟨legacyProgramId, .ofNat 1, .ofNat 1, .ofNat 2, [.ofNat 2, .ofNat
  2]⟩

/-- All five source occurrences survive; the authority is not implicitly signed. -/
theorem duplicate_accounts_retained :
    (mintToPlan .legacy ⟨authority, 513⟩).metas.items.length = 5 ∧
      ((mintToPlan .legacy ⟨authority, 513⟩).metas.items.map (·.signerByte)) = [0, 0, 0, 1, 1] := by
  decide +kernel

/-- Checked burn packs little-endian amount bytes before the decimals byte. -/
theorem checked_burn_byte_order :
    (burnCheckedPlan .legacy ⟨⟨authority, 513⟩, 255⟩).data = [15, 1, 2, 0, 0, 0, 0, 0, 0, 255] := by
  decide +kernel

/-- The mint is writable in BurnChecked, unlike TransferChecked. -/
theorem checked_burn_writable_mint :
    ((burnCheckedPlan .legacy ⟨⟨authority, 0⟩, 6⟩).metas.items.map (·.writableByte))[1]? = some 1
      := by
  decide +kernel

/-- The set-authority capacity includes one unused reserved metadata slot. -/
theorem authority_reservation_is_not_length :
    (setAuthorityPlan .legacy
      (⟨legacyProgramId, .ofNat 1, some .zero, ⟨3, by decide⟩, .ofNat 2, []⟩ : SetAuthorityArgs
        4)).metas =
      .withCapacity 3 [Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 1) false true,
        Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 2) true false] := rfl

/-- `Some zero` is serialized with its Some tag and all32 zero bytes. -/
theorem some_zero_differs_from_none :
    optionalKeySteps (some .zero) ≠ optionalKeySteps none := by decide +kernel

/-- The legacy constructor rejects Token-2022 before any provider is entered. -/
theorem foreign_program_has_no_allocation (types : Types) (before : types.State) :
    Solanalib.Specs.SplToken.instruction.close_account_reference types before
      { authority with programId := token2022ProgramId }
      (.returned (.error .IncorrectProgramId) before) := rfl

/-- The declared native mint is accepted and the zero key is rejected. -/
theorem native_mint_check :
    Solanalib.Specs.SplToken.native_mint.check_id_reference ()
      Solanalib.Specs.SplToken.native_mint.declaredId = (true, ()) ∧
      Solanalib.Specs.SplToken.native_mint.check_id_reference () .zero = (false, ()) := by
        decide +kernel

end SolanalibTest.Specs.SplToken

namespace SolanalibTest.Specs.SplToken.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_burn_checkedBuild : Versioning.Build where
  package := "spl-token"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_burn_checkedCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_burn_checkedBuild, true),
  -- lower; eligible
  (instruction_burn_checkedBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_burn_checkedBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_burn_checkedBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_burn_checkedBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "lit\
    tle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_burn_checkedBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "lin\
    ux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_burn_checkedBuild with dependencies := (instruction_burn_checkedBuild.dependencies
    ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_burn_checkedBuild with dependencies := (instruction_burn_checkedBuild.dependencies
    ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_burn_checkedBuild with dependencies := (instruction_burn_checkedBuild.dependencies
    ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_burn_checkedBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_burn_checked_profile_controls :
    instruction_burn_checkedCases.all (fun test =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.applicability .instruction_burn_checked).any
        (fun profile => ["spl-token-8.0.0-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_burn_checked_callable_identities :
    ["8.0.0", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.forBuild
        { instruction_burn_checkedBuild with version := version }).identities
          .instruction_burn_checked).eraseDups ==
        [⟨"spl-token", version, "spl_token::instruction::burn_checked",
          "spl_token::instruction::burn_checked"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_close_accountBuild : Versioning.Build where
  package := "spl-token"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_close_accountCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_close_accountBuild, true),
  -- lower; eligible
  (instruction_close_accountBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_close_accountBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_close_accountBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_close_accountBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_close_accountBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "li\
    ttle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_close_accountBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "li\
    nux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_close_accountBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_close_accountBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_close_accountBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_close_accountBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_close_accountBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_close_accountBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_close_accountBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_close_account_profile_controls :
    instruction_close_accountCases.all (fun test =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.applicability .instruction_close_account).any
        (fun profile => ["spl-token-8.0.0-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_close_account_callable_identities :
    ["8.0.0", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.forBuild
        { instruction_close_accountBuild with version := version }).identities
          .instruction_close_account).eraseDups ==
        [⟨"spl-token", version, "spl_token::instruction::close_account",
          "spl_token::instruction::close_account"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_mint_toBuild : Versioning.Build where
  package := "spl-token"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_mint_toCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_mint_toBuild, true),
  -- lower; eligible
  (instruction_mint_toBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_mint_toBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_mint_toBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_mint_toBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_mint_toBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-os; unsupported
  ({ instruction_mint_toBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩, ⟨"e\
    ndian",
    "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "linux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨
    "endian",
    "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_mint_toBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_mint_toBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_mint_toBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_mint_toBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_mint_toBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_mint_toBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_mint_toBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_mint_to_profile_controls :
    instruction_mint_toCases.all (fun test =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.applicability .instruction_mint_to).any
        (fun profile => ["spl-token-8.0.0-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_mint_to_callable_identities :
    ["8.0.0", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.forBuild
        { instruction_mint_toBuild with version := version }).identities
          .instruction_mint_to).eraseDups ==
        [⟨"spl-token", version, "spl_token::instruction::mint_to",
          "spl_token::instruction::mint_to"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_set_authorityBuild : Versioning.Build where
  package := "spl-token"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_set_authorityCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_set_authorityBuild, true),
  -- lower; eligible
  (instruction_set_authorityBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_set_authorityBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_set_authorityBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_set_authorityBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "li\
    ttle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_set_authorityBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "li\
    nux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_set_authorityBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_set_authority_profile_controls :
    instruction_set_authorityCases.all (fun test =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.applicability .instruction_set_authority).any
        (fun profile => ["spl-token-8.0.0-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_set_authority_callable_identities :
    ["8.0.0", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.forBuild
        { instruction_set_authorityBuild with version := version }).identities
          .instruction_set_authority).eraseDups ==
        [⟨"spl-token", version, "spl_token::instruction::set_authority",
          "spl_token::instruction::set_authority"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def native_mint_check_idBuild : Versioning.Build where
  package := "spl-token"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def native_mint_check_idCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (native_mint_check_idBuild, true),
  -- lower; eligible
  (native_mint_check_idBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ native_mint_check_idBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ native_mint_check_idBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ native_mint_check_idBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ native_mint_check_idBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ native_mint_check_idBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ native_mint_check_idBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-os; unsupported
  ({ native_mint_check_idBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩, ⟨
    "endian",
    "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "linux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (native_mint_check_idBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (native_mint_check_idBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ native_mint_check_idBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem native_mint_check_id_profile_controls :
    native_mint_check_idCases.all (fun test =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.applicability .native_mint_check_id).any
        (fun profile => ["spl-token-8.0.0-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem native_mint_check_id_callable_identities :
    ["8.0.0", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken.Capabilities.catalog.forBuild
        { native_mint_check_idBuild with version := version }).identities
          .native_mint_check_id).eraseDups ==
        [⟨"spl-token", version, "spl_token::native_mint::check_id",
          "spl_token::native_mint::check_id"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken.Pr575Compatibility
