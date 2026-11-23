/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface.Fees
public import Solanalib.Specs.SplToken2022Interface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplToken2022Interface.Fees

open Solanalib.Specs.Core.Token

/-- The largest representable transfer amount. -/
def maximumAmount : UInt64 := UInt64.ofNat (2^64 - 1)

/-- The checked ceiling helper rounds a nonintegral quotient upwards. -/
theorem ceil_rounds_up : FeeArithmetic.ceilDiv128 10 3 = some 4 := by decide +kernel

/-- Even though the mathematical quotient fits, the first checked sum fails. -/
theorem ceil_checks_sum_before_subtraction :
    FeeArithmetic.ceilDiv128 (2^128 - 1) 1 = none := by decide +kernel

/-- Both zero-numerator and positive-numerator division by zero fail. -/
theorem ceil_zero_denominator :
    FeeArithmetic.ceilDiv128 0 0 = none ∧
    FeeArithmetic.ceilDiv128 1 0 = none := by decide +kernel

/-- At zero rate, even the maximum amount passes through unchanged. -/
theorem zero_rate_at_maximum :
    (TransferFee.mk 17 maximumAmount 0).calculateFee maximumAmount = some 0 ∧
    (TransferFee.mk 17 maximumAmount 0).calculatePostFeeAmount maximumAmount =
      some maximumAmount ∧
    (TransferFee.mk 17 maximumAmount 0).calculatePreFeeAmount maximumAmount =
      some maximumAmount := by decide +kernel

/-- Zero input and output succeed even at the largest representable rate. -/
theorem zero_shortcuts_before_excess_rate :
    (TransferFee.mk 0 maximumAmount 65535).calculateFee 0 = some 0 ∧
    (TransferFee.mk 0 maximumAmount 65535).calculatePostFeeAmount 0 = some 0 ∧
    (TransferFee.mk 0 maximumAmount 65535).calculatePreFeeAmount 0 = some 0 := by
  decide +kernel

/-- One basis point rounds up on each side of its exact 10,000-token boundary. -/
theorem basis_point_rounding :
    (TransferFee.mk 0 100 1).calculateFee 1 = some 1 ∧
    (TransferFee.mk 0 100 1).calculateFee 9999 = some 1 ∧
    (TransferFee.mk 0 100 1).calculateFee 10000 = some 1 ∧
    (TransferFee.mk 0 100 1).calculateFee 10001 = some 2 := by decide +kernel

/-- The fee is rounded before the cap is applied; exceeding the cap saturates. -/
theorem rounding_and_cap :
    (TransferFee.mk 0 3 1000).calculateFee 20 = some 2 ∧
    (TransferFee.mk 0 3 1000).calculateFee 21 = some 3 ∧
    (TransferFee.mk 0 3 1000).calculateFee 31 = some 3 ∧
    (TransferFee.mk 0 3 1000).calculatePostFeeAmount 21 = some 18 := by decide +kernel

/-- Rounding can give two gross amounts the same net amount. The inverse of the source chooses the
smaller gross amount for this concrete case. -/
theorem inverse_chooses_smaller_gross :
    (TransferFee.mk 0 100 1000).calculatePostFeeAmount 10 = some 9 ∧
    (TransferFee.mk 0 100 1000).calculatePostFeeAmount 11 = some 9 ∧
    (TransferFee.mk 0 100 1000).calculatePreFeeAmount 9 = some 10 := by decide +kernel

/-- At 100 percent, the positive-output branch adds the maximum fee. -/
theorem full_rate_capped_inverse :
    (TransferFee.mk 0 7 10000).calculatePreFeeAmount 10 = some 17 ∧
    (TransferFee.mk 0 7 10000).calculatePostFeeAmount 17 = some 10 := by decide +kernel

/-- The 100-percent branch retains `u64` overflow instead of wrapping. -/
theorem full_rate_overflow :
    (TransferFee.mk 0 1 10000).calculatePreFeeAmount maximumAmount = none ∧
    (TransferFee.mk 0 0 10000).calculatePreFeeAmount maximumAmount =
      some maximumAmount := by decide +kernel

/-- Invalid rates are not rejected uniformly by all methods: the raw fee can
fit while the subsequent deduction underflows. -/
theorem excess_rate_can_underflow_deduction :
    (TransferFee.mk 0 2 10001).calculateFee 1 = some 2 ∧
    (TransferFee.mk 0 2 10001).calculatePostFeeAmount 1 = none ∧
    (TransferFee.mk 0 2 10001).calculatePreFeeAmount 1 = none := by decide +kernel

/-- A zero cap can rescue a small direct fee calculation, while the inverse
still fails its checked denominator subtraction. -/
theorem excess_rate_zero_cap_asymmetry :
    (TransferFee.mk 0 0 10001).calculateFee 1 = some 0 ∧
    (TransferFee.mk 0 0 10001).calculatePostFeeAmount 1 = some 1 ∧
    (TransferFee.mk 0 0 10001).calculatePreFeeAmount 1 = none := by decide +kernel

/-- Converting the raw fee fails before either a zero or a positive cap can
be applied. This differs from computing a capped unbounded integer first. -/
theorem raw_conversion_before_cap :
    (TransferFee.mk 0 0 10001).calculateFee maximumAmount = none ∧
    (TransferFee.mk 0 1 10001).calculateFee maximumAmount = none ∧
    (TransferFee.mk 0 0 10000).calculateFee maximumAmount = some 0 := by decide +kernel

/-- Rates use the entire decoded `u16` range. -/
theorem maximum_rate :
    (TransferFee.mk 0 10 65535).calculateFee 1 = some 7 ∧
    (TransferFee.mk 0 0 65535).calculatePreFeeAmount 1 = none := by decide +kernel

/-- Inverse calculation compares the cap before narrowing the raw input to
`u64`, so a zero cap can recover even the maximum output. -/
theorem inverse_cap_before_raw_conversion :
    (TransferFee.mk 0 0 1).calculatePreFeeAmount maximumAmount =
      some maximumAmount := by decide +kernel

/-- Both inverse overflow routes fail: checked cap addition, and narrowing
an uncapped raw amount whose extra fee is below the cap. -/
theorem inverse_overflow_paths :
    (TransferFee.mk 0 1 1).calculatePreFeeAmount maximumAmount = none ∧
    (TransferFee.mk 0 maximumAmount 1).calculatePreFeeAmount maximumAmount = none := by
  decide +kernel

/-- The exact cap-equality threshold still gives the rounded inverse. -/
theorem inverse_at_cap_equality :
    (TransferFee.mk 0 1 1000).calculatePreFeeAmount 9 = some 10 ∧
    (TransferFee.mk 0 1 1000).calculatePostFeeAmount 10 = some 9 := by decide +kernel

/-- An older activation epoch deliberately later than the newer one tests
that selection does not consult it. -/
def reversedEpochConfig : TransferFeeConfig :=
  ⟨.zero, .zero, maximumAmount, ⟨200, 9, 100⟩, ⟨100, 3, 200⟩⟩

/-- Selection uses the newer boundary, including equality, with no lower
bound from the older activation epoch. -/
theorem epoch_boundary_and_older_epoch :
    reversedEpochConfig.getEpochFee 0 = reversedEpochConfig.older ∧
    reversedEpochConfig.getEpochFee 99 = reversedEpochConfig.older ∧
    reversedEpochConfig.getEpochFee 100 = reversedEpochConfig.newer ∧
    reversedEpochConfig.getEpochFee maximumAmount = reversedEpochConfig.newer := by
  decide +kernel

/-- The newer schedule changes the amount actually returned by the shared
fee calculation, rather than merely relabelling an otherwise equal record. -/
theorem epoch_changes_fee :
    (reversedEpochConfig.getEpochFee 99).calculatePostFeeAmount 1000 = some 991 ∧
    (reversedEpochConfig.getEpochFee 100).calculatePostFeeAmount 1000 = some 997 := by
  decide +kernel

open Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFee

/-- The cap theorem applies to every total interpretation satisfying the
versioned contract, without unfolding that interpretation. -/
theorem cap_from_contract
    (run : TransferFee → UInt64 → Option UInt64 × TransferFee)
    (spec : calculate_fee_contract.RealizedBy run)
    (fee : TransferFee) (amount charged : UInt64)
    (success : (run fee amount).1 = some charged) :
    charged.toNat ≤ fee.maximumFee.toNat := by
  have post := spec fee amount trivial
  change (run fee amount).1 = fee.calculateFee amount ∧ (run fee amount).2 = fee at post
  exact TransferFee.calculateFee_le_max (post.1.symm.trans success)

/-- Every interpretation of the inverse contract must return the checked
failure for a positive output and an excessive rate; the record is preserved. -/
theorem excess_rate_failure_from_contract
    (run : TransferFee → UInt64 → Option UInt64 × TransferFee)
    (spec : calculate_pre_fee_amount_contract.RealizedBy run)
    (fee : TransferFee) (amount : UInt64)
    (excess : FeeArithmetic.basisPointScale < fee.basisPoints.toNat)
    (positive : amount.toNat ≠ 0) :
    run fee amount = (none, fee) := by
  have post := spec fee amount trivial
  change (run fee amount).1 = fee.calculatePreFeeAmount amount ∧
    (run fee amount).2 = fee at post
  apply Prod.ext
  · exact post.1.trans (fee.calculatePreFeeAmount_excess_rate amount excess positive)
  · exact post.2

/-- The two versioned contracts jointly give exact amount conservation for
any realizing interpretations and successful results. -/
theorem conservation_from_contracts
    (feeRun netRun : TransferFee → UInt64 → Option UInt64 × TransferFee)
    (feeSpec : calculate_fee_contract.RealizedBy feeRun)
    (netSpec : calculate_post_fee_amount_contract.RealizedBy netRun)
    (fee : TransferFee) (amount charged net : UInt64)
    (chargedResult : (feeRun fee amount).1 = some charged)
    (netResult : (netRun fee amount).1 = some net) :
    net.toNat + charged.toNat = amount.toNat := by
  have feePost := feeSpec fee amount trivial
  have netPost := netSpec fee amount trivial
  change (feeRun fee amount).1 = fee.calculateFee amount ∧ _ at feePost
  change (netRun fee amount).1 = fee.calculatePostFeeAmount amount ∧ _ at netPost
  exact TransferFee.calculatePostFeeAmount_conserves
    (feePost.1.symm.trans chargedResult) (netPost.1.symm.trans netResult)

end SolanalibTest.Specs.SplToken2022Interface.Fees

@[expose] public section

namespace SolanalibTest.Specs.SplToken2022Interface.V3Fees

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SplToken2022Interface.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

def build0 : Versioning.Build where
  package := "spl-token-2022-interface"
  version := "2.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["2.0.0", "2.1.0", "2.2.0"].all (fun version =>
      decide (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-transfer_fee-TransferFeeConfig-calculate_\
          epoch_fee").forBuild
        { build0 with version := version }).identities
          .extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee =
          [⟨"spl-token-2022-interface", version,
            "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::calculat\
              e_epoch_fee",
            "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::calculat\
              e_epoch_fee"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"spl-token-2022-interface", "2.1.0",
      "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::calculate_epoc\
        h_fee",
            "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::calculat\
              e_epoch_fee"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
        build0).identities .extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee)) = true
        := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile
      "spl-token-2022-interface-2.1.0-extension-transfer_fee-TransferFeeConfig-calculate_ep\
        och_fee").applicability
          .extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee).length = 1 ∧
    ["1.999.999", "3.0.0", "2.2.0-rc.1"].all (fun version =>
      (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-transfer_fee-TransferFeeConfig-calculate_\
          epoch_fee").forBuild { build0 with version := version }).identities
        .extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "spl-token-2022-interface-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-pod", "0.7.3", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-zero-copy", "1.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] } ] : List Versioning.Build).all
      (fun build => (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-transfer_fee-TransferFeeConfig-calculate_\
          epoch_fee").forBuild build).identities
        .extension_transfer_fee_TransferFeeConfig_calculate_epoch_fee).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022Interface.V3Fees
