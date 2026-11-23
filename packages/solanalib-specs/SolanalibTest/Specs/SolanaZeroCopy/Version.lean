/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaZeroCopy

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaZeroCopy

/-- The build selector binds the shared contract to this exact source version and function. -/
theorem registered_release_1_0_1 :
    (Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog.forBuild {
      package := "solana-zero-copy"
      version := "1.0.1"
      source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }).identities .unaligned_U64_into_u64 =
      [⟨"solana-zero-copy", "1.0.1", "core::convert::From::from",
        "solana_zero_copy::unaligned::<impl \
          core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from"⟩] := by
            decide +kernel

end SolanalibTest.Specs.SolanaZeroCopy

namespace SolanalibTest.Specs.SolanaZeroCopy

/-- The build selector binds the shared contract to this exact source version and function. -/
theorem registered_release_1_1_0 :
    (Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog.forBuild {
      package := "solana-zero-copy"
      version := "1.1.0"
      source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }).identities .unaligned_U64_into_u64 =
      [⟨"solana-zero-copy", "1.1.0", "core::convert::From::from",
        "solana_zero_copy::unaligned::<impl \
          core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from"⟩] := by
            decide +kernel

end SolanalibTest.Specs.SolanaZeroCopy

namespace SolanalibTest.Specs.SolanaZeroCopy

/-- The build selector binds the shared contract to this exact source version and function. -/
theorem registered_release_1_1_1 :
    (Solanalib.Specs.SolanaZeroCopy.Capabilities.catalog.forBuild {
      package := "solana-zero-copy"
      version := "1.1.1"
      source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }).identities .unaligned_U64_into_u64 =
      [⟨"solana-zero-copy", "1.1.1", "core::convert::From::from",
        "solana_zero_copy::unaligned::<impl \
          core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from"⟩] := by
            decide +kernel

end SolanalibTest.Specs.SolanaZeroCopy
