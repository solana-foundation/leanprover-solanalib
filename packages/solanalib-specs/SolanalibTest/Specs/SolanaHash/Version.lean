/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaHash

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaHash

/-- The build selector binds the shared contract to this exact source version and function. -/
theorem registered_release_4_3_0 :
    (Solanalib.Specs.SolanaHash.Capabilities.catalog.forBuild {
      package := "solana-hash"
      version := "4.3.0"
      source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }).identities .Hash_to_bytes =
      [⟨"solana-hash", "4.3.0", "solana_hash::Hash::to_bytes", "solana_hash::Hash::to_bytes"⟩] :=
        by decide +kernel

end SolanalibTest.Specs.SolanaHash

namespace SolanalibTest.Specs.SolanaHash

/-- The build selector binds the shared contract to this exact source version and function. -/
theorem registered_release_4_4_0 :
    (Solanalib.Specs.SolanaHash.Capabilities.catalog.forBuild {
      package := "solana-hash"
      version := "4.4.0"
      source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }).identities .Hash_to_bytes =
      [⟨"solana-hash", "4.4.0", "solana_hash::Hash::to_bytes", "solana_hash::Hash::to_bytes"⟩] :=
        by decide +kernel

end SolanalibTest.Specs.SolanaHash
