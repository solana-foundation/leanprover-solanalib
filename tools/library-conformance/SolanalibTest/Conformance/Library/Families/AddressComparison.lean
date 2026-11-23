/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Address
import Solanalib.Specs.SolanaAddress.Address.Cmp

/-! Exact native Address 2.6.1 comparison observations, through its reviewed
2.6.0/2.6.1 profile. This checker uses the registered mathematical reference;
source ABI, exact Rust item identity and implementation correctness remain separate. -/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.AddressComparison

def ordering (j : Json) : Result Ordering := do
  match ← j.getStr? with
  | "Less" => pure .lt
  | "Equal" => pure .eq
  | "Greater" => pure .gt
  | other => throw s!"unknown Ordering {other}"

def orderingJson : Ordering → Json
  | .lt => "Less"
  | .eq => "Equal"
  | .gt => "Greater"

def corpora : List (String × List Checker) := [
  ("address_comparison_261", [
    Address.valueChecker "<solana_address::Address as core::cmp::Ord>::cmp"
      "Solanalib.Specs.SolanaAddress.Address.cmp_model"
      Solanalib.Specs.SolanaAddress.Address.cmp_model Address.pairArg ordering orderingJson])]

end SolanalibTest.Conformance.Library.Families.AddressComparison
