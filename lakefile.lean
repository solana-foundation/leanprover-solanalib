import Lake
open Lake DSL

/-!
## Solanalib

A library of formal models and verified results for Solana programs.

Dependencies:
* Mathlib — algebraic infrastructure, tactics, numeric types.
* doc-gen4 — gated behind `-Kenv=dev` so casual builds don't pay its cost.
-/

package solanalib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]
  testDriver := "SolanalibTest"

require "leanprover-community" / "mathlib" @ git "v4.31.0-rc1"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib Solanalib where

lean_lib SolanalibTest where
