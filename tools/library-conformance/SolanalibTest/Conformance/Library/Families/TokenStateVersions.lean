/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Clone

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions

/-- Each exact release has its own actual Rust recording and checked binding. -/
def corpora : List (String × List Checker) :=
  [("token_state_interface_3_1_1", [Clone.checker])]

end SolanalibTest.Conformance.Library.Families.TokenStateVersions
