/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorSystem.Requires

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem

def corpora : List (String × List Checker) := [
  ("anchor_system_0_32_1", checkers ++ [idChecker]),
  ("anchor_system_1_1_2", modernCheckers),
  ("anchor_system_1_0_2", modernCheckers),
  ("anchor_system_0_29_0", checkers),
  ("anchor_system_0_27_0", inlineLegacyCheckers)]

end SolanalibTest.Conformance.Library.Families.AnchorSystem
