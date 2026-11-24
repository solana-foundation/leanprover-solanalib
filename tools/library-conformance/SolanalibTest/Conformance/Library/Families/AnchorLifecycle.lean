/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version0_27_0
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version0_29_0
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version1_0_2
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version1_1_2
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Version0_32_1

/-! The selected Anchor 0.32.1, 1.1.2, 1.0.2, 0.29.0 and 0.27.0 lifecycle checkers use
their registered references with explicit source applicability, scripts, complete account backing
and error resources. The shared family name does not select other releases or
methods. Rust callbacks are test instances; no CPI implementation is invoked. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

def corpora : List (String × List Checker) := [
  ("anchor_lifecycle_0_32_1", Version0_32_1.checkers),
  ("anchor_lifecycle_1_1_2", Version1_1_2.checkers),
  ("anchor_lifecycle_1_0_2", Version1_0_2.checkers),
  ("anchor_lifecycle_0_29_0", Version0_29_0.checkers),
  ("anchor_lifecycle_0_27_0", Version0_27_0.checkers)]

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
