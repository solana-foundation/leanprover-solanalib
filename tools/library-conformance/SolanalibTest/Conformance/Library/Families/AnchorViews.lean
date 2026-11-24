/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Profiles
import SolanalibTest.Conformance.Library.Families.AnchorViews.AdmissionControls

/-! Actual wrapper calls at each exact native crate release. Relations and
preconditions come from the registered models; callback graphs compare current
payloads, source reference identity, account aliases and resource effects. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

def corpora : List (String × List Checker) := [
  ("anchor_views_0_32_1", checkers profile032),
  ("anchor_views_1_1_2", checkers112),
  ("anchor_views_1_0_2", checkers102),
  ("anchor_views_0_29_0", checkers029),
  ("anchor_views_0_27_0", checkers027)]

end SolanalibTest.Conformance.Library.Families.AnchorViews
