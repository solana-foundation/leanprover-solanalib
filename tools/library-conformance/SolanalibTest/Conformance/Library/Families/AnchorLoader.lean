/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Close
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Init
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Construct
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Identity
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Exit
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires

/-! Actual AccountLoader calls at the selected Anchor 0.32.1, 1.0.2 and 1.1.2 releases.
The 1.0.2 corpus additionally checks clone and close. Each checker decides
the registered reference and its reached admission. Unobservable allocation
and guard identifiers are projected only after exact modeled execution; the
native observations retain cells, aliases, guard leases, current views,
callback effects, copied bytes, backing storage and destination Rc cleanup. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader

def common : List Checker := [Construct.uncheckedChecker, Construct.accountsChecker,
  Identity.asRefChecker, Exit.checker] ++ Init.checkers

def corpora : List (String × List Checker) := [
  ("anchor_loader_0_32_1", common),
  ("anchor_loader_1_1_2", common),
  ("anchor_loader_1_0_2", common ++ [Identity.cloneChecker, Close.checker])]

end SolanalibTest.Conformance.Library.Families.AnchorLoader
