/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Instructions
import SolanalibTest.Conformance.Library.Families.TokenInterface.Fees
import SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions
import SolanalibTest.Conformance.Library.Families.TokenInterface.Onchain

/-!
# Family `TokenInterface`: spl-token-interface 2.0.0, spl-token-2022-interface 3.1.1

Drivers `rust/token-interface` (the two interfaces) and
`rust/token-interface-onchain` (spl-token-2022 11.0.0). See the modules under
`Families/TokenInterface/` for the record shapes and the decided references.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface

def corpora : List (String × List Checker) := [
  ("spl_token_interface_2_0_0", Instructions.legacyCheckers),
  ("spl_token_2022_interface_3_1_1", Instructions.tokenCheckers),
  ("spl_token_2022_interface_3_1_1_fee", Fees.checkers),
  ("spl_token_2022_interface_3_1_1_extension", Extensions.checkers),
  ("spl_token_2022_11_0_0", Onchain.checkers)
]

end SolanalibTest.Conformance.Library.Families.TokenInterface
