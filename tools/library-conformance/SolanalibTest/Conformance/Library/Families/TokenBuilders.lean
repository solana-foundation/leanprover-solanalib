/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenBuilders.Checkers

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenBuilders

def corpora : List (String × List Checker) := [
  ("spl_token_8_0_0_instructions", legacy),
  ("spl_token_2022_8_0_1_instructions", token2022),
  ("spl_token_metadata_interface_0_7_0_initialize", [Metadata.checker]),
  ("spl_memo_6_0_0_id", [TokenInterface.Instructions.idChecker
    "spl_memo::id" "Solanalib.Specs.SplMemo.id_reference" Solanalib.Specs.SplMemo.id_reference])]

end SolanalibTest.Conformance.Library.Families.TokenBuilders
