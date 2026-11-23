/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenViews.State
import SolanalibTest.Conformance.Library.Families.TokenViews.Batch
import SolanalibTest.Conformance.Library.Families.TokenViews.Request

/-!
# Family `TokenViews`: pinocchio-token 0.6.0 and pinocchio-token-2022 0.3.1

Driver `rust/token-views` (one dependency lockfile) writes
one corpus per crate. pinocchio-token 0.6.0: Account/Mint parsers and getters,
`Batch::new`, `Batch::invoke_signed`, the single-owner `TransferChecked::new`
and `IntoBatch::into_batch` at two `MultisigSigner` instantiations.
pinocchio-token-2022 0.3.1: Account/Mint parsers and getters and the checked
CPI wrappers `TransferChecked::invoke`/`invoke_signed` and
`CloseAccount::invoke_signed`.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenViews

def corpora : List (String × List Checker) := [
  ("pinocchio_token_0_6_0", State.V060.checkers ++ Batch.checkers),
  ("pinocchio_token_2022_0_3_1", State.V031.checkers ++ Request.checkers)
]

end SolanalibTest.Conformance.Library.Families.TokenViews
