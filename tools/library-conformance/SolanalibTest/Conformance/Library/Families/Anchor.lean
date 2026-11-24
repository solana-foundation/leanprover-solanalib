/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Errors
import SolanalibTest.Conformance.Library.Families.Anchor.Projections
import SolanalibTest.Conformance.Library.Families.Anchor.ConstructCheck
import SolanalibTest.Conformance.Library.Families.Anchor.Loading
import SolanalibTest.Conformance.Library.Families.Anchor.Misc
import SolanalibTest.Conformance.Library.Families.Anchor.Spl
import SolanalibTest.Conformance.Library.Families.Anchor.TransferOwned
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck

/-!
# Family `Anchor`: anchor-lang 1.0.2 and anchor-spl 1.0.2

Driver `rust/anchor` (anchor-lang and anchor-spl 1.0.2;
accounts from loader input regions, `rust/accounts`; syscalls through
`rust/shim`). The `_observation` models have no Rust name of their own: each
checker decides the primary model and its observation model on every record
of the function they describe (`reference` names both). Generic callbacks are
scripted per record and decided through graph lemmas proved from the definitions of the models
(`Anchor/Graph.lean`); natively unobservable ghost state
(guard identities, allocation ledgers) is compared through a projection
(`decideProjected`). The checkers of the models with a non-trivial
precondition decide it on every record (`RequiresCheck`, `decidesRequires`).
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Anchor

def corpora : List (String × List Checker) := [
  ("anchor_lang_1_0_2", RequiresCheck.errorCheckers ++ Projections.checkers ++
    RequiresCheck.constructCheckers ++
    RequiresCheck.loadCheckers ++ RequiresCheck.miscCheckers),
  ("anchor_spl_1_0_2", ([Spl.mintDerefChecker, Spl.interfaceMintDerefChecker].map
    (withFrame [("no syscalls", noSyscalls)])) ++ [RequiresCheck.amountChecker,
      RequiresCheck.transferChecker])
]

end SolanalibTest.Conformance.Library.Families.Anchor
