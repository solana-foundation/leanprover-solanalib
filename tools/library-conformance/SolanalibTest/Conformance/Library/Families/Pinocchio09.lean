/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Pinocchio09.Accounts
import SolanalibTest.Conformance.Library.Families.Pinocchio09.Values
import SolanalibTest.Conformance.Library.Families.Pinocchio09.Logger

/-!
Exact Pinocchio 0.9.2 and pinocchio-log 0.5.1 native conformance.
The driver calls the immutable SDK in the Solana cfg branch. Its providers are
the shared scripted shim, not Agave implementations. Account spare bytes and
duplicate aliases are preserved. Logger tail bytes remain unobserved when the
SDK leaves them uninitialized. The graph lemmas decide registered references
at explicit callback indices, including the reached unwind and terminal exits.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09

def corpora : List (String × List SolanalibTest.Conformance.Library.Checker) := [
  ("pinocchio_0_9_2_accounts", Accounts.checkers),
  ("pinocchio_0_9_2_values", Values.checkers),
  ("pinocchio_log_0_5_1", Logger.checkers)
]

end SolanalibTest.Conformance.Library.Families.Pinocchio09
