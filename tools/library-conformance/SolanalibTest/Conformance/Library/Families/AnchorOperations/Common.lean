/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Errors

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Lean (Json)
open SolanalibTest.Conformance.Library.Families.Anchor

/-- A terminal record reports only the observed syscall prefix, not a native
successor state. Other exits retain their actual state-bearing trace. -/
def noSyscalls (case : Case) : Result Bool := do
  let before ← field case.state "syscalls"
  let after ← if (← strField case.outcome "exit") = "terminated" then
    field case.outcome "syscalls"
  else field (← field case.outcome "state") "syscalls"
  return before.compress = emptySyscalls.compress && after.compress = emptySyscalls.compress

end SolanalibTest.Conformance.Library.Families.AnchorOperations
