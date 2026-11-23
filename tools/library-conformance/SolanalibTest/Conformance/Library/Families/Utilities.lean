/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Utilities.Checked
import SolanalibTest.Conformance.Library.Families.Utilities.Values
import SolanalibTest.Conformance.Library.Families.Utilities.Syscalls

/-!
Exact legacy and split SDK utility releases. The mathematical references are
interpreted with the established native shim; scripted hashes and sysvar replies
make no claim about a validator implementation. The instruction decoders use a
separate allocation and shared-borrow observation.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Utilities

def corpora : List (String × List Checker) := [
  ("utility_split222", [Values.isExempt "solana_rent::Rent::is_exempt", Syscalls.splitClock,
    Syscalls.splitRent, Syscalls.hashv222, Syscalls.hash222 "solana_sha256_hasher::hash",
      Syscalls.msgLog]),
  ("utility_split230", [Syscalls.splitClock, Syscalls.splitRent]),
  ("utility_modern3", [Values.isExempt "solana_rent::Rent::is_exempt", Values.firstSlot,
    Syscalls.epochGet, Syscalls.hash310]),
  ("utility_instructions4", [Checked.current, Checked.atInstruction]),
  ("utility_instructions3", [Checked.current, Checked.atInstruction]),
  ("utility_legacy118", [Values.legacyMinimum, Values.programIsExempt
    "solana_program::rent::Rent::is_exempt",
    Values.legacyToBytes, Syscalls.legacy118Clock, Syscalls.legacy118Rent,
    Syscalls.legacyLog, Syscalls.programHash "solana_program::hash::hash"]),
  ("utility_legacy115", [Values.legacyMinimum, Values.programIsExempt
    "solana_program::rent::Rent::is_exempt",
    Values.lastSlot, Syscalls.legacy115Rent, Syscalls.legacyLog, Syscalls.computeLog])]

end SolanalibTest.Conformance.Library.Families.Utilities
