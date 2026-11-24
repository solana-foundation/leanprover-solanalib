/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.EntryDeserialize.SDK
import SolanalibTest.Conformance.Library.Families.EntryDeserialize.Pinocchio

namespace SolanalibTest.Conformance.Library.Families.EntryDeserialize

def corpora : List (String × List Checker) := [
  ("solana_program_entrypoint_2_3_0_deserialize", [sdkChecker]),
  ("pinocchio_0_9_2_deserialize", [0, 1, 2, 5, 64, 254].map pinChecker)]

end SolanalibTest.Conformance.Library.Families.EntryDeserialize
