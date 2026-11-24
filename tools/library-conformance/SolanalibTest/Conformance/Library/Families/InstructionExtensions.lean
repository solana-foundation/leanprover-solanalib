/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.InstructionExtensions.Clone
import SolanalibTest.Conformance.Library.Families.InstructionExtensions.System

/-!
Registered comparisons cover AccountMeta construction and cloning, seeded
account creation and prefunding. `corpora` lists the exact native profiles.
Each selected reference retains the account-meta and feature
behavior of its constructor. The both-feature native instruction build selects wincode; the
bincode source Entry keeps separate source and provider conditions.
Borrowed `Instruction::clone` remains unregistered here.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.InstructionExtensions

def corpora : List (String × List Checker) := [
  ("instruction_extensions_v2", metadataCheckers false ++ [seededChecker false]),
  ("instruction_extensions_v2_2", [seededChecker false]),
  ("instruction_extensions_wincode", metadataCheckers false ++
    [prefundChecker .wincode]),
  ("instruction_extensions_bincode", metadataCheckers false),
  ("instruction_extensions_legacy_18", metadataCheckers true ++ [programSeededChecker]),
  ("instruction_extensions_legacy_15", [instructionCloneChecker true, programSeededChecker])]

end SolanalibTest.Conformance.Library.Families.InstructionExtensions
