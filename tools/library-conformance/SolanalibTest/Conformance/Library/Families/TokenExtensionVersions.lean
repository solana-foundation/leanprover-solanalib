/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.UnpackChecks

namespace SolanalibTest.Conformance.Library.Families.TokenExtensionVersions

open TokenStateVersions

def corpora : List (String × List Checker) := [
  ("token_state_8_0_1", [UnpackChecks.token8, UnpackChecks.tlv, Checks.types,
    Checks.accountLength, Checks.newLength, Checks.extension, Checks.key false, Checks.key true,
    Values.arithmetic false, Values.arithmetic true, Values.epoch false, Values.epoch true,
    Values.selectedFee, Values.frozen, Values.metadataDefault]),
  ("token_state_interface_2_1_0", [
      UnpackChecks.interface2, Checks.typesForVersion true, Checks.accountLengthForVersion true,
      Checks.required, Values.epochForVersion true false]),
  ("token_state_interface_3_0_1", [UnpackChecks.interface3])]

end SolanalibTest.Conformance.Library.Families.TokenExtensionVersions
