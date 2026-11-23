/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.StakeCodecs.Builder
import SolanalibTest.Conformance.Library.Families.StakeCodecs.Callbacks

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs

def corpora : List (String × List Checker) := [
  ("stake_codecs_interface", [interfaceLookupChecker, PackedLen.checker]),
  ("stake_codecs_program", [programLookupChecker, PackedLen.checkerForVersion false]),
  ("stake_codecs_legacy", [lockupDefaultChecker, lockupForceChecker, delegationChecker,
    lockupChecker, metadataChecker, Pack.checker false, Pack.checker true,
    Builder.initializeChecker, Builder.authorizeChecker, Builder.delegateChecker,
    Builder.setLockupChecker, Builder.mergeChecker, Builder.splitChecker])]

end SolanalibTest.Conformance.Library.Families.StakeCodecs
