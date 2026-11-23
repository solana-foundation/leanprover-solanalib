/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.SdkValues.Values
import SolanalibTest.Conformance.Library.Families.SdkValues.Callbacks
import SolanalibTest.Conformance.Library.Families.SdkValues.Keys

/-! Small SDK values at explicitly reviewed releases. The independently locked
native drivers selected in `corpora` exercise pure values and stateful, unwinding and terminating
callback interpretations. The replay always selects a source relation by its
exact crate version and corpus, including repeated Rust item paths. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.SdkValues

def corpora : List (String × List Checker) := [
  ("sdk_values_pubkey_2_4_0", [Keys.asRef, Keys.isNone, Keys.map]),
  ("sdk_values_solana_program_option_2_2_1",
    [Values.asRef, Values.isNone221, Callbacks.map, Callbacks.unwrapOr]),
  ("sdk_values_spl_pod_0_5_1", [Values.podU16, Values.podU64]),
  ("sdk_values_address_2_6_1", [Keys.eq, Keys.unwrap, Values.loaderId, Values.ed25519Id]),
  ("sdk_values_solana_program_option_3_1_0", [Callbacks.eq, Callbacks.unwrap]),
  ("sdk_values_solana_nullable_1_3_0", [Callbacks.nullable]),
  ("sdk_values_solana_sdk_ids_3_1_0",
    [Values.loaderId, Values.ed25519Id, Values.instructionsId, Values.voteId]),
  ("sdk_values_solana_zero_copy_1_1_1", [Values.zero111]),
  ("sdk_values_spl_pod_0_7_3", [Values.optionalKey]),
  ("sdk_values_solana_zero_copy_1_0_1", [Values.zero101]),
  ("sdk_values_solana_program_1_18_26", [Values.intoOption]),
  ("sdk_values_solana_program_1_15_2", [Callbacks.contains, Values.isNone115,
    Callbacks.unwrapOrDefault])]

end SolanalibTest.Conformance.Library.Families.SdkValues
