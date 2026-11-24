/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Instructions.Values
import SolanalibTest.Conformance.Library.Families.Instructions.Builder
import SolanalibTest.Conformance.Library.Families.Instructions.Borsh
import SolanalibTest.Conformance.Library.Families.Instructions.Switchboard
import SolanalibTest.Conformance.Library.Families.Instructions.Cpi
import SolanalibTest.Conformance.Library.Families.Instructions.CpiAsRef
import SolanalibTest.Conformance.Library.Families.Instructions.SharedToken

/-!
# Family `Instructions`

Drivers `rust/instructions-3-4-0-bincode`, `rust/instructions-3-4-0-wincode`
and `rust/instruction-view-2-1-0-cpi`; `rust/instructions-common` holds
sources two of them include. The System constructors are recorded in distinct
bincode and wincode builds; the same calls of the bincode build are checked against the
value observations (`solana_system_interface`) and the operational models
(`solana_system_interface_3_2_0_bincode`). A function name repeats across corpora where the build
or the model differs, so the corpus selects the checker.

The `shared-token::*` models are checked through family `TokenViews`' records
(`Instructions/SharedToken.lean`). `shared-owned-array::construction` is not tested (README).
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Instructions

open Builder in
def corpora : List (String × List Checker) := [
  ("solana_instruction_3_4_0", [accountMetaNewChecker, accountMetaNewReadonlyChecker] ++
    [u64Ty, vecU8Ty, scriptedTy "conformance_instructions_3_4_0_bincode::builder::ScriptedSerial\
      ize"
      (fun _ m => "Custom(\"" ++ m ++ "\")")].map newWithBincodeChecker),
  ("solana_system_interface_3_2_0", [createAccountChecker, transferChecker]),
  ("solana_system_interface_3_2_0_bincode",
    [createAccountOperationalChecker .bincode, transferOperationalChecker .bincode]),
  ("solana_borsh_3_0_2", SolanaBorsh.checkers),
  ("switchboard_on_demand_0_12_1", [Switchboard.checker]),
  ("pyth_solana_receiver_sdk_2_0_0_getter", [PythGetter.checker]),
  ("solana_instruction_view_2_1_0", [v2SeedFromSliceChecker, readonlySignerChecker] ++
    [0, 1, 32, 33].map v2SeedFromArrayChecker ++ [0, 1, 3].map v2SignerFromArrayChecker ++
    [0, 1, 2, 3].map Cpi.V2.checker ++ [1, 2].map CpiAsRef.checker),
  ("pinocchio_system_0_6_0", [Cpi.PSystem.transferChecker, Cpi.PSystem.allocateChecker,
    Cpi.PSystem.assignChecker]),
  ("pinocchio_associated_token_account_0_4_0", [Cpi.Ata.checker]),
  ("solana_instruction_3_4_0_wincode",
    [u64Ty, vecU8Ty, scriptedTy
      "conformance_instructions_3_4_0_wincode::wincode_builder::ScriptedSerialize"
      (fun _ m => "Custom(\"" ++ m ++ "\")")].map newWithWincodeChecker),
  ("solana_system_interface_3_2_0_wincode",
    [createAccountOperationalChecker .wincode, transferOperationalChecker .wincode]),
  ("solana_instruction_view_1_0_0",
    [v1SeedFromSliceChecker, v1SignerFromSliceChecker, Cpi.V1.signedChecker,
      Cpi.V1.unsignedChecker])
]

end SolanalibTest.Conformance.Library.Families.Instructions
