/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequest

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.PinocchioToken2022.instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token.Request

namespace close_account.CloseAccount

/-- Local three-account construction followed by InstructionView 2.1.0 checks. -/
def invoke_signed_contract : Family := signedCloseFamily
/-- The signed wrapper reference includes current-pool checks and the opaque Unit boundary. -/
def invoke_signed_reference : FamilyRun invoke_signed_contract := signedCloseRun
/-- The exact versioned reference realizes its checked family. -/
theorem invoke_signed_reference_holds :
    FamilyReference invoke_signed_contract invoke_signed_reference := signedCloseReference
/-- The checked family has a concrete admissible input. -/
theorem invoke_signed_satisfiable : FamilySatisfiable invoke_signed_contract sampleTypes :=
  signedCloseSatisfiable
/-- A nonempty actual checked path reaches normal opaque completion. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_reference sampleTypes :=
  signedCloseHasExecution

end close_account.CloseAccount

namespace transfer_checked.TransferChecked

/-- The unsigned checked-transfer wrapper uses the same preparation with no seeds. -/
def invoke_contract : Family := unsignedTransferFamily
/-- The unsigned reference uses the same checked path with no signer seeds. -/
def invoke_reference : FamilyRun invoke_contract := unsignedTransferRun
/-- The exact versioned reference realizes its checked family. -/
theorem invoke_reference_holds : FamilyReference invoke_contract invoke_reference :=
  unsignedTransferReference
/-- The checked family has a concrete admissible input. -/
theorem invoke_satisfiable : FamilySatisfiable invoke_contract sampleTypes :=
  unsignedTransferSatisfiable
/-- A nonempty actual checked path reaches normal opaque completion. -/
theorem invoke_has_execution : FamilyHasExecution invoke_contract invoke_reference sampleTypes :=
  unsignedTransferHasExecution

/-- The signed checked-transfer wrapper runs v2 checks before the opaque Unit boundary. -/
def invoke_signed_contract : Family := signedTransferFamily
/-- The signed wrapper reference includes current-pool checks and the opaque Unit boundary. -/
def invoke_signed_reference : FamilyRun invoke_signed_contract := signedTransferRun
/-- The exact versioned reference realizes its checked family. -/
theorem invoke_signed_reference_holds :
    FamilyReference invoke_signed_contract invoke_signed_reference := signedTransferReference
/-- The checked family has a concrete admissible input. -/
theorem invoke_signed_satisfiable : FamilySatisfiable invoke_signed_contract sampleTypes :=
  signedTransferSatisfiable
/-- A nonempty actual checked path reaches normal opaque completion. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_reference sampleTypes :=
  signedTransferHasExecution

end transfer_checked.TransferChecked
end Solanalib.Specs.PinocchioToken2022.instructions
