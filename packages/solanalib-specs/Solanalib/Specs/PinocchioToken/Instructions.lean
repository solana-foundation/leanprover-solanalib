/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionBatchWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.PinocchioToken.instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token.Batch

namespace batch.Batch

/-- Batch construction over three separately borrowed buffers. A nonempty
data buffer receives only the discriminator; an empty buffer returns InvalidArgument. -/
def new_contract : Solanalib.Contracts.Model Buffers Unit (Except Solanalib.Runtime.InstrError
  Lengths) := newContract

/-- Exact total mathematical constructor reference. -/
def new_reference : Buffers → Unit → Except Solanalib.Runtime.InstrError Lengths × Buffers :=
  newReference

/-- Closed constructor value/effect witness. -/
theorem new_reference_realizes : new_contract.RealizedBy new_reference := newReference_realizes

/-- The constructor has a permitted nonempty buffer input. -/
theorem new_satisfiable : new_contract.Satisfiable := newSatisfiable

/-- Available entries in the committed prefixes are sent to the explicit
unchecked provider. Ordinary unit return becomes Ok; unwind and terminal exits
retain the exact effects of the provider. Source initialization is a binding obligation. -/
def invoke_signed_contract : Family := invokeFamily

/-- Generic mathematical reference, leaving the actual invocation opaque. -/
def invoke_signed_reference : FamilyRun invoke_signed_contract := invokeRun

/-- Closed partial-correctness witness for every provider/type instantiation. -/
theorem invoke_signed_reference_holds :
    FamilyReference invoke_signed_contract invoke_signed_reference := invokeReference

/-- Invocation has a permitted closed sample. -/
theorem invoke_signed_satisfiable : FamilySatisfiable invoke_signed_contract sampleTypes :=
  invokeSatisfiable

/-- The same sample includes an actual provider return with an ambient effect. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_reference sampleTypes :=
      invokeHasExecution

end batch.Batch

namespace transfer_checked.TransferChecked

/-- The single-owner constructor retains all references and integer values and
supplies an empty multisig slice, without performing token/account checks. -/
def new_contract : Solanalib.Contracts.Model Unit SingleTransfer (Transfer AccountView.Handle) :=
  transferNewContract

/-- Exact specialized constructor reference. -/
def new_reference : Unit → SingleTransfer → Transfer AccountView.Handle × Unit :=
  transferNewReference

/-- Closed equality witness for the complete constructed transfer value. -/
theorem new_reference_realizes : new_contract.RealizedBy new_reference :=
  transferNewReference_realizes

/-- The precondition of the specialized constructor is satisfiable. -/
theorem new_satisfiable : new_contract.Satisfiable := transferNewSatisfiable

/-- Generic `IntoBatch` model with independent account and metadata callback
passes, source error order, persistent partial writes, and final-only length
commitment. Target arithmetic and safe references remain Rust-binding obligations. -/
def into_batch_contract : Family := intoFamily

/-- Finite-exit mathematical relation for every generic signer implementation. -/
def into_batch_reference : FamilyRun into_batch_contract := intoRun

/-- Partial correctness covers every type/callback member of the family. -/
theorem into_batch_reference_holds : FamilyReference into_batch_contract into_batch_reference :=
  intoReference

/-- A nonempty generic signer input satisfies the model precondition. -/
theorem into_batch_satisfiable : FamilySatisfiable into_batch_contract sampleTypes :=
  intoSatisfiable

/-- The registered sample executes both callback passes and commits its result. -/
theorem into_batch_has_execution :
    FamilyHasExecution into_batch_contract into_batch_reference sampleTypes := intoHasExecution

end transfer_checked.TransferChecked
end Solanalib.Specs.PinocchioToken.instructions
