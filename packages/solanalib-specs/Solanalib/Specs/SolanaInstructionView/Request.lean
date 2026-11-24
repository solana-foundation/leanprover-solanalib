/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedSliceWitness
public import Solanalib.Specs.Core.CpiRequestCheckedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaInstructionView.cpi

open Solanalib.Specs.Core.Instruction

namespace Seed

/-- Preserve the borrowed slice values and the surrounding mathematical state. -/
def from_slice_model (before : Unit) (args : _root_.Solanalib.Runtime.Bytes) : Seed × Unit :=
  (seedFromSlice args, before)

/-- Exact value conversion, with no validation or additional memory effects. -/
def from_slice_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Bytes) (Seed) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = seedFromSlice args)

theorem from_slice_reference : from_slice_contract.RealizedBy from_slice_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem from_slice_satisfiable : from_slice_contract.Satisfiable :=
  ⟨(), [], trivial⟩

end Seed

namespace Signer

/-- Preserve the borrowed slice values and the surrounding mathematical state. -/
def from_slice_model (before : Unit) (args : List Seed) : Signer × Unit :=
  (signerFromSlice args, before)

/-- Exact value conversion, with no validation or additional memory effects. -/
def from_slice_contract : Solanalib.Contracts.Model Unit (List Seed) (Signer) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = signerFromSlice args)

theorem from_slice_reference : from_slice_contract.RealizedBy from_slice_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem from_slice_satisfiable : from_slice_contract.Satisfiable :=
  ⟨(), [], trivial⟩

end Signer

end Solanalib.Specs.SolanaInstructionView.cpi

namespace Solanalib.Specs.SolanaInstructionView.cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! The local checked slice wrappers include count, address and borrow checks,
plus temporary Box allocation and cleanup. Only the unchecked unit-returning
invocation is opaque. Its finite exits are preserved without filtering. -/

/-- Checked signed slice, including current-state allocation and destruction. -/
def invoke_signed_with_slice_contract : Family := CpiRequest.Checked.signedFamily

/-- Mathematical execution of the selected v1 checked wrapper. -/
def invoke_signed_with_slice_run : FamilyRun invoke_signed_with_slice_contract :=
  CpiRequest.Checked.signedRun

/-- Explicit dependency interpretation used by the nonempty closed witness. -/
def invoke_signed_with_slice_sample : invoke_signed_with_slice_contract.Index :=
  CpiRequest.Checked.sampleSliceTypes

/-- Exact reference correctness; source implementation binding remains separate. -/
theorem invoke_signed_with_slice_reference :
    FamilyReference invoke_signed_with_slice_contract invoke_signed_with_slice_run :=
  CpiRequest.Checked.signedReference

/-- This checked family has a concrete admissible signed call. -/
theorem invoke_signed_with_slice_satisfiable :
    FamilySatisfiable invoke_signed_with_slice_contract invoke_signed_with_slice_sample :=
  CpiRequest.Checked.signedSatisfiable

/-- A nonempty call allocates, validates, invokes and then drops the temporary box. -/
theorem invoke_signed_with_slice_has_execution :
    FamilyHasExecution invoke_signed_with_slice_contract invoke_signed_with_slice_run
      invoke_signed_with_slice_sample :=
  CpiRequest.Checked.signedHasExecution

/-- The unsigned wrapper uses the same checked slice path with empty signers. -/
def invoke_with_slice_contract : Family := CpiRequest.Checked.unsignedFamily

/-- Mathematical execution of the unsigned delegation. -/
def invoke_with_slice_run : FamilyRun invoke_with_slice_contract :=
  CpiRequest.Checked.unsignedRun

/-- Explicit box and invocation interpretation for the unsigned witness. -/
def invoke_with_slice_sample : invoke_with_slice_contract.Index :=
  CpiRequest.Checked.sampleSliceTypes

/-- Exact unsigned reference correctness with every dependency exit retained. -/
theorem invoke_with_slice_reference :
    FamilyReference invoke_with_slice_contract invoke_with_slice_run :=
  CpiRequest.Checked.unsignedReference

/-- The unsigned family has a concrete admissible call. -/
theorem invoke_with_slice_satisfiable :
    FamilySatisfiable invoke_with_slice_contract invoke_with_slice_sample :=
  CpiRequest.Checked.unsignedSatisfiable

/-- The unsigned nonempty witness includes the same allocation and cleanup effects. -/
theorem invoke_with_slice_has_execution :
    FamilyHasExecution invoke_with_slice_contract invoke_with_slice_run invoke_with_slice_sample :=
  CpiRequest.Checked.unsignedHasExecution

end Solanalib.Specs.SolanaInstructionView.cpi

namespace Solanalib.Specs.SolanaInstructionView

open Solanalib.Specs.Core.Instruction

namespace cpi.Seed

/-- Preserve every element and its order in the fixed-size array observation. -/
def from_array_model (before : Unit) (args : ArrayValue UInt8) : Seed × Unit :=
  (seedFromArray args, before)

/-- Exact array value conversion, including empty arrays and repeated values. -/
def from_array_contract : Solanalib.Contracts.Model Unit (ArrayValue UInt8) (Seed) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = seedFromArray args)

theorem from_array_reference : from_array_contract.RealizedBy from_array_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem from_array_satisfiable : from_array_contract.Satisfiable :=
  ⟨(), ⟨0, [], rfl⟩, trivial⟩

end cpi.Seed

namespace cpi.Signer

/-- Preserve every element and its order in the fixed-size array observation. -/
def from_array_model (before : Unit) (args : ArrayValue Seed) : Signer × Unit :=
  (signerFromArray args, before)

/-- Exact array value conversion, including empty arrays and repeated values. -/
def from_array_contract : Solanalib.Contracts.Model Unit (ArrayValue Seed) (Signer) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = signerFromArray args)

theorem from_array_reference : from_array_contract.RealizedBy from_array_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem from_array_satisfiable : from_array_contract.Satisfiable :=
  ⟨(), ⟨0, [], rfl⟩, trivial⟩

end cpi.Signer

namespace InstructionAccount

/-- Construct the selected key with signer true and writable false. -/
def readonly_signer_model (before : Unit) (args : _root_.Solanalib.Runtime.Pubkey) : Meta × Unit :=
  (accountMeta args true false, before)

/-- The local constructor preserves state and fixes the asymmetric access flags. -/
def readonly_signer_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Pubkey)
  (Meta) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = accountMeta args true false)

theorem readonly_signer_reference : readonly_signer_contract.RealizedBy readonly_signer_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem readonly_signer_satisfiable : readonly_signer_contract.Satisfiable :=
  ⟨(), .zero, trivial⟩

end InstructionAccount

end Solanalib.Specs.SolanaInstructionView

namespace Solanalib.Specs.SolanaInstructionView.cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! The checked array wrapper preserves the exact array extent and the
source-ordered count/address/writable-borrow checks. The Rust const-generic
capacity bound is a separate source-binding obligation. Each generic AsRef call
retains its own effects and result; only unchecked invocation stays opaque. -/

/-- The checked v2 array family, indexed by the selected AsRef implementation. -/
def invoke_signed_contract : Family := CpiRequest.Checked.arrayFamily

/-- Actual mathematical sequencing of validation and unchecked unit invocation. -/
def invoke_signed_run : FamilyRun invoke_signed_contract := CpiRequest.Checked.arrayRun

/-- A borrowed-AccountView identity instance for the nonempty closed witness. -/
def invoke_signed_sample : invoke_signed_contract.Index := CpiRequest.Checked.sampleArrayTypes

/-- Reference correctness for every selected AsRef and invocation interpretation. -/
theorem invoke_signed_reference : FamilyReference invoke_signed_contract invoke_signed_run :=
  CpiRequest.Checked.arrayReference

/-- The array family has a concrete admissible call. -/
theorem invoke_signed_satisfiable :
    FamilySatisfiable invoke_signed_contract invoke_signed_sample :=
  CpiRequest.Checked.arraySatisfiable

/-- Nonempty validation initializes the exact prefix before the actual invocation. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_run invoke_signed_sample :=
  CpiRequest.Checked.arrayHasExecution

end Solanalib.Specs.SolanaInstructionView.cpi
