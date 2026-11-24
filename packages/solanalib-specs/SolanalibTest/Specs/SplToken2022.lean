/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.SplToken2022.Instructions
public import SolanalibTest.Specs.SplToken2022.Allocated
public import SolanalibTest.Specs.SplToken2022.Pda
public import SolanalibTest.Specs.SplToken2022.Models
public import Solanalib.Specs.SplToken2022

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Finite mathematical local token-2022 CPI preparation controls at version 11.0.0. -/

@[expose] public section

namespace SolanalibTest.Specs.SplToken2022

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated

/-- These extension initializers construct metadata before packing. -/
theorem extension_allocation_order :
    (initializeImmutableOwnerPlan .either ⟨token2022ProgramId, .ofNat 1⟩).order = .metasThenData ∧
      (initializeMintCloseAuthorityPlan ⟨⟨token2022ProgramId, .ofNat 1⟩, none⟩).order =
        .metasThenData ∧
      (initializeNonTransferableMintPlan ⟨token2022ProgramId, .ofNat 1⟩).order = .metasThenData :=
  ⟨rfl, rfl, rfl⟩

/-- Metadata pointers distinguish an absent optional key from Some zero. -/
theorem pointer_optional_zero :
    MetadataPointer.optionalNonzero none = .ok Solanalib.Runtime.Pubkey.zero.bytes ∧
      MetadataPointer.optionalNonzero (some .zero) = .error .InvalidArgument := by simp
        [MetadataPointer.optionalNonzero]

/-- An invalid optional key is deliberately combined with a first-allocation
terminal outcome, so ordering can be checked. -/
def invalidPointer : MetadataPointer.Args := ⟨token2022ProgramId, .ofNat 1, some .zero, none⟩

/-- Actual first allocator termination; there is no metadata owner to clean. -/
def terminalTypes : Types := { Witness.sampleTypes with
  metas := { Witness.sampleTypes.metas with
    fromList := fun _ _ outcome => outcome = .terminated (71 : Nat) } }

/-- Allocation is reached before optional-key validation. -/
theorem pointer_allocation_precedes_field_error :
    MetadataPointer.run 39 terminalTypes Witness.initialState invalidPointer (.terminated (71 :
      Nat)) :=
  ⟨.terminated (71 : Nat), rfl, rfl⟩

/-- Once metadata exists, a failed field conversion drops that exact owner. -/
theorem pointer_invalid_field_retires_metadata :
    MetadataPointer.run 39 Witness.sampleTypes Witness.initialState invalidPointer
      (.returned (.error .InvalidArgument) ([], [none])) := by
  apply MetadataPointer.from_allocated rfl (Witness.metas_from_list [] [] _)
  apply MetadataPointer.invalid_fields rfl
  exact ⟨.returned () ([], [none]), Witness.metas_drop [] _, rfl⟩

/-- A field-error cleanup can unwind with the actual state of the destructor. -/
def unwindingDropTypes : Types := { Witness.sampleTypes with
  metas := { Witness.sampleTypes.metas with
    drop := fun _ _ outcome => outcome = .unwound (19 : Nat) ([], [none]) } }

/-- Destructor failure remains an unwind instead of becoming the intended Err. -/
theorem pointer_cleanup_unwind_retained :
    MetadataPointer.run 39 unwindingDropTypes Witness.initialState invalidPointer
      (.unwound (19 : Nat) ([], [none])) := by
  apply MetadataPointer.from_allocated (types := unwindingDropTypes) rfl
    (Witness.metas_from_list [] [] _)
  apply MetadataPointer.invalid_fields rfl
  exact ⟨.unwound (19 : Nat) ([], [none]), rfl, rfl⟩

/-- Wrong program admission takes precedence over allocator termination. -/
theorem pointer_program_error_precedes_allocator :
    MetadataPointer.run 39 terminalTypes Witness.initialState { invalidPointer with programId :=
      legacyProgramId }
      (.returned (.error .IncorrectProgramId) Witness.initialState) := rfl

end SolanalibTest.Specs.SplToken2022

namespace SolanalibTest.Specs.SplToken2022

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Both standard program IDs are accepted for immutable-owner construction. -/
theorem immutable_owner_accepts_legacy :
    (initializeImmutableOwnerPlan .either ⟨legacyProgramId, .ofNat 1⟩).value =
      .ok ⟨legacyProgramId, [Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 1) false true],
        [22]⟩ := rfl

/-- Nontransferable initialization rejects the legacy Token program. -/
theorem nontransferable_rejects_legacy :
    (initializeNonTransferableMintPlan ⟨legacyProgramId, .ofNat 1⟩).value = .error
      .IncorrectProgramId := rfl

/-- The released Token-2022 authority enum includes Pause at byte16. -/
theorem authority_pause_byte :
    (setAuthorityPlan .either
      (⟨token2022ProgramId, .ofNat 1, none, ⟨16, by decide⟩, .ofNat 2, []⟩ : SetAuthorityArgs
        17)).data =
      [6, 16, 0] := rfl

/-- Freeze and thaw retain a readonly mint and distinct discriminants. -/
theorem freeze_thaw_layout :
    ((freezeAccountPlan .either Witness.tokenAuthority).metas.items.map (·.writableByte))[1]? =
      some 0 ∧
      (freezeAccountPlan .either Witness.tokenAuthority).data = [10] ∧
      (thawAccountPlan .either Witness.tokenAuthority).data = [11] := by decide +kernel

/-- Token-2022 uses its own constant native mint, not the legacy wrapped SOL ID. -/
theorem native_mint_is_not_legacy :
    Solanalib.Specs.SplToken2022.native_mint.declaredId.bytes ≠
      [6, 155, 136, 87, 254, 171, 129, 132, 251, 104, 127, 99, 70, 24, 192, 53,
        218, 196, 57, 220, 26, 235, 59, 85, 152, 160, 240, 0, 0, 0, 0, 1] := by decide +kernel

end SolanalibTest.Specs.SplToken2022
