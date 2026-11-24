/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.Instructions

@[expose] public section

open Solanalib.Specs

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open InstructionsSysvar

theorem nonempty_constructor_acquires_original_guard :
    Pinocchio.sysvars.instructions.Instructions.try_from_run
      Witness.initial Sysvar.Witness.handle = (.ok Witness.source, Witness.borrowed) := rfl

theorem nonempty_instruction_offset :
    instructionAt Witness.borrowed (Witness.source, 0) = .ok Witness.instruction := rfl

theorem nonempty_program_bytes :
    (programId Witness.borrowed Witness.instruction).bytes Witness.borrowed =
      List.replicate 32 34 := rfl

theorem nonempty_data_bytes :
    (data Witness.borrowed Witness.instruction).bytes Witness.borrowed = [4, 5, 6] := rfl

theorem nonempty_program_extent_conclusion :
    ((programId Witness.borrowed Witness.instruction).bytes Witness.borrowed).length = 32 :=
  programId_bytes_length Witness.borrowed Witness.instruction (by decide)

theorem nonempty_data_extent_conclusion :
    ((data Witness.borrowed Witness.instruction).bytes Witness.borrowed).length =
      (data Witness.borrowed Witness.instruction).length :=
  data_bytes_length Witness.borrowed Witness.instruction (by decide)

/-- One-byte valid storage accepted by the constructor but too short for a footer. -/
def shortAccount : AccountView.Account :=
  { Witness.account with dataLen := 1, entryLen := 1, backing := [1] }

/-- The one-byte account before acquisition. -/
def shortInitial := Sysvar.Witness.singleAccount shortAccount
/-- The one-byte account with its shared captured view. -/
def shortBorrowed := Sysvar.Witness.singleGuard shortAccount .shared

theorem constructor_accepts_short_unvalidated_data :
    tryFrom shortInitial Sysvar.Witness.handle = (.ok Witness.source, shortBorrowed) := rfl

theorem constructor_does_not_establish_decoder_extent :
    ¬ 2 ≤ (Witness.source.bytes shortBorrowed).length := by decide

theorem short_program_observation_has_no_address :
    (programId shortBorrowed ⟨Witness.source, 0⟩).value? shortBorrowed = none := rfl

/-- A readable count with no offset-table storage. -/
def countOnlyAccount : AccountView.Account :=
  { Witness.account with dataLen := 2, entryLen := 2, backing := [1, 0] }

/-- A shared view of the count-only account. -/
def countOnlyBorrowed := Sysvar.Witness.singleGuard countOnlyAccount .shared

theorem out_of_range_does_not_read_absent_offset_table :
    instructionAt countOnlyBorrowed (Witness.source, 1) = .error .invalidInstructionData := rfl

theorem reached_offset_table_still_requires_extent :
    ¬ 4 ≤ (Witness.source.bytes countOnlyBorrowed).length := by decide

theorem instructions_address_error_precedes_exclusive_conflict :
    tryFrom (Sysvar.Witness.singleGuard AccountView.Account.empty .exclusive)
      Sysvar.Witness.handle =
      (.error .unsupportedSysvar,
        Sysvar.Witness.singleGuard AccountView.Account.empty .exclusive) := rfl

theorem matching_address_preserves_borrow_failure :
    tryFrom (Sysvar.Witness.singleGuard shortAccount .exclusive) Sysvar.Witness.handle =
      (.error .accountBorrowFailed, Sysvar.Witness.singleGuard shortAccount .exclusive) := rfl

theorem release_invalidates_derived_instruction_guard :
    AccountView.guardRead (release Witness.borrowed Witness.source).2
      Witness.instruction.source.guard = .error .invalidGuard := rfl

/-- The total observer returns an empty fallback, while the source
contract below rejects the consumed receiver. -/
theorem released_receiver_uses_empty_fallback :
    Pinocchio.sysvars.instructions.Instructions.load_current_index_run
      (release Witness.borrowed Witness.source).2 Witness.source =
      (0, (release Witness.borrowed Witness.source).2) := rfl

/-- No source read is admitted after its captured guard is consumed. -/
theorem released_receiver_is_not_admitted :
    ¬ Pinocchio.sysvars.instructions.Instructions.load_current_index_contract.requires
      (release Witness.borrowed Witness.source).2 Witness.source := by
  rintro ⟨⟨slot, cell, live, rest⟩, _⟩
  change none = some slot at live
  cases live

private theorem whole_ready (account : AccountView.Account)
    (extent : account.dataLen ≤ account.backing.length) (length : account.dataLen < ISIZE_LIMIT) :
    Witness.source.Ready (Sysvar.Witness.singleGuard account .shared) := by
  refine ⟨_, _, rfl, rfl, rfl, ?_, length⟩
  simpa [AccountView.Account.whole] using extent

private theorem whole_constructor_ready (account : AccountView.Account)
    (extent : account.dataLen ≤ account.backing.length) (length : account.dataLen < ISIZE_LIMIT) :
    constructorReady (Sysvar.Witness.singleAccount account) Sysvar.Witness.handle := by
  refine ⟨_, rfl, ?_⟩
  intro _ guard after _
  exact ⟨extent, length⟩

/-- The exact constructor family still executes on a valid one-byte slice. -/
theorem short_constructor_has_execution :
    Pinocchio.sysvars.instructions.Instructions.try_from_contract.HasExecution
      (returnsOf Pinocchio.sysvars.instructions.Instructions.try_from_run) :=
  ⟨shortInitial, Sysvar.Witness.handle, .returned (.ok Witness.source) shortBorrowed,
    whole_constructor_ready shortAccount (by decide) (by decide), rfl⟩

/-- Constructor success is not a proof that the footer read is defined. -/
theorem short_constructor_does_not_admit_footer :
    ¬ currentIndexReady shortBorrowed Witness.source := by
  intro ready
  exact constructor_does_not_establish_decoder_extent ready.2

/-- A checked early count error requires no absent table bytes. -/
theorem count_only_error_is_admitted :
    instructionAtReady countOnlyBorrowed (Witness.source, 1) ∧
      checkedInstructionAt countOnlyBorrowed (Witness.source, 1) =
        some (.error .invalidInstructionData) := by
  refine ⟨⟨whole_ready countOnlyAccount (by decide) (by decide), by decide, ?_⟩, rfl⟩
  intro inside
  have impossible : ¬ (1 : UInt64).toNat < numInstructions countOnlyBorrowed Witness.source := by
    decide
  exact False.elim (impossible inside)

/-- The same bytes reject an in-range lookup before its missing table read. -/
theorem count_only_success_is_not_admitted :
    ¬ instructionAtReady countOnlyBorrowed (Witness.source, 0) := by
  intro ready
  have table := (ready.2.2 (by decide)).2.1
  exact (by decide : ¬ 2 + 2 * (0 : UInt64).toNat + 2 ≤
    (Witness.source.bytes countOnlyBorrowed).length) table

/-- A captured slice shifted by one byte in the same aligned account storage. -/
def oddAccount : AccountView.Account :=
  { Witness.account with dataLen := 79, entryLen := 79, backing := 99 :: Witness.bytes }

/-- The shared guard maps the 78-byte buffer at actual allocation offset one. -/
def oddBorrowed : AccountView.State :=
  { Sysvar.Witness.singleAccount oddAccount with
    slots := [some ⟨Sysvar.Witness.handle, .shared, 0, ⟨1, 78⟩⟩] }

private theorem odd_ready : Witness.source.Ready oddBorrowed := by
  exact ⟨_, _, rfl, rfl, rfl, by decide, by decide⟩

/-- Odd-address byte-array footer reads remain admitted. -/
theorem odd_byte_footer_is_admitted :
    currentIndexReady oddBorrowed Witness.source ∧
      checkedCurrentIndex oddBorrowed Witness.source = some 0 :=
  ⟨⟨odd_ready, by decide⟩, rfl⟩

/-- The native table read uses the mapped guard offset, not just the even
relative table index; the old raw value cannot justify this source execution. -/
theorem odd_native_table_is_not_admitted :
    instructionAt oddBorrowed (Witness.source, 0) = .ok Witness.instruction ∧
      ¬ instructionAtReady oddBorrowed (Witness.source, 0) := by
  refine ⟨rfl, ?_⟩
  intro ready
  have aligned := (ready.2.2 (by decide)).1
  change (1 + (2 + 2 * (0 : UInt64).toNat)) % 2 = 0 at aligned
  contradiction

/-- A count and a valid offset that points exactly one-past the buffer. -/
def onePastAccount : AccountView.Account :=
  { Witness.account with dataLen := 4, entryLen := 4, backing := [1, 0, 4, 0] }

/-- A shared view whose stored instruction offset is one-past. -/
def onePastBorrowed := Sysvar.Witness.singleGuard onePastAccount .shared

/-- Lookup forms a legal one-past raw pointer without reading an entry. -/
theorem one_past_lookup_is_admitted :
    instructionAtReady onePastBorrowed (Witness.source, 0) ∧
      checkedInstructionAt onePastBorrowed (Witness.source, 0) = some (.ok Witness.instruction) :=
        by
  refine ⟨⟨whole_ready onePastAccount (by decide) (by decide), by decide, ?_⟩, rfl⟩
  intro _
  exact ⟨by change (0 + (2 + 2 * (0 : UInt64).toNat)) % 2 = 0; decide, by decide, by decide⟩

/-- The later program read cannot use that one-past pointer as an entry. -/
theorem one_past_program_decode_is_not_admitted :
    ¬ programIdReady onePastBorrowed Witness.instruction := by
  intro ready
  exact (by decide : ¬ Witness.instruction.offset + 2 ≤
    (Witness.source.bytes onePastBorrowed).length) ready.2.1

/-- A complete zero-account entry with an empty payload at one-past. -/
def emptyDataAccount : AccountView.Account :=
  { Witness.account with
    dataLen := 36
    entryLen := 36
    backing := [0, 0] ++ List.replicate 32 17 ++ [0, 0] }

/-- The complete empty-payload entry under a shared lease. -/
def emptyDataBorrowed := Sysvar.Witness.singleGuard emptyDataAccount .shared

/-- Empty payload validity does not skip either scalar read. -/
theorem empty_data_after_real_reads_is_admitted :
    dataReady emptyDataBorrowed ⟨Witness.source, 0⟩ ∧
      checkedData emptyDataBorrowed ⟨Witness.source, 0⟩ = some ⟨Witness.source, 36, 0⟩ :=
  ⟨⟨whole_ready emptyDataAccount (by decide) (by decide), by decide, by decide, by decide⟩, rfl⟩

/-- The length word asks for three bytes but only one byte is present. -/
def truncatedDataAccount : AccountView.Account :=
  { emptyDataAccount with
    dataLen := 37
    entryLen := 37
    backing := [0, 0] ++ List.replicate 32 17 ++ [3, 0, 9] }

/-- The live shared view of the intentionally truncated payload. -/
def truncatedDataBorrowed := Sysvar.Witness.singleGuard truncatedDataAccount .shared

/-- Truncated current payloads have no source-function result. -/
theorem truncated_data_is_not_admitted :
    ¬ dataReady truncatedDataBorrowed ⟨Witness.source, 0⟩ := by
  intro ready
  exact (by decide : ¬ dataLengthOffset truncatedDataBorrowed ⟨Witness.source, 0⟩ + 2 +
    word (Witness.source.bytes truncatedDataBorrowed)
      (dataLengthOffset truncatedDataBorrowed ⟨Witness.source, 0⟩) ≤
    (Witness.source.bytes truncatedDataBorrowed).length) ready.2.2.2

/-- The raw truncating observation remains available without a source claim. -/
theorem truncated_raw_data_is_unchanged :
    (data truncatedDataBorrowed ⟨Witness.source, 0⟩).length = 3 ∧
      (data truncatedDataBorrowed ⟨Witness.source, 0⟩).bytes truncatedDataBorrowed = [9] := ⟨rfl,
        rfl⟩

end SolanalibTest.Specs.Pinocchio.Instructions
