/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressDerived
public import Solanalib.Specs.Core.AddressBorsh

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AddressOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Syscall Solanalib.Specs.Core.Address.Operations

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) :=
  Solanalib.Specs.Core.Borsh.exceptDecEq

def key (first last : UInt8) : Value :=
  ⟨first :: List.replicate 30 0 ++ [last], by simp⟩

theorem comparison_first_byte_wins : compare (key 1 255, key 2 0) = .lt := by decide
theorem comparison_last_byte_matters : compare (key 1 3, key 1 2) = .gt := by decide
theorem comparison_rejects_reversed_order : compare (key 1 255, key 2 0) ≠ .gt := by decide

def statusIndex (status : UInt64) : CreateIndex .zeroed where
  State := Nat
  Unwind := String
  Terminal := String
  syscall := Callback.ofFunction fun before _ => .returned ⟨status, key 7 8⟩ (before + 1)
  panic := Callback.ofFunction fun before reason => .unwound reason (before + 10)

theorem modern_status_two_is_illegal_owner :
    createRun .pubkey (statusIndex 2) (0 : Nat) Operations.sampleInputs
      (.returned (.error .illegalOwner) (1 : Nat)) := by
  change ∃ _, _
  exact ⟨.returned ⟨2, key 7 8⟩ (1 : Nat), rfl, rfl⟩

theorem legacy_status_two_panics_after_syscall :
    createRun .legacyPubkey (statusIndex 2) (0 : Nat) Operations.sampleInputs
      (.unwound "Unsupported PubkeyError" (11 : Nat)) := by
  change ∃ _, _
  exact ⟨.returned ⟨2, key 7 8⟩ (1 : Nat), rfl,
    .unwound "Unsupported PubkeyError" (11 : Nat), rfl, rfl⟩

theorem legacy_rejects_modern_status_two_result :
    ¬ createRun .legacyPubkey (statusIndex 2) (0 : Nat) Operations.sampleInputs
      (.returned (.error .illegalOwner) (1 : Nat)) := by
  simp [createRun, Operations.sampleInputs, badSeeds, statusIndex, Callback.bind,
    Callback.ofFunction,
    finishCreate, ErrorProfile.decode, ErrorProfile.panicMessage, panicAs, Callback.map,
    Outcome.map]

theorem count_error_precedes_every_provider :
    createRun .pubkey (statusIndex 2) (0 : Nat) ⟨List.replicate 17 [], .zero⟩
      (.returned (.error .maxSeedLengthExceeded) (0 : Nat)) := by
  simp [createRun, badSeeds]

theorem long_seed_precedes_every_provider :
    createRun .pubkey (statusIndex 2) (0 : Nat) ⟨[[1], List.replicate 33 0], .zero⟩
      (.returned (.error .maxSeedLengthExceeded) (0 : Nat)) := by
  simp [createRun, badSeeds]

def uninitializedSuccess : CreateIndex .uninitialized where
  State := Unit
  Unwind := Empty
  Terminal := Empty
  syscall := Callback.ofFunction fun before _ => .returned ⟨0, none⟩ before
  panic := fun _ _ _ => False

theorem uninitialized_success_is_not_admitted :
    ¬ createReady uninitializedSuccess () Operations.sampleInputs := by
  intro ready
  obtain ⟨value, impossible⟩ := ready rfl ⟨0, none⟩ () rfl rfl
  cases impossible

theorem successful_create_preserves_returned_buffer :
    createRun .pubkey (statusIndex 0) (0 : Nat) Operations.sampleInputs
      (.returned (.ok (key 7 8)) (1 : Nat)) := by
  change ∃ _, _
  exact ⟨.returned ⟨0, key 7 8⟩ (1 : Nat), rfl, key 7 8, rfl, rfl⟩

def findIndex (status : UInt64) : ZeroFindIndex where
  State := Nat
  Unwind := String
  Terminal := String
  syscall := Callback.ofFunction fun before _ => .returned ⟨status, key 4 9, 0⟩ (before + 1)
  panic := Callback.ofFunction fun before _ => .unwound panicMessage (before + 10)

theorem find_starts_zeroed : (zeroFindRequest Operations.sampleInputs).addressOutput = some .zero
  := rfl

theorem find_returns_actual_bump :
    zeroFindRun (findIndex 0) (0 : Nat) Operations.sampleInputs
      (.returned (key 4 9, 0) (1 : Nat)) :=
  ⟨.returned (some (key 4 9, 0)) (1 : Nat),
    ⟨.returned ⟨0, key 4 9, 0⟩ (1 : Nat), rfl, rfl⟩, rfl⟩

theorem find_nonzero_reaches_panic_in_actual_state :
    zeroFindRun (findIndex 1) (0 : Nat) Operations.sampleInputs
      (.unwound panicMessage (11 : Nat)) :=
  ⟨.returned none (1 : Nat), ⟨.returned ⟨1, key 4 9, 0⟩ (1 : Nat), rfl, rfl⟩,
    .unwound panicMessage (11 : Nat), rfl, rfl⟩

theorem find_does_not_locally_reject_long_seeds :
    zeroFindRun (findIndex 0) (0 : Nat) ⟨List.replicate 17 (List.replicate 33 0), .zero⟩
      (.returned (key 4 9, 0) (1 : Nat)) :=
  ⟨.returned (some (key 4 9, 0)) (1 : Nat),
    ⟨.returned ⟨0, key 4 9, 0⟩ (1 : Nat), rfl, rfl⟩, rfl⟩

theorem seed_byte_length_not_character_count :
    seedError ⟨.zero, "☉☉☉☉☉☉☉☉☉☉☉", .zero⟩ = some .maxSeedLengthExceeded := by
  simp only [seedError, SeedInputs.bytes, String.toUTF8_eq_toByteArray]
  decide +kernel

def illegalOwner : Value :=
  ⟨List.replicate 11 0 ++ marker, by
    simp only [List.length_append, List.length_replicate, marker, Solanalib.Runtime.PDA_MARKER,
      Solanalib.Runtime.strBytes, String.toUTF8_eq_toByteArray]
    decide +kernel⟩

theorem seed_owner_suffix_is_rejected :
    seedError ⟨.zero, "x", illegalOwner⟩ = some .illegalOwner := by
  simp only [seedError, SeedInputs.bytes, illegalOwner, marker, Solanalib.Runtime.PDA_MARKER,
    Solanalib.Runtime.strBytes, String.toUTF8_eq_toByteArray]
  decide +kernel

theorem long_seed_before_illegal_owner :
    seedError ⟨.zero, "123456789012345678901234567890123", illegalOwner⟩ =
      some .maxSeedLengthExceeded := by
  simp only [seedError, SeedInputs.bytes, illegalOwner, marker, Solanalib.Runtime.PDA_MARKER,
    Solanalib.Runtime.strBytes, String.toUTF8_eq_toByteArray]
  decide +kernel

theorem associated_seed_order :
    (associatedInputs ⟨key 1 0, key 2 0, key 3 0⟩).seeds =
      [(key 1 0).bytes, (key 3 0).bytes, (key 2 0).bytes] := rfl

theorem associated_rejects_swapped_mint_and_token_program :
    (associatedInputs ⟨key 1 0, key 2 0, key 3 0⟩).seeds ≠
      [(key 1 0).bytes, (key 2 0).bytes, (key 3 0).bytes] := by decide

theorem loader_has_one_seed : (loaderInputs (key 4 0)).seeds = [(key 4 0).bytes] := rfl

open Solanalib.Specs.Core.Borsh

theorem read_eof_keeps_reader_effects_and_maps_error :
    Address.Borsh.readRun .invalidData Address.Borsh.readSample (0 : Nat) ()
      (.returned (.error ⟨.invalidData, unexpectedLengthMessage⟩) (31 : Nat)) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    Address.Borsh.readSample, Callback.bind, Callback.map, Callback.ofFunction,
    Owned.protect, Owned.onUnwind, Outcome.map]

theorem read_non_eof_error_is_unchanged :
    Address.Borsh.mapReadError .invalidData ⟨⟨"PermissionDenied"⟩, "no"⟩ =
      ⟨⟨"PermissionDenied"⟩, "no"⟩ := rfl

theorem read_profiles_disagree_on_error_kind :
    Address.Borsh.readResult .invalidData
      ⟨.error ⟨⟨"UnexpectedEof"⟩, "short"⟩, .zero⟩ ≠
    Address.Borsh.readResult .invalidInput
      ⟨.error ⟨⟨"UnexpectedEof"⟩, "short"⟩, .zero⟩ := by decide

theorem legacy_short_input_is_preserved :
    Address.Borsh.legacyDecode [7, 8, 9] =
      (.error ⟨.invalidInput, unexpectedLengthMessage⟩, [7, 8, 9]) := by decide

theorem legacy_short_rejects_consumption :
    Address.Borsh.legacyDecode [7, 8, 9] ≠
      (.error ⟨.invalidInput, unexpectedLengthMessage⟩, []) := by decide

def partialWriter : WriterIndex where
  State := Solanalib.Runtime.Bytes
  Unwind := String
  Terminal := String
  writer := Callback.ofFunction fun before bytes =>
    .returned (.error ⟨⟨"WriteZero"⟩, "full"⟩) (before ++ bytes.take 3)

theorem serialize_partial_error_retains_written_prefix :
    Address.Borsh.serializeRun partialWriter [] (key 7 8)
      (.returned (.error ⟨⟨"WriteZero"⟩, "full"⟩) [7, 0, 0]) :=
  (Address.Borsh.serializeRun_iff _ _ _ _).mpr rfl

theorem serialize_error_rejects_rollback :
    ¬ Address.Borsh.serializeRun partialWriter [] (key 7 8)
      (.returned (.error ⟨⟨"WriteZero"⟩, "full"⟩) []) := by
  intro impossible
  have inconsistent := (Address.Borsh.serializeRun_iff partialWriter ([] : Solanalib.Runtime.Bytes)
    (key 7 8) _).mp impossible
  cases inconsistent

def unwindingWriter : WriterIndex where
  State := Solanalib.Runtime.Bytes
  Unwind := String
  Terminal := String
  writer := Callback.ofFunction fun before bytes =>
    .unwound "selected writer" (before ++ bytes.take 3)

theorem serialize_unwind_retains_written_prefix :
    Address.Borsh.serializeRun unwindingWriter [9] (key 7 8)
      (.unwound "selected writer" [9, 7, 0, 0]) :=
  (Address.Borsh.serializeRun_iff _ _ _ _).mpr rfl

theorem serialize_unwind_rejects_rollback :
    ¬ Address.Borsh.serializeRun unwindingWriter [9] (key 7 8)
      (.unwound "selected writer" [9]) := by
  intro impossible
  have inconsistent := (Address.Borsh.serializeRun_iff unwindingWriter ([9] :
    Solanalib.Runtime.Bytes) (key 7 8) _).mp impossible
  cases inconsistent

def terminatingReader : Address.Borsh.ReadIndex where
  State := Nat
  Unwind := String
  Terminal := String
  readExact := Callback.ofFunction fun _ _ => .terminated "selected reader"
  constructError := fun _ _ _ => False
  dropError := fun _ _ _ => False
  unwindReturnPlace := fun _ _ _ => False
  doubleUnwind := fun _ _ _ _ => False

theorem reader_terminal_bypasses_error_mapping :
    Address.Borsh.readRun .invalidInput terminatingReader (3 : Nat) ()
      (.terminated "selected reader") :=
  ⟨.terminated "selected reader", rfl, rfl⟩

theorem reader_terminal_cannot_become_eof_return :
    ¬ Address.Borsh.readRun .invalidInput terminatingReader (3 : Nat) ()
      (.returned (.error ⟨.invalidInput, unexpectedLengthMessage⟩) (3 : Nat)) := by
  rintro ⟨actual, called, returned⟩
  change Outcome.terminated "selected reader" = actual at called
  subst actual
  cases returned

namespace EofCleanup

/-- The trace and both live owners are observed at each actual callback state. -/
structure State where
  trace : List String := []
  originalLive : Bool := false
  replacementLive : Bool := false
  deriving DecidableEq

def original : IoError := ⟨⟨"UnexpectedEof"⟩, "payload"⟩
def replacement : IoError := ⟨.invalidInput, unexpectedLengthMessage⟩
def afterRead : State := ⟨["read"], true, false⟩
def afterConstruct : State := ⟨["read", "construct:InvalidInput"], true, true⟩
def afterDrop : State := ⟨["read", "construct:InvalidInput", "drop:payload"], false, true⟩
def afterCleanup : State :=
  ⟨["read", "construct:InvalidInput", "drop:payload", "cleanup:InvalidInput"], false, false⟩

abbrev Step := Callback.Run State IoError Unit String String

def construct : Step := Callback.ofFunction fun before error =>
  .returned () { before with
    trace := before.trace ++ ["construct:" ++ error.kind.debugName], replacementLive := true }

def drop (unwinds : Bool) : Step := Callback.ofFunction fun before error =>
  let after := { before with trace := before.trace ++ ["drop:" ++ error.message], originalLive :=
    false }
  if unwinds then .unwound "payload" after else .returned () after

def retainReturn : Step := Callback.ofFunction fun before _ => .returned () before

def cleanup (unwinds : Bool) : Step := Callback.ofFunction fun before error =>
  let after := { before with
    trace := before.trace ++ ["cleanup:" ++ error.kind.debugName], replacementLive := false }
  if unwinds then .unwound "cleanup" after else .returned () after

def reader (make destroy finish : Step) : Address.Borsh.ReadIndex where
  State := State
  Unwind := String
  Terminal := String
  readExact := Callback.ofFunction fun before buffer =>
    .returned ⟨.error original, buffer⟩
      { before with trace := before.trace ++ ["read"], originalLive := true }
  constructError := make
  dropError := destroy
  unwindReturnPlace := finish
  doubleUnwind := fun _ first second terminal => terminal = "double:" ++ first ++ ":" ++ second

-- These kernel proofs expand only the selected concrete callback graphs.
-- The generic family never assumes the callbacks are complete.
theorem construction_precedes_payload_drop :
    Address.Borsh.readRun .invalidInput (reader construct (drop false) retainReturn)
      ({} : State) () (.returned (.error replacement) afterDrop) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, drop, retainReturn, original, replacement, afterDrop,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind, Outcome.map]
  rfl

theorem eof_cannot_reuse_read_exact_state :
    ¬ Address.Borsh.readRun .invalidInput (reader construct (drop false) retainReturn)
      ({} : State) () (.returned (.error replacement) afterRead) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, drop, retainReturn, original, replacement, afterRead,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind, Outcome.map]

theorem pinned_return_place_is_retained_after_payload_unwind :
    Address.Borsh.readRun .invalidInput (reader construct (drop true) retainReturn)
      ({} : State) () (.unwound "payload" afterDrop) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, drop, retainReturn, original, afterDrop,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
    Owned.cleanup, Outcome.map]
  rfl

theorem payload_unwind_cannot_become_an_ordinary_error :
    ¬ Address.Borsh.readRun .invalidInput (reader construct (drop true) retainReturn)
      ({} : State) () (.returned (.error replacement) afterDrop) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, drop, retainReturn, original, replacement, afterDrop,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
    Owned.cleanup, Outcome.map]

theorem selected_return_place_cleanup_uses_payload_unwind_state :
    Address.Borsh.readRun .invalidInput (reader construct (drop true) (cleanup false))
      ({} : State) () (.unwound "payload" afterCleanup) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, drop, cleanup, original, afterCleanup,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
    Owned.cleanup, Outcome.map]
  exact ⟨rfl, rfl⟩

theorem second_cleanup_unwind_is_terminal :
    Address.Borsh.readRun .invalidInput (reader construct (drop true) (cleanup true))
      ({} : State) () (.terminated "double:payload:cleanup") := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, drop, cleanup, original,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
    Owned.cleanup, Outcome.map]

def constructionUnwind : Step := Callback.ofFunction fun before _ =>
  .unwound "constructor" { before with trace := before.trace ++ ["construct-unwind"] }

theorem construction_unwind_drops_only_original :
    Address.Borsh.readRun .invalidInput (reader constructionUnwind (drop false) (fun _ _ _ =>
      False))
      ({} : State) ()
      (.unwound "constructor" ⟨["read", "construct-unwind", "drop:payload"], false, false⟩) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, constructionUnwind, drop, original,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
    Owned.cleanup, Outcome.map]

theorem construction_and_original_drop_double_unwind :
    Address.Borsh.readRun .invalidInput (reader constructionUnwind (drop true) (fun _ _ _ => False))
      ({} : State) () (.terminated "double:constructor:payload") := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, constructionUnwind, drop, original,
    Callback.bind, Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind,
    Owned.cleanup, Outcome.map]

theorem constructor_terminal_stops_all_cleanup :
    Address.Borsh.readRun .invalidInput
      (reader (Callback.ofFunction fun _ _ => .terminated "constructor")
        (fun _ _ _ => False) (fun _ _ _ => False))
      ({} : State) () (.terminated "constructor") := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, original, Callback.bind, Callback.map, Callback.ofFunction,
    Owned.protect, Owned.onUnwind, Owned.cleanup, Outcome.map]

theorem original_drop_terminal_stops_return_place_cleanup :
    Address.Borsh.readRun .invalidInput
      (reader construct (Callback.ofFunction fun _ _ => .terminated "payload") (fun _ _ _ => False))
      ({} : State) () (.terminated "payload") := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, original, Callback.bind, Callback.map, Callback.ofFunction,
    Owned.protect, Owned.onUnwind, Owned.cleanup, Outcome.map]

def directReader (reply : Address.Borsh.ReadReply) : Address.Borsh.ReadIndex where
  State := State
  Unwind := String
  Terminal := String
  readExact := Callback.ofFunction fun _ _ => .returned reply afterRead
  constructError := fun _ _ _ => False
  dropError := fun _ _ _ => False
  unwindReturnPlace := fun _ _ _ => False
  doubleUnwind := fun _ _ _ _ => False

theorem success_needs_no_error_callbacks :
    Address.Borsh.readRun .invalidInput (directReader ⟨.ok (), key 7 9⟩)
      ({} : State) () (.returned (.ok (key 7 9)) afterRead) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, directReader,
    Callback.bind, Callback.ofFunction]

theorem non_eof_moves_original_error_without_cleanup :
    Address.Borsh.readRun .invalidInput (directReader ⟨.error ⟨⟨"Other"⟩, "keep"⟩, .zero⟩)
      ({} : State) () (.returned (.error ⟨⟨"Other"⟩, "keep"⟩) afterRead) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    directReader, Callback.bind, Callback.map, Callback.ofFunction, Outcome.map]

theorem missing_constructor_does_not_invent_a_return :
    ¬ Address.Borsh.readRun .invalidInput (reader (fun _ _ _ => False) (drop false) retainReturn)
      ({} : State) () (.returned (.error replacement) afterDrop) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, original, Callback.bind, Callback.map, Callback.ofFunction, Owned.protect]

theorem missing_original_destructor_does_not_invent_a_return :
    ¬ Address.Borsh.readRun .invalidInput (reader construct (fun _ _ _ => False) retainReturn)
      ({} : State) () (.returned (.error replacement) afterDrop) := by
  simp [Address.Borsh.readRun, Address.Borsh.readAfter, Address.Borsh.mapReadErrorRun,
    reader, construct, original, Callback.bind, Callback.map, Callback.ofFunction,
    Owned.protect, Owned.onUnwind]

end EofCleanup

end SolanalibTest.Specs.Core.AddressOperations
