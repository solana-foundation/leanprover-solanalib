/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface.Extensions
public import Solanalib.Specs.SplToken2022Interface.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplToken2022Interface.Extensions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.SplToken2022Interface.extension

/-- Structural equality used only by these finite mathematical controls. -/
def exceptDecEq {Failure Value : Type} [DecidableEq Failure] [DecidableEq Value] :
    DecidableEq (Except Failure Value)
  | .ok left, .ok right =>
    if same : left = right then isTrue (same ▸ rfl)
    else isFalse (fun equal => same (Except.ok.inj equal))
  | .error left, .error right =>
    if same : left = right then isTrue (same ▸ rfl)
    else isFalse (fun equal => same (Except.error.inj equal))
  | .ok _, .error _ => isFalse (by intro equal; cases equal)
  | .error _, .ok _ => isFalse (by intro equal; cases equal)

local instance {Failure Value : Type} [DecidableEq Failure] [DecidableEq Value] :
    DecidableEq (Except Failure Value) := exceptDecEq

/-- A complete initialized base Mint; no tested extension behavior is assumed. -/
def mintBase : Bytes := StateWithExtensions.initializedMintSample

/-- Extend a Mint with the 83 zero padding bytes and mint marker of the source. -/
def mintWith (tlv : Bytes) : Bytes := mintBase ++ List.replicate 83 0 ++ [1] ++ tlv

/-- A complete frozen token-account base. -/
def frozenAccountBase : Bytes := List.replicate 108 0 ++ [2] ++ List.replicate 56 0

/-- The expected copied Mint value for the independent base bytes. -/
def emptyMintValue : Mint := ⟨none, 0, 0, true, none⟩

/-- One well-formed TLV entry; malformed controls supply their bytes directly. -/
def entry (tag : Nat) (value : Bytes) : Bytes :=
  Solanalib.Runtime.u16le tag ++ Solanalib.Runtime.u16le value.length ++ value

/-- A valid bare Mint has a successful typed, empty-tail result. -/
theorem unpack_bare_mint_success :
    unpackMintWithExtensions mintBase = .ok ⟨emptyMintValue, []⟩ := by decide +kernel

/-- A frozen Account is initialized and admits the extension wrapper. -/
theorem unpack_frozen_account_success :
    (unpackAccountWithExtensions frozenAccountBase).map (fun value => value.base.state) =
      .ok .frozen := by decide +kernel

/-- Short input and a partial mint-padding area are rejected. -/
theorem unpack_short_lengths :
    unpackMintWithExtensions [] = .error .InvalidAccountData ∧
    unpackMintWithExtensions (mintBase ++ [0]) = .error .InvalidAccountData ∧
    unpackMintWithExtensions (mintBase ++ List.replicate 83 0) =
      .error .InvalidAccountData := by decide +kernel

/-- Correct extended layout can hold an empty TLV slice. -/
theorem unpack_empty_extended_mint :
    unpackMintWithExtensions (mintWith []) = .ok ⟨emptyMintValue, []⟩ := by decide +kernel

/-- Nonzero padding, wrong base association and an unknown marker fail. -/
theorem unpack_padding_and_marker :
    unpackMintWithExtensions (mintBase ++ [1] ++ List.replicate 82 0 ++ [1]) =
      .error .InvalidAccountData ∧
    unpackMintWithExtensions (mintBase ++ List.replicate 83 0 ++ [2]) =
      .error .InvalidAccountData ∧
    unpackMintWithExtensions (mintBase ++ List.replicate 83 0 ++ [3]) =
      .error .InvalidAccountData := by decide +kernel

/-- The 355-byte multisig length is rejected even with a valid mint prefix,
padding and marker. -/
theorem unpack_multisig_collision_rejected :
    unpackMintWithExtensions (mintWith (List.replicate 189 0)) =
      .error .InvalidAccountData := by decide +kernel

/-- Base initialization failure precedes a malformed extension layout. -/
theorem unpack_base_error_precedes_layout :
    unpackMintWithExtensions ((mintBase.set 45 0) ++ [9]) =
      .error .UninitializedAccount := by decide +kernel

/-- Base field checks precede the Pack initialization check. -/
theorem unpack_base_representation_error_precedes_initialization :
    unpackMintWithExtensions ((mintBase.set 0 9).set 45 0) =
      .error .InvalidAccountData := by decide +kernel

/-- The wrapper deliberately defers TLV validation; the same tail subsequently
fails when a caller lists its types. -/
theorem unpack_defers_tlv_validation :
    unpackMintWithExtensions (mintWith [1, 0, 0]) = .ok ⟨emptyMintValue, [1, 0, 0]⟩ ∧
    getExtensionTypes [1, 0, 0] = .error .InvalidAccountData := by decide +kernel

/-- PodMint admits noncanonical COption and nonzero Boolean encodings which
the packed Mint parser rejects; sizing uses the former. -/
theorem pod_mint_acceptance_differs_from_pack :
    unpackMintWithExtensions ((mintBase.set 0 9).set 45 2) =
      .error .InvalidAccountData ∧
    calculateAccountLengthFromMint ((mintBase.set 0 9).set 45 2) [] = .ok 165 := by
  decide +kernel

/-- Type iteration accepts either an empty tail or a single arbitrary realloc byte. -/
theorem type_list_short_tail :
    getExtensionTypes [] = .ok [] ∧
    getExtensionTypes [255] = .ok [] ∧
    getExtensionTypes [255, 255] = .error .InvalidAccountData := by decide +kernel

/-- Two zero bytes terminate type listing before any following malformed bytes. -/
theorem type_list_sentinel_ignores_tail :
    getExtensionTypes [0, 0, 255, 255, 1] = .ok [] := by decide +kernel

/-- Lookup demands the complete header before recognizing a zero sentinel. -/
theorem lookup_sentinel_requires_header :
    findExtension 1 0 [0, 0] = .error .InvalidAccountData ∧
    findExtension 1 0 [0, 0, 0, 0] = .error (.Custom 48) := by decide +kernel

/-- Known tags still require their length and complete declared value range. -/
theorem type_list_checks_length_and_value :
    getExtensionTypes [1, 0] = .error .InvalidAccountData ∧
    getExtensionTypes [1, 0, 0] = .error .InvalidAccountData ∧
    getExtensionTypes [1, 0, 2, 0, 9] = .error .InvalidAccountData := by decide +kernel

/-- Lookup skips an unknown tag while full type iteration rejects it. -/
theorem unknown_tags_have_distinct_lookup_and_iteration_behavior :
    findExtension 8 0 [231, 3, 0, 0, 8, 0, 1, 0, 9] = .ok ⟨8, [9]⟩ ∧
    getExtensionTypes [231, 3, 0, 0, 8, 0, 1, 0, 9] =
      .error .InvalidAccountData := by decide +kernel

/-- the test-only high discriminants of Rust are not admitted in production. -/
theorem test_only_extension_tags_rejected :
    getExtensionTypes [253, 255, 0, 0] = .error .InvalidAccountData ∧
    getExtensionTypes [254, 255, 0, 0] = .error .InvalidAccountData ∧
    getExtensionTypes [255, 255, 0, 0] = .error .InvalidAccountData := by decide +kernel

/-- Type iteration keeps duplicates and their original order. -/
theorem types_preserve_order_and_duplicates :
    getExtensionTypes (entry 8 [9] ++ entry 7 [] ++ entry 8 [10]) =
      .ok [.memoTransfer, .immutableOwner, .memoTransfer] := by decide +kernel

/-- Lookup returns the first duplicate, and a malformed tail after that match
does not invalidate the selected extension. -/
theorem lookup_first_duplicate_and_early_return :
    findExtension 8 0 (entry 8 [9] ++ entry 8 [10]) = .ok ⟨4, [9]⟩ ∧
    findExtension 8 0 (entry 8 [9] ++ [255, 255]) = .ok ⟨4, [9]⟩ := by decide +kernel

/-- Neither lookup nor type iteration repairs an out-of-range declared value. -/
theorem lookup_declared_value_bounds :
    findExtension 8 0 [8, 0, 2, 0, 9] = .error .InvalidAccountData ∧
    findExtension 8 0 [231, 3, 255, 255] = .error .InvalidAccountData := by decide +kernel

/-- Type listing does not enforce official payload sizes, but Pod lookup does. -/
theorem pod_size_distinct_from_tlv_bounds :
    getExtensionTypes (entry 1 [9]) = .ok [.transferFeeConfig] ∧
    getTransferFeeConfig 4096 (entry 1 [9]) = .error .InvalidArgument := by decide +kernel

/-- The base-type check precedes missing-extension or layout errors. -/
theorem pod_base_mismatch_first :
    getExtension .account transferFeeConfigPod 4096 [] = .error .InvalidAccountData ∧
    getExtension .mint transferFeeConfigPod 4096 [0, 0, 0, 0] = .error (.Custom 48) := by
  decide +kernel

/-- Generic Pod alignment uses the returned value address, including its
four-byte header offset; it is independent from payload size. -/
theorem pod_alignment_uses_value_offset :
    getExtension .account ⟨.memoTransfer, 1, 8⟩ 4 (entry 8 [9]) = .ok ⟨4, [9]⟩ ∧
    getExtension .account ⟨.memoTransfer, 1, 8⟩ 1 (entry 8 [9]) =
      .error .InvalidArgument := by decide +kernel

/-- A zero-size extension is still a real matching TLV entry. -/
theorem zero_size_extension_lookup :
    getExtension .account ⟨.immutableOwner, 0, 1⟩ 4096 (entry 7 []) = .ok ⟨4, []⟩ := by
  decide +kernel

/-- Unextended mints need the ordinary token-account base size. -/
theorem account_size_no_extensions : calculateAccountLengthFromMint mintBase [] = .ok 165 := by
  decide +kernel

/-- Required and additional extensions share one deduplication set. -/
theorem account_size_deduplicates_required_and_additional :
    calculateAccountLengthFromMint (mintWith (entry 9 []))
      [.immutableOwner, .nonTransferableAccount, .immutableOwner] = .ok 174 ∧
    calculateAccountLengthFromMint (mintWith (entry 9 [] ++ entry 9 [])) [] = .ok 174 := by
  decide +kernel

/-- Sizing is driven by bounded TLV types rather than semantic payload size. -/
theorem account_size_uses_tags_only :
    calculateAccountLengthFromMint (mintWith (entry 1 [])) [] = .ok 178 ∧
    calculateAccountLengthFromMint (mintWith (entry 1 [1, 2, 3, 4, 5])) [] = .ok 178 := by
  decide +kernel

/-- Account tags accidentally stored in mint TLV add no requirements, and
variable-length metadata is accepted when merely walking the tags of the mint. -/
theorem account_size_ignores_unrequired_tags :
    calculateAccountLengthFromMint (mintWith (entry 7 [])) [] = .ok 165 ∧
    calculateAccountLengthFromMint (mintWith (entry 19 [])) [] = .ok 165 := by decide +kernel

/-- The four mint features induce the exact ordered account extension sizes. -/
theorem account_size_all_required_features :
    calculateAccountLengthFromMint
      (mintWith (entry 1 [] ++ entry 9 [] ++ entry 14 [] ++ entry 26 [])) [] = .ok 195 := by
  decide +kernel

/-- Arbitrary account additions include confidential account payload sizes. -/
theorem account_size_all_account_types :
    calculateAccountLengthFromMint mintBase
      [.transferFeeAmount, .confidentialTransferAccount, .immutableOwner, .memoTransfer,
        .cpiGuard, .nonTransferableAccount, .transferHookAccount,
        .confidentialTransferFeeAmount, .pausableAccount] = .ok 572 := by decide +kernel

/-- Invalid additional types are rejected before parsing an invalid mint. -/
theorem account_size_additional_type_error_first :
    calculateAccountLengthFromMint [] [.transferFeeConfig] = .error (.Custom 20) ∧
    calculateAccountLengthFromMint [] [.uninitialized] = .error (.Custom 20) ∧
    calculateAccountLengthFromMint [] [] = .error (.Custom 2) := by decide +kernel

/-- Base/layout errors map to InvalidMint; a later TLV error keeps its own code. -/
theorem account_size_mint_and_tlv_error_distinction :
    calculateAccountLengthFromMint (mintBase.set 45 0) [] = .error (.Custom 2) ∧
    calculateAccountLengthFromMint (mintBase ++ [0]) [] = .error (.Custom 2) ∧
    calculateAccountLengthFromMint (mintWith [1, 0, 0]) [] = .error .InvalidAccountData ∧
    calculateAccountLengthFromMint (mintWith [231, 3, 0, 0]) [] = .error .InvalidAccountData := by
  decide +kernel

/-- Sizing preserves both end-marker exceptions of TLV iteration. -/
theorem account_size_trailing_byte_and_sentinel :
    calculateAccountLengthFromMint (mintWith (entry 1 [] ++ [255])) [] = .ok 178 ∧
    calculateAccountLengthFromMint (mintWith (entry 1 [] ++ [0, 0, 255, 255, 1])) [] = .ok 178 := by
  decide +kernel

/-- The generic fixed-size helper omits the association check that the
mint-data sizing entrypoint performs, and retains multisig adjustment. -/
theorem generic_size_multisig_adjustment :
    calculateExtensionAccountLength 165
      [.transferFeeConfig, .metadataPointer, .cpiGuard, .immutableOwner] = .ok 357 ∧
    calculateExtensionAccountLength 165 [.tokenMetadata] = .error .InvalidArgument ∧
    calculateExtensionAccountLength 165 [.uninitialized] = .ok 170 := by decide +kernel

/-- Independently assembled fee configuration bytes with distinguishable fields. -/
def feeConfigBytes : Bytes :=
  List.replicate 32 3 ++ List.replicate 32 4 ++ Solanalib.Runtime.u64le 777 ++
  Solanalib.Runtime.u64le 200 ++ Solanalib.Runtime.u64le 9 ++ Solanalib.Runtime.u16le 100 ++
  Solanalib.Runtime.u64le 100 ++ Solanalib.Runtime.u64le 3 ++ Solanalib.Runtime.u16le 200

/-- Typed extension retrieval connects selected bytes to the actual fee fields. -/
theorem typed_fee_config_field_offsets :
    (getTransferFeeConfig 4096 (entry 1 feeConfigBytes)).map (fun reference =>
      (reference.view.offset, reference.value.withheldAmount,
        reference.value.older, reference.value.newer)) =
      .ok (4, 777, ⟨200, 9, 100⟩, ⟨100, 3, 200⟩) := by decide +kernel

/-- Retrieved fee data drives the shared epoch and arithmetic models. -/
theorem typed_fee_config_epoch_to_amount :
    (getTransferFeeConfig 4096 (entry 1 feeConfigBytes)).map (fun reference =>
      ((reference.value.getEpochFee 99).calculatePostFeeAmount 1000,
        (reference.value.getEpochFee 100).calculatePostFeeAmount 1000)) =
      .ok (some 991, some 997) := by decide +kernel

/-- Pod decoding preserves excessive rates for the arithmetic methods to
handle; it does not silently validate or clamp a configuration. -/
theorem typed_fee_preserves_full_rate :
    decodeTransferFee (Solanalib.Runtime.u64le 7 ++ Solanalib.Runtime.u64le 8 ++ [255, 255]) =
      .ok ⟨7, 8, 65535⟩ ∧
    decodeTransferFee [0] = .error .InvalidArgument := by decide +kernel

/-- The registered sample of the get_extension family is a successful typed call. -/
theorem family_extension_sample_success :
    (getTransferFeeConfig BaseStateWithExtensions.feeExtensionSample.address
      BaseStateWithExtensions.feeExtensionSample.bytes).map (fun value => value.value) =
      .ok ⟨.zero, .zero, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩ := by decide +kernel

/-- A stateful base parser that records exactly the prefix it inspected before
returning an ordinary error. This is a generic callback control, not a Rust body. -/
def recordingErrorParser : ExtensionBaseParser where
  State := List Bytes
  Value := Unit
  Unwind := Nat
  Terminal := Nat
  byteLength := 82
  accountType := .mint
  parse := fun before bytes outcome =>
    outcome = .returned (.error (.Custom 77)) (before ++ [bytes])

/-- A malformed tail cannot overwrite the error or actual state of the base parser. -/
theorem generic_parser_error_retains_prefix_and_state :
    unpackExtensionState recordingErrorParser [] (mintBase ++ [9])
      (.returned (.error (.Custom 77)) [mintBase]) := by
  apply unpackExtensionState_base_error
  · decide +kernel
  · rfl

/-- A concrete provider shell for effectful resolved-method controls. -/
def getterWith (run : ExtensionPod → Nat → Outcome Nat (Except Error Nat) Nat Nat → Prop) :
    ExtensionByteProvider where
  State := Nat
  Reference := Nat
  Unwind := Nat
  Terminal := Nat
  bytes := fun state _ => List.replicate state 0
  address := fun reference => 4096 + reference
  getBytes := run

/-- A resolved getter override whose returned reference observes changed state. -/
def changingGetter : ExtensionByteProvider :=
  getterWith (fun _ before outcome => outcome = .returned (.ok 3) (before + 1))

/-- The cast uses the returned state, not a snapshot from before the override. -/
theorem getter_cast_reads_actual_state :
    castExtensionReference changingGetter transferFeeConfigRepresentation (107 : Nat) (3 : Nat) =
      .error .InvalidArgument ∧
    castExtensionReference changingGetter transferFeeConfigRepresentation (108 : Nat) (3 : Nat) =
      .ok ⟨(3 : Nat), observeTransferFeeConfig (List.replicate 108 0)⟩ := by
  simp [castExtensionReference, changingGetter, getterWith, transferFeeConfigRepresentation,
    transferFeeConfigPod]

/-- An override may return bytes from another reference and change the state;
the generic getter preserves both and still performs the required cast. -/
theorem getter_override_success_preserves_reference_and_state :
    getExtensionOperational changingGetter transferFeeConfigRepresentation (107 : Nat)
      (.returned (.ok ⟨(3 : Nat), observeTransferFeeConfig (List.replicate 108 0)⟩) (108 : Nat)) :=
        by
  have run := getExtensionOperational_returned changingGetter transferFeeConfigRepresentation
    (107 : Nat) (108 : Nat) (3 : Nat) rfl
  rw [getter_cast_reads_actual_state.2] at run
  exact run

/-- The error path of a resolved override also changes state in this control. -/
def errorGetter : ExtensionByteProvider :=
  getterWith (fun _ before outcome => outcome = .returned (.error (.Custom 77)) (before + 5))

/-- Generic retrieval cannot replace the actual error from an override with a default
TLV or account-kind error, nor discard its state change. -/
theorem getter_override_error_preserves_state :
    getExtensionOperational errorGetter transferFeeConfigRepresentation (10 : Nat)
      (.returned (.error (.Custom 77)) (15 : Nat)) :=
  getExtensionOperational_error errorGetter transferFeeConfigRepresentation
    (10 : Nat) (15 : Nat) (.Custom 77) rfl

/-- An override with an actual unwind outcome. -/
def unwindGetter : ExtensionByteProvider :=
  getterWith (fun _ before outcome => outcome = .unwound 7 (before + 5))

/-- The operational getter preserves the unwind and changed state of an override. -/
theorem getter_override_unwind_preserves_state :
    getExtensionOperational unwindGetter transferFeeConfigRepresentation (10 : Nat)
      (.unwound (7 : Nat) (15 : Nat)) :=
  getExtensionOperational_unwound unwindGetter transferFeeConfigRepresentation
    (10 : Nat) (15 : Nat) (7 : Nat) rfl

/-- An override which terminates instead of returning a byte slice. -/
def terminalGetter : ExtensionByteProvider :=
  getterWith (fun _ _ outcome => outcome = .terminated 9)

/-- Terminal getter exits remain terminal with no invented post-state. -/
theorem getter_override_terminal_exit :
    getExtensionOperational terminalGetter transferFeeConfigRepresentation (10 : Nat)
      (.terminated (9 : Nat)) :=
  getExtensionOperational_terminated terminalGetter transferFeeConfigRepresentation
    (10 : Nat) (9 : Nat) rfl

/-- An override with no finite exit. -/
def noExitGetter : ExtensionByteProvider :=
  getterWith (fun _ _ _ => False)

/-- A generic retrieval contract cannot invent an exit for a diverging override. -/
theorem getter_override_no_invented_exit
    (outcome : Outcome Nat
      (Except Error (TypedExtensionReference Nat TransferFeeConfig)) Nat Nat) :
    ¬ getExtensionOperational noExitGetter transferFeeConfigRepresentation (10 : Nat) outcome :=
  getExtensionOperational_no_invented_exit noExitGetter transferFeeConfigRepresentation
    (10 : Nat) (fun _ impossible => impossible) outcome

/-- A callback which unwinds after recording the number of bytes inspected. -/
def unwindingParser : ExtensionBaseParser where
  State := Nat
  Value := Unit
  Unwind := Nat
  Terminal := Nat
  byteLength := 82
  accountType := .mint
  parse := fun before bytes outcome => outcome = .unwound 7 (before + bytes.length)

/-- Unwinding propagates the changed state of the callback through the generic API. -/
theorem generic_parser_unwind_retains_state :
    unpackExtensionState unwindingParser (10 : Nat) mintBase
      (.unwound (7 : Nat) (92 : Nat)) := by
  have admitted : ¬ extensionInputRejected 82 mintBase := by decide +kernel
  have prefixLength : (List.take 82 mintBase).length = 82 := by decide +kernel
  refine unpackExtensionState_unwound unwindingParser (10 : Nat) (92 : Nat)
    mintBase (7 : Nat) admitted ?_
  change Outcome.unwound (7 : Nat) (92 : Nat) =
    Outcome.unwound (7 : Nat) (10 + (List.take 82 mintBase).length)
  rw [prefixLength]

/-- A parser with no finite exit models divergence at the explicit callback. -/
def nonreturningParser : ExtensionBaseParser where
  State := Unit
  Value := Unit
  Unwind := Empty
  Terminal := Empty
  byteLength := 82
  accountType := .mint
  parse := fun _ _ _ => False

/-- Generic unpack never fabricates a finite exit after a nonreturning parser. -/
theorem generic_parser_no_invented_exit
    (outcome : Outcome Unit (Except Error (Solanalib.Specs.Core.Token.StateWithExtensions Unit))
      Empty Empty) :
    ¬ unpackExtensionState nonreturningParser () mintBase outcome := by
  simp [unpackExtensionState, nonreturningParser, extensionInputRejected,
    mintBase, StateWithExtensions.initializedMintSample, multisigLength]

/-- A rejected input returns before calling even a nonreturning parser. -/
theorem length_failure_does_not_call_parser :
    unpackExtensionState nonreturningParser () [] (.returned (.error .InvalidAccountData) ()) := by
  apply (unpackExtensionState_rejected _ _ _ _ (by decide)).mpr
  rfl

/-- Every interpretation satisfying the typed retrieval contract must retain
the selected bytes and pass the same exact size/alignment checks. -/
theorem successful_generic_contract_retains_layout
    (run : FamilyRun BaseStateWithExtensions.get_extension_contract)
    (satisfies : FamilyReference BaseStateWithExtensions.get_extension_contract run)
    (representation : ExtensionRepresentation) (before after : ExtensionSlice)
    (value : ExtensionReference representation.Value)
    (execution : run representation before () (.returned (.ok value) after)) :
    after = before ∧ value.view.bytes.length = representation.pod.byteLength ∧
      (before.address + value.view.offset) % representation.pod.alignment = 0 := by
  have post := satisfies representation before () (.returned (.ok value) after) trivial execution
  change .ok value = getRepresentedExtension representation before.accountType before.address
    before.bytes ∧ after = before at post
  have raw := getRepresentedExtension_raw representation before.accountType before.address
    before.bytes
  rw [← post.1] at raw
  have selected : getExtension before.accountType representation.pod before.address before.bytes =
      .ok value.view := raw.symm
  have layout := (getExtension_ok_iff before.accountType representation.pod before.address
    before.bytes value.view).mp selected
  exact ⟨post.2, layout.2.2⟩

/-- A concrete ledger for operational allocation controls. -/
abbrev ListState := Owned.VectorState ExtensionType

/-- Concrete primitive vector operations with explicit possible reason types. -/
def listOps : Owned.VectorOps ListState ExtensionType Nat Nat Nat := Owned.vectorReference

/-- The ordinary vector control satisfies every primitive dependency law. -/
theorem listOps_laws : listOps.Laws := Owned.vectorReference_laws

/-- No double unwind can arise from the ordinary vector reference. -/
def noListDouble : Owned.DoubleUnwind ListState Nat Nat := fun _ _ _ _ => False

/-- One initialized zero-size extension supplies a complete first push site. -/
def firstListEntry : Bytes := [7, 0, 0, 0]

/-- Constant bytes for an operational slice with fixed metadata. -/
def listByteAt (bytes : Bytes) (_state : ListState) (index : Fin bytes.length) : UInt8 :=
  bytes[index.val]

/-- The versioned operational sample genuinely creates a nonempty live result. -/
theorem list_operational_sample_success :
    getExtensionTypesCurrent BaseStateWithExtensions.get_extension_types_operational_sample []
      (.returned (.ok (0 : Nat)) [some extensionListSampleValues]) ∧
    Owned.VectorState.current [some extensionListSampleValues] 0 =
      some [.immutableOwner, .memoTransfer] :=
  ⟨extensionListSample_executes, extensionListSample_current⟩

/-- A valid first entry followed by an unknown second tag. -/
def malformedListTail : Bytes := [7, 0, 0, 0, 29, 0]

/-- A later malformed tag retains the first push, then drops that actual
accumulated vector before returning the ordinary parse error. -/
theorem list_late_error_cleans_accumulated_vector :
    collectCurrentExtensionTypes listOps noListDouble 0 malformedListTail.length
      (listByteAt malformedListTail) 0 [some []]
      (.returned (.error .InvalidAccountData) [none]) := by
  apply collectCurrentExtensionTypes_push (kind := .immutableOwner) (consumed := 4)
    (tail := [29, 0]) (middle := [some [.immutableOwner]])
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · apply collectCurrentExtensionTypes_error
    · decide +kernel
    · exact ⟨.returned () [none], ⟨[.immutableOwner], rfl, rfl⟩, rfl⟩

/-- The current-state scanner cannot admit any successful result for that
malformed tail under the actual vector reference and a constant source slice. -/
theorem list_late_error_has_no_success (resource : Nat) (after : ListState) :
    ¬ collectCurrentExtensionTypes listOps noListDouble 0 malformedListTail.length
      (listByteAt malformedListTail) 0 [some []] (.returned (.ok resource) after) := by
  intro run
  have frame : ExtensionReadFrame listOps malformedListTail.length
      (listByteAt malformedListTail) := fun _ _ _ _ _ _ => rfl
  obtain ⟨values, used, _, _, fold⟩ := collectCurrentExtensionTypes_success
    listOps listOps_laws.push_current noListDouble 0 resource malformedListTail.length
    (listByteAt malformedListTail) frame 0 [some []] after [] rfl run
  have invalid : foldExtensionTypes (fun prior kind => .ok (prior ++ [kind])) [] 0
      ((currentExtensionBytes malformedListTail.length (listByteAt malformedListTail)
        [some []]).drop 0) = .error .InvalidAccountData := by decide +kernel
  rw [invalid] at fold
  cases fold

/-- A lawful provider which partially changes its vector before unwinding.
Its destructor accepts only the changed nonempty current vector; an old empty
snapshot cannot be substituted for the actual cleanup state. -/
def partialListOps : Owned.VectorOps ListState ExtensionType Nat Nat Nat :=
  { listOps with
    push := fun before (resource, kind) outcome =>
      ∃ values, before.current resource = some values ∧
        outcome = .unwound 7 (before.set resource (some (values ++ [kind])))
    drop := fun before resource outcome =>
      ∃ values, before.current resource = some values ∧ values ≠ [] ∧
        outcome = .returned () (before.set resource none) }

/-- Partial unwind effects and a conditional destructor satisfy the primitive
laws without assuming termination or preserving a stale contents snapshot. -/
theorem partialListOps_laws : partialListOps.Laws := by
  constructor
  · exact listOps_laws.empty_current
  · exact listOps_laws.empty_fresh
  · exact listOps_laws.capacity_current
  · exact listOps_laws.capacity_fresh
  · exact listOps_laws.list_current
  · exact listOps_laws.list_fresh
  · intro before resource kind values after current run
    obtain ⟨_, _, impossible⟩ := run
    cases impossible
  · intro before resource kind reason after live run
    obtain ⟨values, current, same⟩ := run
    cases same
    exact ⟨values ++ [kind], Owned.VectorState.current_set before resource
      (some (values ++ [kind])) (Owned.VectorState.current_bound current)⟩
  · exact listOps_laws.extend_current
  · exact listOps_laws.extend_unwind_live
  · intro before resource after live run
    obtain ⟨values, current, _, same⟩ := run
    cases same
    exact Owned.VectorState.current_set before resource none
      (Owned.VectorState.current_bound current)
  · intro before resource reason after live run
    obtain ⟨_, _, _, impossible⟩ := run
    cases impossible

/-- Cleanup succeeds on the actual partially modified vector of the provider. -/
theorem list_push_unwind_cleans_actual_state :
    collectCurrentExtensionTypes partialListOps noListDouble 0 firstListEntry.length
      (listByteAt firstListEntry) 0 [some []] (.unwound 7 [none]) := by
  apply collectCurrentExtensionTypes_push_unwind (kind := .immutableOwner) (consumed := 4)
    (tail := []) (middle := [some [.immutableOwner]]) (reason := 7)
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · exact ⟨.returned () [none], ⟨[.immutableOwner], rfl, by decide, rfl⟩, rfl⟩

/-- The same destructor has no finite exit on the discarded old snapshot. -/
theorem list_old_snapshot_cannot_clean
    (outcome : Outcome ListState Unit Nat Nat) : ¬ partialListOps.drop [some []] 0 outcome := by
  rintro ⟨values, current, nonempty, _⟩
  have empty : values = [] := Option.some.inj current.symm
  exact nonempty empty

/-- A destructor which retires its actual owner before a second unwind. -/
def doubleListOps : Owned.VectorOps ListState ExtensionType Nat Nat Nat :=
  { partialListOps with drop := fun before resource outcome =>
      ∃ values, before.current resource = some values ∧
        outcome = .unwound 11 (before.set resource none) }

/-- The double-unwind control also meets the primitive
dependency laws of the operational contract; an unwinding destructor consumes its actual resource.
-/
theorem doubleListOps_laws : doubleListOps.Laws := by
  constructor
  · exact partialListOps_laws.empty_current
  · exact partialListOps_laws.empty_fresh
  · exact partialListOps_laws.capacity_current
  · exact partialListOps_laws.capacity_fresh
  · exact partialListOps_laws.list_current
  · exact partialListOps_laws.list_fresh
  · exact partialListOps_laws.push_current
  · exact partialListOps_laws.push_unwind_live
  · exact partialListOps_laws.extend_current
  · exact partialListOps_laws.extend_unwind_live
  · intro before resource after live run
    obtain ⟨_, _, impossible⟩ := run
    cases impossible
  · intro before resource reason after live run
    obtain ⟨values, current, same⟩ := run
    cases same
    exact Owned.VectorState.current_set before resource none
      (Owned.VectorState.current_bound current)

/-- The second unwind must carry both actual reasons and the retired state. -/
def exactListDouble : Owned.DoubleUnwind ListState Nat Nat :=
  fun state first second terminal =>
    state = [none] ∧ first = 7 ∧ second = 11 ∧ terminal = 42

/-- A second cleanup unwind uses the explicit terminal policy. -/
theorem list_double_unwind_uses_actual_state :
    collectCurrentExtensionTypes doubleListOps exactListDouble 0 firstListEntry.length
      (listByteAt firstListEntry) 0 [some []] (.terminated 42) := by
  apply collectCurrentExtensionTypes_push_unwind (kind := .immutableOwner) (consumed := 4)
    (tail := []) (middle := [some [.immutableOwner]]) (reason := 7)
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · exact ⟨.unwound 11 [none], ⟨[.immutableOwner], rfl, rfl⟩,
      42, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- A terminal allocation provider with no permitted destructor exit. -/
def terminalListOps : Owned.VectorOps ListState ExtensionType Nat Nat Nat :=
  { listOps with
    push := fun _ _ outcome => outcome = .terminated 41
    drop := fun _ _ _ => False }

/-- A terminal-only provider satisfies the primitive laws without acquiring
an invented return, unwind or destructor execution. -/
theorem terminalListOps_laws : terminalListOps.Laws := by
  constructor
  · exact listOps_laws.empty_current
  · exact listOps_laws.empty_fresh
  · exact listOps_laws.capacity_current
  · exact listOps_laws.capacity_fresh
  · exact listOps_laws.list_current
  · exact listOps_laws.list_fresh
  · intro before resource kind values after current run
    cases run
  · intro before resource kind reason after live run
    cases run
  · exact listOps_laws.extend_current
  · exact listOps_laws.extend_unwind_live
  · intro before resource after live run
    exact False.elim run
  · intro before resource reason after live run
    exact False.elim run

/-- A terminal push does not require or invent any cleanup execution. -/
theorem list_terminal_push_skips_cleanup :
    collectCurrentExtensionTypes terminalListOps noListDouble 0 firstListEntry.length
      (listByteAt firstListEntry) 0 [some []] (.terminated 41) := by
  apply collectCurrentExtensionTypes_push_terminal (kind := .immutableOwner) (consumed := 4)
    (tail := [])
  · decide +kernel
  · rfl

/-- A fixed-length source view whose second tag changes after the first push.
This tests generic provider effects without assuming a Rust borrow frame law. -/
def changingListByteAt (state : ListState) (index : Fin extensionListSample.length) : UInt8 :=
  if index.val = 4 ∧ state.current 0 = some [.immutableOwner] then 29
  else extensionListSample[index.val]

/-- The second iteration reads the actual returned state and catches the newly
invalid tag; taking a frozen snapshot would incorrectly admit success here. -/
theorem list_reads_current_state_after_push :
    collectCurrentExtensionTypes listOps noListDouble 0 extensionListSample.length
      changingListByteAt
      0 [some []] (.returned (.error .InvalidAccountData) [none]) := by
  apply collectCurrentExtensionTypes_push (kind := .immutableOwner) (consumed := 4)
    (tail := [8, 0, 1, 0, 1]) (middle := [some [.immutableOwner]])
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · apply collectCurrentExtensionTypes_error
    · decide +kernel
    · exact ⟨.returned () [none], ⟨[.immutableOwner], rfl, rfl⟩, rfl⟩

/-- The changing source view fails the explicit condition needed to use the
pure list observation; primitive vector laws alone cannot establish it. -/
theorem changing_list_view_is_not_framed :
    ¬ ExtensionReadFrame listOps extensionListSample.length changingListByteAt := by
  intro frame
  have wrong := frame [some []] 0 .immutableOwner [some [.immutableOwner]]
    ⟨[], rfl, rfl⟩ ⟨4, by decide⟩
  have impossible : (29 : UInt8) = 8 := wrong
  cases impossible

/-- A fixed-type operational unpacker used to expose parser and destructor
effects without imposing Copy on the generic owned base. -/
abbrev unpackerWith
    (read : (state : Nat) → (bytes : Bytes) → Fin bytes.length → UInt8)
    (parse : Nat → ExtensionRegion Bytes → Outcome Nat (Except Error Nat) Nat Nat → Prop)
    (drop : Nat → Nat → Outcome Nat Unit Nat Nat → Prop) : ExtensionUnpacker where
  State := Nat
  Reference := Bytes
  Base := Nat
  Unwind := Nat
  Terminal := Nat
  length := List.length
  byteAt := read
  baseLength := 165
  accountType := .account
  parse := parse
  dropBase := drop

/-- A source-byte interpretation unchanged by the state effects of the control. -/
def unpackByteAt (_state : Nat) (bytes : Bytes) (index : Fin bytes.length) : UInt8 :=
  bytes[index.val]

/-- A parser checks its supplied prefix region, returns owned value 37, and
changes the actual state before the enclosing function checks the layout. -/
def ownedBaseParser (before : Nat) (region : ExtensionRegion Bytes)
    (outcome : Outcome Nat (Except Error Nat) Nat Nat) : Prop :=
  region.offset = 0 ∧ region.length = 165 ∧ outcome = .returned (.ok 37) (before + 1)

/-- A malformed marker after a full generic base. -/
def unpackBadInput : Bytes := List.replicate 165 0 ++ [9]

/-- A valid account marker with an unparsed, nonempty immutable-owner TLV. -/
def unpackGoodInput : Bytes := List.replicate 165 0 ++ [2, 7, 0, 0, 0]

/-- The constant shared view reconstructs exactly the original byte list. -/
theorem unpack_static_layout
    (parse : Nat → ExtensionRegion Bytes → Outcome Nat (Except Error Nat) Nat Nat → Prop)
    (drop : Nat → Nat → Outcome Nat Unit Nat Nat → Prop) (state : Nat) (bytes : Bytes) :
    unpackExtensionTailReference (unpackerWith unpackByteAt parse drop) state bytes =
      (unpackExtensionTail 165 .account (bytes.drop 165)).map (fun tlv =>
        if (bytes.drop 165).isEmpty then .empty
        else .borrowed ⟨bytes, 166, tlv.length⟩) := by
  have original : (unpackerWith unpackByteAt parse drop).inputBytes state bytes = bytes := by
    change (List.ofFn fun index : Fin bytes.length => bytes[index.val]) = bytes
    exact List.ofFn_getElem
  simp only [unpackExtensionTailReference, original]
  rfl

/-- A fixed complete prefix is removed structurally before evaluating the
short layout control, without reducing the large replicated byte list. -/
theorem unpack_prefixed_layout
    (parse : Nat → ExtensionRegion Bytes → Outcome Nat (Except Error Nat) Nat Nat → Prop)
    (drop : Nat → Nat → Outcome Nat Unit Nat Nat → Prop) (state : Nat) (tail : Bytes) :
    unpackExtensionTailReference (unpackerWith unpackByteAt parse drop) state
      (List.replicate 165 0 ++ tail) =
      (unpackExtensionTail 165 .account tail).map (fun tlv =>
        if tail.isEmpty then .empty
        else .borrowed ⟨List.replicate 165 0 ++ tail, 166, tlv.length⟩) := by
  rw [unpack_static_layout]
  have suffix : (List.replicate 165 (0 : UInt8) ++ tail).drop 165 = tail :=
    List.drop_left' List.length_replicate
  simp only [suffix]

/-- The bad-marker control fails layout for every parser/destructor relation. -/
theorem unpack_bad_layout
    (parse : Nat → ExtensionRegion Bytes → Outcome Nat (Except Error Nat) Nat Nat → Prop)
    (drop : Nat → Nat → Outcome Nat Unit Nat Nat → Prop) (state : Nat) :
    unpackExtensionTailReference (unpackerWith unpackByteAt parse drop) state unpackBadInput =
      .error .InvalidAccountData := by
  rw [unpackBadInput, unpack_prefixed_layout]
  rfl

/-- The good-marker control preserves its four-byte TLV and original input. -/
theorem unpack_good_layout
    (parse : Nat → ExtensionRegion Bytes → Outcome Nat (Except Error Nat) Nat Nat → Prop)
    (drop : Nat → Nat → Outcome Nat Unit Nat Nat → Prop) (state : Nat) :
    unpackExtensionTailReference (unpackerWith unpackByteAt parse drop) state unpackGoodInput =
      .ok (.borrowed ⟨unpackGoodInput, 166, 4⟩) := by
  rw [unpackGoodInput, unpack_prefixed_layout]
  rfl

/-- The malformed marker still has an admitted base length. -/
theorem unpack_bad_length :
    ¬ (unpackBadInput.length = multisigLength ∨ unpackBadInput.length < 165) := by
  simp only [unpackBadInput, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, multisigLength]
  decide +kernel

/-- The successful layout control also passes the initial length checks. -/
theorem unpack_good_length :
    ¬ (unpackGoodInput.length = multisigLength ∨ unpackGoodInput.length < 165) := by
  simp only [unpackGoodInput, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, multisigLength]
  decide +kernel

/-- A nontrivial destructor uses the actual parser-return state and owned base. -/
abbrev droppingUnpacker : ExtensionUnpacker := unpackerWith unpackByteAt ownedBaseParser
  (fun before base outcome => outcome = .returned () (before + base))

/-- A layout error runs the owned base destructor and preserves its changes. -/
theorem unpack_layout_error_drops_owned_base :
    unpackExtensionOperational droppingUnpacker 0 unpackBadInput
      (.returned (.error .InvalidAccountData) 38) := by
  have allowed : ¬ (droppingUnpacker.length unpackBadInput = multisigLength ∨
      droppingUnpacker.length unpackBadInput < droppingUnpacker.baseLength) := unpack_bad_length
  have parsed : droppingUnpacker.parse 0 ⟨unpackBadInput, 0, 165⟩
      (.returned (.ok 37) 1) := ⟨rfl, rfl, rfl⟩
  have layout : unpackExtensionTailReference droppingUnpacker 1 unpackBadInput =
      .error .InvalidAccountData := unpack_bad_layout _ _ _
  have destroyed : droppingUnpacker.dropBase 1 37 (.returned () 38) := rfl
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, parsed, ?_⟩
  simp only [finishExtensionUnpack, layout]
  exact ⟨.returned () 38, destroyed, rfl⟩

/-- A destructor may unwind after changing the actual state. -/
abbrev unwindingUnpacker : ExtensionUnpacker := unpackerWith unpackByteAt ownedBaseParser
  (fun before base outcome => outcome = .unwound 11 (before + base))

/-- The destructor unwind replaces the pending layout error and keeps its state. -/
theorem unpack_layout_error_propagates_drop_unwind :
    unpackExtensionOperational unwindingUnpacker 0 unpackBadInput (.unwound 11 38) := by
  have allowed : ¬ (unwindingUnpacker.length unpackBadInput = multisigLength ∨
      unwindingUnpacker.length unpackBadInput < unwindingUnpacker.baseLength) := unpack_bad_length
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [finishExtensionUnpack, unpack_bad_layout]
  exact ⟨.unwound 11 38, rfl, rfl⟩

/-- A destructor may terminate without an invented post-state. -/
abbrev terminatingUnpacker : ExtensionUnpacker := unpackerWith unpackByteAt ownedBaseParser
  (fun _ _ outcome => outcome = .terminated 99)

/-- A terminal destructor exit is propagated from layout-error cleanup. -/
theorem unpack_layout_error_propagates_drop_terminal :
    unpackExtensionOperational terminatingUnpacker 0 unpackBadInput (.terminated 99) := by
  have allowed : ¬ (terminatingUnpacker.length unpackBadInput = multisigLength ∨
      terminatingUnpacker.length unpackBadInput < terminatingUnpacker.baseLength) :=
        unpack_bad_length
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [finishExtensionUnpack, unpack_bad_layout]
  exact ⟨.terminated 99, rfl, rfl⟩

/-- The destructor has no finite exit, while parsing still succeeds. -/
abbrev noDropExitUnpacker : ExtensionUnpacker := unpackerWith unpackByteAt ownedBaseParser
  (fun _ _ _ => False)

/-- An error path cannot bypass a nonreturning destructor. -/
theorem unpack_no_drop_error (bytes : Bytes)
    (admitted : ¬ (bytes.length = multisigLength ∨ bytes.length < 165))
    (layout : unpackExtensionTailReference noDropExitUnpacker 1 bytes =
      .error .InvalidAccountData)
    (outcome : Outcome Nat (Except Error (ExtensionUnpacked Nat Bytes)) Nat Nat) :
    ¬ unpackExtensionOperational noDropExitUnpacker 0 bytes outcome := by
  intro run
  simp only [unpackExtensionOperational, admitted, ↓reduceIte] at run
  obtain ⟨parsed, ⟨_, _, same⟩, finished⟩ := run
  subst parsed
  simp only [finishExtensionUnpack, layout] at finished
  obtain ⟨_, impossible, _⟩ := finished
  exact impossible

/-- The malformed control has no finite return, unwind or terminal exit when
its required destructor has none. -/
theorem unpack_layout_error_has_no_exit
    (outcome : Outcome Nat (Except Error (ExtensionUnpacked Nat Bytes)) Nat Nat) :
    ¬ unpackExtensionOperational noDropExitUnpacker 0 unpackBadInput outcome :=
  unpack_no_drop_error unpackBadInput unpack_bad_length (unpack_bad_layout _ _ _) outcome

/-- Success transfers the exact base and input region even when no destructor
exit exists; no local destructor is called on this path. -/
theorem unpack_success_retains_region_without_drop :
    unpackExtensionOperational noDropExitUnpacker 0 unpackGoodInput
      (.returned (.ok ⟨37, .borrowed ⟨unpackGoodInput, 166, 4⟩⟩) 1) := by
  have allowed : ¬ (noDropExitUnpacker.length unpackGoodInput = multisigLength ∨
      noDropExitUnpacker.length unpackGoodInput < noDropExitUnpacker.baseLength) :=
        unpack_good_length
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [finishExtensionUnpack, unpack_good_layout]

/-- A parser-state change affects the marker observation of the live input. -/
def changedUnpackByteAt (state : Nat) (bytes : Bytes) (index : Fin bytes.length) : UInt8 :=
  if state = 1 ∧ index.val = 165 then 9 else bytes[index.val]

/-- A state-changing input interpretation with the same reference and length. -/
abbrev changedInputUnpacker : ExtensionUnpacker := unpackerWith changedUnpackByteAt ownedBaseParser
  (fun before base outcome => outcome = .returned () (before + base))

/-- Reading just the marker through the post-parser state detects its change,
without constructing or reducing an entire concrete observed input list. -/
theorem unpack_changed_layout :
    unpackExtensionTailReference changedInputUnpacker 1 unpackGoodInput =
      .error .InvalidAccountData := by
  let rest := (changedInputUnpacker.inputBytes 1 unpackGoodInput).drop 165
  have inputLength : unpackGoodInput.length = 170 := by
    simp only [unpackGoodInput, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
  have restLength : rest.length = 5 := by
    simp only [rest, List.length_drop, ExtensionUnpacker.inputBytes_length]
    change unpackGoodInput.length - 165 = 5
    rw [inputLength]
  have nonempty : rest.isEmpty = false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro empty
    have zero := congrArg List.length empty
    rw [restLength] at zero
    cases zero
  have inBounds : 165 < unpackGoodInput.length := by rw [inputLength]; decide +kernel
  have marker : rest[0]? = some 9 := by
    rw [List.getElem?_drop, Nat.add_zero]
    change (List.ofFn fun index : Fin unpackGoodInput.length =>
      changedUnpackByteAt 1 unpackGoodInput index)[165]? = some 9
    rw [List.getElem?_ofFn]
    simp only [inBounds, ↓reduceDIte, changedUnpackByteAt]
    rfl
  have layout : unpackExtensionTail 165 .account rest = .error .InvalidAccountData := by
    simp only [unpackExtensionTail, nonempty, Bool.false_eq_true, ↓reduceIte,
      accountLength, Nat.sub_self, Nat.zero_add, restLength, List.take_zero, List.any_nil,
      marker, ExtensionAccountType.tag]
    rfl
  dsimp only [rest] at layout
  simp only [unpackExtensionTailReference, layout, Except.map]

/-- Tail validation reads the state returned by the parser; a frozen input
snapshot would wrongly return this apparently valid original marker. -/
theorem unpack_checks_current_bytes_after_parse :
    unpackExtensionOperational changedInputUnpacker 0 unpackGoodInput
      (.returned (.error .InvalidAccountData) 38) := by
  have allowed : ¬ (changedInputUnpacker.length unpackGoodInput = multisigLength ∨
      changedInputUnpacker.length unpackGoodInput < changedInputUnpacker.baseLength) :=
        unpack_good_length
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [finishExtensionUnpack, unpack_changed_layout]
  exact ⟨.returned () 38, rfl, rfl⟩

/-- A bare base returns the source static empty reference. -/
theorem unpack_bare_base_uses_empty_literal :
    unpackExtensionOperational noDropExitUnpacker 0 (List.replicate 165 0)
      (.returned (.ok ⟨37, .empty⟩) 1) := by
  have allowed : ¬ (noDropExitUnpacker.length (List.replicate 165 0) = multisigLength ∨
      noDropExitUnpacker.length (List.replicate 165 0) < noDropExitUnpacker.baseLength) := by
    change ¬ ((List.replicate 165 (0 : UInt8)).length = 355 ∨
      (List.replicate 165 (0 : UInt8)).length < 165)
    rw [List.length_replicate]
    decide +kernel
  have layout : unpackExtensionTailReference noDropExitUnpacker 1 (List.replicate 165 0) =
      .ok .empty := by
    rw [unpack_static_layout]
    simp only [List.drop_replicate, Nat.sub_self]
    rfl
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [finishExtensionUnpack, layout]

/-- A present marker and zero-length TLV retain an empty range of the original
input; this is distinguished from the bare-base static empty literal. -/
theorem unpack_extended_empty_keeps_input_identity :
    unpackExtensionOperational noDropExitUnpacker 0 (List.replicate 165 0 ++ [2])
      (.returned (.ok ⟨37, .borrowed ⟨List.replicate 165 0 ++ [2], 166, 0⟩⟩) 1) := by
  have allowed : ¬ (noDropExitUnpacker.length (List.replicate 165 0 ++ [2]) = multisigLength ∨
      noDropExitUnpacker.length (List.replicate 165 0 ++ [2]) < noDropExitUnpacker.baseLength) := by
    change ¬ ((List.replicate 165 (0 : UInt8) ++ [2]).length = 355 ∨
      (List.replicate 165 (0 : UInt8) ++ [2]).length < 165)
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    decide +kernel
  have layout : unpackExtensionTailReference noDropExitUnpacker 1 (List.replicate 165 0 ++ [2]) =
      .ok (.borrowed ⟨List.replicate 165 0 ++ [2], 166, 0⟩) := by
    rw [unpack_prefixed_layout]
    rfl
  simp only [unpackExtensionOperational, allowed, ↓reduceIte]
  refine ⟨.returned (.ok 37) 1, ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [finishExtensionUnpack, layout]

end SolanalibTest.Specs.SplToken2022Interface.Extensions

@[expose] public section

namespace SolanalibTest.Specs.SplToken2022Interface.V3Extensions

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.SplToken2022Interface.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.applicability key).filter (fun
        profile => profile.id == id) }

def build0 : Versioning.Build where
  package := "spl-token-2022-interface"
  version := "2.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["2.0.0", "2.1.0", "2.2.0"].all (fun version =>
      decide (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-BaseStateWithExtensions-get_extension_typ\
          es").forBuild
        { build0 with version := version }).identities
          .extension_BaseStateWithExtensions_get_extension_types_push_before_payload =
          [⟨"spl-token-2022-interface", version,
            "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_ty\
              pes",
            "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_ty\
              pes"⟩]))
              = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"spl-token-2022-interface", "2.1.0",
      "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_types",
            "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_ty\
              pes"⟩] :
              List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
        build0).identities
        .extension_BaseStateWithExtensions_get_extension_types_push_before_payload)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile
      "spl-token-2022-interface-2.1.0-extension\
        -BaseStateWithExtensions-get_extension_types").applicability
          .extension_BaseStateWithExtensions_get_extension_types_push_before_payload).length = 1 ∧
    ["1.999.999", "3.0.0", "2.2.0-rc.1"].all (fun version =>
      (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-BaseStateWithExtensions-get_extension_typ\
          es").forBuild { build0 with version := version }).identities
        .extension_BaseStateWithExtensions_get_extension_types_push_before_payload).isEmpty) = true
          := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "spl-token-2022-interface-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with target := [] },
      { build0 with target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "64"⟩] },
      { build0 with target := [⟨"pointer_width", "unsupported-target-value"⟩] } ] : List
        Versioning.Build).all
      (fun build => (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-BaseStateWithExtensions-get_extension_typ\
          es").forBuild build).identities
        .extension_BaseStateWithExtensions_get_extension_types_push_before_payload).isEmpty) = true
          := by
  decide +kernel

def build1 : Versioning.Build where
  package := "spl-token-2022-interface"
  version := "2.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["2.0.0", "2.1.0", "2.2.0"].all (fun version =>
      decide (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-ExtensionType-get_required_init_account_e\
          xtensions").forBuild
        { build1 with version := version }).identities
          .extension_ExtensionType_get_required_init_account_extensions =
          [⟨"spl-token-2022-interface", version,
            "spl_token_2022_interface::extension::ExtensionType::get_required_init_account_\
              extensions",
            "spl_token_2022_interface::extension::ExtensionType::get_required_init_account_\
              extensions"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"spl-token-2022-interface", "2.1.0",
      "spl_token_2022_interface::extension::ExtensionType::get_required_init_account_extens\
        ions",
            "spl_token_2022_interface::extension::ExtensionType::get_required_init_account_\
              extensions"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
        build1).identities .extension_ExtensionType_get_required_init_account_extensions)) = true
        := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile
      "spl-token-2022-interface-2.1.0-extension-ExtensionType-get_required_init_account_ext\
        ensions").applicability
          .extension_ExtensionType_get_required_init_account_extensions).length = 1 ∧
    ["1.999.999", "3.0.0", "2.2.0-rc.1"].all (fun version =>
      (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-ExtensionType-get_required_init_account_e\
          xtensions").forBuild { build1 with version := version }).identities
        .extension_ExtensionType_get_required_init_account_extensions).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "spl-token-2022-interface-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with target := [] },
      { build1 with target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "64"⟩] },
      { build1 with target := [⟨"pointer_width", "unsupported-target-value"⟩] } ] : List
        Versioning.Build).all
      (fun build => (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension-ExtensionType-get_required_init_account_e\
          xtensions").forBuild build).identities
        .extension_ExtensionType_get_required_init_account_extensions).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "spl-token-2022-interface"
  version := "2.1.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"pointer_width", "64"⟩]
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["2.0.0", "2.1.0", "2.2.0"].all (fun version =>
      decide (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension\
        -ExtensionType-try_calculate_account_len").forBuild
        { build2 with version := version }).identities
          .extension_ExtensionType_try_calculate_account_len =
          [⟨"spl-token-2022-interface", version,
            "spl_token_2022_interface::extension::ExtensionType::try_calculate_account_len",
            "spl_token_2022_interface::extension::ExtensionType::try_calculate_account_len"⟩])) =
              true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"spl-token-2022-interface", "2.1.0",
      "spl_token_2022_interface::extension::ExtensionType::try_calculate_account_len",
            "spl_token_2022_interface::extension::ExtensionType::try_calculate_account_len"⟩] :
              List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.SplToken2022Interface.Capabilities.catalog.forBuild
        build2).identities .extension_ExtensionType_try_calculate_account_len)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile
      "spl-token-2022-interface-2.1.0-extension\
        -ExtensionType-try_calculate_account_len").applicability
          .extension_ExtensionType_try_calculate_account_len).length = 1 ∧
    ["1.999.999", "3.0.0", "2.2.0-rc.1"].all (fun version =>
      (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension\
        -ExtensionType-try_calculate_account_len").forBuild { build2 with version := version
          }).identities
        .extension_ExtensionType_try_calculate_account_len).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "spl-token-2022-interface-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build2 with target := [] },
      { build2 with target := [⟨"pointer_width", "64"⟩, ⟨"pointer_width", "64"⟩] },
      { build2 with target := [⟨"pointer_width", "unsupported-target-value"⟩] } ] : List
        Versioning.Build).all
      (fun build => (((selectedProfile
        "spl-token-2022-interface-2.1.0-extension\
        -ExtensionType-try_calculate_account_len").forBuild build).identities
        .extension_ExtensionType_try_calculate_account_len).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022Interface.V3Extensions
