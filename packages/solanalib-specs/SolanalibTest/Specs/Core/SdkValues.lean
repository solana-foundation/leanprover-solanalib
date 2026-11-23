/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgram.ProgramOption


public import Solanalib.Specs.SolanaZeroCopy.U16
public import Solanalib.Specs.SplPod.OptionalKeys

public import Solanalib.Specs.SolanaProgramOption.Operations
public import Solanalib.Specs.SolanaSdkIds.AdditionalIds

public import Solanalib.Specs.SplPod.Primitives

public import Solanalib.Specs.SolanaProgramOption.COption

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem is_none_empty_type :
    ProgramOption.isNoneRun Empty () .none (.returned true ()) := rfl

theorem is_none_rejects_some (value : Nat) :
    ¬ (Solanalib.Specs.SolanaProgramOption.COption.is_none_contract.contract Nat).ensures ()
      (.some value) true () := by
  change ¬ (() = () ∧ true = false)
  decide +kernel

theorem reborrow_preserves_parent :
    ProgramOption.asRef (7 : Nat) true = .some ⟨7, ()⟩ ∧
    ProgramOption.asRef (7 : Nat) false = .none := ⟨rfl, rfl⟩

theorem reborrow_rejects_fresh_parent :
    ¬ (Solanalib.Specs.SolanaProgramOption.COption.as_ref_contract.contract Nat).ensures ()
      (7, true) (.some ⟨8, ()⟩) () := by
  unfold Solanalib.Specs.SolanaProgramOption.COption.as_ref_contract ProgramOption.asRefFamily
    Solanalib.Contracts.Model.ensures
  decide +kernel

theorem map_some_calls_once :
    ProgramOption.mapRun ProgramOption.mapSample (0 : Nat) (.some 7, 3)
      (.returned (.some 10) 1) := ⟨.returned 10 1, rfl, rfl⟩

theorem map_none_drops_closure :
    ProgramOption.mapRun ProgramOption.mapSample (0 : Nat) (.none, 3) (.returned .none 1) :=
  ⟨.returned () 1, rfl, rfl⟩

theorem map_none_rejects_skipped_drop :
    ¬ ProgramOption.mapRun ProgramOption.mapSample (0 : Nat) (.none, 3) (.returned .none 0) := by
  simp [ProgramOption.mapRun, ProgramOption.mapSample, Callback.map_ofFunction, Outcome.map]

abbrev panicMap : ProgramOption.MapIndex :=
  { ProgramOption.mapSample with
    call := Callback.ofFunction fun before _ => .unwound "call" (before + 1)
    dropClosure := Callback.ofFunction fun before _ => .unwound "closure drop" (before + 2) }

theorem map_none_drop_unwinds :
    ProgramOption.mapRun panicMap (0 : Nat) (.none, 3) (.unwound "closure drop" 2) :=
  ⟨.unwound "closure drop" 2, rfl, rfl⟩

theorem map_some_call_unwinds :
    ProgramOption.mapRun panicMap (0 : Nat) (.some 7, 3) (.unwound "call" 1) :=
  ⟨.unwound "call" 1, rfl, rfl⟩

theorem unwrap_or_drops_fallback :
    ProgramOption.unwrapOrRun ProgramOption.unwrapOrSample (0 : Nat) (.some 7, 8)
      (.returned 7 1) := ⟨.returned 7 1, ⟨.returned () 1, rfl, rfl⟩, rfl⟩

theorem unwrap_or_none_moves_fallback :
    ProgramOption.unwrapOrRun ProgramOption.unwrapOrSample (0 : Nat) (.none, 8)
      (.returned 8 0) := rfl

abbrev panicFallback : ProgramOption.UnwrapOrIndex :=
  { ProgramOption.unwrapOrSample with
    dropValue := Callback.ofFunction fun before _ => .unwound "drop" (before + 1) }

/-- The pinned lowering leaves the moved return place retained after the
fallback destructor panics; it still cannot return that payload normally. -/
theorem unwrap_or_drop_panic :
    ProgramOption.unwrapOrRun panicFallback (0 : Nat) (.some 7, 8) (.unwound "drop" 1) :=
  ⟨.unwound "drop" 1, ⟨.unwound "drop" 1, rfl, rfl⟩, rfl⟩

theorem unwrap_or_drop_panic_ne_return :
    ¬ ProgramOption.unwrapOrRun panicFallback (0 : Nat) (.some 7, 8) (.returned 7 1) := by
  simp [ProgramOption.unwrapOrRun, panicFallback, ProgramOption.unwrapOrSample,
    Callback.map_ofFunction, Outcome.map]

/-- The two owned branches have different terminal exits, so choosing the
wrong callback cannot satisfy the registered map contract. -/
abbrev terminalMap : ProgramOption.MapIndex :=
  { ProgramOption.mapSample with
    call := Callback.ofFunction fun _ _ => .terminated "call"
    dropClosure := Callback.ofFunction fun _ _ => .terminated "closure drop" }

theorem map_some_terminal :
    (Solanalib.Specs.SolanaProgramOption.COption.map_contract.contract terminalMap).post
      (0 : Nat) (.some 7, 3) (.terminated "call") :=
  ⟨.terminated "call", rfl, rfl⟩

theorem map_none_terminal :
    (Solanalib.Specs.SolanaProgramOption.COption.map_contract.contract terminalMap).post
      (0 : Nat) (.none, 3) (.terminated "closure drop") :=
  ⟨.terminated "closure drop", rfl, rfl⟩

/-- A terminal destructor does not manufacture an ordinary None with an
arbitrary caller state. -/
theorem map_terminal_rejects_return (value : ProgramOption.Value Nat) (after : Nat) :
    ¬ (Solanalib.Specs.SolanaProgramOption.COption.map_contract.contract terminalMap).post
      (0 : Nat) (.none, 3) (.returned value after) := by
  simp [Solanalib.Specs.SolanaProgramOption.COption.map_contract, ProgramOption.mapFamily,
    ProgramOption.mapRun, terminalMap, ProgramOption.mapSample,
    Callback.map_ofFunction, Outcome.map]

abbrev terminalFallback : ProgramOption.UnwrapOrIndex :=
  { ProgramOption.unwrapOrSample with
    dropValue := Callback.ofFunction fun _ _ => .terminated "fallback drop" }

/-- None moves the fallback even when its destructor would terminate. -/
theorem unwrap_or_none_does_not_call_destructor :
    (Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_contract.contract terminalFallback).post
      (0 : Nat) (.none, 8) (.returned (8 : Nat) (0 : Nat)) := rfl

theorem unwrap_or_some_terminal :
    (Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_contract.contract terminalFallback).post
      (0 : Nat) (.some 7, 8) (.terminated "fallback drop") :=
  ⟨.terminated "fallback drop", ⟨.terminated "fallback drop", rfl, rfl⟩, rfl⟩

theorem unwrap_or_terminal_rejects_return (value after : Nat) :
    ¬ (Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_contract.contract
      terminalFallback).post
      (0 : Nat) (.some 7, 8) (.returned value after) := by
  simp [Solanalib.Specs.SolanaProgramOption.COption.unwrap_or_contract,
    ProgramOption.unwrapOrFamily,
    ProgramOption.unwrapOrRun, terminalFallback, ProgramOption.unwrapOrSample,
    Callback.map_ofFunction, Outcome.map]

end SolanalibTest.Specs.Core.SdkValues

namespace SolanalibTest.Specs.Core.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem pod_u64_max : Solanalib.Specs.SplPod.primitives.PodU64.into_u64_model ()
    (Unaligned.ofUInt64 18446744073709551615) = (18446744073709551615, ()) := by
  exact congrArg (fun value => (value, ())) (Unaligned.toUInt64_ofUInt64 _)

theorem pod_u64_rejects_truncation :
    ¬ Solanalib.Specs.SplPod.primitives.PodU64.into_u64_contract.ensures ()
      (Unaligned.ofUInt64 18446744073709551615) 4294967295 () := by
  unfold Solanalib.Specs.SplPod.primitives.PodU64.into_u64_contract Unaligned.intoU64Contract
    Solanalib.Contracts.Model.ensures
  decide +kernel

end SolanalibTest.Specs.Core.SdkValues

namespace SolanalibTest.Specs.Core.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev word16 : SdkValue.U16 := ⟨[0x12, 0x34], rfl⟩

theorem u16_rejects_big_endian :
    ¬ Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_contract.ensures () word16 0x1234 () :=
      by
  unfold Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_contract SdkValue.intoU16Contract
    Solanalib.Contracts.Model.ensures
  decide +kernel

theorem u16_max_roundtrip : SdkValue.toUInt16 (SdkValue.ofUInt16 65535) = 65535 :=
  SdkValue.toUInt16_ofUInt16 _

theorem eq_callback_effect :
    ProgramOption.eqRun ProgramOption.eqSample (0 : Nat) (.some 7, .some 7)
      (.returned true 1) := rfl

theorem eq_mixed_skips_callback :
    ProgramOption.eqRun ProgramOption.eqSample (0 : Nat) (.none, .some 7)
      (.returned false 0) := rfl

theorem eq_rejects_lost_callback_effect :
    ¬ ProgramOption.eqRun ProgramOption.eqSample (0 : Nat) (.some 7, .some 7)
      (.returned true 0) := by
  unfold ProgramOption.eqRun ProgramOption.eqSample Callback.ofFunction
  simp

theorem unwrap_present :
    ProgramOption.unwrapRun ProgramOption.unwrapSample () (.some 7) (.returned 7 ()) := rfl

theorem unwrap_none_unwinds :
    ProgramOption.unwrapRun ProgramOption.unwrapSample () .none
      (.unwound ProgramOption.unwrapMessage ()) :=
  ⟨.unwound ProgramOption.unwrapMessage (), rfl, rfl⟩

abbrev abortUnwrap : ProgramOption.UnwrapIndex where
  State := Unit
  T := Nat
  Unwind := String
  Terminal := String
  panic := Callback.ofFunction fun _ message => .terminated message

theorem unwrap_none_terminates :
    ProgramOption.unwrapRun abortUnwrap () .none (.terminated ProgramOption.unwrapMessage) :=
  ⟨.terminated ProgramOption.unwrapMessage, rfl, rfl⟩

theorem unwrap_none_ne_success :
    ¬ ProgramOption.unwrapRun ProgramOption.unwrapSample () .none (.returned 0 ()) :=
  ProgramOption.unwrap_none_ne_returned _ _ _ _

end SolanalibTest.Specs.Core.SdkValues

namespace SolanalibTest.Specs.Core.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem u16_little_endian :
    Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_contract.ensures () word16 0x3412 () ∧
    Solanalib.Specs.SplPod.primitives.PodU16.into_u16_contract.ensures () word16 0x3412 () := by
  unfold Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_contract
    Solanalib.Specs.SplPod.primitives.PodU16.into_u16_contract SdkValue.intoU16Contract
    Solanalib.Contracts.Model.ensures
  decide +kernel

theorem zero_key_is_none :
    Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_model ()
      Solanalib.Runtime.Ids.systemProgram = (none, ()) := by decide +kernel

theorem nonzero_key_retained :
    Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_model ()
      Solanalib.Runtime.Ids.voteProgram = (some Solanalib.Runtime.Ids.voteProgram, ()) := by
        decide +kernel

theorem nonzero_key_rejects_none :
    ¬ Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_contract.ensures ()
      Solanalib.Runtime.Ids.voteProgram none () := by
  unfold Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_contract
    SdkValue.optionalKeyContract Solanalib.Contracts.Model.ensures
  decide +kernel

/-- The four functions return distinct canonical IDs. -/
theorem exact_ids :
    Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_model () () =
      (Solanalib.Runtime.Ids.bpfLoaderUpgradeable, ()) ∧
    Solanalib.Specs.SolanaSdkIds.ed25519_program.id_model () () =
      (Solanalib.Runtime.Ids.ed25519Program, ()) ∧
    Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_model () () =
      (Solanalib.Runtime.Ids.sysvarInstructions, ()) ∧
    Solanalib.Specs.SolanaSdkIds.vote.id_model () () = (Solanalib.Runtime.Ids.voteProgram, ()) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ids_reject_cross_wiring :
    ¬ Solanalib.Specs.SolanaSdkIds.vote.id_contract.ensures () ()
      Solanalib.Runtime.Ids.ed25519Program () ∧
    ¬ Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_contract.ensures () ()
      Solanalib.Runtime.Ids.bpfLoaderUpgradeable () := by
  unfold Solanalib.Specs.SolanaSdkIds.vote.id_contract
    Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_contract SdkValue.idContract
    Solanalib.Contracts.Model.ensures
  decide +kernel

end SolanalibTest.Specs.Core.SdkValues

namespace SolanalibTest.Specs.Core.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem into_option_moves_payload :
    ProgramOption.intoOptionRun Nat () (.some 19) (.returned (some 19) ()) := rfl

theorem into_option_rejects_lost_payload :
    ¬ (Solanalib.Specs.SolanaProgram.program_option.COption.into_option_contract.contract
      Nat).ensures ()
      (.some 19) none () := by
  unfold Solanalib.Specs.SolanaProgram.program_option.COption.into_option_contract
    ProgramOption.intoOptionFamily Solanalib.Contracts.Model.ensures
  decide +kernel

end SolanalibTest.Specs.Core.SdkValues

namespace SolanalibTest.Specs.Core.SdkValues

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev directedContains : ProgramOption.ContainsIndex where
  State := Nat
  T := Nat
  Query := Nat
  Unwind := String
  Terminal := String
  equal := Callback.ofFunction fun before args => .returned (args.1 < args.2) (before + 1)

theorem contains_query_on_left :
    ProgramOption.containsRun directedContains (0 : Nat) (.some 9, 3) (.returned true 1) := rfl

theorem contains_rejects_reversed_comparison :
    ¬ ProgramOption.containsRun directedContains (0 : Nat) (.some 9, 3)
      (.returned false 1) := by
  unfold ProgramOption.containsRun directedContains Callback.ofFunction
  simp

theorem default_only_when_absent :
    ProgramOption.unwrapOrDefaultRun ProgramOption.unwrapOrDefaultSample (0 : Nat) .none
      (.returned 9 1) ∧
    ProgramOption.unwrapOrDefaultRun ProgramOption.unwrapOrDefaultSample (0 : Nat) (.some 7)
      (.returned 7 0) := ⟨rfl, rfl⟩

theorem default_rejects_eager_call :
    ¬ ProgramOption.unwrapOrDefaultRun ProgramOption.unwrapOrDefaultSample (0 : Nat) (.some 7)
      (.returned 7 1) := by
  unfold ProgramOption.unwrapOrDefaultRun
  simp

end SolanalibTest.Specs.Core.SdkValues
