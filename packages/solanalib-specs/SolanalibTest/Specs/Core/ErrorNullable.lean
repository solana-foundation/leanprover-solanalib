/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgramError.ProgramError
public import Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.Address

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.ErrorNullable

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Every builtin entry is checked, together with the special custom-zero tag. -/
theorem all_builtin_error_tags :
    ((List.range 26).map (fun n => n + 1)).all (fun tag =>
      ProgramError.V3_0_1.fromStatus (UInt64.ofNat (tag * 2^32)) ==
        (ProgramError.V3_0_1.ofBuiltinTag tag).getD (.custom 0)) = true := by decide +kernel

theorem custom_status_edges :
    Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model () 0 = (.custom 0, ()) ∧
    Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model () 18446744073709551615 =
      (.custom 4294967295, ()) ∧
    Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model () (2 * 2^32 + 7) =
      (.custom 7, ()) ∧
    Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model () (27 * 2^32) =
      (.custom 0, ()) := by decide +kernel

theorem custom_zero_encodes_nonzero :
    Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_model () (.custom 0) = (4294967296,
      ()) ∧
    ¬ Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_contract.ensures () (.custom 0) 0 ()
      := by
  unfold Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_contract
    SdkValue.errorToStatusContract Solanalib.Contracts.Model.ensures
  decide +kernel

theorem error_decoder_rejects_tag_only_test :
    ¬ Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_contract.ensures ()
      (2 * 2^32 + 7) .invalidArgument () := by
  unfold Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_contract
    SdkValue.errorFromStatusContract Solanalib.Contracts.Model.ensures
  decide +kernel

theorem nullable_null_drops : Nullable.getRun Nullable.sample (0 : Nat) 0 (.returned none 2) :=
  ⟨.returned true 1, rfl, .returned () 2, rfl, rfl⟩

theorem nullable_nonnull_moves :
    Nullable.getRun Nullable.sample (0 : Nat) 7 (.returned (some 7) 1) :=
  Nullable.get_some _ _ _ _ rfl

abbrev nullableOverride : Nullable.Index :=
  { Nullable.sample with isNone := Callback.ofFunction fun before _ => .returned false (before + 1)
    }

theorem nullable_override_is_respected :
    Nullable.getRun nullableOverride (0 : Nat) 0 (.returned (some 0) 1) :=
  Nullable.get_some _ _ _ _ rfl

abbrev nullablePanic : Nullable.Index :=
  { Nullable.sample with
    isNone := Callback.ofFunction fun before _ => .unwound "query" (before + 1)
    dropValue := Callback.ofFunction fun before _ => .unwound "drop" (before + 1) }

theorem nullable_double_panic_terminal :
    Nullable.getRun nullablePanic (0 : Nat) 7 (.terminated "double panic") :=
  Nullable.get_double_unwind nullablePanic 0 1 2 7 "query" "drop" "double panic" rfl rfl rfl

theorem nullable_null_rejects_lost_drop :
    ¬ Nullable.getRun Nullable.sample (0 : Nat) 0 (.returned none 1) := by
  simp [Nullable.getRun, Nullable.sample, Callback.ofFunction, Callback.map, Outcome.map]

theorem nullable_double_panic_ne_return :
    ¬ Nullable.getRun nullablePanic (0 : Nat) 7 (.returned none 2) := by
  simp [Nullable.getRun, nullablePanic, Nullable.sample, Callback.ofFunction, Owned.cleanup]

abbrev nullableQueryUnwind : Nullable.Index :=
  { Nullable.sample with
    isNone := Callback.ofFunction fun before _ => .unwound "query" (before + 1)
    dropValue := Callback.ofFunction fun before _ => .returned () (before + 10) }

/-- Unwind cleanup starts in the actual state of the query and retains its reason. -/
theorem nullable_query_unwind_keeps_cleanup_state :
    Nullable.getRun nullableQueryUnwind (0 : Nat) 7 (.unwound "query" 11) :=
  ⟨.unwound "query" 1, rfl, .returned () 11, rfl, rfl⟩

theorem nullable_query_unwind_rejects_skipped_cleanup :
    ¬ Nullable.getRun nullableQueryUnwind (0 : Nat) 7 (.unwound "query" 1) := by
  simp [Nullable.getRun, nullableQueryUnwind, Nullable.sample, Callback.ofFunction, Owned.cleanup]

abbrev nullableDropUnwind : Nullable.Index :=
  { Nullable.sample with
    dropValue := Callback.ofFunction fun before _ => .unwound "drop" (before + 10) }

/-- A null-path destructor unwind is propagated with its effects. -/
theorem nullable_null_drop_unwind :
    Nullable.getRun nullableDropUnwind (0 : Nat) 0 (.unwound "drop" 11) :=
  ⟨.returned true 1, rfl, .unwound "drop" 11, rfl, rfl⟩

theorem nullable_null_drop_unwind_rejects_return :
    ¬ Nullable.getRun nullableDropUnwind (0 : Nat) 0 (.returned none 11) := by
  simp [Nullable.getRun, nullableDropUnwind, Nullable.sample,
    Callback.ofFunction, Callback.map, Outcome.map]

abbrev nullableDropTerminal : Nullable.Index :=
  { Nullable.sample with
    dropValue := Callback.ofFunction fun _ _ => .terminated "drop stopped" }

/-- The null-path destructor may terminate without returning None. -/
theorem nullable_null_drop_terminal :
    Nullable.getRun nullableDropTerminal (0 : Nat) 0 (.terminated "drop stopped") :=
  ⟨.returned true 1, rfl, .terminated "drop stopped", rfl, rfl⟩

abbrev nullableUnwindDropTerminal : Nullable.Index :=
  { nullableDropTerminal with
    isNone := Callback.ofFunction fun before _ => .unwound "query" (before + 1) }

theorem nullable_unwind_drop_terminal :
    Nullable.getRun nullableUnwindDropTerminal (0 : Nat) 7 (.terminated "drop stopped") :=
  ⟨.unwound "query" 1, rfl, .terminated "drop stopped", rfl, rfl⟩

abbrev nullableQueryTerminal : Nullable.Index :=
  { Nullable.sample with
    isNone := Callback.ofFunction fun _ _ => .terminated "query stopped"
    dropValue := fun _ _ _ => False }

/-- A terminal query has a real execution even when the unreached destructor
has no finite outcome. No callback precondition is assumed. -/
theorem nullable_terminal_query_skips_drop :
    Nullable.getRun nullableQueryTerminal (0 : Nat) 7 (.terminated "query stopped") :=
  Nullable.get_terminal nullableQueryTerminal 0 7 "query stopped" rfl

theorem nullable_terminal_query_rejects_return :
    ¬ Nullable.getRun nullableQueryTerminal (0 : Nat) 7 (.returned (some 7) 0) := by
  simp [Nullable.getRun, nullableQueryTerminal, Nullable.sample, Callback.ofFunction]

end SolanalibTest.Specs.Core.ErrorNullable
