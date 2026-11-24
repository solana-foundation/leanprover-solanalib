/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAddress
public import Solanalib.Specs.Core.Curve

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAddress.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Syscall

theorem request_keeps_seed_tree_and_initial_outputs :
    (pdaRequest sampleInputs).seeds = [[], [7, 0, 9], []] ∧
    (pdaRequest sampleInputs).seedCount = 3 ∧
    (pdaRequest sampleInputs).addressOutput = none ∧
    (pdaRequest sampleInputs).bumpOutput = 255 := ⟨rfl, rfl, rfl, rfl⟩

theorem success_uses_returned_bump_and_actual_state :
    Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run sampleTypes
      (3 : Nat) sampleFindCall (.returned (.zero, 254) (10 : Nat)) := sampleFind_execution

def failedReply : PdaReply := ⟨8, none, 17⟩

def failedStatusEight : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .returned failedReply (before + 4)

theorem nonzero_status_ignores_uninitialized_output :
    tryRun failedStatusEight 5 sampleInputs (.returned none 9) := by
  apply tryRun_returned failedStatusEight 5 9 sampleInputs failedReply _ rfl
  simp [decodePda, failedReply]

def nonzeroInitializedSyscall : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .returned ⟨1, some .zero, 42⟩ (before + 4)

theorem nonzero_status_ignores_initialized_output_too :
    tryRun nonzeroInitializedSyscall 5 sampleInputs (.returned none 9) := by
  apply tryRun_returned nonzeroInitializedSyscall 5 9 sampleInputs ⟨1, some .zero, 42⟩ _ rfl
  simp [decodePda]

def uninitializedSuccess : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .returned ⟨0, none, 255⟩ before

/-- The finite syscall exit exists, but both source-facing families reject
the missing successful output before a partial decoder can erase that exit. -/
theorem uninitialized_success_rejected_by_both_families :
    uninitializedSuccess 4 (pdaRequest sampleInputs) (.returned ⟨0, none, 255⟩ 4) ∧
      ¬ (tryFamily.contract sampleTypes).requires (4 : Nat)
        ⟨sampleInputs, uninitializedSuccess⟩ ∧
      ¬ (findFamily.contract sampleTypes).requires (4 : Nat)
        ⟨⟨sampleInputs, uninitializedSuccess⟩, samplePanic⟩ := by
  have rejected : ¬ SuccessInitialized uninitializedSuccess 4 sampleInputs := by
    intro ready
    obtain ⟨_, initialized⟩ := ready ⟨0, none, 255⟩ 4 rfl rfl
    cases initialized
  exact ⟨rfl, rejected, rejected⟩

/-- Raw execution is partial when assume_init has no initialized address. -/
theorem status_zero_without_initialization_has_no_outcome
    (before : Nat) (inputs : PdaInputs)
    (outcome : Outcome Nat (Option (Value × UInt8)) Nat Nat) :
    ¬ tryRun uninitializedSuccess before inputs outcome := by
  rintro ⟨actual, source, next⟩
  change actual = .returned ⟨0, none, 255⟩ before at source
  subst actual
  obtain ⟨result, decoded, _⟩ := next
  simp [decodePda] at decoded

/-- An uninitialized successful reply never reaches the local panic site of the find. -/
theorem uninitialized_success_has_no_find_outcome
    (panic : Callback.Run Nat SearchPanic Empty Nat Nat) (before : Nat)
    (inputs : PdaInputs) (outcome : Outcome Nat (Value × UInt8) Nat Nat) :
    ¬ findRun uninitializedSuccess panic before inputs outcome := by
  rintro ⟨actual, tried, _⟩
  exact status_zero_without_initialization_has_no_outcome before inputs actual tried

def mixedSuccess : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome =>
    outcome = .returned sampleReply (before + 7) ∨
      outcome = .returned ⟨0, none, 7⟩ (before + 8)

/-- An available good result cannot hide the other actual successful reply
whose missing output would be filtered by the decoder. -/
theorem mixed_success_is_not_admitted :
    tryRun mixedSuccess 3 sampleInputs (.returned (some (.zero, 254)) 10) ∧
      ¬ (tryFamily.contract sampleTypes).requires (3 : Nat) ⟨sampleInputs, mixedSuccess⟩ := by
  refine ⟨tryRun_returned mixedSuccess 3 10 sampleInputs sampleReply _
    (Or.inl rfl) ⟨.zero, rfl, rfl⟩, ?_⟩
  intro ready
  obtain ⟨_, initialized⟩ := ready ⟨0, none, 7⟩ (11 : Nat) (Or.inr rfl) rfl
  cases initialized

def returnedSyscall (reply : PdaReply) : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .returned reply (before + 4)

/-- Every nonzero status admits the absent or changed output slot and keeps
the exact ordinary None result and returned state. -/
theorem every_nonzero_reply_is_admitted (reply : PdaReply) (nonzero : reply.status ≠ 0) :
    (tryFamily.contract sampleTypes).requires (5 : Nat) ⟨sampleInputs, returnedSyscall reply⟩ ∧
      tryRun (returnedSyscall reply) 5 sampleInputs (.returned none 9) := by
  refine ⟨?_, tryRun_returned (returnedSyscall reply) 5 9 sampleInputs reply none rfl ?_⟩
  · intro actual after called zero
    cases called
    exact False.elim (nonzero zero)
  · simp only [decodePda, nonzero, ↓reduceIte]

theorem failed_syscall_is_admitted : SuccessInitialized failedStatusEight 5 sampleInputs := by
  intro reply after called zero
  cases called
  cases zero

def failedFindCall : FindCall sampleTypes :=
  ⟨⟨sampleInputs, failedStatusEight⟩, samplePanic⟩

theorem none_panics_using_actual_syscall_state :
    Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run sampleTypes
      (5 : Nat) failedFindCall (.unwound (91 : Nat) (20 : Nat)) :=
  findRun_retains failedStatusEight samplePanic 5 sampleInputs failed_syscall_is_admitted
    (.returned failedReply 9) rfl (.unwound 91 20) rfl

def terminalPanic : Callback.Run Nat SearchPanic Empty Nat Nat :=
  fun before _ outcome => outcome = .terminated (before + 100)

theorem none_can_terminate_from_actual_syscall_state :
    findRun failedStatusEight terminalPanic 5 sampleInputs (.terminated 109) :=
  ⟨.returned none 9, nonzero_status_ignores_uninitialized_output,
    .terminated 109, rfl, rfl⟩

def impossiblePanic : Callback.Run Nat SearchPanic Empty Nat Nat := fun _ _ _ => False

theorem success_never_calls_unwrap_panic :
    findRun sampleSyscall impossiblePanic 3 sampleInputs (.returned (.zero, 254) 10) :=
  ⟨.returned (some (.zero, 254)) 10, sampleTry_execution, rfl⟩

/-- A nonterminating/empty panic relation is not assigned an invented exit.
The syscall initialization law addresses decoding, not callback termination. -/
theorem nonzero_reply_does_not_invent_panic_exit :
    (findFamily.contract sampleTypes).requires (5 : Nat)
        ⟨⟨sampleInputs, failedStatusEight⟩, impossiblePanic⟩ ∧
      ¬ ∃ outcome, findRun failedStatusEight impossiblePanic 5 sampleInputs outcome := by
  refine ⟨failed_syscall_is_admitted, ?_⟩
  rintro ⟨outcome, exit, tried, continued⟩
  have actual := tryRun_post failedStatusEight 5 sampleInputs exit tried
  cases exit with
  | returned result after =>
      obtain ⟨reply, called, decoded⟩ := actual
      cases called
      have absent : result = none := decoded
      subst result
      obtain ⟨_, impossible, _⟩ := continued
      exact impossible
  | unwound _ _ => cases actual
  | terminated _ => cases actual

def pureSuccessInputs : PdaInputs := ⟨[], .zero⟩

def terminal77 : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun _ _ outcome => outcome = .terminated 77

def terminalFind77 : FindCall sampleTypes :=
  ⟨⟨pureSuccessInputs, terminal77⟩, impossiblePanic⟩

/-- Regression for the previous pure-only contract: a mathematical PDA answer
does not suppress a syscall terminal exit or force the local panic callback. -/
theorem pure_pda_answer_does_not_exclude_syscall_termination :
    tryFind witnessSearch = some (.zero, 255) ∧
    Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run sampleTypes
      (2 : Nat) terminalFind77 (.terminated (77 : Nat)) :=
  ⟨rfl, .terminated (77 : Nat), ⟨.terminated (77 : Nat), rfl, rfl⟩, rfl⟩

def unwindSyscall : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .unwound 67 (before + 6)

theorem syscall_unwind_preserves_state_without_unwrap :
    findRun unwindSyscall impossiblePanic 2 pureSuccessInputs (.unwound 67 8) :=
  ⟨.unwound 67 8, ⟨.unwound 67 8, rfl, rfl⟩, rfl⟩

theorem abnormal_providers_remain_admitted :
    (findFamily.contract sampleTypes).requires (2 : Nat) terminalFind77 ∧
      (findFamily.contract sampleTypes).requires (2 : Nat)
        ⟨⟨pureSuccessInputs, unwindSyscall⟩, impossiblePanic⟩ := by
  constructor <;> intro _ _ returned _ <;> cases returned

/-- The source-facing progress theorem consumes actual provider execution
and the minimal family admission, with no successful-call assumption. -/
theorem admitted_try_progress_uses_actual_provider :
    ∃ outcome, Solanalib.Specs.SolanaAddress.Address.try_find_program_address_solana_run sampleTypes
      (5 : Nat) ⟨sampleInputs, failedStatusEight⟩ outcome :=
  (Solanalib.Specs.SolanaAddress.Address.try_find_program_address_solana_hasOutcome_iff sampleTypes
    (5 : Nat) ⟨sampleInputs, failedStatusEight⟩ failed_syscall_is_admitted).2
      ⟨.returned failedReply (9 : Nat), rfl⟩

theorem no_local_seed_limit_precheck :
    (pdaRequest ⟨[List.replicate 33 7], .zero⟩).seedCount = 1 ∧
    findRun terminal77 impossiblePanic 2 ⟨[List.replicate 33 7], .zero⟩ (.terminated 77) :=
  ⟨rfl, .terminated 77, ⟨.terminated 77, rfl, rfl⟩, rfl⟩

/-- the null output of Address and the initialized scratch destination of the Curve SDK
are intentionally different primitive requests. -/
theorem address_null_differs_from_curve_sdk_scratch :
    (curveRequest .zero).curve = 0 ∧
    (curveRequest .zero).output = .nullPointer ∧
    (Curve.edwardsRequest Curve.samplePoint).initialScratch = 0 ∧
    CurveOutput.nullPointer ≠ .initializedByte 0 := by decide

def scratchOnly : Callback.Run Nat CurveRequest UInt64 Nat Nat :=
  fun before request outcome =>
    request.output = .initializedByte 0 ∧ outcome = .returned 0 (before + 4)

theorem scratch_provider_cannot_replace_address_null_call :
    ¬ curveRun scratchOnly 0 .zero (.returned true 4) := by
  rintro ⟨_, ⟨wrongDestination, _⟩, _⟩
  cases wrongDestination

def curveNonzero : Callback.Run Nat CurveRequest UInt64 Nat Nat :=
  fun before _ outcome => outcome = .returned 9 (before + 4)

theorem curve_nonzero_returns_false_with_effects :
    curveRun curveNonzero 2 .zero (.returned false 6) :=
  ⟨.returned (9 : UInt64) 6, rfl, rfl⟩

def curveTerminal : Callback.Run Nat CurveRequest UInt64 Nat Nat :=
  fun _ _ outcome => outcome = .terminated 88

theorem curve_syscall_terminal_is_preserved :
    curveRun curveTerminal 2 .zero (.terminated 88) :=
  ⟨.terminated 88, rfl, rfl⟩

def curveUnwind : Callback.Run Nat CurveRequest UInt64 Nat Nat :=
  fun before _ outcome => outcome = .unwound 81 (before + 9)

theorem curve_syscall_unwind_state_is_preserved :
    curveRun curveUnwind 2 .zero (.unwound 81 11) :=
  ⟨.unwound 81 11, rfl, rfl⟩

theorem curve_normal_projection_requires_register_agreement :
    NormalCurveAgreement curveNonzero witnessCrypto := by
  intro before _ status after returned
  change Outcome.returned status after = Outcome.returned (9 : UInt64) (before + 4) at returned
  cases returned
  rfl

theorem curve_projection_keeps_returned_state_observation :
    isOnCurve witnessCrypto .zero = false ∧
    curveRun curveNonzero 2 .zero (.returned false 6) :=
  ⟨(curveRun_returned_projection curveNonzero witnessCrypto
      curve_normal_projection_requires_register_agreement 2 6 .zero false
      curve_nonzero_returns_false_with_effects).symm,
    curve_nonzero_returns_false_with_effects⟩

end SolanalibTest.Specs.SolanaAddress.Syscalls

namespace SolanalibTest.Specs.SolanaAddress.Syscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Syscall

theorem selected_try_find_uses_actual_outputs :
    Solanalib.Specs.SolanaAddress.Address.try_find_program_address_solana_run sampleTypes
      (3 : Nat) sampleTryCall (.returned (some (.zero, 254)) (10 : Nat)) := sampleTry_execution

theorem selected_find_success_is_not_initial_bump_snapshot :
    (pdaRequest sampleInputs).bumpOutput = 255 ∧
    Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run sampleTypes
      (3 : Nat) sampleFindCall (.returned (.zero, 254) (10 : Nat)) :=
  ⟨rfl, sampleFind_execution⟩

def failedStatusThree : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun before _ outcome => outcome = .returned ⟨3, none, 1⟩ (before + 9)

theorem nonzero_uninitialized_try_output_is_none :
    tryRun failedStatusThree 2 sampleInputs (.returned none 11) := by
  apply tryRun_returned failedStatusThree 2 11 sampleInputs ⟨3, none, 1⟩ _ rfl
  simp [decodePda]

theorem local_panic_follows_actual_none_state :
    findRun failedStatusThree samplePanic 2 sampleInputs (.unwound 91 22) :=
  ⟨.returned none 11, nonzero_uninitialized_try_output_is_none,
    .unwound 91 22, rfl, rfl⟩

def terminal37 : Callback.Run Nat PdaRequest PdaReply Nat Nat :=
  fun _ _ outcome => outcome = .terminated 37

def terminalFind37 : FindCall sampleTypes :=
  ⟨⟨⟨[], .zero⟩, terminal37⟩, impossiblePanic⟩

theorem pure_answer_does_not_prevent_selected_syscall_terminal :
    tryFind witnessSearch = some (.zero, 255) ∧
    Solanalib.Specs.SolanaAddress.Address.find_program_address_solana_run sampleTypes
      (1 : Nat) terminalFind37 (.terminated (37 : Nat)) := by
  exact ⟨rfl, .terminated (37 : Nat), ⟨.terminated (37 : Nat), rfl, rfl⟩, rfl⟩

end SolanalibTest.Specs.SolanaAddress.Syscalls
