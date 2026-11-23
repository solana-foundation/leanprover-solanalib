/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestOnchainContract

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenOnchainAdmission

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Onchain

/-- The mint points at the existing lamports cell; every other argument is the
ordinary aliasing fixture, including the accepted Token program. -/
def wrongMintArgs : Args :=
  { witnessArgs with mint := { witnessInfo with data := witnessInfo.lamports } }

/-- The malformed input really acquires a live guard before the typed read
fails; this is not an invented missing provider result. -/
theorem wrong_mint_borrow_succeeds :
    AccountInfo.tryBorrow .shared wrongMintArgs.mint.data witnessState =
      (.ok ⟨0, 0⟩, (witnessState.issue wrongMintArgs.mint.data .shared .whole).2) := rfl

/-- Current lamports storage is the exact failed typed read. -/
theorem wrong_mint_current_is_lamports :
    Borrow.current (witnessState.issue wrongMintArgs.mint.data .shared .whole).2 ⟨0, 0⟩ =
      .ok (.whole, .lamports 40) := rfl

/-- The unchanged pure preparation exposes its existing malformed branch. -/
theorem wrong_mint_preparation_malformed :
    (prepare witnessState wrongMintArgs).1 = .malformed := rfl

/-- The new local requirement rejects the exact previously erased path. -/
theorem wrong_mint_entry_rejected : ¬ PreparationReady witnessState wrongMintArgs := by
  intro ready
  exact prepare_not_malformed ready wrong_mint_preparation_malformed

/-- A provider that has no finite exits; the wrapper must not manufacture one. -/
def absentProvider : CpiRequest.Invocation (State × Nat) Onchain.Account Error Nat Nat :=
  fun _ _ _ => False

/-- No CPI provider can repair a malformed local preparation. -/
theorem malformed_path_has_no_raw_exit :
    ¬ ∃ outcome, run sampleTypes (witnessState, (0 : Nat))
      ⟨wrongMintArgs, absentProvider⟩ outcome := by
  rintro ⟨outcome, impossible⟩
  exact impossible

/-- Invalid program admission precedes all storage reads and scalar encoding. -/
def earlyCall : Call sampleTypes where
  args := { wrongMintArgs with
    tokenProgramId := .zero
    amount := Solanalib.Runtime.U64_LIMIT + 1
    decimals := 999
    profile := { witnessArgs.profile with wordBits := 1 } }
  invoke := absentProvider

/-- No broad width or AccountInfo-validity gate is restored on the early error. -/
theorem early_error_is_admitted :
    (invokeTransferCheckedFamily.contract sampleTypes).requires (⟨[], []⟩, (0 : Nat)) earlyCall :=
  True.intro

/-- The rejected program has its actual finite error even when storage is
absent and the CPI provider has no exit. -/
theorem early_error_executes :
    run sampleTypes (⟨[], []⟩, (0 : Nat)) earlyCall
      (.returned (.error .IncorrectProgramId) (⟨[], []⟩, (0 : Nat))) := rfl

/-- This early error is admitted without conditions on the later instruction arguments. -/
theorem early_error_outside_old_widths : ¬ earlyCall.args.Valid ⟨[], []⟩ := by
  intro valid
  have impossible : 32 ≤ 1 := valid.1
  contradiction

/-- A preexisting exclusive lease on the malformed mint cell blocks its read. -/
def lockedWrongMint : State :=
  (Borrow.acquire witnessState wrongMintArgs.mint.data .exclusive AccountInfo.View.whole).2

/-- A checked borrow error does not need a later typed data projection. -/
theorem checked_error_skips_wrong_content :
    PreparationReady lockedWrongMint wrongMintArgs ∧
      prepare lockedWrongMint wrongMintArgs = (.error .AccountBorrowFailed, lockedWrongMint) := by
  constructor
  · with_unfolding_all repeat' constructor
  · rfl

/-- A missing mathematical mint handle follows the raw checked-error path. -/
def absentMintArgs : Args := { witnessArgs with mint := { witnessInfo with data := ⟨99⟩ } }

/-- This control describes the mathematical error branch, not permission to
construct a dangling Rust AccountInfo. No data read follows the borrow error. -/
theorem missing_checked_cell_keeps_error :
    PreparationReady witnessState absentMintArgs ∧
      prepare witnessState absentMintArgs = (.error .AccountBorrowFailed, witnessState) := by
  constructor
  · with_unfolding_all repeat' constructor
  · rfl

/-- A short but correctly typed mint buffer. -/
def shortMintState : State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [7], AccountInfo.sampleProfile.policy⟩], []⟩

/-- Byte-format errors remain ordinary errors and release their actual token. -/
theorem short_mint_error_releases :
    PreparationReady shortMintState witnessArgs ∧
      prepare shortMintState witnessArgs =
        (.error .InvalidAccountData, { shortMintState with slots := [none] }) := by
  constructor
  · with_unfolding_all repeat' constructor
  · rfl

/-- A correctly sized uninitialized mint retains the distinct parser error. -/
def uninitializedMintState : State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data (List.replicate 82 0), AccountInfo.sampleProfile.policy⟩], []⟩

/-- Initialization failure is admitted and drops the mint guard. -/
theorem uninitialized_mint_error_releases :
    PreparationReady uninitializedMintState witnessArgs ∧
      prepare uninitializedMintState witnessArgs =
        (.error .UninitializedAccount, { uninitializedMintState with slots := [none] }) := by
  constructor
  · with_unfolding_all repeat' constructor
  · rfl

/-- The multisig reader observes a source-local out-of-range signer count. -/
def multisigState : State :=
  { witnessState with cells := witnessState.cells ++
    [⟨.data ([1, 12, 0] ++ List.replicate 352 0), AccountInfo.sampleProfile.policy⟩] }

/-- A recognized multisig authority; the later mint remains malformed. -/
def multisigArgs : Args :=
  { wrongMintArgs with authority := { witnessInfo with owner := legacyProgramId, data := ⟨2⟩ } }

-- The primitive lemmas are at default limits. Reducing this closed 355-byte
-- fixture exhausted the default recursion limit; the exception is local.
set_option maxRecDepth 2048 in
/-- An early multisig panic bypasses the bad mint and retires both actual
getter/parser guards. The count is not sanitized into a ProgramError. -/
theorem multisig_panic_skips_mint_and_releases :
    PreparationReady multisigState multisigArgs ∧
      prepare multisigState multisigArgs =
        (.panic .multisigSignerRange, { multisigState with slots := [none, none] }) := by
  constructor
  · with_unfolding_all repeat' constructor
  · decide +kernel

-- This exact finite panic control traverses the same 355-byte fixture.
set_option maxRecDepth 2048 in
/-- The unwinding profile exposes the post-cleanup state of that actual panic. -/
theorem local_unwind_keeps_cleanup :
    run sampleTypes (multisigState, (3 : Nat))
      ⟨{ multisigArgs with profile := { multisigArgs.profile with aborts := false } },
        absentProvider⟩
      (.unwound (.inl .multisigSignerRange)
        ({ multisigState with slots := [none, none] }, (3 : Nat))) := by
  rfl

-- This exact finite panic control traverses the same 355-byte fixture.
set_option maxRecDepth 2048 in
/-- The aborting profile has the same local panic kind and no invented state. -/
theorem local_abort_keeps_kind :
    run sampleTypes (multisigState, (3 : Nat))
      ⟨{ multisigArgs with profile := { multisigArgs.profile with aborts := true } },
        absentProvider⟩
      (.terminated (.inl .multisigSignerRange)) := by
  rfl

/-- A hook identity distinct from the zero validation-PDA fixture. -/
def hookId : Solanalib.Runtime.Pubkey := .ofNat 99
/-- A resolved extra account with its own data cell. -/
def extraInfo : AccountInfo.Value := { witnessInfo with key := .ofNat 88, data := ⟨3⟩ }
/-- The validation account retains a distinct byte buffer. -/
def validationInfo : AccountInfo.Value := { witnessInfo with key := .zero, data := ⟨2⟩ }
/-- The hook program account is looked up but its bytes are not collected. -/
def hookInfo : AccountInfo.Value := { witnessInfo with key := hookId, data := ⟨3⟩ }
/-- An initialized mint with one TransferHook TLV payload. -/
def hookMintBytes : Bytes :=
  witnessMintBytes ++ List.replicate 83 0 ++ [1, 14, 0, 64, 0] ++
    List.replicate 32 0 ++ hookId.bytes
/-- The validation list has one nonempty static extra-meta record. -/
def validationBytes : Bytes :=
  Hook.executeDiscriminator ++ Solanalib.Runtime.u32le 39 ++ Solanalib.Runtime.u32le 1 ++
    [0] ++ extraInfo.key.bytes ++ [7, 255]
/-- Two outer scopes surround a nonempty five-account collection with aliases. -/
def hookState : State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data hookMintBytes, AccountInfo.sampleProfile.policy⟩,
    ⟨.data validationBytes, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [], AccountInfo.sampleProfile.policy⟩], []⟩
/-- Additional accounts are searched by key, in this concrete order. -/
def hookArgs : Args :=
  { witnessArgs with additional := [hookInfo, validationInfo, extraInfo] }

-- The decomposed primitive guarantees above use default budgets. Computing
-- this finite seven-guard fixture exceeded the default recursion limit.
set_option maxRecDepth 2048 in
/-- The actual nested nonempty path satisfies the composed local requirements. -/
theorem nested_hook_admitted : PreparationReady hookState hookArgs := by
  with_unfolding_all repeat' constructor

/-- All five collected guards and both enclosing guards are actually retired. -/
theorem nested_hook_cleanup :
    (prepare hookState hookArgs).2.slots = List.replicate 7 none := by
  decide +kernel

/-- The resolved extra, validation and hook accounts retain their source order. -/
theorem nested_hook_order :
    ((prepare hookState hookArgs).1 = .success {
      instruction := { witnessPrepared.instruction with metas := witnessPrepared.instruction.metas
        ++
        [Instruction.accountMeta extraInfo.key false true,
          Instruction.accountMeta validationInfo.key false false,
          Instruction.accountMeta hookInfo.key false false] }
      accounts := witnessPrepared.accounts ++ [extraInfo, validationInfo, hookInfo] }) := by
  decide +kernel

/-- Redirecting only the reached validation read to lamports recreates a
malformed nested prefix even though the outer mint read is valid. -/
def wrongValidationArgs : Args :=
  { hookArgs with additional := [hookInfo, { validationInfo with data := ⟨0⟩ }, extraInfo] }

/-- Independent body admission prevents a bad nested read from hiding behind
the successful release of the outer scope. -/
theorem malformed_nested_read_rejected :
    (prepare hookState wrongValidationArgs).1 = .malformed ∧
      ¬ PreparationReady hookState wrongValidationArgs := by
  have malformed : (prepare hookState wrongValidationArgs).1 = .malformed := by decide +kernel
  exact ⟨malformed, fun ready => prepare_not_malformed ready malformed⟩

/-- A synthetic local body destroys its held token before returning an error.
This tests the shared scope rule, without changing ordinary preparation. -/
def destroysGuard (during : State) (_ : Bytes) : Step Unit × State :=
  (.error .InvalidArgument, { during with slots := [] })

/-- Raw cleanup cannot invent a release for a destroyed token. -/
theorem destroyed_scope_rejected :
    ¬ ScopeReady true witnessState witnessInfo destroysGuard (fun _ _ => True) := by
  intro ready
  have safe := withData_not_malformed ready (fun _ _ _ => by simp [destroysGuard])
  exact safe rfl

/-- One provider exposes all four finite exit forms with distinct state effects. -/
def mixedProvider : CpiRequest.Invocation (State × Nat) Onchain.Account Error Nat Nat :=
  fun before request result =>
    result = .returned (.ok ()) (before.1, before.2 + request.accounts.length) ∨
    result = .returned (.error .InsufficientFunds) (before.1, before.2 + 8) ∨
    result = .unwound 17 (before.1, before.2 + 12) ∨
    result = .terminated 23

/-- The same admitted preparation is paired with that nondeterministic provider. -/
def mixedCall : Call sampleTypes := ⟨witnessArgs, mixedProvider⟩

/-- Every actual finite provider exit is retained, not merely one chosen sample. -/
theorem every_provider_exit_retained :
    ∀ result, mixedProvider (witnessAfter, (0 : Nat))
      (witnessPrepared.request witnessArgs.signers) result →
      run sampleTypes (witnessState, (0 : Nat)) mixedCall (providerOutcome result) := by
  have retained := run_retains (types := sampleTypes) (before := (witnessState, (0 : Nat)))
    (call := mixedCall) witness_ready
  simpa only [mixedCall, witness_prepares, sampleTypes] using retained

/-- Success, ordinary error, unwind effects and terminal reason all survive
the same local preparation. This is not a provider success guarantee. -/
theorem all_provider_exit_forms_execute :
    run sampleTypes (witnessState, (0 : Nat)) mixedCall
      (.returned (.ok ()) (witnessAfter, (4 : Nat))) ∧
    run sampleTypes (witnessState, (0 : Nat)) mixedCall
      (.returned (.error .InsufficientFunds) (witnessAfter, (8 : Nat))) ∧
    run sampleTypes (witnessState, (0 : Nat)) mixedCall
      (.unwound (.inr (17 : Nat)) (witnessAfter, (12 : Nat))) ∧
    run sampleTypes (witnessState, (0 : Nat)) mixedCall (.terminated (.inr (23 : Nat))) := by
  refine ⟨every_provider_exit_retained _ (Or.inl rfl),
    every_provider_exit_retained _ (Or.inr (Or.inl rfl)),
    every_provider_exit_retained _ (Or.inr (Or.inr (Or.inl rfl))),
    every_provider_exit_retained _ (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- Admitted local preparation does not imply an opaque provider terminates. -/
theorem absent_provider_has_no_invented_exit :
    ¬ ∃ outcome, run sampleTypes (witnessState, (0 : Nat))
      ⟨witnessArgs, absentProvider⟩ outcome := by
  intro execution
  have reached := (run_hasOutcome_iff (types := sampleTypes) (before := (witnessState, (0 : Nat)))
    (call := ⟨witnessArgs, absentProvider⟩)
    witness_ready).mp execution witnessPrepared witnessAfter witness_prepares
  obtain ⟨_, impossible⟩ := reached
  exact impossible

end SolanalibTest.Specs.Core.TokenOnchainAdmission
