/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Cpi

@[expose] public section

/-!
# CPI preparation order

These cases distinguish the three passes of Agave 4.3.2
`prepare_next_cpi_instruction` (`program-runtime/src/invoke_context.rs:349-495`):
transaction lookup and duplicate merging, caller membership and privileges per
first occurrence, then callee-program lookup. They inspect preparation only;
the invoked program remains an external execution boundary.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.CpiOrdering

def accountA : Pubkey := Pubkey.ofNat 101
def accountB : Pubkey := Pubkey.ofNat 102
def calleeKey : Pubkey := Pubkey.ofNat 103
def callerKey : Pubkey := Pubkey.ofNat 104
def absentKey : Pubkey := Pubkey.ofNat 105

def state : TxState where
  keys := [accountA, accountB, calleeKey, callerKey]
  accts := List.replicate 4 ⟨1000000, [], Ids.systemProgram, false, 0⟩
  lamportsDelta := 0
  resizeDelta := 0
  stack := []
  trace := []
  returnData := (Ids.systemProgram, [])
  topIndex := 0

/-- A is readonly and unsigned; B is in the transaction but absent from the caller. -/
def caller : Frame where
  programIdx := 3
  accounts := [⟨0, false, false⟩, ⟨2, false, false⟩]
  data := []

/-- An earlier writable escalation is reported before a later missing caller account. -/
theorem writable_before_missing_caller :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 0, 1⟩, ⟨accountB, 0, 0⟩], []⟩ [] =
      .error .PrivilegeEscalation := rfl

/-- Reversing those accounts reverses which failed check is reached first. -/
theorem missing_caller_before_writable :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountB, 0, 0⟩, ⟨accountA, 0, 1⟩], []⟩ [] =
      .error .MissingAccount := rfl

/-- A missing transaction account is detected in the first pass, even after a
meta that would fail its caller privilege check in the second pass. -/
theorem missing_transaction_before_writable :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 0, 1⟩, ⟨absentKey, 0, 0⟩], []⟩ [] =
      .error .MissingAccount := rfl

/-- A later duplicate strengthens A before the second pass reaches the absent B. -/
theorem duplicate_writable_before_missing_caller :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 0, 0⟩, ⟨accountB, 0, 0⟩, ⟨accountA, 0, 1⟩], []⟩ [] =
      .error .PrivilegeEscalation := rfl

/-- Duplicate merging preserves the order of first occurrence. -/
theorem missing_caller_before_duplicate_writable :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountB, 0, 0⟩, ⟨accountA, 0, 0⟩, ⟨accountA, 0, 1⟩], []⟩ [] =
      .error .MissingAccount := rfl

/-- Signer escalation has the same per-account priority as writable escalation. -/
theorem signer_before_missing_caller :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 1, 0⟩, ⟨accountB, 0, 0⟩], []⟩ [] =
      .error .PrivilegeEscalation := rfl

theorem missing_caller_before_signer :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountB, 0, 0⟩, ⟨accountA, 1, 0⟩], []⟩ [] =
      .error .MissingAccount := rfl

theorem missing_transaction_before_signer :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 1, 0⟩, ⟨absentKey, 0, 0⟩], []⟩ [] =
      .error .MissingAccount := rfl

theorem duplicate_signer_before_missing_caller :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 0, 0⟩, ⟨accountB, 0, 0⟩, ⟨accountA, 1, 0⟩], []⟩ [] =
      .error .PrivilegeEscalation := rfl

/-- PDA authority discharges A, so the later missing caller account is reached. -/
theorem pda_signer_then_missing_caller :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountA, 1, 0⟩, ⟨accountB, 0, 0⟩], []⟩ [accountA] =
      .error .MissingAccount := rfl

/-- Membership is required even when a missing caller account has PDA authority. -/
theorem pda_does_not_supply_caller_membership :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountB, 1, 0⟩], []⟩ [accountB] =
      .error .MissingAccount := rfl

/-- An absent caller account requesting a write fails membership, not privileges. -/
theorem same_account_membership_before_writable :
    prepareCallee state caller
      ⟨calleeKey, [⟨accountB, 0, 1⟩], []⟩ [] =
      .error .MissingAccount := rfl

/-- Privilege checks precede the final callee-program lookup. -/
theorem writable_before_missing_program :
    prepareCallee state caller
      ⟨absentKey, [⟨accountA, 0, 1⟩], []⟩ [] =
      .error .PrivilegeEscalation := rfl

theorem valid_accounts_then_missing_program :
    prepareCallee state caller
      ⟨absentKey, [⟨accountA, 0, 0⟩], []⟩ [] =
      .error .MissingAccount := rfl

/-- On success, every duplicate position receives both merged privileges. -/
theorem successful_duplicate_flags :
    prepareCallee state
      { caller with accounts := [⟨0, true, true⟩, ⟨2, false, false⟩] }
      ⟨calleeKey, [⟨accountA, 0, 0⟩, ⟨accountA, 1, 0⟩, ⟨accountA, 0, 1⟩], [7]⟩ [] =
      .ok { programIdx := 2
            accounts := [⟨0, true, true⟩, ⟨0, true, true⟩, ⟨0, true, true⟩]
            data := [7] } := rfl

/-- A derived signer permits an unsigned caller account without making it writable. -/
theorem successful_pda_signer :
    prepareCallee state caller ⟨calleeKey, [⟨accountA, 1, 0⟩], []⟩ [accountA] =
      .ok { programIdx := 2, accounts := [⟨0, true, false⟩], data := [] } := rfl

end SolanalibTest.Runtime.CpiOrdering
