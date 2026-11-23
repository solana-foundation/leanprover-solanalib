/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Transfer

/-!
# System transfer regressions

The concrete successful case exercises the general conservation theorem. Additional
cases cover zero transfers, a fully drained source, aliased instruction accounts,
and the signature, data, ownership, writability, index and arithmetic checks.
-/

namespace SolanalibTest.Transfer

open Solanalib.Runtime

private def sender : Account := ⟨100, [], Ids.systemProgram, false, 0⟩
private def recipient : Account := ⟨20, [], Ids.systemProgram, false, 0⟩

private def before : TxState where
  keys := [Pubkey.ofNat 1, Pubkey.ofNat 2, Ids.systemProgram]
  accts := [sender, recipient, ⟨1, [], Ids.nativeLoader, true, 0⟩]
  lamportsDelta := 0
  resizeDelta := 0
  stack := []
  trace := []
  returnData := (Ids.systemProgram, [])
  topIndex := 0

private def frame : Frame :=
  { programIdx := 2, accounts := [⟨0, true, true⟩, ⟨1, false, true⟩], data := [] }

private def context : SysCtx := ⟨before, frame, .agave_4_3_2⟩

private def after : TxState :=
  { before with
    accts := [{ sender with lamports := 93 }, { recipient with lamports := 27 }, before.acct 2]
    touched := [1, 0] }

example : sender.WF ∧ recipient.WF := by cbv

example : after.lamportSum = before.lamportSum := by
  exact transfer_preserves_total (context := context) (source := 0) (destination := 1)
    (amount := 7) (by cbv)

example : (sysTransfer context before 0 1 100).map (fun state =>
    ((state.acct 0).lamports, (state.acct 1).lamports, state.lamportsDelta)) =
    .ok (0, 120, 0) := by cbv

example : (sysTransfer context before 0 1 0).map (fun state =>
    (state.accts, state.lamportsDelta, state.touched)) =
    .ok (before.accts, 0, []) := by cbv

-- Distinct instruction positions can refer to the same transaction account.
private def aliased : SysCtx :=
  { context with f := { frame with accounts := [⟨0, true, true⟩, ⟨0, true, true⟩] } }

example : (sysTransfer aliased before 0 1 7).map (fun state =>
    (state.accts, state.lamportsDelta, state.touched)) =
    .ok (before.accts, 0, [0, 0]) := by cbv

example : (sysTransfer context before 0 0 7).map (fun state =>
    (state.accts, state.lamportsDelta)) = .ok (before.accts, 0) := by cbv

example : sysTransfer context before 0 1 101 = .error (sysErr 1) := by cbv

example : sysTransfer context
    (before.setAcct 1 { recipient with lamports := U64_MAX }) 0 1 1 =
    .error .ArithmeticOverflow := by cbv

example : sysTransfer { context with f := { frame with
    accounts := [⟨0, false, true⟩, ⟨1, false, true⟩] } } before 0 1 7 =
    .error .MissingRequiredSignature := by cbv

example : sysTransfer context (before.setAcct 0 { sender with data := [1] }) 0 1 7 =
    .error .InvalidArgument := by cbv

example : sysTransfer context
    (before.setAcct 0 { sender with owner := Pubkey.ofNat 3 }) 0 1 7 =
    .error .ExternalAccountLamportSpend := by cbv

-- Writability is required even for a zero debit or zero credit.
example : sysTransfer { context with f := { frame with
    accounts := [⟨0, true, false⟩, ⟨1, false, true⟩] } } before 0 1 0 =
    .error .ReadonlyLamportChange := by cbv

example : sysTransfer { context with f := { frame with
    accounts := [⟨0, true, true⟩, ⟨1, false, false⟩] } } before 0 1 0 =
    .error .ReadonlyLamportChange := by cbv

example : sysTransfer { context with f := { frame with
    accounts := [⟨0, true, true⟩, ⟨3, false, true⟩] } } before 0 1 7 =
    .error .MissingAccount := by cbv

end SolanalibTest.Transfer
