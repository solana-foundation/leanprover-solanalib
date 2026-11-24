/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.System

@[expose] public section

/-!
# Lamport conservation for System transfers

A successful `sysTransfer` preserves the sum of all transaction balances. Its
success premise includes the signature, data, ownership, writability, account
index and arithmetic checks of the runtime path. The proof also covers two
instruction positions that name the same transaction account.

Balances remain mathematical `Nat` values. `Account.WF` supplies their `u64`
bound for source correspondence; the conservation theorem itself needs only a
successful transfer and does not assume account well-formedness or distinctness.
-/

namespace Solanalib.Runtime

private theorem setLamports_delta {before after : TxState} {context : SetterCtx} {value : Nat}
    (written : setLamports before context value = .ok after) :
    after.lamportsDelta = before.lamportsDelta +
      ((value : Int) - (before.acct context.txIdx).lamports) := by
  unfold setLamports at written
  split at written
  · split at written
    · cases written
    · split at written
      · cases written
      · split at written
        · cases written
          rename_i unchanged
          simp [unchanged]
        · cases written
          rfl
  · cases written

private theorem checkedSubLamports_delta {before after : TxState} {context : SetterCtx}
    {amount : Nat} (written : checkedSubLamports before context amount = .ok after) :
    after.lamportsDelta = before.lamportsDelta - amount := by
  unfold checkedSubLamports at written
  split at written
  · cases written
  · have delta := setLamports_delta written
    omega

private theorem checkedAddLamports_delta {before after : TxState} {context : SetterCtx}
    {amount : Nat} (written : checkedAddLamports before context amount = .ok after) :
    after.lamportsDelta = before.lamportsDelta + amount := by
  unfold checkedAddLamports at written
  split at written
  · cases written
  · have delta := setLamports_delta written
    omega

/-- The checked debit and credit conserve the total even when their account indices coincide. -/
theorem sysTransferVerified_preserves_total {context : SysCtx} {before after : TxState}
    {source destination amount : Nat}
    (transferred : sysTransferVerified context before source destination amount = .ok after) :
    after.lamportSum = before.lamportSum := by
  unfold sysTransferVerified at transferred
  dsimp only at transferred
  split at transferred
  · cases transferred
  · split at transferred
    · cases transferred
    · split at transferred
      · cases transferred
      · rename_i middle debited
        have debitBalance := (SetterStep.of_checkedSubLamports debited).balance
        have creditBalance := (SetterStep.of_checkedAddLamports transferred).balance
        have debitDelta := checkedSubLamports_delta debited
        have creditDelta := checkedAddLamports_delta transferred
        omega

/-- A successful System transfer preserves the sum of all balances in the transaction. -/
theorem transfer_preserves_total {context : SysCtx} {before after : TxState}
    {source destination amount : Nat}
    (transferred : sysTransfer context before source destination amount = .ok after) :
    after.lamportSum = before.lamportSum := by
  unfold sysTransfer at transferred
  split at transferred
  · cases transferred
  · exact sysTransferVerified_preserves_total transferred

end Solanalib.Runtime
