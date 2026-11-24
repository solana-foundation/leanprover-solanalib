/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Message

@[expose] public section

/-!
# Consistent instruction privileges

Message frames and prepared CPI frames give every occurrence of a transaction
account the same flags. For a caller with this property, the flag queries based
on `List.any` agree with the first caller occurrence selected by Agave 4.3.2
`program-runtime/src/invoke_context.rs:434-459`.

The construction lemmas do not require additional message or transaction
well-formedness assumptions. The privilege-check correspondence requires
consistency of the caller being checked; consistency of the newly prepared
callee does not replace that premise.
-/

namespace Solanalib.Runtime

/-- Top-level message flags depend only on the transaction-account index. -/
theorem message_frame_flagsConsistent (p : Profile) (m : Message) (ix : CompiledIx) :
    (Message.frame p m ix).FlagsConsistent := by
  intro a ha b hb same
  simp only [Message.frame, List.mem_map] at ha hb
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hb
  cases same
  rfl

private theorem calleeAccounts_lookup {ts : TxState} {ix : CpiInstruction}
    {dedup : List InstrAcct} {account : InstrAcct}
    (member : account ∈ calleeAccounts ts ix dedup) :
    dedup.find? (fun candidate => candidate.txIdx == account.txIdx) = some account := by
  obtain ⟨metadata, _, found⟩ := List.mem_filterMap.mp member
  cases index : txIndexOf ts metadata.key with
  | none => simp [index] at found
  | some i =>
    have lookup : dedup.find? (fun candidate => candidate.txIdx == i) = some account := by
      simpa [index] using found
    have sameIndex : account.txIdx = i := by
      simpa using List.find?_some lookup
    simpa [sameIndex] using lookup

/-- Re-expansion always selects the same account for a transaction index,
even without an invariant on the input list named `dedup`. -/
theorem calleeAccounts_flagsConsistent (ts : TxState) (ix : CpiInstruction)
    (dedup : List InstrAcct) (programIdx : Nat) (data : Bytes) :
    (⟨programIdx, calleeAccounts ts ix dedup, data⟩ : Frame).FlagsConsistent := by
  intro a ha b hb same
  have first := calleeAccounts_lookup ha
  have second := calleeAccounts_lookup hb
  rw [same] at first
  exact Option.some.inj (first.symm.trans second)

/-- Every successful preparation constructs a consistent callee frame. This
does not assume consistency of the caller supplied to preparation. -/
theorem prepareCallee_flagsConsistent {ts : TxState} {f g : Frame}
    {ix : CpiInstruction} {pdas : List Pubkey} :
    prepareCallee ts f ix pdas = .ok g → g.FlagsConsistent := by
  intro prepared
  unfold prepareCallee at prepared
  split at prepared
  · cases prepared
  · rename_i dedup merged
    split at prepared
    · cases prepared
    · split at prepared
      · cases prepared
      · rename_i pia found
        cases prepared
        exact calleeAccounts_flagsConsistent ts ix dedup pia.txIdx ix.data

private theorem flagsConsistent_any {f : Frame} (consistent : f.FlagsConsistent)
    {account : InstrAcct} (member : account ∈ f.accounts) {t : Nat}
    (index : account.txIdx = t) (flag : InstrAcct → Bool) :
    f.accounts.any (fun candidate => candidate.txIdx == t && flag candidate) = flag account := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨candidate, present, sameIndex, selected⟩
    have same := consistent candidate present account member (sameIndex.trans index.symm)
    simpa [same] using selected
  · intro selected
    exact ⟨account, member, index, selected⟩

/-- The optional indexing result supplies the selected account without a
separate index-bound hypothesis. Both queries equal its flags. -/
theorem flagsConsistent_queries {f : Frame} (consistent : f.FlagsConsistent) {t j : Nat}
    (found : f.firstIdx t = some j) :
    ∃ account : InstrAcct, f.accounts[j]? = some account ∧
      f.writableTx t = account.writable ∧ f.signerTx t = account.signer := by
  obtain ⟨bound, predicate, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  let account : InstrAcct := f.accounts[j]
  have member : account ∈ f.accounts := List.getElem_mem bound
  have index : account.txIdx = t := by simpa [account] using predicate
  exact ⟨account, List.getElem?_eq_getElem bound,
    flagsConsistent_any consistent member index InstrAcct.writable,
    flagsConsistent_any consistent member index InstrAcct.signer⟩

/-- For a consistent caller, privilege checks have the first-occurrence form:
caller membership, writable privilege, then signer privilege or a derived signer.
The premise concerns the caller, not the result of preparing the callee. -/
theorem checkPrivileges_first {ts : TxState} {caller : Frame} {pdas : List Pubkey}
    {account : InstrAcct} (consistent : caller.FlagsConsistent) :
    checkPrivileges ts caller pdas account =
      match caller.accounts.find? (fun candidate => candidate.txIdx == account.txIdx) with
      | none => .error .MissingAccount
      | some first =>
        if account.writable && !first.writable then .error .PrivilegeEscalation
        else if account.signer && !(first.signer || pdas.contains (ts.key account.txIdx)) then
          .error .PrivilegeEscalation
        else .ok () := by
  cases found : caller.accounts.find? (fun candidate => candidate.txIdx == account.txIdx) with
  | none =>
    have missing : caller.hasTx account.txIdx = false := by
      simpa [Frame.hasTx] using List.find?_eq_none.mp found
    simp [checkPrivileges, missing]
  | some first =>
    have member : first ∈ caller.accounts := List.mem_of_find?_eq_some found
    have index : first.txIdx = account.txIdx := by
      simpa using List.find?_some found
    have present : caller.hasTx account.txIdx = true := by
      simp only [Frame.hasTx, List.any_eq_true, beq_iff_eq]
      exact ⟨first, member, index⟩
    have writable := flagsConsistent_any consistent member index InstrAcct.writable
    have signer := flagsConsistent_any consistent member index InstrAcct.signer
    simp only [checkPrivileges, present, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Frame.writableTx, Frame.signerTx, writable, signer]

end Solanalib.Runtime
