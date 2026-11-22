/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Account
public import Solanalib.Runtime.Error
public import Solanalib.Runtime.ProgramCache

@[expose] public section

/-!
# Transaction context

The mathematical state corresponding to the observable parts of `TransactionContext`:
the accounts with their addresses, the transaction-wide lamport and resize counters,
the instruction stack, the instruction trace, the return data and the index of the
current top-level instruction. Its correspondence with Agave 4.3.2, including the
numeric bounds and the abstraction of error states, is described in
[execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit).
-/

namespace Solanalib.Runtime

/-- An instruction account: an index into the accounts of the transaction with the
signer and writable flags of the instruction (`InstructionAccount`). -/
structure InstrAcct where
  txIdx : Nat
  signer : Bool
  writable : Bool
  deriving DecidableEq, Repr, Inhabited

/-- An instruction as the transaction context holds it: the transaction index of the
program account, the instruction accounts in order, and the instruction data. -/
structure Frame where
  programIdx : Nat
  accounts : List InstrAcct
  data : Bytes
  deriving DecidableEq, Repr

/-- An entry of the instruction trace: the stack height at which the instruction ran,
and the instruction. -/
structure TraceEntry where
  height : Nat
  frame : Frame
  deriving DecidableEq, Repr

/-- The transaction context. -/
structure TxState where
  keys : List Pubkey
  accts : List Account
  /-- `lamports_delta`, the signed sum of all balance changes applied through
  `set_lamports` in the transaction. Agave 4.3.2 stores this as an `i128`; the
  mathematical integer needs bounded runtime accounts for correspondence. -/
  lamportsDelta : Int
  /-- `resize_delta`, the signed sum of all data-length changes, represented here
  as an unbounded mathematical integer. -/
  resizeDelta : Int
  /-- The instruction stack, the current instruction first. -/
  stack : List Frame
  /-- The instruction trace in push order. -/
  trace : List TraceEntry
  /-- The return data: the id of the program that set it, and the bytes. -/
  returnData : Pubkey × Bytes
  /-- The index of the current top-level instruction, which `push` writes into the
  Instructions sysvar; see
  [message privileges and the Instructions
  sysvar](../../source-notes/agave-4.3.2.md#message-privileges-and-instructions-sysvar). -/
  topIndex : Nat
  /-- Account indices marked by runtime mutation operations. These are execution
  metadata, not a comparison of the final and initial account values
  (`transaction-context/src/transaction_accounts.rs:238-290`, Agave 4.3.2). -/
  touched : List Nat := []
  /-- Cache entries changed by successful loader management. Lookup consults
  these entries before the initial cache supplied by the bank. The same overlay
  is threaded through top-level instructions and CPI. -/
  modifiedPrograms : ProgramCacheChanges := []
  deriving Repr

namespace TxState

/-- The account at transaction index `i`. -/
def acct (ts : TxState) (i : Nat) : Account := ts.accts.getD i default

/-- The address at transaction index `i`. -/
def key (ts : TxState) (i : Nat) : Pubkey := ts.keys.getD i default

/-- Replace an account as a runtime mutation and retain its touched flag. -/
def setAcct (ts : TxState) (i : Nat) (a : Account) : TxState :=
  { ts with
    accts := ts.accts.set i a
    touched := if i < ts.accts.length then i :: ts.touched else ts.touched }

/-- The sum of all balances, which `execute_loaded_transaction` in Agave 4.3.2
compares before and after execution as a `u128`. The mathematical sum agrees under
the runtime account-count and balance bounds; see
[execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
def lamportSum (ts : TxState) : Nat := (ts.accts.map Account.lamports).sum

/-- The key of the program of the current instruction. -/
def currentProgram (ts : TxState) : Option Pubkey :=
  ts.stack.head?.map fun f => ts.key f.programIdx

/-- The transaction index of the Instructions sysvar account, if the transaction has one. -/
def ixSysvarIdx (ts : TxState) : Option Nat := ts.keys.idxOf? Ids.sysvarInstructions

@[simp] theorem acct_setAcct_self (ts : TxState) (i : Nat) (a : Account)
    (h : i < ts.accts.length) : (ts.setAcct i a).acct i = a := by
  simp [setAcct, acct, List.getD_eq_getElem?_getD, h]

@[simp] theorem acct_setAcct_ne (ts : TxState) (i j : Nat) (a : Account) (h : i ≠ j) :
    (ts.setAcct i a).acct j = ts.acct j := by
  simp [setAcct, acct, List.getD_eq_getElem?_getD, h]

@[simp] theorem length_setAcct (ts : TxState) (i : Nat) (a : Account) :
    (ts.setAcct i a).accts.length = ts.accts.length := by
  simp [setAcct]

@[simp] theorem keys_setAcct (ts : TxState) (i : Nat) (a : Account) :
    (ts.setAcct i a).keys = ts.keys := rfl

end TxState

/-- The native `TransactionContext::set_return_data` operation. Native callers
supply the program tag and bytes directly; the SBF syscall adds its own current
program tag and size check before calling this operation. -/
def setNativeReturnData (ts : TxState) (programId : Pubkey) (data : Bytes) : TxState :=
  { ts with returnData := (programId, data) }

/-- Runtime touch flags only grow. An account without a final touch retains its
value, except for the administrative update of the Instructions sysvar. -/
structure TouchChanges (before after : TxState) : Prop where
  keys : after.keys = before.keys
  mono : ∀ i, i ∈ before.touched → i ∈ after.touched
  untouched : ∀ i, i ∉ after.touched → before.ixSysvarIdx ≠ some i →
    after.acct i = before.acct i

namespace TouchChanges

theorem refl (state : TxState) : TouchChanges state state :=
  ⟨rfl, fun _ member => member, fun _ _ _ => rfl⟩

theorem trans {first middle last : TxState}
    (left : TouchChanges first middle) (right : TouchChanges middle last) :
    TouchChanges first last := by
  refine ⟨right.keys.trans left.keys, fun i member => right.mono i (left.mono i member), ?_⟩
  intro i untouched ordinary
  have middleUntouched : i ∉ middle.touched := fun member => untouched (right.mono i member)
  have middleOrdinary : middle.ixSysvarIdx ≠ some i := by
    simpa only [TxState.ixSysvarIdx, left.keys] using ordinary
  exact (right.untouched i untouched middleOrdinary).trans
    (left.untouched i middleUntouched ordinary)

theorem of_eq {before after : TxState} (keys : after.keys = before.keys)
    (accounts : after.accts = before.accts) (touched : after.touched = before.touched) :
    TouchChanges before after :=
  ⟨keys, fun _ member => touched ▸ member,
    fun i _ _ => by simp only [TxState.acct, accounts]⟩

theorem of_update {before after : TxState} {index : Nat} {account : Account}
    (keys : after.keys = before.keys) (accounts : after.accts = before.accts.set index account)
    (touched : after.touched = (before.setAcct index account).touched) :
    TouchChanges before after := by
  refine ⟨keys, ?_, ?_⟩
  · intro i member
    simp only [touched, TxState.setAcct]
    split
    · exact List.mem_cons_of_mem _ member
    · exact member
  · intro i unchanged _
    by_cases valid : index < before.accts.length
    · have different : index ≠ i := by
        intro same
        subst i
        exact unchanged (by simp [touched, TxState.setAcct, valid])
      have preserved := TxState.acct_setAcct_ne before index i account different
      simpa only [TxState.acct, TxState.setAcct, accounts] using preserved
    · have same := List.set_eq_of_length_le (l := before.accts) (i := index)
        (a := account) (by omega)
      simp only [TxState.acct, accounts, same]

theorem of_sysvar_update {before after : TxState} {index : Nat} {account : Account}
    (keys : after.keys = before.keys) (accounts : after.accts = before.accts.set index account)
    (touched : after.touched = before.touched) (sysvar : before.ixSysvarIdx = some index) :
    TouchChanges before after := by
  refine ⟨keys, fun _ member => touched ▸ member, ?_⟩
  intro i _ ordinary
  have different : index ≠ i := by
    intro same
    subst i
    exact ordinary sysvar
  have preserved := TxState.acct_setAcct_ne before index i account different
  simpa only [TxState.acct, TxState.setAcct, accounts] using preserved

end TouchChanges

namespace Frame

/-- The index of the first instruction account that refers to transaction index `t`. -/
def firstIdx (f : Frame) (t : Nat) : Option Nat := f.accounts.findIdx? (·.txIdx == t)

/-- Whether instruction account `j` repeats an earlier one, corresponding to
`is_instruction_account_duplicate` in Agave 4.3.2
`transaction-context/src/instruction.rs`. -/
def isDup (f : Frame) (j : Nat) : Bool :=
  match f.accounts[j]? with
  | some a => f.firstIdx a.txIdx != some j
  | none => false

/-- Whether the transaction account `t` is an account of the instruction. -/
def hasTx (f : Frame) (t : Nat) : Bool := f.accounts.any (·.txIdx == t)

/-- Whether the transaction account `t` is writable in the instruction. -/
def writableTx (f : Frame) (t : Nat) : Bool := f.accounts.any fun a => a.txIdx == t && a.writable

/-- Whether the transaction account `t` is a signer of the instruction. -/
def signerTx (f : Frame) (t : Nat) : Bool := f.accounts.any fun a => a.txIdx == t && a.signer

/-- Repeated instruction accounts carry equal flags: the message gives flags per
transaction account, and `prepare_next_instruction` merges the flags of all
occurrences. See [CPI](../../source-notes/agave-4.3.2.md#cpi). -/
def FlagsConsistent (f : Frame) : Prop :=
  ∀ a ∈ f.accounts, ∀ b ∈ f.accounts, a.txIdx = b.txIdx → a = b

end Frame

/-- The setter context of `BorrowedAccount`: the key of the program of the instruction
context through which the account was borrowed, the transaction index of the account,
and its writable flag in that instruction. See the current
[account-mutation analysis](../../source-notes/agave-4.3.2.md#account-mutation). -/
structure SetterCtx where
  program : Pubkey
  txIdx : Nat
  writable : Bool
  release : Release := .agave_4_3_2
  deriving DecidableEq, Repr

namespace SetterCtx

/-- `is_owned_by_current_program`. -/
def owned (sc : SetterCtx) (ts : TxState) : Bool := (ts.acct sc.txIdx).owner == sc.program

end SetterCtx

/-- The setter context of instruction account `ia` of an instruction whose program has
transaction index `programIdx`. -/
def setterCtxOf (ts : TxState) (programIdx : Nat) (ia : InstrAcct)
    (release : Release := .agave_4_3_2) : SetterCtx :=
  { program := ts.key programIdx, txIdx := ia.txIdx, writable := ia.writable, release }

/-! ## Push and pop -/

/-- The write of the current top-level index into the last two bytes of the
Instructions sysvar. `TransactionContext::push` in Agave 4.3.2 performs this
administrative write without the mutation checks of `BorrowedAccount`; see
[execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
def writeIxSysvarIndex (ts : TxState) : Except InstrError TxState :=
  match ts.ixSysvarIdx with
  | none => .ok ts
  | some j =>
    let a := ts.acct j
    if a.owner ≠ Ids.sysvarOwner then .error .InvalidAccountOwner
    else if a.data.length < 2 then .error .AccountDataTooSmall
    else
      let updated := { a with data := writeAt a.data (a.data.length - 2) (u16le ts.topIndex) }
      .ok { ts with accts := ts.accts.set j updated }

/-- The reentrancy rule of `InvokeContext::push` in Agave 4.3.2: the program is on
the instruction stack and is not the immediate caller. -/
def isReentry (ts : TxState) (f : Frame) : Bool :=
  ts.stack.any (fun g => ts.key g.programIdx == ts.key f.programIdx) &&
    !(match ts.stack.head? with
      | some g => ts.key g.programIdx == ts.key f.programIdx
      | none => false)

/-- The represented checks of `InvokeContext::push` followed by
`TransactionContext::push` in Agave 4.3.2. The model records trace entries in push
order rather than using the allocation of trace slots in the runtime; sibling
queries use this logical order. Successful executions also advance `topIndex` at
pop rather than at the next top-level push. See the correspondence conditions in
[execution and commit](../../source-notes/agave-4.3.2.md#execution-and-commit). -/
def push (p : Profile) (ts : TxState) (f : Frame) : Except InstrError TxState :=
  if isReentry ts f then .error .ReentrancyNotAllowed
  else if !ts.stack.isEmpty && ts.lamportsDelta ≠ 0 then .error .UnbalancedInstruction
  else if MAX_INSTRUCTION_TRACE_LENGTH ≤ ts.trace.length then
    .error .MaxInstructionTraceLengthExceeded
  else if p.maxStackDepth ≤ ts.stack.length then .error .CallDepth
  else
    match writeIxSysvarIndex ts with
    | .error e => .error e
    | .ok ts1 =>
      .ok { ts1 with
        stack := f :: ts1.stack
        trace := ts1.trace ++ [⟨ts1.stack.length + 1, f⟩] }

/-- The balance check of `TransactionContext::pop` in Agave 4.3.2,
`transaction-context/src/transaction.rs`.
The runtime also rejects an empty stack; the intended correspondence applies to
the nonempty stack produced by a successful invocation push.
The check `AccountBorrowOutstanding` on the program account concerns borrows of the
transaction context, which the model never leaves open. -/
def pop (ts : TxState) : Except InstrError TxState :=
  let ts' := { ts with
    stack := ts.stack.tail
    topIndex := if ts.stack.length = 1 then ts.topIndex + 1 else ts.topIndex }
  if ts.lamportsDelta ≠ 0 then .error .UnbalancedInstruction else .ok ts'

/-- The modeled reset of return data before program execution. Agave 4.3.2 resets
it in `process_executable_chain` after successful dispatch. The model resets it
earlier and discards the intermediate state on a dispatch error; this is an
outcome abstraction, not equality of every intermediate runtime state. -/
def resetReturnData (ts : TxState) : TxState :=
  { ts with returnData := (ts.currentProgram.getD default, []) }

/-- The combination of a program result with the pop. In Agave 4.3.2,
`process_instruction` pops whenever the push succeeded and a program error takes
precedence over a pop error. An error here carries no intermediate state, so only
the success branch needs to compute the pop. -/
def afterProgram (r : Except InstrError TxState) : Except InstrError TxState :=
  match r with
  | .error e => .error e
  | .ok ts => pop ts

end Solanalib.Runtime
