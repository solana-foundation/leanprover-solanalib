/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.ReadBack

@[expose] public section

/-!
# Runtime allocation and balance boundaries

These checks use writable accounts owned by the current program. The program
account and large byte strings remain parameters; length hypotheses avoid
evaluating megabytes of replicated bytes in the kernel. Every cumulative resize
counter below is reached through account setters from an initial counter of zero.
The tests concern the runtime boundaries, not executable-program admission.
-/

open Solanalib.Runtime

namespace SolanalibTest.Runtime.RuntimeBoundariesTest

def programKey : Pubkey := Pubkey.ofNat 7000

def funding : Nat := 1000000000000

def dataAccount (data : Bytes) : Account :=
  ⟨funding, data, programKey, false, 0⟩

def caller : Frame :=
  ⟨0, [⟨1, false, true⟩, ⟨2, false, true⟩, ⟨3, false, true⟩], []⟩

def fixture (program : Account) (first second third : Bytes := []) : TxState where
  keys := [programKey, Pubkey.ofNat 7001, Pubkey.ofNat 7002, Pubkey.ofNat 7003]
  accts := [program, dataAccount first, dataAccount second, dataAccount third]
  lamportsDelta := 0
  resizeDelta := 0
  stack := [caller]
  trace := [⟨1, caller⟩]
  returnData := (programKey, [])
  topIndex := 0

def setter (index : Nat) : SetterCtx :=
  ⟨programKey, index, true, .agave_4_3_2⟩

def values (data : Bytes) : BufVals := ⟨funding, data.length, data, programKey⟩

def dataSnapshot (state : TxState) : Bytes × Bytes × Bytes × Int :=
  ((state.acct 1).data, (state.acct 2).data, (state.acct 3).data, state.resizeDelta)

/-- The size hypotheses used by the fixtures have concrete witnesses without
requiring the evaluator to construct them. -/
theorem sized_bytes_exist (length : Nat) : ∃ data : Bytes, data.length = length :=
  ⟨List.replicate length 0, List.length_replicate⟩

theorem data_account_wf (data : Bytes) (bounded : data.length ≤ MAX_ACCOUNT_DATA_LEN) :
    (dataAccount data).WF := by
  simp [Account.WF, dataAccount, funding, bounded, U64_LIMIT]

theorem fixture_accounts_wf (program : Account) (programWf : program.WF)
    (first second third : Bytes)
    (firstBound : first.length ≤ MAX_ACCOUNT_DATA_LEN)
    (secondBound : second.length ≤ MAX_ACCOUNT_DATA_LEN)
    (thirdBound : third.length ≤ MAX_ACCOUNT_DATA_LEN) :
    ∀ account ∈ (fixture program first second third).accts, account.WF := by
  simp only [fixture, List.mem_cons, List.not_mem_nil, or_false]
  intro account member
  rcases member with rfl | rfl | rfl | rfl
  · exact programWf
  · exact data_account_wf first firstBound
  · exact data_account_wf second secondBound
  · exact data_account_wf third thirdBound

theorem setter_is_current_writable_account (program : Account) :
    setterCtxOf (fixture program) caller.programIdx caller.accounts[0] = setter 1 := by
  rfl

/-- The imbalance is produced by a real debit of a writable, owned account. -/
def debit (program : Account) : Except InstrError TxState :=
  checkedSubLamports (fixture program) (setter 1) 1

theorem debit_records_negative_delta (program : Account) :
    (debit program).map TxState.lamportsDelta = .ok (-1) := by
  simp [Except.map, debit, checkedSubLamports, setLamports, fixture, setter, dataAccount,
    SetterCtx.owned, TxState.acct, TxState.setAcct, funding]

theorem pop_rejects_unbalanced_debit (program : Account) :
    ((debit program).bind pop) = .error .UnbalancedInstruction := by
  simp [Except.bind, debit, checkedSubLamports, setLamports, fixture, setter, dataAccount,
    SetterCtx.owned, TxState.acct, TxState.setAcct, funding, pop]

/-- A call to the immediate caller is permitted by reentrancy and depth checks;
the actual outstanding lamport debit therefore selects UnbalancedInstruction. -/
theorem nested_push_rejects_unbalanced_debit (program : Account) :
    ((debit program).bind fun state => push mainnet state caller) =
      .error .UnbalancedInstruction := by
  simp [Except.bind, debit, checkedSubLamports, setLamports, fixture, setter, dataAccount,
    SetterCtx.owned, TxState.acct, TxState.setAcct, funding, push, isReentry, caller,
    TxState.key]

/-- Read-back accepts exactly 10 KiB of growth from an empty account. -/
theorem permitted_increase_exact (program : Account) (data : Bytes)
    (length : data.length = MAX_PERMITTED_DATA_INCREASE) :
    (readBackAcct .v1 .L (fixture program) (setter 1) (values data) 0).map dataSnapshot =
      .ok (data, [], [], (MAX_PERMITTED_DATA_INCREASE : Int)) := by
  simp [Except.map, readBackAcct, lamportStep, lengthBoundOk, dataStep, dataStepL, ownerStep,
    setDataFromSlice, canDataBeResized, txCanDataBeResized, canDataBeChanged,
    fixture, setter, values, dataAccount, SetterCtx.owned, TxState.acct, TxState.setAcct,
    dataSnapshot, length, MAX_PERMITTED_DATA_INCREASE, MAX_ACCOUNT_DATA_LEN,
    MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

/-- The next byte is rejected while remaining far below the absolute 10 MiB limit. -/
theorem permitted_increase_plus_one (program : Account) (data : Bytes)
    (length : data.length = MAX_PERMITTED_DATA_INCREASE + 1) :
    readBackAcct .v1 .L (fixture program) (setter 1) (values data) 0 =
      .error .InvalidRealloc := by
  simp [readBackAcct, lamportStep, lengthBoundOk, fixture, setter, values, dataAccount,
    TxState.acct, length, MAX_PERMITTED_DATA_INCREASE, MAX_ACCOUNT_DATA_LEN]

/-- A one-byte increase reaches the absolute account-size limit. -/
theorem account_size_exact (program : Account) (before after : Bytes)
    (beforeLength : before.length = MAX_ACCOUNT_DATA_LEN - 1)
    (afterLength : after.length = MAX_ACCOUNT_DATA_LEN) :
    (readBackAcct .v1 .L (fixture program before) (setter 1) (values after)
      before.length).map dataSnapshot = .ok (after, [], [], 1) := by
  simp [Except.map, readBackAcct, lamportStep, lengthBoundOk, dataStep, dataStepL, ownerStep,
    setDataFromSlice, canDataBeResized, txCanDataBeResized, canDataBeChanged,
    fixture, setter, values, dataAccount, SetterCtx.owned, TxState.acct, TxState.setAcct,
    dataSnapshot, beforeLength, afterLength, MAX_PERMITTED_DATA_INCREASE,
    MAX_ACCOUNT_DATA_LEN, MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

/-- Two bytes of growth are within the per-invocation allowance, but the second
byte exceeds the absolute account limit and is rejected before any data update. -/
theorem account_size_plus_one (program : Account) (before after : Bytes)
    (beforeLength : before.length = MAX_ACCOUNT_DATA_LEN - 1)
    (afterLength : after.length = MAX_ACCOUNT_DATA_LEN + 1) :
    readBackAcct .v1 .L (fixture program before) (setter 1) (values after)
      before.length = .error .InvalidRealloc := by
  simp [readBackAcct, lamportStep, lengthBoundOk, fixture, setter, values, dataAccount,
    TxState.acct, beforeLength, afterLength, MAX_PERMITTED_DATA_INCREASE,
    MAX_ACCOUNT_DATA_LEN]

/-- These direct account-setter calls model allocations such as native program
mutations. They are not a claim that SBF read-back permits 10 MiB in one invocation. -/
def allocateTwo (program : Account) (data : Bytes) : Except InstrError TxState := do
  let first ← setDataFromSlice (fixture program) (setter 1) data
  setDataFromSlice first (setter 2) data

/-- Two independently bounded accounts reach exactly the 20 MiB transaction limit. -/
theorem cumulative_growth_exact (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    (allocateTwo program data).map dataSnapshot =
      .ok (data, data, [], (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int)) := by
  simp [Bind.bind, Except.map, Except.bind, allocateTwo, setDataFromSlice, canDataBeResized,
    txCanDataBeResized,
    canDataBeChanged, fixture, setter, dataAccount, SetterCtx.owned, TxState.acct,
    TxState.setAcct, dataSnapshot, length, MAX_ACCOUNT_DATA_LEN,
    MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

/-- The third account would still have only one byte, but cumulative growth is exhausted. -/
theorem cumulative_growth_plus_one (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    ((allocateTwo program data).bind fun state => setDataFromSlice state (setter 3) [0]) =
      .error .MaxAccountsDataAllocationsExceeded := by
  simp [Bind.bind, Except.bind, allocateTwo, setDataFromSlice, canDataBeResized, txCanDataBeResized,
    canDataBeChanged, fixture, setter, dataAccount, SetterCtx.owned, TxState.acct,
    TxState.setAcct, length, MAX_ACCOUNT_DATA_LEN,
    MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

def shrinkFirst (program : Account) (data : Bytes) : Except InstrError TxState := do
  let grown ← allocateTwo program data
  setDataFromSlice grown (setter 1) []

/-- Shrinking one account subtracts its old length from the signed counter. -/
theorem cumulative_shrink_releases_capacity (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    (shrinkFirst program data).map dataSnapshot =
      .ok ([], data, [], (MAX_ACCOUNT_DATA_LEN : Int)) := by
  simp [Bind.bind, Except.map, Except.bind, shrinkFirst, allocateTwo, setDataFromSlice,
    canDataBeResized, txCanDataBeResized,
    canDataBeChanged, fixture, setter, dataAccount, SetterCtx.owned, TxState.acct,
    TxState.setAcct, dataSnapshot, length, MAX_ACCOUNT_DATA_LEN,
    MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

def growThirdAfterShrink (program : Account) (data : Bytes) : Except InstrError TxState := do
  let shrunk ← shrinkFirst program data
  setDataFromSlice shrunk (setter 3) [0]

/-- The same third-account byte rejected at 20 MiB succeeds after the actual shrink. -/
theorem cumulative_growth_after_shrink (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    (growThirdAfterShrink program data).map dataSnapshot =
      .ok ([], data, [0], (MAX_ACCOUNT_DATA_LEN : Int) + 1) := by
  simp [Bind.bind, Except.map, Except.bind, growThirdAfterShrink, shrinkFirst, allocateTwo,
    setDataFromSlice,
    canDataBeResized, txCanDataBeResized, canDataBeChanged, fixture, setter,
    dataAccount, SetterCtx.owned, TxState.acct, TxState.setAcct, dataSnapshot,
    length, MAX_ACCOUNT_DATA_LEN, MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

/-- Regrowing the first account now exceeds the cumulative limit by one again. -/
theorem cumulative_regrowth_still_counts (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    ((growThirdAfterShrink program data).bind fun state =>
      setDataFromSlice state (setter 1) data) = .error .MaxAccountsDataAllocationsExceeded := by
  simp [Bind.bind, Except.bind, growThirdAfterShrink, shrinkFirst, allocateTwo, setDataFromSlice,
    canDataBeResized, txCanDataBeResized, canDataBeChanged, fixture, setter,
    dataAccount, SetterCtx.owned, TxState.acct, TxState.setAcct,
    length, MAX_ACCOUNT_DATA_LEN, MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

/-- Existing account bytes do not count as growth: removing them can make the
transaction-wide resize counter negative. -/
def shrinkInitiallyLarge (program : Account) (data : Bytes) : Except InstrError TxState :=
  setDataFromSlice (fixture program data) (setter 1) []

theorem signed_shrink_below_zero (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    (shrinkInitiallyLarge program data).map dataSnapshot =
      .ok ([], [], [], -(MAX_ACCOUNT_DATA_LEN : Int)) := by
  simp [Except.map, shrinkInitiallyLarge, setDataFromSlice, canDataBeResized,
    txCanDataBeResized, canDataBeChanged, fixture, setter, dataAccount, SetterCtx.owned,
    TxState.acct, TxState.setAcct, dataSnapshot, length, MAX_ACCOUNT_DATA_LEN,
    MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

def allocateAfterInitialShrink (program : Account) (data : Bytes) : Except InstrError TxState := do
  let shrunk ← shrinkInitiallyLarge program data
  let second ← setDataFromSlice shrunk (setter 2) data
  let third ← setDataFromSlice second (setter 3) data
  setDataFromSlice third (setter 1) data

/-- Starting with 10 MiB, three final 10 MiB accounts have exactly 20 MiB of net
growth. The negative intermediate counter is derived from the first setter. -/
theorem signed_growth_uses_initial_baseline (program : Account) (data : Bytes)
    (length : data.length = MAX_ACCOUNT_DATA_LEN) :
    (allocateAfterInitialShrink program data).map dataSnapshot =
      .ok (data, data, data, (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int)) := by
  simp [Bind.bind, Except.bind, Except.map, allocateAfterInitialShrink, shrinkInitiallyLarge,
    setDataFromSlice, canDataBeResized, txCanDataBeResized, canDataBeChanged,
    fixture, setter, dataAccount, SetterCtx.owned, TxState.acct, TxState.setAcct,
    dataSnapshot, length, MAX_ACCOUNT_DATA_LEN, MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION]

end SolanalibTest.Runtime.RuntimeBoundariesTest
