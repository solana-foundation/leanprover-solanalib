/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Layout

@[expose] public section

/-!
# Read-back

The deserialization that the loader performs when a program exits with r0 = 0:
for each non-duplicate instruction account, in order, the lamports, the length bound,
the data and the owner, through the setters of `BorrowedAccount`
(`deserialize_parameters_for_abiv1` and `deserialize_parameters_for_abiv0` in
Agave 4.3.2, `program-runtime/src/serialization.rs`). The selected configuration L
is compared under valid buffer, layout and bounded account-state premises; see
[serialization and read-back](../../source-notes/agave-4.3.2.md#serialization-and-read-back).

The step lemmas `lamportStep_ok_iff`, `dataStepL_ok_iff` and `ownerStep_ok_iff` state
the conditions under which each step succeeds; together they are the per-account
obligation `WritesLegal` of the report (cf. `Solanalib.Runtime.WritesLegal`).
-/

namespace Solanalib.Runtime

/-- The lamport step: `set_lamports` when the buffer value differs. -/
def lamportStep (ts : TxState) (sc : SetterCtx) (v : Nat) : Except InstrError TxState :=
  if (ts.acct sc.txIdx).lamports = v then .ok ts else setLamports ts sc v

/-- The data step of configuration L: copy when the account may be resized to the new
length, and otherwise accept only unchanged data
(`deserialize_parameters_for_abiv1`, Agave 4.3.2).
The slice `data` has `postLen` bytes, since the record reserves the entry length
plus 10 KiB and the length bound precedes this step. -/
def dataStepL (ts : TxState) (sc : SetterCtx) (data : Bytes) (postLen : Nat) :
    Except InstrError TxState :=
  match canDataBeResized ts sc postLen with
  | .ok () => setDataFromSlice ts sc data
  | .error e => if (ts.acct sc.txIdx).data = data then .ok ts else .error e

/-- The data step of configuration S represented from the split-region branch of
`deserialize_parameters_for_abiv1`, Agave 4.3.2. -/
def dataStepS (ts : TxState) (sc : SetterCtx) (data : Bytes) (postLen : Nat) :
    Except InstrError TxState :=
  match canDataBeChanged ts sc with
  | .ok () => setDataFromSlice ts sc data
  | .error _ =>
    if (ts.acct sc.txIdx).data.length = postLen then .ok ts else setDataLength ts sc postLen

/-- The data step of configuration D, where the data bytes are already in the account
(`deserialize_parameters_for_abiv1`, Agave 4.3.2). -/
def dataStepD (ts : TxState) (sc : SetterCtx) (postLen : Nat) : Except InstrError TxState :=
  if (ts.acct sc.txIdx).data.length = postLen then .ok ts else setDataLength ts sc postLen

/-- The data step, per configuration. -/
def dataStep (cfg : MemConfig) (ts : TxState) (sc : SetterCtx) (data : Bytes) (postLen : Nat) :
    Except InstrError TxState :=
  match cfg with
  | .L => dataStepL ts sc data postLen
  | .S => dataStepS ts sc data postLen
  | .D => dataStepD ts sc postLen

/-- The owner step: `set_owner` last, when the buffer value differs. -/
def ownerStep (ts : TxState) (sc : SetterCtx) (o : Pubkey) : Except InstrError TxState :=
  if (ts.acct sc.txIdx).owner = o then .ok ts else setOwner ts sc o

/-- The values that read-back takes from the record of a non-duplicate account. -/
structure BufVals where
  lamports : Nat
  postLen : Nat
  data : Bytes
  owner : Pubkey
  deriving DecidableEq, Repr

/-- The values in the buffer for the account at position `s`. A loader-v1 record has
no length the runtime reads at exit, so the length is the entry length, as in
`deserialize_parameters_for_abiv0`. -/
def bufVals (abi : Abi) (buf : Bytes) (s : SerAcct) : BufVals :=
  let postLen := match abi with
    | .v1 => leNat (slice buf (s.offset + abi.lenOff) 8)
    | .v0 => s.entryLen
  { lamports := leNat (slice buf (s.offset + abi.lamportsOff) 8)
    postLen := postLen
    data := slice buf (s.offset + abi.dataOff) postLen
    owner := Pubkey.ofBytes (slice buf (s.offset + abi.ownerOff s.entryLen) 32) }

/-- The bound of 10 KiB over the entry length and of 10 MiB, which read-back checks
before the data step in `deserialize_parameters_for_abiv1`, Agave 4.3.2. -/
def lengthBoundOk (abi : Abi) (entryLen postLen : Nat) : Bool :=
  match abi with
  | .v1 => decide (postLen - entryLen ≤ MAX_PERMITTED_DATA_INCREASE ∧ postLen ≤
    MAX_ACCOUNT_DATA_LEN)
  | .v0 => true

/-- The read-back of one non-duplicate account. -/
def readBackAcct (abi : Abi) (cfg : MemConfig) (ts : TxState) (sc : SetterCtx) (v : BufVals)
    (entryLen : Nat) : Except InstrError TxState :=
  match lamportStep ts sc v.lamports with
  | .error e => .error e
  | .ok ts1 =>
    if lengthBoundOk abi entryLen v.postLen = false then .error .InvalidRealloc
    else match dataStep cfg ts1 sc v.data v.postLen with
      | .error e => .error e
      | .ok ts2 =>
        match abi with
        | .v1 => ownerStep ts2 sc v.owner
        | .v0 => .ok ts2

/-- The read-back of all instruction accounts; duplicates are skipped. -/
def readBack (abi : Abi) (cfg : MemConfig) (programIdx : Nat) (buf : Bytes)
    (ts : TxState) (layout : List SerAcct) (release : Release := .agave_4_3_2) :
    Except InstrError TxState :=
  match layout with
  | [] => .ok ts
  | s :: rest =>
    match s.slot with
    | .dup _ => readBack abi cfg programIdx buf ts rest release
    | .acct ia =>
      match readBackAcct abi cfg ts (setterCtxOf ts programIdx ia release) (bufVals abi buf s)
        s.entryLen with
      | .error e => .error e
      | .ok ts' => readBack abi cfg programIdx buf ts' rest release

/-! ## The conditions of each step -/

/-- The condition under which `set_lamports` accepts a new balance `v`. -/
def LamportsOk (ts : TxState) (sc : SetterCtx) (v : Nat) : Prop :=
  v = (ts.acct sc.txIdx).lamports ∨
    (sc.writable = true ∧ (sc.owned ts = true ∨ (ts.acct sc.txIdx).lamports ≤ v))

theorem lamportStep_ok_iff {ts : TxState} {sc : SetterCtx} {v : Nat}
    (hi : sc.txIdx < ts.accts.length) :
    (∃ ts', lamportStep ts sc v = .ok ts') ↔ LamportsOk ts sc v := by
  unfold lamportStep LamportsOk
  by_cases he : (ts.acct sc.txIdx).lamports = v
  · simp [he]
  · simp only [he, ↓reduceIte, setLamports, hi]
    constructor
    · rintro ⟨ts', h⟩
      split at h
      · cases h
      · rename_i h1
        split at h
        · cases h
        · rename_i hw
          refine Or.inr ⟨by simpa using hw, ?_⟩
          cases ho : sc.owned ts
          · right; simp [ho] at h1; omega
          · left; rfl
    · rintro (h | ⟨hw, ho⟩)
      · exact absurd h.symm he
      · have h1 : ¬(sc.owned ts = false ∧ v < (ts.acct sc.txIdx).lamports) := by
          rintro ⟨hf, hlt⟩
          rcases ho with ho | ho
          · simp [ho] at hf
          · omega
        simp only [h1, ↓reduceIte, hw, Bool.true_eq_false]
        split
        · rename_i h2; exact absurd h2.symm he
        · exact ⟨_, rfl⟩

theorem lamportStep_result {ts ts' : TxState} {sc : SetterCtx} {v : Nat}
    (hi : sc.txIdx < ts.accts.length) (h : lamportStep ts sc v = .ok ts') :
    ts'.acct sc.txIdx = { ts.acct sc.txIdx with lamports := v } ∧
    ts'.lamportsDelta = ts.lamportsDelta + ((v : Int) - (ts.acct sc.txIdx).lamports) ∧
    ts'.resizeDelta = ts.resizeDelta := by
  unfold lamportStep at h
  split at h
  · rename_i he; cases h; subst he; simp
  · unfold setLamports at h
    simp only [hi, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i _ _ he'; cases h; subst he'; simp
        · cases h
          refine ⟨?_, rfl, rfl⟩
          exact TxState.acct_setAcct_self ts _ _ hi

/-- The condition under which `can_data_be_resized` accepts a length `n`. -/
def ResizeOk (ts : TxState) (sc : SetterCtx) (n : Nat) : Prop :=
  sc.writable = true ∧ sc.owned ts = true ∧ n ≤ MAX_ACCOUNT_DATA_LEN ∧
    ts.resizeDelta + ((n : Int) - (ts.acct sc.txIdx).data.length) ≤
      (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int)

theorem canDataBeChanged_ok_iff {ts : TxState} {sc : SetterCtx} :
    canDataBeChanged ts sc = .ok () ↔ sc.writable = true ∧ sc.owned ts = true := by
  constructor
  · intro h; exact ⟨canDataBeChanged_writable h, canDataBeChanged_owned h⟩
  · rintro ⟨hw, ho⟩; simp [canDataBeChanged, hw, ho]

theorem txCanDataBeResized_ok_iff {ts : TxState} {old n : Nat} :
    txCanDataBeResized ts old n = .ok () ↔
      n ≤ MAX_ACCOUNT_DATA_LEN ∧
        ts.resizeDelta + ((n : Int) - old) ≤ (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int) := by
  unfold txCanDataBeResized
  split
  · simp only [reduceCtorEq, false_iff]; omega
  · split
    · simp only [reduceCtorEq, false_iff]; omega
    · simp only [true_iff]; omega

theorem canDataBeResized_ok_iff {ts : TxState} {sc : SetterCtx} {n : Nat} :
    canDataBeResized ts sc n = .ok () ↔ ResizeOk ts sc n := by
  constructor
  · intro h
    have ⟨hw, ho⟩ := canDataBeChanged_ok_iff.mp (canDataBeResized_changed h)
    have ⟨hm, hg⟩ := txCanDataBeResized_ok_iff.mp (canDataBeResized_tx h)
    exact ⟨hw, ho, hm, hg⟩
  · rintro ⟨hw, ho, hm, hg⟩
    have h1 : ¬(sc.release ≠ .agave_4_3_2 ∧
        n ≠ (ts.acct sc.txIdx).data.length ∧ sc.owned ts = false) := by
      rintro ⟨_, _, hf⟩; simp [ho] at hf
    have ht := txCanDataBeResized_ok_iff.mpr ⟨hm, hg⟩
    have hc := canDataBeChanged_ok_iff.mpr ⟨hw, ho⟩
    simp [canDataBeResized, h1, ht, hc]

/-- The condition under which the data step of configuration L succeeds: the data is
unchanged, or the account may be resized to the new length. -/
def DataOkL (ts : TxState) (sc : SetterCtx) (data : Bytes) (n : Nat) : Prop :=
  data = (ts.acct sc.txIdx).data ∨ ResizeOk ts sc n

theorem dataStepL_ok_iff {ts : TxState} {sc : SetterCtx} {data : Bytes} {n : Nat}
    (hi : sc.txIdx < ts.accts.length) (hn : data.length = n) :
    (∃ ts', dataStepL ts sc data n = .ok ts') ↔ DataOkL ts sc data n := by
  subst hn
  unfold dataStepL DataOkL
  cases hr : canDataBeResized ts sc data.length with
  | ok u =>
    have hr' : canDataBeResized ts sc data.length = .ok () := hr
    constructor
    · intro _; exact Or.inr (canDataBeResized_ok_iff.mp hr')
    · intro _; simp only [setDataFromSlice, hi, ↓reduceIte, hr']; exact ⟨_, rfl⟩
  | error e =>
    simp only
    by_cases he : (ts.acct sc.txIdx).data = data
    · simp [he]
    · have hn : ¬ ResizeOk ts sc data.length := fun hok => by
        rw [canDataBeResized_ok_iff.mpr hok] at hr; cases hr
      simp only [he, ↓reduceIte, reduceCtorEq, exists_false, false_iff]
      rintro (h | h)
      · exact he h.symm
      · exact hn h

theorem dataStepL_result {ts ts' : TxState} {sc : SetterCtx} {data : Bytes} {n : Nat}
    (hi : sc.txIdx < ts.accts.length) (hn : data.length = n) (h : dataStepL ts sc data n = .ok ts')
      :
    ts'.acct sc.txIdx = { ts.acct sc.txIdx with data := data } ∧
    ts'.lamportsDelta = ts.lamportsDelta ∧
    (ts'.resizeDelta = ts.resizeDelta + ((data.length : Int) - (ts.acct sc.txIdx).data.length) ∨
      (ts'.resizeDelta = ts.resizeDelta ∧ data = (ts.acct sc.txIdx).data)) := by
  subst hn
  unfold dataStepL at h
  cases hr : canDataBeResized ts sc data.length with
  | ok u =>
    have hr' : canDataBeResized ts sc data.length = .ok () := hr
    simp only [hr', setDataFromSlice, hi, ↓reduceIte] at h
    cases h
    exact ⟨TxState.acct_setAcct_self ts _ _ hi, rfl, Or.inl rfl⟩
  | error e =>
    simp only [hr] at h
    split at h
    · rename_i he; cases h; rw [← he]; exact ⟨by simp, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · cases h

/-- The condition under which `set_owner` accepts a new owner `o`. -/
def OwnerOk (ts : TxState) (sc : SetterCtx) (o : Pubkey) : Prop :=
  o = (ts.acct sc.txIdx).owner ∨
    (sc.owned ts = true ∧ sc.writable = true ∧ isZeroed (ts.acct sc.txIdx).data = true)

theorem ownerStep_ok_iff {ts : TxState} {sc : SetterCtx} {o : Pubkey}
    (hi : sc.txIdx < ts.accts.length) :
    (∃ ts', ownerStep ts sc o = .ok ts') ↔ OwnerOk ts sc o := by
  unfold ownerStep OwnerOk
  by_cases he : (ts.acct sc.txIdx).owner = o
  · simp [he]
  · simp only [he, ↓reduceIte, setOwner, hi]
    constructor
    · rintro ⟨ts', h⟩
      split at h
      · cases h
      · rename_i ho
        split at h
        · cases h
        · rename_i hw
          split at h
          · cases h
          · rename_i hz
            exact Or.inr ⟨by simpa using ho, by simpa using hw, by simpa using hz⟩
    · rintro (h | ⟨ho, hw, hz⟩)
      · exact absurd h.symm he
      · simp [ho, hw, hz]

theorem ownerStep_result {ts ts' : TxState} {sc : SetterCtx} {o : Pubkey}
    (hi : sc.txIdx < ts.accts.length) (h : ownerStep ts sc o = .ok ts') :
    ts'.acct sc.txIdx = { ts.acct sc.txIdx with owner := o } ∧
    ts'.lamportsDelta = ts.lamportsDelta ∧ ts'.resizeDelta = ts.resizeDelta := by
  unfold ownerStep at h
  by_cases he : (ts.acct sc.txIdx).owner = o
  · simp only [he, ↓reduceIte] at h
    cases h; subst he; simp
  · simp only [he, ↓reduceIte, setOwner, hi] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; exact ⟨TxState.acct_setAcct_self ts _ _ hi, rfl, rfl⟩

/-! ## What a successful read-back changes -/

/-- The effect of a sequence of setter calls: the accounts outside `W` keep their state,
the structure of the context is unchanged, and the balance invariant holds. -/
structure Changes (ts ts' : TxState) (W : Nat → Prop) : Prop where
  keys : ts'.keys = ts.keys
  stack : ts'.stack = ts.stack
  trace : ts'.trace = ts.trace
  returnData : ts'.returnData = ts.returnData
  topIndex : ts'.topIndex = ts.topIndex
  length : ts'.accts.length = ts.accts.length
  other : ∀ j, ¬ W j → ts'.acct j = ts.acct j
  balance : (ts'.lamportSum : Int) - ts'.lamportsDelta = ts.lamportSum - ts.lamportsDelta
  touches : TouchChanges ts ts'

theorem Changes.refl (ts : TxState) (W : Nat → Prop) : Changes ts ts W :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, TouchChanges.refl ts⟩

theorem Changes.trans {ts ts' ts'' : TxState} {W : Nat → Prop}
    (h1 : Changes ts ts' W) (h2 : Changes ts' ts'' W) : Changes ts ts'' W :=
  ⟨h2.keys.trans h1.keys, h2.stack.trans h1.stack, h2.trace.trans h1.trace,
    h2.returnData.trans h1.returnData, h2.topIndex.trans h1.topIndex,
    h2.length.trans h1.length, fun j hj => (h2.other j hj).trans (h1.other j hj),
    h2.balance.trans h1.balance, h1.touches.trans h2.touches⟩

theorem Changes.mono {ts ts' : TxState} {W W' : Nat → Prop} (h : Changes ts ts' W)
    (hW : ∀ j, W j → W' j) : Changes ts ts' W' :=
  ⟨h.keys, h.stack, h.trace, h.returnData, h.topIndex, h.length,
    fun j hj => h.other j (fun hw => hj (hW j hw)), h.balance, h.touches⟩

theorem Changes.of_setterStep {ts ts' : TxState} {sc : SetterCtx} (h : SetterStep ts ts' sc) :
    Changes ts ts' (fun j => j = sc.txIdx ∧ sc.writable = true) :=
  ⟨h.keys, h.stack, h.trace, h.returnData, h.topIndex, h.length,
    fun j hj => h.other j (fun he => hj ⟨he, h.writable⟩), h.balance, h.touches⟩

/-- The accounts that a read-back of layout `lay` may change: the non-duplicate
instruction accounts with the writable flag. -/
def WritableIn (lay : List SerAcct) (j : Nat) : Prop :=
  ∃ s ∈ lay, ∃ ia, s.slot = .acct ia ∧ ia.txIdx = j ∧ ia.writable = true

theorem Changes.of_lamportStep {ts ts' : TxState} {sc : SetterCtx} {v : Nat}
    (h : lamportStep ts sc v = .ok ts') :
    Changes ts ts' (fun j => j = sc.txIdx ∧ sc.writable = true) := by
  unfold lamportStep at h
  split at h
  · cases h; exact Changes.refl _ _
  · exact Changes.of_setterStep (SetterStep.of_setLamports h)

theorem Changes.of_ownerStep {ts ts' : TxState} {sc : SetterCtx} {o : Pubkey}
    (h : ownerStep ts sc o = .ok ts') :
    Changes ts ts' (fun j => j = sc.txIdx ∧ sc.writable = true) := by
  unfold ownerStep at h
  split at h
  · cases h; exact Changes.refl _ _
  · exact Changes.of_setterStep (SetterStep.of_setOwner h)

theorem Changes.of_dataStep {cfg : MemConfig} {ts ts' : TxState} {sc : SetterCtx} {d : Bytes}
    {n : Nat} (h : dataStep cfg ts sc d n = .ok ts') :
    Changes ts ts' (fun j => j = sc.txIdx ∧ sc.writable = true) := by
  cases cfg with
  | L =>
    simp only [dataStep, dataStepL] at h
    cases hr : canDataBeResized ts sc n with
    | ok u =>
      simp only [hr] at h
      exact Changes.of_setterStep (SetterStep.of_setDataFromSlice h)
    | error e =>
      simp only [hr] at h
      split at h
      · cases h; exact Changes.refl _ _
      · cases h
  | S =>
    simp only [dataStep, dataStepS] at h
    cases hc : canDataBeChanged ts sc with
    | ok u =>
      simp only [hc] at h
      exact Changes.of_setterStep (SetterStep.of_setDataFromSlice h)
    | error e =>
      simp only [hc] at h
      split at h
      · cases h; exact Changes.refl _ _
      · exact Changes.of_setterStep (SetterStep.of_setDataLength h)
  | D =>
    simp only [dataStep, dataStepD] at h
    split at h
    · cases h; exact Changes.refl _ _
    · exact Changes.of_setterStep (SetterStep.of_setDataLength h)

theorem Changes.of_readBackAcct {abi : Abi} {cfg : MemConfig} {ts ts' : TxState}
    {sc : SetterCtx} {v : BufVals} {n : Nat} (h : readBackAcct abi cfg ts sc v n = .ok ts') :
    Changes ts ts' (fun j => j = sc.txIdx ∧ sc.writable = true) := by
  unfold readBackAcct at h
  split at h
  · cases h
  · rename_i ts1 h1
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ts2 h2
        have c1 := Changes.of_lamportStep h1
        have c2 := Changes.of_dataStep h2
        cases abi with
        | v1 => exact c1.trans (c2.trans (Changes.of_ownerStep h))
        | v0 => cases h; exact c1.trans c2

/-- A successful read-back changes only the writable non-duplicate accounts of the
layout, and keeps the balance invariant. -/
theorem Changes.of_readBack {abi : Abi} {cfg : MemConfig} {pidx : Nat} {buf : Bytes} {release :
  Release} :
    ∀ {lay : List SerAcct} {ts ts' : TxState}, readBack abi cfg pidx buf ts lay release = .ok ts' →
      Changes ts ts' (WritableIn lay)
  | [], ts, ts', h => by cases h; exact Changes.refl _ _
  | s :: rest, ts, ts', h => by
    unfold readBack at h
    split at h
    · exact (Changes.of_readBack h).mono fun j ⟨s', hs', hrest⟩ => ⟨s', List.mem_cons_of_mem _ hs',
      hrest⟩
    · rename_i ia hslot
      split at h
      · cases h
      · rename_i ts1 h1
        have c1 := Changes.of_readBackAcct h1
        have c2 := Changes.of_readBack h
        refine (c1.mono ?_).trans (c2.mono ?_)
        · rintro j ⟨rfl, hw⟩
          exact ⟨s, List.mem_cons_self .., ia, hslot, rfl, hw⟩
        · rintro j ⟨s', hs', hrest⟩
          exact ⟨s', List.mem_cons_of_mem _ hs', hrest⟩

end Solanalib.Runtime
