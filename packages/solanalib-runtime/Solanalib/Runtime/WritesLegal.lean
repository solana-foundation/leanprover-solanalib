/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.ReadBack

@[expose] public section

/-!
# The obligation `WritesLegal`

The obligation of the report on the writes of a program (§3.3), stated without reference
to the setters, for configuration L, the configuration of mainnet.
It includes the length bounds checked by Agave 4.3.2: 10 KiB over the length at
entry, 10 MiB per account and net growth of 20 MiB per transaction. See
[serialization and read-back](../../source-notes/agave-4.3.2.md#serialization-and-read-back).

The theorem `readBackL_of_legal` is the core of T1: when the buffer that a program
leaves satisfies the obligation, read-back succeeds and applies exactly the lamports,
data and owner of the buffer to each account, and changes no other account.
-/

namespace Solanalib.Runtime

variable {release : Release}

/-- The obligation for one account, given its state `a` at read-back, the program `P` of
the instruction, the writable flag `w`, the length at entry `entryLen` and the values `v`
of the buffer. -/
structure AcctLegal (a : Account) (P : Pubkey) (w : Bool) (entryLen : Nat) (v : BufVals) : Prop
  where
  /-- The balance is unchanged, or the account is writable and its balance decreases only
  when the program owns it. -/
  lamports : v.lamports = a.lamports ∨ (w = true ∧ (a.owner = P ∨ a.lamports ≤ v.lamports))
  /-- The length grows by at most 10 KiB over the length at entry and stays within 10 MiB. -/
  length : v.postLen - entryLen ≤ MAX_PERMITTED_DATA_INCREASE ∧ v.postLen ≤ MAX_ACCOUNT_DATA_LEN
  /-- The buffer holds the data of the length it declares. -/
  slice : v.data.length = v.postLen
  /-- The data is unchanged, or the account is writable and owned by the program. -/
  data : v.data = a.data ∨ (w = true ∧ a.owner = P)
  /-- The owner is unchanged, or the program owns the writable account and the new data is
  zero. -/
  owner : v.owner = a.owner ∨ (a.owner = P ∧ w = true ∧ isZeroed v.data = true)

/-- The account after read-back. -/
def applied (a : Account) (v : BufVals) : Account :=
  { a with lamports := v.lamports, data := v.data, owner := v.owner }

/-- The growth of all non-duplicate accounts in the buffer, which bounds every partial
sum of the transaction-wide resize counter. -/
def growth (ts : TxState) (buf : Bytes) : List SerAcct → Nat
  | [] => 0
  | s :: rest =>
    match s.slot with
    | .dup _ => growth ts buf rest
    | .acct ia => ((bufVals .v1 buf s).postLen - (ts.acct ia.txIdx).data.length) + growth ts buf
      rest

/-- The non-duplicate positions of a layout refer to distinct accounts. -/
def NonDupDistinct : List SerAcct → Prop
  | [] => True
  | s :: rest =>
    (∀ ia, s.slot = .acct ia → ∀ s' ∈ rest, ∀ ia', s'.slot = .acct ia' → ia'.txIdx ≠ ia.txIdx) ∧
      NonDupDistinct rest

/-- The pairwise form of `NonDupDistinct`. -/
def NonDupRel (s s' : SerAcct) : Prop :=
  ∀ ia, s.slot = .acct ia → ∀ ia', s'.slot = .acct ia' → ia'.txIdx ≠ ia.txIdx

theorem nonDupDistinct_iff_pairwise : ∀ {l : List SerAcct}, NonDupDistinct l ↔ l.Pairwise NonDupRel
  | [] => by simp [NonDupDistinct]
  | s :: rest => by
    rw [List.pairwise_cons, ← nonDupDistinct_iff_pairwise]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun s' hs' ia hs ia' hs'' => h1 ia hs s' hs' ia' hs'', h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun ia hs s' hs' ia' hs'' => h1 s' hs' ia hs ia' hs'', h2⟩

theorem findIdx?_le {α : Type} {p : α → Bool} :
    ∀ {l : List α} {j : Nat} (hj : j < l.length), p l[j] = true → ∃ k, l.findIdx? p = some k ∧ k ≤ j
  | [], _, hj, _ => by simp at hj
  | a :: as, j, hj, hp => by
    rw [List.findIdx?_cons]
    by_cases ha : p a = true
    · exact ⟨0, by simp [ha], Nat.zero_le _⟩
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      cases j with
      | zero => simp at hp; exact absurd hp ha
      | succ j =>
        obtain ⟨k, hk, hkj⟩ := findIdx?_le (l := as) (j := j) (by simp at hj; omega) (by simpa
          using hp)
        exact ⟨k + 1, by simp [hk], by omega⟩

/-- A non-duplicate slot is the first occurrence of its account. -/
theorem slotOf_acct_first {f : Frame} {j : Nat} (hj : j < f.accounts.length) {ia : InstrAcct}
    (h : slotOf f j f.accounts[j] = .acct ia) :
    ∀ k (hk : k < j), (f.accounts[k]'(by omega)).txIdx ≠ ia.txIdx := by
  intro k hk he
  have hia : ia = f.accounts[j] := slotOf_acct h
  obtain ⟨k', hk', hle⟩ := findIdx?_le (p := fun a => a.txIdx == f.accounts[j].txIdx)
    (l := f.accounts) (j := k) (by omega) (by simp [← hia, he])
  unfold slotOf at h
  simp only [Frame.firstIdx, hk'] at h
  split at h
  · cases h
  · rename_i hnot
    exact hnot (by omega)

/-- The non-duplicate positions of a serialized layout refer to distinct accounts. -/
theorem layout_nonDupDistinct (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) :
    NonDupDistinct (layout abi p ts f) := by
  rw [nonDupDistinct_iff_pairwise, List.pairwise_iff_getElem]
  intro i j hi hj hij ia hsi ia' hsj
  simp only [layout, List.length_mapIdx] at hi hj
  simp only [layout, List.getElem_mapIdx] at hsi hsj
  have hia' : ia' = f.accounts[j] := slotOf_acct hsj
  have hia : ia = f.accounts[i] := slotOf_acct hsi
  have := slotOf_acct_first hj hsj i hij
  rw [← hia] at this
  exact fun he => this he.symm

/-- The obligation `WritesLegal` for a read-back in configuration L. -/
def WritesLegalL (pidx : Nat) (buf : Bytes) (ts : TxState) (lay : List SerAcct) : Prop :=
  (∀ s ∈ lay, ∀ ia, s.slot = .acct ia →
    AcctLegal (ts.acct ia.txIdx) (ts.key pidx) ia.writable s.entryLen (bufVals .v1 buf s)) ∧
  ts.resizeDelta + (growth ts buf lay : Int) ≤ (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int)

theorem owned_setterCtxOf {ts : TxState} {pidx : Nat} {ia : InstrAcct} :
    (setterCtxOf ts pidx ia release).owned ts = true ↔ (ts.acct ia.txIdx).owner = ts.key pidx := by
  simp [SetterCtx.owned, setterCtxOf]

/-- The read-back of one account under its obligation. -/
theorem readBackAcctL_ok {ts : TxState} {pidx : Nat} {ia : InstrAcct} {v : BufVals} {n : Nat}
    (hi : ia.txIdx < ts.accts.length)
    (h : AcctLegal (ts.acct ia.txIdx) (ts.key pidx) ia.writable n v)
    (hg : ts.resizeDelta + ((v.postLen - (ts.acct ia.txIdx).data.length : Nat) : Int) ≤
      (MAX_ACCOUNT_DATA_GROWTH_PER_TRANSACTION : Int)) :
    ∃ ts3, readBackAcct .v1 .L ts (setterCtxOf ts pidx ia release) v n = .ok ts3 ∧
      ts3.acct ia.txIdx = applied (ts.acct ia.txIdx) v ∧
      (∀ t, t ≠ ia.txIdx → ts3.acct t = ts.acct t) ∧
      ts3.keys = ts.keys ∧ ts3.accts.length = ts.accts.length ∧
      ts3.resizeDelta = ts.resizeDelta + ((v.postLen : Int) - (ts.acct ia.txIdx).data.length) := by
  have hi' : (setterCtxOf ts pidx ia release).txIdx < ts.accts.length := hi
  -- the lamport step
  have hl : LamportsOk ts (setterCtxOf ts pidx ia release) v.lamports := by
    rcases h.lamports with h1 | ⟨hw, ho⟩
    · exact Or.inl h1
    · refine Or.inr ⟨hw, ?_⟩
      rcases ho with ho | ho
      · exact Or.inl (owned_setterCtxOf.mpr ho)
      · exact Or.inr ho
  obtain ⟨ts1, h1⟩ := (lamportStep_ok_iff hi').mpr hl
  obtain ⟨ha1', _, hr1⟩ := lamportStep_result hi' h1
  have ha1 : ts1.acct ia.txIdx = { ts.acct ia.txIdx with lamports := v.lamports } := ha1'
  have c1 := Changes.of_lamportStep h1
  have hi1 : (setterCtxOf ts pidx ia release).txIdx < ts1.accts.length := by rw [c1.length]; exact
    hi
  -- the data step
  have hdata : DataOkL ts1 (setterCtxOf ts pidx ia release) v.data v.postLen := by
    rcases h.data with h2 | ⟨hw, ho⟩
    · left
      show v.data = (ts1.acct ia.txIdx).data
      rw [ha1]
      exact h2
    · right
      refine ⟨hw, ?_, h.length.2, ?_⟩
      · show ((ts1.acct ia.txIdx).owner == ts.key pidx) = true
        rw [ha1]
        simp [ho]
      · show ts1.resizeDelta + ((v.postLen : Int) - ((ts1.acct ia.txIdx).data.length : Int)) ≤ _
        rw [hr1, ha1]
        simp only
        omega
  obtain ⟨ts2, h2⟩ := (dataStepL_ok_iff hi1 h.slice).mpr hdata
  obtain ⟨ha2', _, hr2'⟩ := dataStepL_result hi1 h.slice h2
  have ha2 : ts2.acct ia.txIdx = { ts1.acct ia.txIdx with data := v.data } := ha2'
  have hr2 : ts2.resizeDelta =
      ts1.resizeDelta + ((v.data.length : Int) - ((ts1.acct ia.txIdx).data.length : Int)) ∨
      (ts2.resizeDelta = ts1.resizeDelta ∧ v.data = (ts1.acct ia.txIdx).data) := hr2'
  have c2 := Changes.of_dataStep (cfg := .L)
    (show dataStep .L ts1 (setterCtxOf ts pidx ia release) v.data v.postLen = .ok ts2 from h2)
  have hi2 : (setterCtxOf ts pidx ia release).txIdx < ts2.accts.length := by rw [c2.length]; exact
    hi1
  have hacct2 : ts2.acct ia.txIdx = { ts.acct ia.txIdx with lamports := v.lamports, data := v.data
    } := by
    rw [ha2, ha1]
  -- the owner step
  have hown : OwnerOk ts2 (setterCtxOf ts pidx ia release) v.owner := by
    rcases h.owner with h3 | ⟨ho, hw, hz⟩
    · left
      show v.owner = (ts2.acct ia.txIdx).owner
      rw [hacct2]; exact h3
    · right
      refine ⟨?_, hw, ?_⟩
      · show ((ts2.acct ia.txIdx).owner == ts.key pidx) = true
        rw [hacct2]; simp [ho]
      · show isZeroed (ts2.acct ia.txIdx).data = true
        rw [hacct2]; exact hz
  obtain ⟨ts3, h3⟩ := (ownerStep_ok_iff hi2).mpr hown
  obtain ⟨ha3', _, hr3⟩ := ownerStep_result hi2 h3
  have ha3 : ts3.acct ia.txIdx = { ts2.acct ia.txIdx with owner := v.owner } := ha3'
  have c3 := Changes.of_ownerStep h3
  refine ⟨ts3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold readBackAcct
    have hb : lengthBoundOk .v1 n v.postLen = true := by
      simp [lengthBoundOk, h.length.1, h.length.2]
    simp only [h1, hb, Bool.true_eq_false, ↓reduceIte]
    rw [show dataStep .L ts1 (setterCtxOf ts pidx ia release) v.data v.postLen = .ok ts2 from h2]
    exact h3
  · rw [ha3, hacct2]
    rfl
  · intro t ht
    have n1 : ¬ (t = (setterCtxOf ts pidx ia release).txIdx ∧ (setterCtxOf ts pidx ia
      release).writable = true) :=
      fun ⟨he, _⟩ => ht he
    rw [c3.other t n1, c2.other t n1, c1.other t n1]
  · rw [c3.keys, c2.keys, c1.keys]
  · rw [c3.length, c2.length, c1.length]
  · rw [hr3]
    rcases hr2 with hr2 | ⟨hr2, hdeq⟩
    · rw [hr2, hr1, ha1, h.slice]
    · rw [hr2, hr1]
      have hlen : v.postLen = (ts.acct ia.txIdx).data.length := by
        rw [← h.slice, hdeq, ha1]
      rw [hlen]
      simp

/-- The core of T1: under `WritesLegal`, read-back succeeds, sets each non-duplicate
account to the lamports, data and owner of the buffer, and changes no other account. -/
theorem readBackL_of_legal {pidx : Nat} {buf : Bytes} :
    ∀ (lay : List SerAcct) (ts : TxState), NonDupDistinct lay →
      (∀ s ∈ lay, ∀ ia, s.slot = .acct ia → ia.txIdx < ts.accts.length) →
      WritesLegalL pidx buf ts lay →
      ∃ ts', readBack .v1 .L pidx buf ts lay release = .ok ts' ∧
        (∀ s ∈ lay, ∀ ia, s.slot = .acct ia →
          ts'.acct ia.txIdx = applied (ts.acct ia.txIdx) (bufVals .v1 buf s)) ∧
        (∀ t, (∀ s ∈ lay, ∀ ia, s.slot = .acct ia → ia.txIdx ≠ t) → ts'.acct t = ts.acct t) ∧
        ts'.keys = ts.keys ∧ ts'.accts.length = ts.accts.length
  | [], ts, _, _, _ => ⟨ts, rfl, by simp, fun _ _ => rfl, rfl, rfl⟩
  | s :: rest, ts, hd, hidx, ⟨hleg, hgrow⟩ => by
    have hidx' : ∀ s' ∈ rest, ∀ ia, s'.slot = .acct ia → ia.txIdx < ts.accts.length :=
      fun s' hs' => hidx s' (List.mem_cons_of_mem _ hs')
    cases hs : s.slot with
    | dup k =>
      have hg : growth ts buf (s :: rest) = growth ts buf rest := by simp [growth, hs]
      obtain ⟨ts', h1, h2, h3, h4, h5⟩ := readBackL_of_legal rest ts hd.2 hidx'
        ⟨fun s' hs' => hleg s' (List.mem_cons_of_mem _ hs'), by rw [hg] at hgrow; exact hgrow⟩
      refine ⟨ts', by simp only [readBack, hs]; exact h1, ?_, ?_, h4, h5⟩
      · intro s' hs' ia hslot
        rcases List.mem_cons.mp hs' with rfl | hs'
        · rw [hs] at hslot; cases hslot
        · exact h2 s' hs' ia hslot
      · intro t ht
        exact h3 t fun s' hs' ia hslot => ht s' (List.mem_cons_of_mem _ hs') ia hslot
    | acct ia =>
      have hg : growth ts buf (s :: rest) =
          ((bufVals .v1 buf s).postLen - (ts.acct ia.txIdx).data.length) + growth ts buf rest := by
        simp [growth, hs]
      have hi := hidx s (List.mem_cons_self ..) ia hs
      have hl := hleg s (List.mem_cons_self ..) ia hs
      obtain ⟨ts3, h3, ha3, ho3, hk3, hl3, hr3⟩ := readBackAcctL_ok (release := release) (pidx :=
        pidx) hi hl
        (by rw [hg] at hgrow; push_cast at hgrow; omega)
      -- the remaining positions refer to other accounts
      have hne : ∀ s' ∈ rest, ∀ ia', s'.slot = .acct ia' → ia'.txIdx ≠ ia.txIdx := hd.1 ia hs
      have hrest : WritesLegalL pidx buf ts3 rest := by
        refine ⟨fun s' hs' ia' hslot => ?_, ?_⟩
        · have hkey : ts3.key pidx = ts.key pidx := by simp only [TxState.key, hk3]
          rw [ho3 _ (hne s' hs' ia' hslot), hkey]
          exact hleg s' (List.mem_cons_of_mem _ hs') ia' hslot
        · have hgr : growth ts3 buf rest = growth ts buf rest := by
            have : ∀ l : List SerAcct, (∀ s' ∈ l, ∀ ia', s'.slot = .acct ia' → ia'.txIdx ≠
              ia.txIdx) →
                growth ts3 buf l = growth ts buf l := by
              intro l hl'
              induction l with
              | nil => rfl
              | cons x xs ihx =>
                have hxs := fun s' hs' => hl' s' (List.mem_cons_of_mem _ hs')
                cases hx : x.slot with
                | dup _ => simp [growth, hx, ihx hxs]
                | acct ib =>
                  simp only [growth, hx]
                  rw [ho3 _ (hl' x (List.mem_cons_self ..) ib hx), ihx hxs]
            exact this rest hne
          rw [hgr, hr3]
          rw [hg] at hgrow
          push_cast at hgrow
          omega
      have hidx3 : ∀ s' ∈ rest, ∀ ia', s'.slot = .acct ia' → ia'.txIdx < ts3.accts.length := by
        intro s' hs' ia' hslot; rw [hl3]; exact hidx' s' hs' ia' hslot
      obtain ⟨ts', h1, h2, h4, h5, h6⟩ := readBackL_of_legal rest ts3 hd.2 hidx3 hrest
      refine ⟨ts', ?_, ?_, ?_, ?_, ?_⟩
      · simp only [readBack, hs]
        rw [h3]
        exact h1
      · intro s' hs' ib hslot
        rcases List.mem_cons.mp hs' with rfl | hs'
        · rw [hs] at hslot
          cases hslot
          rw [h4 _ (fun s'' hs'' ib' hslot' => hne s'' hs'' ib' hslot'), ha3]
        · rw [h2 s' hs' ib hslot, ho3 _ (hne s' hs' ib hslot)]
      · intro t ht
        have htia : ia.txIdx ≠ t := ht s (List.mem_cons_self ..) ia hs
        rw [h4 t fun s' hs' ib hslot => ht s' (List.mem_cons_of_mem _ hs') ib hslot,
          ho3 t (Ne.symm htia)]
      · rw [h5, hk3]
      · rw [h6, hl3]

end Solanalib.Runtime
