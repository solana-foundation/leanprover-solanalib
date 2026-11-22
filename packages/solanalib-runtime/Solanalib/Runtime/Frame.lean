/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Transaction

@[expose] public section

/-!
# The frame property of instructions

Every change that an instruction makes to an account passes a check that requires the
writable flag of the account in the instruction that makes it, and a callee receives the
writable flag only where its caller holds it. The source argument uses Agave 4.3.2,
`transaction-context/src/instruction_accounts.rs:91-205,286-310,338-357` for the mutation
checks and `program-runtime/src/invoke_context.rs:434-459` for CPI privileges;
see the [current CPI justification](../../source-notes/agave-4.3.2.md#cpi).
The theorem `ProcInstr.frame` states the consequence for a whole instruction, with its
CPIs, its builtins and every program, a program about which nothing is known included:
only the writable accounts of the instruction change, apart from the two index bytes of
the Instructions sysvar that `push` writes, and the balance invariant
`lamportSum - lamportsDelta` holds.
`ProcInstr.lamports` derives that a successful top-level instruction keeps the sum of all
balances, and `Execute.not_unbalanced` that the check `UnbalancedTransaction` after
execution never fails.
These are theorems of the Lean model. Applying them to deployed execution requires
the source and input correspondence, including the CPI feature and memory assumptions
in `Solanalib.Runtime.Cpi`.
-/

namespace Solanalib.Runtime

/-- An account writable in an instruction. -/
def WritableTx (f : Frame) (j : Nat) : Prop := ∃ ia ∈ f.accounts, ia.txIdx = j ∧ ia.writable = true

/-- The index of the Instructions sysvar among the keys of a transaction. -/
def IsIxSysvar (keys : List Pubkey) (j : Nat) : Prop := keys.idxOf? Ids.sysvarInstructions = some j

/-- The accounts that an instruction may change. -/
def MayChange (keys : List Pubkey) (f : Frame) (j : Nat) : Prop := WritableTx f j ∨ IsIxSysvar keys
  j

/-- The effect of an execution on the accounts: the keys and the number of accounts stay,
the accounts outside `W` keep their state, and the balance invariant holds. -/
structure ExecChanges (ts ts' : TxState) (W : Nat → Prop) : Prop where
  keys : ts'.keys = ts.keys
  length : ts'.accts.length = ts.accts.length
  other : ∀ j, ¬ W j → ts'.acct j = ts.acct j
  balance : (ts'.lamportSum : Int) - ts'.lamportsDelta = ts.lamportSum - ts.lamportsDelta
  touches : TouchChanges ts ts'

namespace ExecChanges

theorem refl (ts : TxState) (W : Nat → Prop) : ExecChanges ts ts W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, TouchChanges.refl ts⟩

theorem trans {ts ts' ts'' : TxState} {W : Nat → Prop} (h1 : ExecChanges ts ts' W)
    (h2 : ExecChanges ts' ts'' W) : ExecChanges ts ts'' W :=
  ⟨h2.keys.trans h1.keys, h2.length.trans h1.length,
    fun j hj => (h2.other j hj).trans (h1.other j hj), h2.balance.trans h1.balance,
    h1.touches.trans h2.touches⟩

theorem mono {ts ts' : TxState} {W W' : Nat → Prop} (h : ExecChanges ts ts' W)
    (hW : ∀ j, W j → W' j) : ExecChanges ts ts' W' :=
  ⟨h.keys, h.length, fun j hj => h.other j (fun hw => hj (hW j hw)), h.balance, h.touches⟩

theorem of_changes {ts ts' : TxState} {W : Nat → Prop} (h : Changes ts ts' W) : ExecChanges ts ts'
  W :=
  ⟨h.keys, h.length, h.other, h.balance, h.touches⟩

/-- Two states with the same keys, accounts and lamport counter. -/
theorem of_eq {ts ts' : TxState} {W : Nat → Prop} (hk : ts'.keys = ts.keys)
    (ha : ts'.accts = ts.accts) (hd : ts'.lamportsDelta = ts.lamportsDelta)
    (ht : ts'.touched = ts.touched) : ExecChanges ts ts' W :=
  ⟨hk, by rw [ha], fun j _ => by simp only [TxState.acct, ha],
    by simp only [TxState.lamportSum, ha, hd], TouchChanges.of_eq hk ha ht⟩

end ExecChanges

/-! ## Push, pop and the reset of the return data -/

theorem writeIxSysvarIndex_spec {ts ts' : TxState} (h : writeIxSysvarIndex ts = .ok ts') :
    ExecChanges ts ts' (IsIxSysvar ts.keys) ∧ ts'.lamportsDelta = ts.lamportsDelta := by
  unfold writeIxSysvarIndex at h
  dsimp only at h
  split at h
  · cases h; exact ⟨ExecChanges.refl _ _, rfl⟩
  · rename_i j hj
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        have hc : Changes ts { ts with accts := ts.accts.set j { ts.acct j with
            data := writeAt (ts.acct j).data ((ts.acct j).data.length - 2) (u16le ts.topIndex) } }
            (· = j) :=
          Changes.of_setAcct rfl rfl rfl rfl rfl rfl rfl rfl
            (TouchChanges.of_sysvar_update rfl rfl rfl hj)
        refine ⟨(ExecChanges.of_changes hc).mono ?_, rfl⟩
        intro k hk
        subst hk
        exact hj

theorem push_spec {p : Profile} {ts ts1 : TxState} {f : Frame} (h : push p ts f = .ok ts1) :
    ExecChanges ts ts1 (IsIxSysvar ts.keys) ∧ ts1.lamportsDelta = ts.lamportsDelta := by
  unfold push at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i ts2 hw
            cases h
            obtain ⟨hc, hd⟩ := writeIxSysvarIndex_spec hw
            exact ⟨⟨hc.keys, hc.length, hc.other, hc.balance,
              ⟨hc.touches.keys, hc.touches.mono, hc.touches.untouched⟩⟩, hd⟩

theorem pop_spec {ts ts' : TxState} (h : pop ts = .ok ts') :
    ts'.keys = ts.keys ∧ ts'.accts = ts.accts ∧ ts'.lamportsDelta = ts.lamportsDelta ∧
    ts.lamportsDelta = 0 := by
  unfold pop at h
  dsimp only at h
  by_cases hd : ts.lamportsDelta = 0
  · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, by simp [hd], hd⟩
  · simp [hd] at h

theorem pop_touched {ts ts' : TxState} (h : pop ts = .ok ts') : ts'.touched = ts.touched := by
  unfold pop at h
  dsimp only at h
  by_cases balanced : ts.lamportsDelta = 0
  · simp only [balanced, ne_eq, not_true_eq_false, ↓reduceIte, Except.ok.injEq] at h
    subst h
    rfl
  · simp [balanced] at h

theorem afterProgram_ok {r : Except InstrError TxState} {ts' : TxState}
    (h : afterProgram r = .ok ts') : ∃ ts2, r = .ok ts2 ∧ pop ts2 = .ok ts' := by
  unfold afterProgram at h
  split at h
  · cases h
  · rename_i ts2
    exact ⟨ts2, rfl, h⟩

theorem resetReturnData_changes (ts : TxState) (W : Nat → Prop) :
    ExecChanges ts (resetReturnData ts) W := ExecChanges.of_eq rfl rfl rfl rfl

theorem setNativeReturnData_changes (ts : TxState) (programId : Pubkey) (data : Bytes)
    (W : Nat → Prop) : ExecChanges ts (setNativeReturnData ts programId data) W :=
  ExecChanges.of_eq rfl rfl rfl rfl

/-- The loader cache update preserves all account observations of the frame theorem. -/
theorem applyLoaderV3Effect_changes (slot : Nat) (before : TxState) (frame : Frame)
    (after : TxState) (W : Nat → Prop) :
    ExecChanges after (applyLoaderV3Effect slot before frame after) W :=
  ExecChanges.of_eq (applyLoaderV3Effect_keys slot before after frame)
    (applyLoaderV3Effect_accts slot before after frame)
    (applyLoaderV3Effect_lamportsDelta slot before after frame)
    (applyLoaderV3Effect_touched slot before after frame)

/-! ## The callee of a CPI -/

theorem prepareCallee_writable {ts : TxState} {caller g : Frame} {ix : CpiInstruction}
    {pdas : List Pubkey} (h : prepareCallee ts caller ix pdas = .ok g) :
    ∀ ia ∈ g.accounts, ia.writable = true → WritableTx caller ia.txIdx := by
  unfold prepareCallee at h
  split at h
  · cases h
  · rename_i dedup hd
    split at h
    · cases h
    · rename_i hp
      split at h
      · cases h
      · cases h
        intro ia hia hw
        have hmem : ia ∈ dedup := by
          unfold calleeAccounts at hia
          obtain ⟨m, _, hm⟩ := List.mem_filterMap.mp hia
          cases ht : txIndexOf ts m.key with
          | none => simp [ht] at hm
          | some t =>
            simp only [ht, Option.bind_some] at hm
            exact List.mem_of_find?_eq_some hm
        have hc := forE_mem hp ia hmem
        unfold checkPrivileges at hc
        split at hc
        · cases hc
        · split at hc
          · cases hc
          · rename_i hn
            have hwt : caller.writableTx ia.txIdx = true := by
              cases hx : caller.writableTx ia.txIdx
              · simp [hw, hx] at hn
              · rfl
            unfold Frame.writableTx at hwt
            obtain ⟨b, hb, hb2⟩ := List.any_eq_true.mp hwt
            simp only [Bool.and_eq_true, beq_iff_eq] at hb2
            exact ⟨b, hb, hb2.1, hb2.2⟩

theorem translateOne_spec {p : Profile} {c : InvCtx} {ts : TxState} {req : CpiReq}
    {ia : InstrAcct} {x : Translated} (h : translateOne p c ts req ia = .ok (some x)) :
    x.t = ia.txIdx ∧ (x.callerWritable = true → WritableTx c.frame x.t) := by
  unfold translateOne at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · rename_i k s _ _
      simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
          refine ⟨rfl, fun hw => ?_⟩
          simp only at hw
          split at hw
          · rename_i cia hcia
            have hmem := List.mem_of_find?_eq_some hcia
            have hp := List.find?_some hcia
            simp only [beq_iff_eq] at hp
            exact ⟨cia, hmem, hp, hw⟩
          · cases hw

theorem translateInfos_spec {p : Profile} {c : InvCtx} {ts : TxState} {req : CpiReq}
    {callee : Frame} {tr : List Translated} (h : translateInfos p c ts req callee = .ok tr) :
    ∀ x ∈ tr, x.callerWritable = true → WritableTx c.frame x.t := by
  unfold translateInfos at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i xs hxs
        cases h
        intro x hx hw
        obtain ⟨o, ho, hox⟩ := List.mem_filterMap.mp hx
        simp only [id] at hox
        subst hox
        obtain ⟨ia, _, hia⟩ := mapE_mem hxs (some x) ho
        exact (translateOne_spec hia).2 hw

theorem cpiPrepare_spec {p : Profile} {P : Prims} {c : InvCtx} {ts : TxState} {req : CpiReq}
    {prep : CpiPrep} (h : cpiPrepare p P c ts req = .ok prep) :
    (∀ ia ∈ prep.callee.accounts, ia.writable = true → WritableTx c.frame ia.txIdx) ∧
    (∀ x ∈ prep.translated, x.callerWritable = true → WritableTx c.frame x.t) := by
  unfold cpiPrepare at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i callee hcallee
          split at h
          · cases h
          · rename_i tr htr
            cases h
            exact ⟨prepareCallee_writable hcallee, translateInfos_spec htr⟩

/-! ## The System program -/

theorem acctAt_writable {f : Frame} {j : Nat} (h : (f.accounts.getD j default).writable = true) :
    WritableTx f (f.accounts.getD j default).txIdx := by
  rw [List.getD_eq_getElem?_getD] at h ⊢
  cases hj : f.accounts[j]? with
  | none => simp [hj] at h; cases h
  | some ia =>
    simp only [hj, Option.getD_some] at h ⊢
    exact ⟨ia, List.mem_of_getElem? hj, rfl, h⟩

theorem sysSetter_changes {c : SysCtx} {ts ts' : TxState} {j : Nat}
    (h : SetterStep ts ts' (c.sc ts j)) : Changes ts ts' (WritableTx c.f) :=
  (Changes.of_setterStep h).mono fun k ⟨hk, hw⟩ => by
    subst hk
    exact acctAt_writable hw

theorem sysAllocate_changes {c : SysCtx} {ts ts' : TxState} {j : Nat} {a : Pubkey × Option Pubkey}
    {space : Nat} (h : sysAllocate c ts j a space = .ok ts') : Changes ts ts' (WritableTx c.f) := by
  unfold sysAllocate at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · exact sysSetter_changes (SetterStep.of_setDataLength h)

theorem sysAssign_changes {c : SysCtx} {ts ts' : TxState} {j : Nat} {a : Pubkey × Option Pubkey}
    {o : Pubkey} (h : sysAssign c ts j a o = .ok ts') : Changes ts ts' (WritableTx c.f) := by
  unfold sysAssign at h
  split at h
  · cases h; exact Changes.refl _ _
  · split at h
    · cases h
    · exact sysSetter_changes (SetterStep.of_setOwner h)

theorem sysAllocateAndAssign_changes {c : SysCtx} {ts ts' : TxState} {j : Nat}
    {a : Pubkey × Option Pubkey} {space : Nat} {o : Pubkey}
    (h : sysAllocateAndAssign c ts j a space o = .ok ts') : Changes ts ts' (WritableTx c.f) := by
  unfold sysAllocateAndAssign at h
  split at h
  · cases h
  · rename_i ts1 h1
    exact (sysAllocate_changes h1).trans (sysAssign_changes h)

theorem sysTransferVerified_changes {c : SysCtx} {ts ts' : TxState} {s d n : Nat}
    (h : sysTransferVerified c ts s d n = .ok ts') : Changes ts ts' (WritableTx c.f) := by
  unfold sysTransferVerified at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i ts1 h1
        exact (sysSetter_changes (SetterStep.of_checkedSubLamports h1)).trans
          (sysSetter_changes (SetterStep.of_checkedAddLamports h))

theorem sysTransfer_changes {c : SysCtx} {ts ts' : TxState} {s d n : Nat}
    (h : sysTransfer c ts s d n = .ok ts') : Changes ts ts' (WritableTx c.f) := by
  unfold sysTransfer at h
  split at h
  · cases h
  · exact sysTransferVerified_changes h

theorem sysCreateAccount_changes {c : SysCtx} {ts ts' : TxState} {a : Pubkey × Option Pubkey}
    {l s : Nat} {o : Pubkey} (h : sysCreateAccount c ts a l s o = .ok ts') :
    Changes ts ts' (WritableTx c.f) := by
  unfold sysCreateAccount at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i ts1 h1
      exact (sysAllocateAndAssign_changes h1).trans (sysTransfer_changes h)

theorem systemProcess_changes {p : Profile} {P : Prims} {ts ts' : TxState} {f : Frame}
    (h : systemProcess p P ts f = some (.ok ts')) : Changes ts ts' (WritableTx f) := by
  unfold systemProcess at h
  split at h
  · cases h
  · rename_i ix _
    split at h <;> (try cases h) <;> (simp only [Option.some.injEq] at h) <;>
      (repeat' split at h) <;> (try cases h) <;>
      first
        | exact Changes.refl _ _
        | exact sysCreateAccount_changes (c := ⟨ts, f, p.release⟩) h
        | exact sysAssign_changes (c := ⟨ts, f, p.release⟩) h
        | exact sysTransfer_changes (c := ⟨ts, f, p.release⟩) h
        | exact sysTransferVerified_changes (c := ⟨ts, f, p.release⟩) h
        | exact sysAllocate_changes (c := ⟨ts, f, p.release⟩) h
        | exact sysAllocateAndAssign_changes (c := ⟨ts, f, p.release⟩) h
        | (refine Changes.trans ?_ (sysTransfer_changes (c := ⟨ts, f, p.release⟩) h)
           exact sysAllocateAndAssign_changes (c := ⟨ts, f, p.release⟩) (by assumption))
        | exact sysAllocateAndAssign_changes (c := ⟨ts, f, p.release⟩) (by assumption)

theorem applySetter_step {r : RentParams} {op : SetterOp} {ts ts' : TxState} {sc : SetterCtx}
    (h : applySetter r op ts sc = .ok ts') : SetterStep ts ts' sc := by
  cases op with
  | lamports v => exact SetterStep.of_setLamports h
  | dataFromSlice d => exact SetterStep.of_setDataFromSlice h
  | dataLength n => exact SetterStep.of_setDataLength h
  | owner o => exact SetterStep.of_setOwner h
  | executable b => exact SetterStep.of_setExecutable h

/-! ## The layout of an invocation -/

/-- The positions of an invocation context are instruction accounts of its frame. -/
def LayoutIn (c : InvCtx) : Prop :=
  ∀ s ∈ c.layout, ∀ ia, s.slot = .acct ia → ia ∈ c.frame.accounts

theorem layoutIn_invCtxOf (W : World) (abi : Abi) (ts : TxState) (f : Frame) :
    LayoutIn (invCtxOf W abi ts f) := by
  intro s hs ia hslot
  simp only [invCtxOf, layout, List.mem_mapIdx] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  simp only at hslot
  rw [slotOf_acct hslot]
  exact List.getElem_mem hj

theorem writableIn_of_layoutIn {c : InvCtx} (hc : LayoutIn c) {j : Nat}
    (h : WritableIn c.layout j) : WritableTx c.frame j := by
  obtain ⟨s, hs, ia, hslot, hj, hw⟩ := h
  exact ⟨ia, hc s hs ia hslot, hj, hw⟩

/-! ## The frame theorem -/

/-- The frame property of each judgment: a successful instruction, program or open
builtin changes only the accounts its frame may change, and a successful run only those
of the frame of its invocation. -/
def FrameProp : Judgment → Prop
  | .procInstr ts f r => ∀ ts', r = .ok ts' → ExecChanges ts ts' (MayChange ts.keys f)
  | .runProgram ts f r => ∀ ts', r = .ok ts' → ExecChanges ts ts' (MayChange ts.keys f)
  | .havoc ts f r => ∀ ts', r = .ok ts' → ExecChanges ts ts' (MayChange ts.keys f)
  | .invoke c st _ _ r =>
    LayoutIn c → ∀ ts', r = .ok ts' → ExecChanges st.ts ts' (MayChange st.ts.keys c.frame)

/-- The frame theorem, by induction over the execution relation. -/
theorem Exec.frame {W : World} {j : Judgment} (h : Exec W j) : FrameProp j := by
  induction h with
  | pushFail _ => intro ts' hr; cases hr
  | @run ts ts1 f r hpush _ ih =>
    intro ts' hr
    obtain ⟨ts2, hr2, hpop⟩ := afterProgram_ok hr
    obtain ⟨hp, _⟩ := push_spec hpush
    have e3 : ExecChanges _ ts2 _ := ih ts2 hr2
    obtain ⟨hk, ha, hd, _⟩ := pop_spec hpop
    have e1 := hp.mono (W' := MayChange ts.keys f) fun j hj => Or.inr hj
    have e2 := resetReturnData_changes ts1 (MayChange ts.keys f)
    have hk3 : (resetReturnData ts1).keys = ts.keys := hp.keys
    rw [hk3] at e3
    exact e1.trans (e2.trans (e3.trans (ExecChanges.of_eq hk ha hd (pop_touched hpop))))
  | compute _ => intro ts' hr; cases hr
  | unsupported _ => intro ts' hr; cases hr
  | serializationFailed _ _ => intro ts' hr; cases hr
  | system _ hs =>
    intro ts' hr
    subst hr
    exact (ExecChanges.of_changes (systemProcess_changes hs)).mono fun j hj => Or.inl hj
  | systemNonce _ _ _ ih => exact ih
  | computeBudget _ => intro ts' hr; cases hr; exact ExecChanges.refl _ _
  | unmodelled _ _ _ ih => exact ih
  | loaderV3 _ _ finished _ ih =>
    intro ts' hr
    obtain ⟨returned, returnedOk, rfl⟩ := finishLoaderV3_ok (finished.trans hr)
    exact (ih returned returnedOk).trans (applyLoaderV3Effect_changes _ _ _ _ _)
  | sbf _ _ _ _ ih =>
    intro ts' hr
    exact ih (layoutIn_invCtxOf _ _ _ _) ts' hr
  | havocDone => intro ts' hr; cases hr; exact ExecChanges.refl _ _
  | havocFail => intro ts' hr; cases hr
  | @havocReturnData ts f r programId data _ ih =>
    intro ts' hr
    exact (setNativeReturnData_changes ts programId data _).trans (ih ts' hr)
  | @havocSetter ts ts₁ f r op ia hia hset _ ih =>
    intro ts' hr
    have hs := applySetter_step hset
    have e1 : ExecChanges ts ts₁ (MayChange ts.keys f) :=
      (ExecChanges.of_changes (Changes.of_setterStep hs)).mono fun j ⟨hj, hw⟩ =>
        Or.inl ⟨ia, hia, hj.symm, hw⟩
    have e2 : ExecChanges ts₁ ts' _ := ih ts' hr
    rw [hs.keys] at e2
    exact e1.trans e2
  | @havocInvoke ts ts₁ f g r ix seeds pdas _ hprep _ _ ihp ihr =>
    intro ts' hr
    have e1 : ExecChanges ts ts₁ (MayChange ts.keys g) := ihp ts₁ rfl
    have hw := prepareCallee_writable hprep
    have e1' := e1.mono (W' := MayChange ts.keys f) fun j hj => by
      rcases hj with ⟨ia, hia, hj, hw'⟩ | hj
      · exact Or.inl (hj ▸ hw ia hia hw')
      · exact Or.inr hj
    have e2 : ExecChanges ts₁ ts' _ := ihr ts' hr
    rw [e1.keys] at e2
    exact e1'.trans e2
  | @exit0 c st r hrb =>
    intro hc ts' hr
    subst hr
    exact (ExecChanges.of_changes (Changes.of_readBack hrb)).mono fun j hj =>
      Or.inl (writableIn_of_layoutIn hc hj)
  | exitErr _ => intro _ ts' hr; cases hr
  | fault => intro _ ts' hr; cases hr
  | invCompute _ => intro _ ts' hr; cases hr
  | load _ _ ih => exact ih
  | loadFail _ => intro _ ts' hr; cases hr
  | @store c st st' a bs rest fin r hs _ ih =>
    intro hc ts' hr
    have e1 := (ExecChanges.of_changes (Changes.of_storeRegion hs)).mono
      (W' := MayChange st.ts.keys c.frame) fun j hj => Or.inl (writableIn_of_layoutIn hc hj)
    have e2 : ExecChanges st'.ts ts' _ := ih hc ts' hr
    rw [e1.keys] at e2
    exact e1.trans e2
  | storeFail _ => intro _ ts' hr; cases hr
  | unregistered _ => intro _ ts' hr; cases hr
  | @sys c st st' req ans rest fin r _ hs _ ih =>
    intro hc ts' hr
    obtain ⟨ha, hk, hd, _⟩ := sysStep_accts hs
    have e1 : ExecChanges st.ts st'.ts (MayChange st.ts.keys c.frame) :=
      ExecChanges.of_eq hk ha hd (sysStep_touched hs)
    have e2 : ExecChanges st'.ts ts' _ := ih hc ts' hr
    rw [e1.keys] at e2
    exact e1.trans e2
  | sysFail _ _ _ _ => intro _ ts' hr; cases hr
  | remainingComputeUnits _ _ ih => exact ih
  | @cpi c st st1 st2 req prep ts2 lens rest fin r hprep hcallee _ hcaller _ ihp ihr =>
    intro hc ts' hr
    obtain ⟨hpw, htw⟩ := cpiPrepare_spec hprep
    have e1 := (ExecChanges.of_changes (Changes.of_updateCallee hcallee)).mono
      (W' := MayChange st.ts.keys c.frame) fun j ⟨x, hx, hj, hw⟩ => Or.inl (hj ▸ htw x hx hw)
    have e2 : ExecChanges st1.ts ts2 (MayChange st1.ts.keys prep.callee) := ihp ts2 rfl
    have e2' := e2.mono (W' := MayChange st.ts.keys c.frame) fun j hj => by
      rcases hj with ⟨ia, hia, hj, hw⟩ | hj
      · exact Or.inl (hj ▸ hpw ia hia hw)
      · rw [e1.keys] at hj; exact Or.inr hj
    have hts := updateCaller_ts hcaller
    have e3 : ExecChanges st2.ts ts' _ := ihr hc ts' hr
    rw [hts] at e3
    simp only at e3
    rw [e2.keys, e1.keys] at e3
    exact e1.trans (e2'.trans e3)
  | cpiPrepareFail _ => intro _ ts' hr; cases hr
  | cpiCalleeSyncFail _ _ => intro _ ts' hr; cases hr
  | cpiCalleeFail _ _ _ _ => intro _ ts' hr; cases hr
  | cpiCallerSyncFail _ _ _ _ _ => intro _ ts' hr; cases hr

/-- The frame theorem for instructions: a successful instruction changes only its
writable accounts and the index bytes of the Instructions sysvar, and keeps the balance
invariant. -/
theorem ProcInstr.frame {W : World} {ts : TxState} {f : Frame} {r : Except InstrError TxState}
    (h : ProcInstr W ts f r) : ∀ ts', r = .ok ts' → ExecChanges ts ts' (MayChange ts.keys f) :=
  Exec.frame h

/-! ## Conservation of lamports -/

/-- A successful instruction leaves the lamport counter at zero, which the pop checks. -/
theorem ProcInstr.delta_zero {W : World} {ts ts' : TxState} {f : Frame}
    (h : ProcInstr W ts f (.ok ts')) : ts'.lamportsDelta = 0 := by
  change Exec W (Judgment.procInstr ts f (.ok ts')) at h
  generalize hj : Judgment.procInstr ts f (.ok ts') = j at h
  cases h with
  | run _ _ =>
    injection hj with _ _ hr
    obtain ⟨ts2, _, hpop⟩ := afterProgram_ok hr.symm
    obtain ⟨_, _, hd, hd0⟩ := pop_spec hpop
    rw [hd, hd0]
  | _ => cases hj

/-- A successful instruction that starts with a zero lamport counter keeps the sum of all
balances. Every top-level instruction starts so, since the counter starts at zero and
every successful pop requires it to be zero. -/
theorem ProcInstr.lamports {W : World} {ts ts' : TxState} {f : Frame}
    (h : ProcInstr W ts f (.ok ts')) (h0 : ts.lamportsDelta = 0) :
    ts'.lamportSum = ts.lamportSum ∧ ts'.lamportsDelta = 0 := by
  have e := ProcInstr.frame h ts' rfl
  have hd := ProcInstr.delta_zero h
  have := e.balance
  rw [hd, h0] at this
  exact ⟨by omega, hd⟩

theorem processPrecompile_lamports {W : World} {ts ts' : TxState} {f : Frame} {d : List Bytes}
    (h : processPrecompile W ts f d = .ok ts') :
    ts'.lamportSum = ts.lamportSum ∧ ts'.lamportsDelta = 0 ∧ ts'.keys = ts.keys ∧
    ts'.accts.length = ts.accts.length := by
  unfold processPrecompile at h
  split at h
  · cases h
  · rename_i ts1 hpush
    split at h
    · cases h
    · obtain ⟨hp, hd1⟩ := push_spec hpush
      obtain ⟨hk, ha, hd, hd0⟩ := pop_spec h
      have := hp.balance
      refine ⟨?_, by rw [hd, hd0], by rw [hk, hp.keys], by rw [ha, hp.length]⟩
      have hs : ts'.lamportSum = ts1.lamportSum := by simp only [TxState.lamportSum, ha]
      rw [hd1] at this
      rw [hd0, hd1] at *
      omega

/-- A successful message keeps the sum of all balances. -/
theorem ProcMessage.lamports {W : World} {d : List Bytes} :
    ∀ {ts : TxState} {fs : List Frame} {k : Nat} {ts' : TxState},
      ProcMessage W d ts fs k (.ok ts') → ts.lamportsDelta = 0 →
      ts'.lamportSum = ts.lamportSum := by
  intro ts fs k ts' h h0
  generalize hr : (Except.ok ts' : Except TxError TxState) = r at h
  induction h with
  | nil => cases hr; rfl
  | precompile _ hpre _ ih =>
    obtain ⟨hs, hd, _, _⟩ := processPrecompile_lamports hpre
    rw [ih hd hr, hs]
  | precompileFail _ _ => cases hr
  | instr _ hproc _ ih =>
    obtain ⟨hs, hd⟩ := ProcInstr.lamports hproc h0
    rw [ih hd hr, hs]
  | instrFail _ _ => cases hr

theorem ProcMessage.error_form {W : World} {d : List Bytes} {ts : TxState} {fs : List Frame}
    {k : Nat} {e : TxError} (h : ProcMessage W d ts fs k (.error e)) :
    ∃ i ie, e = .InstructionError i ie := by
  generalize hr : (Except.error e : Except TxError TxState) = r at h
  induction h with
  | nil => cases hr
  | precompile _ _ _ ih => exact ih hr
  | precompileFail _ _ => cases hr; exact ⟨_, _, rfl⟩
  | instr _ _ _ ih => exact ih hr
  | instrFail _ _ => cases hr; exact ⟨_, _, rfl⟩

theorem rentCheckAll_error {p : Profile} {m : Message} {pre post : List Account} {e : TxError}
    (h : rentCheckAll p m pre post = .error e) : ∃ i, e = .InsufficientFundsForRent i := by
  unfold rentCheckAll at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- Successful invocation keeps every prior touch and preserves accounts that
remain untouched, apart from the administrative Instructions-sysvar update. -/
theorem ProcInstr.touches {W : World} {before after : TxState} {frame : Frame}
    (execution : ProcInstr W before frame (.ok after)) : TouchChanges before after :=
  (ProcInstr.frame execution after rfl).touches

theorem processPrecompile_touches {W : World} {before after : TxState} {frame : Frame}
    {data : List Bytes} (execution : processPrecompile W before frame data = .ok after) :
    TouchChanges before after := by
  unfold processPrecompile at execution
  split at execution
  · cases execution
  · rename_i pushed pushedEq
    split at execution
    · cases execution
    · have pushedChanges := (push_spec pushedEq).1.touches
      obtain ⟨keys, accounts, _, _⟩ := pop_spec execution
      exact pushedChanges.trans (TouchChanges.of_eq keys accounts (pop_touched execution))

/-- Touch metadata is preserved compositionally through the actual message run. -/
theorem ProcMessage.touches {W : World} {data : List Bytes} {before after : TxState}
    {frames : List Frame} {index : Nat}
    (execution : ProcMessage W data before frames index (.ok after)) :
    TouchChanges before after := by
  generalize result : (Except.ok after : Except TxError TxState) = returned at execution
  induction execution with
  | nil => cases result; exact TouchChanges.refl _
  | precompile _ step _ ih => exact (processPrecompile_touches step).trans (ih result)
  | precompileFail _ _ => cases result
  | instr _ step _ ih => exact (ProcInstr.touches step).trans (ih result)
  | instrFail _ _ => cases result

theorem Execute.touches {B : BankEnv} {tx : Tx} {loaded : List Account} {post : TxState}
    (execution : Execute B tx loaded (.ok post)) :
    TouchChanges (initTxState tx.message.keys loaded) post := by
  cases execution with
  | ok run _ _ => exact ProcMessage.touches run

/-- An untouched ordinary account retains its exact loaded value. Eligibility
for storage separately excludes the Instructions sysvar. -/
theorem Execute.untouched {B : BankEnv} {tx : Tx} {loaded : List Account} {post : TxState}
    (execution : Execute B tx loaded (.ok post)) (index : Nat)
    (untouched : index ∉ post.touched) (ordinary : ¬ IsIxSysvar tx.message.keys index) :
    post.acct index = loaded.getD index default :=
  execution.touches.untouched index untouched ordinary

/-- The check `UnbalancedTransaction` after execution never fails: the checks of the
lamport counter at every push and pop already keep the sum of all balances. -/
theorem Execute.not_unbalanced {B : BankEnv} {tx : Tx} {loaded : List Account} :
    ¬ Execute B tx loaded (.error .UnbalancedTransaction) := by
  intro h
  generalize he : (Except.error TxError.UnbalancedTransaction : Except TxError TxState) = r at h
  cases h with
  | ok _ _ _ => cases he
  | rentFail _ hr =>
    cases he
    obtain ⟨i, hi⟩ := rentCheckAll_error hr
    cases hi
  | unbalanced hm _ hne =>
    exact hne (ProcMessage.lamports hm rfl)
  | fail hm =>
    cases he
    obtain ⟨i, ie, hi⟩ := ProcMessage.error_form hm
    cases hi

end Solanalib.Runtime
