/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.WritesLegal
public import Solanalib.Runtime.Frame

@[expose] public section

/-!
# Theorems connecting the layers

`readBackL_of_legal` proves successful read-back under `WritesLegalL`. For a successful
run without CPI in configuration L, `noCpi_result` identifies the final read-back and
its exact account effects. Both results retain their layout and validity hypotheses.

At a CPI boundary the runtime checks caller synchronization and privileges. `Exec.frame`
bounds the effects of a successful callee; a particular callee behavior remains an
explicit contract. No callee implementation proof is supplied by this package.

The package also supplies the library representation predicates and `Env` for
implementation proofs, and `copyBack_run` for well-bracketed abstract store operations.
That theorem does not establish equivalence of the three runtime memory configurations.

See the [model report](../../README.md#model-report) for checked results and correspondence.
The [current source
justification](../../source-notes/agave-4.3.2.md#library-state-and-derived-proofs)
distinguishes these internal Lean theorems from the additional conditions needed
to connect a concrete program and the selected Agave runtime to the model.
-/

namespace Solanalib.Runtime

/-- A run without CPI. -/
def NoCpi : List (Event × Reply) → Prop
  | [] => True
  | (.sys (.invoke _), _) :: _ => False
  | _ :: rest => NoCpi rest

theorem storeRegion_L_ts {c : InvCtx} {st st' : InvState} {a : Nat} {bs : Bytes} (hL : c.cfg = .L)
    (h : storeRegion c st a bs = .ok st') : st'.ts = st.ts := by
  unfold storeRegion at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · unfold storeAt at h
      rw [hL] at h
      cases h
      rfl

/-- The property of runs without CPI in configuration L: a successful run ends in the
read-back of its final buffer, with the accounts, keys and resize counter it started
with. -/
def NoCpiProp : Judgment → Prop
  | .invoke c st evs fin r =>
    c.cfg = .L → NoCpi evs → fin = .exit 0 → ∀ ts', r = .ok ts' →
      ∃ st' : InvState, st'.ts.accts = st.ts.accts ∧ st'.ts.keys = st.ts.keys ∧
        st'.ts.resizeDelta = st.ts.resizeDelta ∧
        readBack c.abi .L c.frame.programIdx st'.buf st'.ts c.layout c.release = .ok ts'
  | _ => True

theorem Exec.noCpiL {W : World} {j : Judgment} (h : Exec W j) : NoCpiProp j := by
  induction h with
  | @exit0 c st r hrb =>
    intro hL _ _ ts' hr
    refine ⟨st, rfl, rfl, rfl, ?_⟩
    rw [← hL, hrb, hr]
  | exitErr _ => intro _ _ _ ts' hr; cases hr
  | fault => intro _ _ hf; cases hf
  | invCompute _ => intro _ _ _ ts' hr; cases hr
  | load _ _ ih => intro hL hn hf ts' hr; exact ih hL hn hf ts' hr
  | loadFail _ => intro _ _ _ ts' hr; cases hr
  | @store c st st' a bs rest fin r hs _ ih =>
    intro hL hn hf ts' hr
    obtain ⟨st'', h1, h2, h3, h4⟩ := ih hL hn hf ts' hr
    have hts := storeRegion_L_ts hL hs
    exact ⟨st'', by rw [h1, hts], by rw [h2, hts], by rw [h3, hts], h4⟩
  | storeFail _ => intro _ _ _ ts' hr; cases hr
  | unregistered _ => intro _ _ _ ts' hr; cases hr
  | @sys c st st' req ans rest fin r _ hs _ ih =>
    intro hL hn hf ts' hr
    have hn' : NoCpi rest := by
      cases req <;> simp_all [NoCpi]
    obtain ⟨st'', h1, h2, h3, h4⟩ := ih hL hn' hf ts' hr
    obtain ⟨ha, hk, _, hrd, _⟩ := sysStep_accts hs
    exact ⟨st'', by rw [h1, ha], by rw [h2, hk], by rw [h3, hrd], h4⟩
  | sysFail _ _ _ _ => intro _ _ _ ts' hr; cases hr
  | remainingComputeUnits _ _ ih =>
    intro hL hn hf ts' hr
    exact ih hL (by simpa [NoCpi] using hn) hf ts' hr
  | cpi _ _ _ _ _ _ _ => intro _ hn; exact absurd hn (by simp [NoCpi])
  | cpiPrepareFail _ => intro _ _ _ ts' hr; cases hr
  | cpiCalleeSyncFail _ _ => intro _ _ _ ts' hr; cases hr
  | cpiCalleeFail _ _ _ _ => intro _ _ _ ts' hr; cases hr
  | cpiCallerSyncFail _ _ _ _ _ => intro _ _ _ ts' hr; cases hr
  | _ => trivial

/-- T1 for a run without CPI in configuration L: if the run succeeds, its result is the
read-back of its final buffer from the accounts the run started with; and when that buffer
satisfies `WritesLegal`, the result sets each account to the values of the buffer and
changes no other account. -/
theorem noCpi_result {W : World} {c : InvCtx} {st : InvState} {evs : List (Event × Reply)}
    {r : Except InstrError TxState} (h : Invoke W c st evs (.exit 0) r) (hL : c.cfg = .L)
    (hv1 : c.abi = .v1) (hn : NoCpi evs) {ts' : TxState} (hr : r = .ok ts') :
    ∃ st' : InvState, st'.ts.accts = st.ts.accts ∧ st'.ts.keys = st.ts.keys ∧
      st'.ts.resizeDelta = st.ts.resizeDelta ∧
      readBack .v1 .L c.frame.programIdx st'.buf st'.ts c.layout c.release = .ok ts' ∧
      (NonDupDistinct c.layout →
        (∀ s ∈ c.layout, ∀ ia, s.slot = .acct ia → ia.txIdx < st'.ts.accts.length) →
        WritesLegalL c.frame.programIdx st'.buf st'.ts c.layout →
        (∀ s ∈ c.layout, ∀ ia, s.slot = .acct ia →
          ts'.acct ia.txIdx = applied (st'.ts.acct ia.txIdx) (bufVals .v1 st'.buf s)) ∧
        (∀ t, (∀ s ∈ c.layout, ∀ ia, s.slot = .acct ia → ia.txIdx ≠ t) →
          ts'.acct t = st'.ts.acct t)) := by
  obtain ⟨st', h1, h2, h3, h4⟩ := Exec.noCpiL h hL hn rfl ts' hr
  rw [hv1] at h4
  refine ⟨st', h1, h2, h3, h4, fun hd hidx hleg => ?_⟩
  obtain ⟨ts'', h5, h6, h7, _, _⟩ := readBackL_of_legal (release := c.release) c.layout st'.ts hd
    hidx hleg
  rw [h4] at h5
  cases h5
  exact ⟨h6, h7⟩

end Solanalib.Runtime
