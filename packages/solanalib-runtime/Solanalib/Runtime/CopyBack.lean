/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.StoreOps

@[expose] public section

/-!
# Copy-back as an abstract store implementation

`stepCopyBack` is a second mathematical implementation of the operations in
`StoreOps`. `copyBack_run` proves agreement with `stepInPlace` under `CopyRel`
and `WellBracketedRun`; those are explicit hypotheses of the theorem. It does
not assert that an upstream account interface delays writes until release, or
establish equivalence of the runtime memory configurations. See
[library state and derived
proofs](../../source-notes/agave-4.3.2.md#library-state-and-derived-proofs).
-/

namespace Solanalib.Runtime

/-- The release under copy-back: the release of an exclusive lease writes the copy back. -/
def releaseCopy (c : Cell) (l : Lease) : Cell :=
  if c.lease = .exclusive then { c with lease := l, data := c.copy.getD c.data, copy := none }
  else { c with lease := l }

/-- A step with copy-back: an exclusive borrow takes a copy, writes go to the copy, and
the release writes it back. An observation reads the account itself. -/
def stepCopyBack (S : Store) (op : StoreOp) : Option (Store × Option Bytes) :=
  let c := S op.target
  match op with
  | .borrow i => (leaseStep c op).map fun l => (S.upd i { c with lease := l }, none)
  | .borrowMut i =>
    (leaseStep c op).map fun l => (S.upd i { c with lease := l, copy := some c.data }, none)
  | .release i =>
    (leaseStep c op).map fun l =>
      (S.upd i (releaseCopy c l), none)
  | .write i off bs =>
    if c.lease = .exclusive ∧ off + bs.length ≤ (c.copy.getD c.data).length then
      some (S.upd i { c with copy := some (writeAt (c.copy.getD c.data) off bs) }, none)
    else none
  | .resize i n =>
    if c.lease = .exclusive ∧ n ≤ c.entryLen + MAX_PERMITTED_DATA_INCREASE then
      some (S.upd i { c with copy := some (resizeZero (c.copy.getD c.data) n) }, none)
    else none
  | .setLamports i v => some (S.upd i { c with lamports := v }, none)
  | .assign i o => some (S.upd i { c with owner := o }, none)
  | .observe _ => some (S, some c.data)

/-- The relation between a store in place `S` and a store with copy-back `T`: equal
fields and leases, an outstanding copy exactly under an exclusive lease, and the data in
place equal to the copy where there is one. -/
def CopyRel (S T : Store) : Prop :=
  ∀ i, (S i).owner = (T i).owner ∧ (S i).lamports = (T i).lamports ∧
    (S i).entryLen = (T i).entryLen ∧ (S i).lease = (T i).lease ∧
    ((T i).lease = .exclusive → ∃ d, (T i).copy = some d ∧ (S i).data = d) ∧
    ((T i).lease ≠ .exclusive → (T i).copy = none ∧ (S i).data = (T i).data)

/-- Observations happen without an exclusive lease on the observed account. -/
def WellBracketed (T : Store) : StoreOp → Prop
  | .observe i => (T i).lease ≠ .exclusive
  | _ => True

theorem copyRel_upd {S T : Store} (h : CopyRel S T) {i : Nat} {c d : Cell}
    (hc : c.owner = d.owner ∧ c.lamports = d.lamports ∧ c.entryLen = d.entryLen ∧
      c.lease = d.lease ∧ (d.lease = .exclusive → ∃ x, d.copy = some x ∧ c.data = x) ∧
      (d.lease ≠ .exclusive → d.copy = none ∧ c.data = d.data)) :
    CopyRel (S.upd i c) (T.upd i d) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hc
  · simpa [Store.upd_ne _ _ _ _ hj] using h j

/-- T6 for one step: under the relation, both semantics succeed or fail together, keep
the relation, and agree on observations of accounts without an exclusive lease. -/
theorem copyBack_step {S T : Store} (h : CopyRel S T) (op : StoreOp) (hwb : WellBracketed T op) :
    match stepInPlace S op, stepCopyBack T op with
    | some (S', o), some (T', o') => CopyRel S' T' ∧ o = o'
    | none, none => True
    | _, _ => False := by
  obtain ⟨ho, hl, he, hlease, hex, hne⟩ := h op.target
  cases op with
  | borrow i =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target, leaseStep, hlease]
    cases hT : (T i).lease with
    | free =>
      have ⟨hc, hd⟩ := hne (by simp [hT])
      simp only [Lease.addShared, Option.map_some]
      exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, by simp, fun _ => ⟨hc, hd⟩⟩, trivial⟩
    | shared n =>
      have ⟨hc, hd⟩ := hne (by simp [hT])
      by_cases room : n < 254
      · simp only [Lease.addShared, room, ↓reduceIte, Option.map_some]
        exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, by simp, fun _ => ⟨hc, hd⟩⟩, trivial⟩
      · simp [Lease.addShared, room]
    | exclusive => simp [Lease.addShared]
  | borrowMut i =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target, leaseStep, hlease]
    by_cases hT : (T i).lease = .free
    · have ⟨_, hd⟩ := hne (by simp [hT])
      simp only [hT, ↓reduceIte, Option.map_some]
      exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, fun _ => ⟨_, rfl, hd⟩, fun hx => absurd rfl hx⟩,
        trivial⟩
    · simp [hT]
  | release i =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target, leaseStep, hlease]
    cases hT : (T i).lease with
    | free => simp [Lease.release]
    | shared n =>
      have ⟨hc, hd⟩ := hne (by simp [hT])
      match n with
      | 0 => simp [Lease.release]
      | 1 =>
        simp only [Lease.release, Option.map_some, releaseCopy, hT, reduceCtorEq, ↓reduceIte]
        exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, by simp, fun _ => ⟨hc, hd⟩⟩, trivial⟩
      | n + 2 =>
        simp only [Lease.release, Option.map_some, releaseCopy, hT, reduceCtorEq, ↓reduceIte]
        exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, by simp, fun _ => ⟨hc, hd⟩⟩, trivial⟩
    | exclusive =>
      obtain ⟨d, hc, hd⟩ := hex hT
      simp only [Lease.release, Option.map_some, releaseCopy, hT, ↓reduceIte, hc, Option.getD_some]
      exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, by simp, fun _ => ⟨rfl, hd⟩⟩, trivial⟩
  | write i off bs =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target]
    by_cases hT : (T i).lease = .exclusive
    · obtain ⟨d, hc, hd⟩ := hex hT
      simp only [hlease, hT, hc, hd, Option.getD_some, true_and]
      by_cases hb : off + bs.length ≤ d.length
      · simp only [hb, ↓reduceIte]
        exact ⟨copyRel_upd h ⟨ho, hl, he, rfl, fun _ => ⟨_, rfl, rfl⟩,
          fun hx => absurd rfl hx⟩, trivial⟩
      · simp [hb]
    · simp [hlease, hT]
  | resize i n =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target]
    by_cases hT : (T i).lease = .exclusive
    · obtain ⟨d, hc, hd⟩ := hex hT
      simp only [hlease, hT, hc, hd, he, Option.getD_some, true_and]
      by_cases hb : n ≤ (T i).entryLen + MAX_PERMITTED_DATA_INCREASE
      · simp only [hb, ↓reduceIte]
        exact ⟨copyRel_upd h ⟨ho, hl, rfl, rfl, fun _ => ⟨_, rfl, rfl⟩,
          fun hx => absurd rfl hx⟩, trivial⟩
      · simp [hb]
    · simp [hlease, hT]
  | setLamports i v =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target]
    exact ⟨copyRel_upd h ⟨ho, rfl, he, hlease, hex, hne⟩, trivial⟩
  | assign i o =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target]
    exact ⟨copyRel_upd h ⟨rfl, hl, he, hlease, hex, hne⟩, trivial⟩
  | observe i =>
    simp only [StoreOp.target] at ho hl he hlease hex hne
    simp only [stepInPlace, stepCopyBack, StoreOp.target]
    simp only [WellBracketed] at hwb
    exact ⟨h, by rw [(hne hwb).2]⟩

/-- A run of operations, with the observations in order. -/
def runOps (step : Store → StoreOp → Option (Store × Option Bytes)) :
    Store → List StoreOp → Option (Store × List (Option Bytes))
  | S, [] => some (S, [])
  | S, op :: ops =>
    match step S op with
    | none => none
    | some (S', o) =>
      match runOps step S' ops with
      | none => none
      | some (S'', os) => some (S'', o :: os)

/-- The well-bracketing of a whole trace, along the run with copy-back. -/
def WellBracketedRun : Store → List StoreOp → Prop
  | _, [] => True
  | T, op :: ops =>
    WellBracketed T op ∧
      match stepCopyBack T op with
      | some (T', _) => WellBracketedRun T' ops
      | none => True

/-- T6: on a well-bracketed trace, writes in place and copy-back succeed or fail
together, read the same values at every observation, and end in related stores. -/
theorem copyBack_run : ∀ {S T : Store} {ops : List StoreOp}, CopyRel S T →
    WellBracketedRun T ops →
    match runOps stepInPlace S ops, runOps stepCopyBack T ops with
    | some (S', os), some (T', os') => CopyRel S' T' ∧ os = os'
    | none, none => True
    | _, _ => False
  | S, T, [], h, _ => by simp only [runOps]; exact ⟨h, trivial⟩
  | S, T, op :: ops, h, hwb => by
    obtain ⟨hwb1, hwb2⟩ := hwb
    have hs := copyBack_step h op hwb1
    simp only [runOps]
    rcases hi : stepInPlace S op with _ | ⟨S', o⟩ <;>
      rcases hc : stepCopyBack T op with _ | ⟨T', o'⟩ <;> simp only [hi, hc] at hs ⊢
    · obtain ⟨hR, ho⟩ := hs
      simp only [hc] at hwb2
      have ih := copyBack_run (ops := ops) hR hwb2
      rcases h1 : runOps stepInPlace S' ops with _ | ⟨S'', os⟩ <;>
        rcases h2 : runOps stepCopyBack T' ops with _ | ⟨T'', os'⟩ <;>
        simp only [h1, h2] at ih ⊢
      exact ⟨ih.1, by rw [ho, ih.2]⟩

/-- When no lease is outstanding, related stores hold the same data. -/
theorem CopyRel.data_eq {S T : Store} (h : CopyRel S T) {i : Nat} (hfree : (T i).lease ≠
  .exclusive) :
    (S i).data = (T i).data := ((h i).2.2.2.2.2 hfree).2

end Solanalib.Runtime
