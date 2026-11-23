/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedControl
public import Solanalib.Specs.Core.AccountInfoGuardCallback

/-!
Pointwise admission for primitive effects while Token holds data references.
The law is checked before any dependent read or cleanup. In particular it
quantifies the finite exits of a primitive even when the enclosing computation has
no final outcome. The raw operational relations remain unchanged.
-/

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

open AccountInfo.GuardCallback

/-- The actual AccountInfo borrow store and the captured state of the provider. -/
abbrev World (Extra : Type) := AccountInfo.State × Extra

/-- A primitive may retire only the guards it owns at this actual call input.
Every other live guard is protected on every returned or unwound exit. The
law constrains no terminal post-state and supplies no callback termination. -/
def PreservesExcept {Extra Args Value Unwind Terminal : Type}
    (owned : World Extra → Args → List Borrow.Guard)
    (run : Callback.Run (World Extra) Args Value Unwind Terminal) : Prop :=
  ∀ before args, before.1.Valid → ∀ guard slot,
    before.1.resolve guard = some slot → guard ∉ owned before args →
      Admissible guard run before args

/-- Allocation, scalar writes and other non-guard-owning primitive calls must
preserve every live caller-held guard, including guards in enclosing scopes. -/
def Preserves {Extra Args Value Unwind Terminal : Type}
    (run : Callback.Run (World Extra) Args Value Unwind Terminal) : Prop :=
  PreservesExcept (fun _ _ => []) run

/-- A provider with no finite exits satisfies a partial-correctness law without
asserting a normal return, unwind, terminal exit or termination. -/
theorem Preserves.empty {Extra Args Value Unwind Terminal : Type} :
    Preserves (fun (_ : World Extra) (_ : Args)
      (_ : Outcome (World Extra) Value Unwind Terminal) => False) := by
  intro _ _ _ _ _ _ _ _ impossible
  exact False.elim impossible

/-- A primitive that keeps the borrow store unchanged may still change all of
its auxiliary state. Such an effect preserves every live guard. -/
theorem Preserves.of_accounts {Extra Args Value Unwind Terminal : Type}
    {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (unchanged : ∀ before args outcome, run before args outcome →
      match outcome with
      | .returned _ after | .unwound _ after => after.1 = before.1
      | .terminated _ => True) : Preserves run := by
  intro before args valid guard _ _ _ outcome called
  have same := unchanged before args outcome called
  cases outcome with
  | returned _ after =>
    change StateFrame before.1 after.1 guard
    rw [same]
    exact StateFrame.refl _ _ valid
  | unwound _ after =>
    change StateFrame before.1 after.1 guard
    rw [same]
    exact StateFrame.refl _ _ valid
  | terminated _ => trivial

/-- The no-owned-guard law implies any weaker, explicitly owned exemption. -/
theorem Preserves.except {Extra Args Value Unwind Terminal : Type}
    {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves run) (owned : World Extra → Args → List Borrow.Guard) :
    PreservesExcept owned run := by
  intro before args valid guard slot live _
  exact law before args valid guard slot live (by simp)

/-- Mapping a return value does not alter admission or any callback effect. -/
theorem Preserves.map {Extra Args Value Next Unwind Terminal : Type}
    (f : Value → Next) {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves run) : Preserves (Callback.map f run) := by
  intro before args valid guard slot live absent
  exact (law before args valid guard slot live absent).map f

/-- Composition checks the first primitive independently of any later exit.
The next call is checked at every actual returned state of that primitive. A
later missing read therefore cannot excuse destruction of an earlier guard. -/
theorem Preserves.bind {Extra Args Value Next Unwind Terminal : Type}
    {first : Callback.Run (World Extra) Args Value Unwind Terminal}
    {next : Value → World Extra → Outcome (World Extra) Next Unwind Terminal → Prop}
    (firstLaw : Preserves first)
    (nextLaw : ∀ value, Preserves (fun state (_ : Unit) => next value state)) :
    Preserves (Callback.bind first next) := by
  intro before args valid guard slot live absent
  have admitted := firstLaw before args valid guard slot live absent
  apply admitted.bind
  intro value after called
  have frame : StateFrame before.1 after.1 guard := admitted _ called
  exact nextLaw value after () frame.valid guard slot (frame.resolve live) absent

/-- Restricting call arguments does not add or discard primitive exits. -/
theorem Preserves.arguments {Extra Args Selected Value Unwind Terminal : Type}
    {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves run) (select : Selected → Args) :
    Preserves (fun state selected => run state (select selected)) := by
  intro before args valid guard slot live absent
  exact law before (select args) valid guard slot live absent

/-- An actual successful reference read identifies a live guard and a present
data cell. This is an input observation, not a freely supplied guard identity. -/
theorem read_live {Extra : Type} {reference : AllocatedControl.DataRef}
    {before : World Extra} {bytes : Bytes} (read : reference.read before = some bytes) :
    ∃ slot cell, before.1.resolve reference.guard = some slot ∧
      before.1.lookupCell slot.cell = some cell ∧ cell.value = .data bytes ∧
      bytes.length = reference.length := by
  unfold AllocatedControl.DataRef.read Borrow.current at read
  cases live : before.1.resolve reference.guard with
  | none => simp [live] at read
  | some slot =>
    cases found : before.1.lookupCell slot.cell with
    | none => simp [live, found] at read
    | some cell =>
      cases contents : cell.value with
      | lamports _ => simp [live, found, contents] at read
      | data actual =>
        simp only [live, found, contents] at read
        split at read
        · rename_i length
          cases read
          exact ⟨slot, cell, rfl, found, contents, length⟩
        · cases read

/-- The protected reference is re-read from the actual after-state. The
pointwise frame preserves its exact current bytes and captured slice length. -/
theorem read_preserved {Extra : Type} {reference : AllocatedControl.DataRef}
    {before after : World Extra} {bytes : Bytes}
    (read : reference.read before = some bytes)
    (frame : StateFrame before.1 after.1 reference.guard) :
    reference.read after = some bytes := by
  obtain ⟨slot, cell, live, found, contents, length⟩ := read_live read
  obtain ⟨next, nextFound, _, same⟩ := frame.current live found
  have nextContents : next.value = .data bytes := same.trans contents
  simp only [AllocatedControl.DataRef.read, Borrow.current, frame.resolve live,
    nextFound, nextContents, length, ↓reduceIte]

/-- This prefix conclusion uses a real primitive return, with no hypothesis
that a subsequent read, source body or cleanup ever produces an outcome. -/
theorem Preserves.read_returned {Extra Args Value Unwind Terminal : Type}
    {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves run) {before after : World Extra} {args : Args}
    {reference : AllocatedControl.DataRef} {bytes : Bytes} {value : Value}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (called : run before args (.returned value after)) :
    reference.read after = some bytes := by
  obtain ⟨slot, _, live, _⟩ := read_live read
  exact read_preserved read (law before args valid reference.guard slot live (by simp) _ called)

/-- An unwinding primitive retains the same live reference in its actual
unwind state, where the enclosing scope performs checked cleanup. -/
theorem Preserves.read_unwound {Extra Args Value Unwind Terminal : Type}
    {run : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : Preserves run) {before after : World Extra} {args : Args}
    {reference : AllocatedControl.DataRef} {bytes : Bytes} {reason : Unwind}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    (called : run before args (.unwound reason after)) :
    reference.read after = some bytes := by
  obtain ⟨slot, _, live, _⟩ := read_live read
  exact read_preserved read (law before args valid reference.guard slot live (by simp) _ called)

end Solanalib.Specs.Core.Token.AllocatedGuard
