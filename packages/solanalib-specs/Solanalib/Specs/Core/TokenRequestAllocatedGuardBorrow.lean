/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuardScope
public import Solanalib.Specs.Core.TokenRequestAllocatedCollect
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardInputs

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

open AccountInfo.GuardCallback

/-- The checked and unchecked source borrow use the same actual acquisition
state. Their different error/panic interpretations do not roll it back. -/
theorem borrowData_state (checked : Bool) (state : AccountInfo.State) (info : AccountInfo.Value) :
    (Onchain.borrowData checked state info).2 =
      (Borrow.acquire state info.data .shared .whole).2 := by
  unfold Onchain.borrowData AccountInfo.tryBorrow
  cases Borrow.acquire state info.data .shared .whole with
  | mk result after =>
    cases result with
    | error _ => cases checked <;> rfl
    | ok guard =>
      dsimp only [Except.mapError]
      cases Borrow.current after guard with
      | error _ => rfl
      | ok value => cases value with
        | mk view content => cases content <;> rfl

/-- Every represented normal borrow return came from the actual successful
acquisition and current data observation, with the same new guard identity. -/
theorem borrowData_success {checked : Bool} {before after : AccountInfo.State}
    {info : AccountInfo.Value} {borrowed : Onchain.Borrowed}
    (success : Onchain.borrowData checked before info = (.success borrowed, after)) :
    Borrow.acquire before info.data .shared .whole = (.ok borrowed.guard, after) ∧
      Borrow.current after borrowed.guard = .ok (.whole, .data borrowed.bytes) := by
  unfold Onchain.borrowData at success
  cases acquired : AccountInfo.tryBorrow .shared info.data before with
  | mk result during =>
    cases result with
    | error _ => cases checked <;> simp only [acquired] at success <;> cases success
    | ok guard =>
      simp only [acquired] at success
      cases current : Borrow.current during guard with
      | error _ => simp only [current] at success; cases success
      | ok value =>
        cases value with
        | mk view contents =>
          cases contents with
          | lamports _ => simp only [current] at success; cases success
          | data bytes =>
            simp only [current] at success
            cases success
            have actual := tryBorrow_acquire acquired
            have live := Borrow.acquire_success actual
            obtain ⟨cell, found⟩ := live.2.2
            have now := Borrow.acquire_current actual found
            have eqView : view = .whole := (Prod.mk.inj (Except.ok.inj (current.symm.trans now))).1
            cases eqView
            exact ⟨actual, current⟩

/-- Successful acquisition always appends a fresh guard id. An old live guard
therefore cannot be returned as the newly acquired collection element. -/
theorem acquire_fresh {before after : AccountInfo.State} {handle : Borrow.Handle}
    {mode : Borrow.Mode} {view : AccountInfo.View} {guard : Borrow.Guard}
    (success : Borrow.acquire before handle mode view = (.ok guard, after)) :
    guard.id = before.slots.length := by
  cases present : before.lookupCell handle with
  | none => simp only [Borrow.acquire, present, Prod.mk.injEq, reduceCtorEq, false_and] at success
  | some cell =>
    cases mode with
    | shared =>
      simp only [Borrow.acquire, present] at success
      split at success
      · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at success
      · split at success
        · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at success
        · exact (congrArg Borrow.Guard.id (Except.ok.inj (Prod.mk.inj success).1)).symm
    | exclusive =>
      simp only [Borrow.acquire, present] at success
      split at success
      · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at success
      · exact (congrArg Borrow.Guard.id (Except.ok.inj (Prod.mk.inj success).1)).symm

/-- Borrowing is an actual local protocol operation, followed only on unchecked
failure by the separately admitted panic callback. Every old live guard stays
framed, including when the new acquisition fails. -/
theorem borrow_preserves {Extra Unwind Terminal : Type}
    {raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal}
    (raiseLaw : Preserves raise) (checked : Bool) (info : AccountInfo.Value) :
    Preserves (fun state (_ : Unit) => AllocatedControl.borrow raise checked info state) := by
  intro before _ valid guard slot live _ outcome called
  have stateFrame := acquire_other valid live info.data .shared .whole
  rw [← borrowData_state checked before.1 info] at stateFrame
  unfold AllocatedControl.borrow AllocatedControl.fromStep at called
  cases result : Onchain.borrowData checked before.1 info with
  | mk step after =>
    simp only [result] at stateFrame called
    cases step with
    | success borrowed => cases called; exact stateFrame
    | error error => cases called; exact stateFrame
    | malformed => exact False.elim called
    | panic reason =>
      obtain ⟨actual, raised, same⟩ := called
      have frame := raiseLaw (after, before.2) reason stateFrame.valid guard slot
        (stateFrame.resolve live) (by simp) actual raised
      cases actual with
      | returned impossible _ => exact nomatch impossible
      | unwound _ _ => cases same; exact Frame.prepend stateFrame frame
      | terminated _ => cases same; trivial

/-- A successful allocated borrow exposes its true acquisition, immediate read
and unchanged auxiliary state. Panic has no fabricated ordinary return. -/
theorem borrow_returned {Extra Unwind Terminal : Type}
    {raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal}
    {checked : Bool} {info : AccountInfo.Value} {before after : World Extra}
    {reference : AllocatedControl.DataRef}
    (called : AllocatedControl.borrow raise checked info before (.returned (.ok reference) after)) :
    Borrow.acquire before.1 info.data .shared .whole = (.ok reference.guard, after.1) ∧
      after.2 = before.2 ∧ ∃ bytes, reference.read after = some bytes := by
  unfold AllocatedControl.borrow AllocatedControl.fromStep at called
  cases result : Onchain.borrowData checked before.1 info with
  | mk step during =>
    simp only [result] at called
    cases step with
    | success borrowed =>
      cases called
      obtain ⟨acquired, current⟩ := borrowData_success result
      exact ⟨acquired, rfl, borrowed.bytes, by simp only [AllocatedControl.DataRef.read, current,
        ↓reduceIte]⟩
    | error _ => cases called
    | malformed => exact False.elim called
    | panic _ =>
      obtain ⟨actual, _, same⟩ := called
      cases actual with
      | returned impossible _ => exact nomatch impossible
      | unwound _ _ => cases same
      | terminated _ => cases same

/-- The exact source collection callback preserves all preexisting live guards.
This conclusion is derived from acquisition and panic primitives. -/
theorem borrowElement_preserves {Extra Unwind Terminal : Type}
    {raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal}
    (raiseLaw : Preserves raise) : Preserves (AllocatedCollect.borrowElement raise) := by
  intro before info valid guard slot live absent outcome called
  obtain ⟨pending, borrowed, continued⟩ := called
  have frame := borrow_preserves raiseLaw true info before () valid guard slot live absent pending
    borrowed
  cases pending with
  | returned value state =>
    cases value with
    | ok reference => cases continued; exact frame
    | error error => cases continued; exact frame
  | unwound reason state => cases continued; exact frame
  | terminated reason => cases continued; trivial

/-- A returned collection element owns a fresh identity, distinct from every
guard that was already live when this particular callback was invoked. -/
theorem borrowElement_fresh {Extra Unwind Terminal : Type}
    {raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal}
    {before after : World Extra} {info : AccountInfo.Value} {element : AllocatedCollect.Element}
    {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    (live : before.1.resolve guard = some slot)
    (called : AllocatedCollect.borrowElement raise before info (.returned (.ok element) after)) :
    element.2.guard ≠ guard := by
  obtain ⟨pending, borrowed, continued⟩ := called
  cases pending with
  | returned value state =>
    cases value with
    | error _ => cases continued
    | ok reference =>
      cases continued
      have fresh := acquire_fresh (borrow_returned borrowed).1
      have old := Borrow.State.lookupSlot_bound (Borrow.State.resolve_some_iff.mp live).1
      intro same
      have ids := congrArg Borrow.Guard.id same
      change reference.guard.id = before.1.slots.length at fresh
      change reference.guard.id = guard.id at ids
      omega
  | unwound _ _ => cases continued
  | terminated _ => cases continued

/-- A represented checked borrow always has its exact local normal outcome:
either AccountBorrowFailed or a newly acquired readable DataRef. This is a
fact about the local pure borrow, not termination of an arbitrary callback. -/
theorem checked_borrow_exists {Extra Unwind Terminal : Type}
    (raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal)
    (before : World Extra) {profile : AccountInfo.Profile} {info : AccountInfo.Value}
    (ready : AccountInfo.Valid profile before.1 info) :
    ∃ result after, AllocatedControl.borrow raise true info before (.returned result after) := by
  cases acquired : AccountInfo.tryBorrow .shared info.data before.1 with
  | mk result during =>
    cases result with
    | error _ =>
      refine ⟨.error .AccountBorrowFailed, (during, before.2), ?_⟩
      simp only [AllocatedControl.borrow, AllocatedControl.fromStep, Onchain.borrowData,
        acquired, ↓reduceIte]
    | ok guard =>
      obtain ⟨stored, present, _⟩ := ready.2.2.2.2
      obtain ⟨bytes, current⟩ := data_current ⟨stored, profile.policy, present⟩ acquired
      refine ⟨.ok ⟨guard, bytes.length⟩, (during, before.2), ?_⟩
      simp only [AllocatedControl.borrow, AllocatedControl.fromStep, Onchain.borrowData,
        acquired, current]

/-- A primitive cannot disappear at the next checked acquisition by changing
an input data cell into lamports or removing it. The proof consumes its actual
return and the pointwise input law, with no complete body outcome premise. -/
theorem InputPreserves.borrow_after {Extra Args Value Unwind Terminal : Type}
    {wordBits : Nat} {call : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : InputPreserves wordBits call)
    (raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal)
    {before after : World Extra} {args : Args} {value : Value}
    {profile : AccountInfo.Profile} {info : AccountInfo.Value}
    (width : profile.wordBits = wordBits)
    (ready : AccountInfo.Valid profile before.1 info)
    (called : call before args (.returned value after)) :
    ∃ result final, AllocatedControl.borrow raise true info after (.returned result final) :=
  checked_borrow_exists raise after ((law before args ready.2.1 _ called).accountInfo width ready)

end Solanalib.Specs.Core.Token.AllocatedGuard
