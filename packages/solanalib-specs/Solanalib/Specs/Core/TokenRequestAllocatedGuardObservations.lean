/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuardCollection
public import Solanalib.Specs.Core.TokenRequestAllocatedHooks

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

private def entryRead {Extra : Type} (state : World Extra)
    (entry : AllocatedCollect.Element) : Option (Solanalib.Runtime.Pubkey × Option Bytes) := do
  let bytes ← entry.2.read state
  return (entry.1, some bytes)

private theorem entry_reads {Extra : Type} {before after : World Extra}
    (same : ∀ reference bytes, AllocatedControl.DataRef.read reference before = some bytes →
      reference.read after = some bytes)
    (entries : List AllocatedCollect.Element) (values : Hook.Observations)
    (read : entries.mapM (entryRead before) = some values) :
    entries.mapM (entryRead after) = some values := by
  induction entries generalizing values with
  | nil => exact read
  | cons entry rest induction =>
    rcases entry with ⟨key, reference⟩
    cases firstRead : reference.read before with
    | none =>
      have firstValue : entryRead before (key, reference) = none := by
        unfold entryRead
        rw [firstRead]
        rfl
      rw [List.mapM_cons, firstValue] at read
      cases read
    | some bytes =>
      have nextRead := same reference bytes firstRead
      have firstValue : entryRead before (key, reference) = some (key, some bytes) := by
        unfold entryRead
        rw [firstRead]
        rfl
      have nextValue : entryRead after (key, reference) = some (key, some bytes) := by
        unfold entryRead
        rw [nextRead]
        rfl
      rw [List.mapM_cons, firstValue] at read
      change ((rest.mapM (entryRead before)).bind
        (fun tail => some ((key, some bytes) :: tail))) = some values at read
      cases tailRead : rest.mapM (entryRead before) with
      | none => rw [tailRead] at read; cases read
      | some tail =>
        have nextTail := induction tail tailRead
        rw [tailRead] at read
        cases read
        rw [List.mapM_cons, nextValue]
        change ((rest.mapM (entryRead after)).bind
          (fun tail => some ((key, some bytes) :: tail))) = _
        rw [nextTail]
        rfl

/-- The actual normal exit of a callback retains the complete guard observation:
both the same vector entries and the same live current account bytes. -/
theorem guardObservations_returned {types : OnchainAllocated.Types}
    {Args Result : Type} {call : Callback.Run (World types.Extra) Args Result
      types.Unwind types.Terminal}
    (frames : Preserves call) (storage : Retains types.guards.current call)
    {before after : World types.Extra} {args : Args} {result : Result}
    {resource : types.GuardResource} {values : Hook.Observations}
    (valid : before.1.Valid)
    (read : OnchainAllocated.guardObservations types resource before = some values)
    (called : call before args (.returned result after)) :
    OnchainAllocated.guardObservations types resource after = some values := by
  unfold OnchainAllocated.guardObservations at read ⊢
  cases current : types.guards.current before resource with
  | none => rw [current] at read; cases read
  | some entries =>
    have kept := storage before args resource entries current _ called
    rw [current] at read
    rw [show types.guards.current after resource = some entries from kept]
    exact entry_reads (fun _ _ readable => frames.read_returned valid readable called) entries
      values read

/-- Unwind preserves the same observation until actual scope cleanup begins;
neither callback state effects nor the unwind reason are discarded. -/
theorem guardObservations_unwound {types : OnchainAllocated.Types}
    {Args Result : Type} {call : Callback.Run (World types.Extra) Args Result
      types.Unwind types.Terminal}
    (frames : Preserves call) (storage : Retains types.guards.current call)
    {before after : World types.Extra} {args : Args} {reason : types.Unwind}
    {resource : types.GuardResource} {values : Hook.Observations}
    (valid : before.1.Valid)
    (read : OnchainAllocated.guardObservations types resource before = some values)
    (called : call before args (.unwound reason after)) :
    OnchainAllocated.guardObservations types resource after = some values := by
  unfold OnchainAllocated.guardObservations at read ⊢
  cases current : types.guards.current before resource with
  | none => rw [current] at read; cases read
  | some entries =>
    have kept := storage before args resource entries current _ called
    rw [current] at read
    rw [show types.guards.current after resource = some entries from kept]
    exact entry_reads (fun _ _ readable => frames.read_unwound valid readable called) entries
      values read

/-- The exact retained list fixes the vector-drop exemption. An outer guard
cannot become an owned element merely through an unrelated primitive effect. -/
theorem guardDrop_outer {types : OnchainAllocated.Types}
    (law : PreservesExcept (ownedGuards types.guards) types.guards.drop)
    {before : World types.Extra}
    {resource : types.GuardResource} {entries : List AllocatedCollect.Element}
    {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    (valid : before.1.Valid) (live : before.1.resolve guard = some slot)
    (current : types.guards.current before resource = some entries)
    (outside : guard ∉ entries.map (fun entry => entry.2.guard))
    {outcome : Outcome (World types.Extra) Unit types.Unwind types.Terminal}
    (called : types.guards.drop before resource outcome) :
    AccountInfo.GuardCallback.Frame before guard outcome :=
  law before resource valid guard slot live
    (by simpa only [ownedGuards, current, Option.getD_some] using outside) outcome called

/-- A returned internal collection chunk leaves the next indexed iterator
read available with the original order/count. No later Trace is assumed. -/
theorem collection_internal_iterator {types : OnchainAllocated.Types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    {before after : World types.Extra} {resource : types.InfoResource}
    {length index step : Nat} {info : AccountInfo.Value}
    {acquired : List AllocatedCollect.Element}
    (law : Retains types.infos.current (fun state (_ : Unit) => protocol.internal step acquired
      state))
    (read : (OnchainAllocated.infoIterator types resource length).elementAt before index = some
      info)
    (called : protocol.internal step acquired before (.returned () after)) :
    (OnchainAllocated.infoIterator types resource length).elementAt after index = some info := by
  change (do
    let infos ← types.infos.current before resource
    if infos.length = length then infos[index]? else none) = some info at read
  cases current : types.infos.current before resource with
  | none => rw [current] at read; cases read
  | some entries =>
    have kept := law before () resource entries current _ called
    simpa only [OnchainAllocated.infoIterator, show types.infos.current after resource = some
      entries
      from kept, current] using read

/-- Actual successful source acquisition changes only the account guard
store. The borrowed input vector therefore keeps its exact next element. -/
theorem collection_borrow_iterator {types : OnchainAllocated.Types}
    (law : CurrentOnAux types.infos.current)
    {before after : World types.Extra} {resource : types.InfoResource}
    {length index : Nat} {info argument : AccountInfo.Value} {element : AllocatedCollect.Element}
    (read : (OnchainAllocated.infoIterator types resource length).elementAt before index = some
      info)
    (called : AllocatedCollect.borrowElement types.raise before argument (.returned (.ok element)
      after)) :
    (OnchainAllocated.infoIterator types resource length).elementAt after index = some info := by
  obtain ⟨pending, borrowed, continued⟩ := called
  cases pending with
  | returned result state =>
    cases result with
    | error _ => cases continued
    | ok reference =>
      cases continued
      have same := law.same (borrow_returned borrowed).2.1 resource
      simpa only [OnchainAllocated.infoIterator, same] using read
  | unwound _ _ => cases continued
  | terminated _ => cases continued

end Solanalib.Specs.Core.Token.AllocatedGuard
