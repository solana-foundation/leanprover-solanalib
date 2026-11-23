/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedReferenceLaws

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

variable {State Outer Inner Resource Value Args StringResource BoxResource Terminal Target : Type}

/-- Changing terminal encodings leaves the exact normal callback relation. -/
theorem mapTerminal_returned_iff (convert : Terminal → Target)
    (run : Callback.Run State Args Value Empty Terminal)
    (before after : State) (args : Args) (value : Value) :
    mapTerminal convert run before args (.returned value after) ↔
      run before args (.returned value after) := by
  constructor
  · rintro ⟨actual, called, equal⟩
    cases actual with
    | unwound impossible _ => nomatch impossible
    | terminated _ => cases equal
    | returned _ _ => cases equal; exact called
  · intro called
    exact ⟨.returned value after, called, rfl⟩

/-- A focused normal callback has the corresponding actual inner execution. -/
theorem focus_returned_inner (part : Owned.Focus Outer Inner)
    {run : Callback.Run Inner Args Value Empty Terminal}
    {before after : Outer} {args : Args} {value : Value}
    (called : part.lift run before args (.returned value after)) :
    run (part.get before) args (.returned value (part.get after)) := by
  obtain ⟨actual, executed, equal⟩ := called
  cases actual with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases equal
  | returned _ _ =>
    cases equal
    simpa only [part.get_set] using executed

private theorem focus_store_inner (part : Owned.Focus Outer Inner)
    {write : Inner → Resource → Value → Option Inner}
    {before after : Outer} {resource : Resource} {value : Value}
    (stored : (write (part.get before) resource value).map (part.set before) = some after) :
    write (part.get before) resource value = some (part.get after) := by
  cases actual : write (part.get before) resource value with
  | none => rw [actual] at stored; cases stored
  | some inner =>
    rw [actual] at stored
    cases stored
    simp only [part.get_set]

/-- Fresh exact allocation laws survive a change of terminal vocabulary. -/
theorem AllocationLaws.mapTerminal
    {read : State → Resource → Option Value}
    {allocate : Callback.Run State Value Resource Empty Terminal}
    (laws : AllocationLaws read allocate) (convert : Terminal → Target) :
    AllocationLaws read (AnchorErrorOwned.mapTerminal convert allocate) where
  current := fun _ _ _ _ run =>
    laws.current _ _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  fresh := fun _ _ _ _ run =>
    laws.fresh _ _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  other := fun _ _ _ _ run =>
    laws.other _ _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)

/-- Retirement and rejection of absent resources survive terminal re-encoding. -/
theorem RetirementLaws.mapTerminal
    {read : State → Resource → Option Value}
    {retire : Callback.Run State Resource Unit Empty Terminal}
    (laws : RetirementLaws read retire) (convert : Terminal → Target) :
    RetirementLaws read (AnchorErrorOwned.mapTerminal convert retire) where
  present := by
    intro before resource outcome run
    obtain ⟨actual, called, _⟩ := run
    exact laws.present _ _ actual called
  current := fun _ _ _ run =>
    laws.current _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  other := fun _ _ _ run =>
    laws.other _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)

/-- A lawful focus retains all local allocation observations and freshness. -/
theorem AllocationLaws.focus (part : Owned.Focus Outer Inner)
    {read : Inner → Resource → Option Value}
    {allocate : Callback.Run Inner Value Resource Empty Terminal}
    (laws : AllocationLaws read allocate) :
    AllocationLaws (fun before resource => read (part.get before) resource) (part.lift allocate)
      where
  current := fun _ _ _ _ run =>
    laws.current _ _ _ _ (focus_returned_inner part run)
  fresh := fun _ _ _ _ run =>
    laws.fresh _ _ _ _ (focus_returned_inner part run)
  other := fun _ _ _ _ run =>
    laws.other _ _ _ _ (focus_returned_inner part run)

/-- Retirement laws are local to the same focused component. -/
theorem RetirementLaws.focus (part : Owned.Focus Outer Inner)
    {read : Inner → Resource → Option Value}
    {retire : Callback.Run Inner Resource Unit Empty Terminal}
    (laws : RetirementLaws read retire) :
    RetirementLaws (fun before resource => read (part.get before) resource) (part.lift retire) where
  present := by
    intro before resource outcome run
    obtain ⟨actual, called, _⟩ := run
    exact laws.present _ _ actual called
  current := fun _ _ _ run =>
    laws.current _ _ _ (focus_returned_inner part run)
  other := fun _ _ _ run =>
    laws.other _ _ _ (focus_returned_inner part run)

/-- A lawful focused store preserves identity and updates only its component. -/
theorem StoreLaws.focus (part : Owned.Focus Outer Inner)
    {read : Inner → Resource → Option Value}
    {write : Inner → Resource → Value → Option Inner}
    (laws : StoreLaws read write) :
    StoreLaws (fun before resource => read (part.get before) resource)
      (fun before resource value => (write (part.get before) resource value).map (part.set before))
        where
  available := by
    intro before resource old value present
    obtain ⟨after, stored⟩ := laws.available _ _ _ _ present
    exact ⟨part.set before after, by rw [stored]; rfl⟩
  present := fun _ _ _ _ stored =>
    laws.present _ _ _ _ (focus_store_inner part stored)
  current := fun _ _ _ _ stored =>
    laws.current _ _ _ _ (focus_store_inner part stored)
  other := fun _ _ _ _ stored =>
    laws.other _ _ _ _ (focus_store_inner part stored)

/-- All String/Box laws survive changing only terminal-reason representation. -/
theorem Ops.mapTerminal_laws (ops : Ops State StringResource BoxResource Terminal)
    (laws : ops.Laws) (convert : Terminal → Target) : (ops.mapTerminal convert).Laws where
  copy := laws.copy.mapTerminal convert
  format := laws.format.mapTerminal convert
  box := laws.box.mapTerminal convert
  stringDrop := laws.stringDrop.mapTerminal convert
  boxFree := laws.boxFree.mapTerminal convert
  store := laws.store
  copy_boxes := fun _ _ _ _ run =>
    laws.copy_boxes _ _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  format_boxes := fun _ _ _ _ run =>
    laws.format_boxes _ _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  box_strings := fun _ _ _ _ run =>
    laws.box_strings _ _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  drop_boxes := fun _ _ _ run =>
    laws.drop_boxes _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)
  store_strings := laws.store_strings
  free_strings := fun _ _ _ run =>
    laws.free_strings _ _ _ ((mapTerminal_returned_iff _ _ _ _ _ _).mp run)

/-- All primitive local and cross-resource laws survive a lawful focus;
the ambient frame remains exactly the one specified by that focus. -/
theorem Ops.focus_laws (ops : Ops Inner StringResource BoxResource Terminal)
    (laws : ops.Laws) (part : Owned.Focus Outer Inner) : (ops.focus part).Laws where
  copy := laws.copy.focus part
  format := laws.format.focus part
  box := laws.box.focus part
  stringDrop := laws.stringDrop.focus part
  boxFree := laws.boxFree.focus part
  store := laws.store.focus part
  copy_boxes := fun _ _ _ _ run =>
    laws.copy_boxes _ _ _ _ (focus_returned_inner part run)
  format_boxes := fun _ _ _ _ run =>
    laws.format_boxes _ _ _ _ (focus_returned_inner part run)
  box_strings := fun _ _ _ _ run =>
    laws.box_strings _ _ _ _ (focus_returned_inner part run)
  drop_boxes := fun _ _ _ run =>
    laws.drop_boxes _ _ _ (focus_returned_inner part run)
  store_strings := fun _ _ _ _ stored =>
    laws.store_strings _ _ _ _ (focus_store_inner part stored)
  free_strings := fun _ _ _ run =>
    laws.free_strings _ _ _ (focus_returned_inner part run)

/-- The Nat-terminal variant of the finite heap has the same complete primitive laws. -/
theorem Reference.natOps_laws : Reference.natOps.Laws :=
  Reference.ops.mapTerminal_laws Reference.ops_laws Reference.Failure.code

end Solanalib.Specs.Core.AnchorErrorOwned
