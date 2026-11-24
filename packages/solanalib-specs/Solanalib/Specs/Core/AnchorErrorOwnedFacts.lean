/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

variable {State StringResource BoxResource Terminal : Type}

/-- A normal program-error conversion is exactly its primitive Box allocation. -/
theorem fromProgram_returned_iff (ops : Ops State StringResource BoxResource Terminal)
    (before after : State) (program : ProgramError.Value) (error : Error BoxResource) :
    fromProgram ops before program (.returned error after) ↔
      ops.newBox before (.program ⟨program, none, none⟩) (.returned error.resource after) := by
  cases error with
  | mk resource =>
      constructor
      · rintro ⟨intermediate, allocated, returned⟩
        cases intermediate with
        | returned actual final => cases returned; exact allocated
        | unwound impossible _ => nomatch impossible
        | terminated _ => cases returned
      · intro allocated
        exact ⟨.returned resource after, allocated, rfl⟩

/-- A normal fixed-code construction records all three actual intermediate
states and the two String identities before the final Box identity. -/
theorem buildCode_returned_iff (ops : Ops State StringResource BoxResource Terminal)
    (before after : State) (code : Code) (error : Error BoxResource) :
    buildCode ops before code (.returned error after) ↔
      ∃ name afterName message afterMessage,
        ops.copyLiteral before code.name (.returned name afterName) ∧
        ops.formatLiteral afterName code.message (.returned message afterMessage) ∧
        ops.newBox afterMessage (.anchor ⟨name, code.number, message, none, none⟩)
          (.returned error.resource after) := by
  cases error with
  | mk resource =>
      constructor
      · rintro ⟨first, copied, remaining⟩
        cases first with
        | unwound impossible _ => nomatch impossible
        | terminated _ => cases remaining
        | returned name afterName =>
            obtain ⟨second, formatted, last⟩ := remaining
            cases second with
            | unwound impossible _ => nomatch impossible
            | terminated _ => cases last
            | returned message afterMessage =>
                obtain ⟨third, allocated, returned⟩ := last
                cases third with
                | unwound impossible _ => nomatch impossible
                | terminated _ => cases returned
                | returned actual final =>
                    cases returned
                    exact ⟨name, afterName, message, afterMessage, copied, formatted, allocated⟩
      · rintro ⟨name, afterName, message, afterMessage, copied, formatted, allocated⟩
        exact ⟨.returned name afterName, copied, .returned message afterMessage, formatted,
          .returned resource after, allocated, rfl⟩

/-- A normal diagnostic replacement returns the identical Box handle. -/
theorem withPubkeys_identity (ops : Ops State StringResource BoxResource Terminal)
    {before after : State} {error result : Error BoxResource} {left right :
      Solanalib.Runtime.Pubkey}
    (run : withPubkeys ops before (error, left, right) (.returned result after)) :
    result = error := by
  obtain ⟨_, _, intermediate, _, remaining⟩ := run
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned _ _ =>
      obtain ⟨_, _, _, _, returned⟩ := remaining
      cases returned
      rfl

/-- A dead Box cannot supply a second finite error drop, including a terminal
one manufactured from a missing resource. -/
theorem dropError_dead (ops : Ops State StringResource BoxResource Terminal)
    (before : State) (error : Error BoxResource)
    (dead : ops.currentBox before error.resource = none)
    (outcome : Outcome State Unit Empty Terminal) : ¬ dropError ops error before outcome := by
  rintro ⟨payload, present, _⟩
  rw [dead] at present
  cases present

/-- A dead Box also cannot be revived by diagnostic replacement. -/
theorem withPubkeys_dead (ops : Ops State StringResource BoxResource Terminal)
    (before : State) (error : Error BoxResource) (left right : Solanalib.Runtime.Pubkey)
    (dead : ops.currentBox before error.resource = none)
    (outcome : Outcome State (Error BoxResource) Empty Terminal) :
    ¬ withPubkeys ops before (error, left, right) outcome := by
  rintro ⟨payload, present, _⟩
  rw [dead] at present
  cases present

/-- Widening a fixed dependency cannot invent an unwind exit. -/
theorem lift_no_unwind {Args Value Unwind : Type}
    (run : Callback.Run State Args Value Empty Terminal) (before after : State)
    (args : Args) (reason : Unwind) : ¬ lift run before args (.unwound reason after) := by
  rintro ⟨actual, _, equal⟩
  cases actual with
  | unwound impossible _ => nomatch impossible
  | returned _ _ | terminated _ => cases equal

/-- A focused normal program-error conversion preserves the exact outer frame. -/
theorem fromProgram_focus_returned {Outer Inner : Type}
    (ops : Ops Inner StringResource BoxResource Terminal) (part : Owned.Focus Outer Inner)
    (before : Outer) (program : ProgramError.Value) (error : Error BoxResource) (after : Inner)
    (run : fromProgram ops (part.get before) program (.returned error after)) :
    fromProgram (ops.focus part) before program (.returned error (part.set before after)) := by
  apply (fromProgram_returned_iff _ _ _ _ _).mpr
  exact part.lift_returned ops.newBox before _ error.resource after
    ((fromProgram_returned_iff _ _ _ _ _).mp run)

/-- Focused construction threads the actual inner state of each allocation and
returns the final heap inside the original outer frame. -/
theorem buildCode_focus_returned {Outer Inner : Type}
    (ops : Ops Inner StringResource BoxResource Terminal) (part : Owned.Focus Outer Inner)
    (before : Outer) (code : Code) (error : Error BoxResource) (after : Inner)
    (run : buildCode ops (part.get before) code (.returned error after)) :
    buildCode (ops.focus part) before code (.returned error (part.set before after)) := by
  obtain ⟨name, afterName, message, afterMessage, copied, formatted, allocated⟩ :=
    (buildCode_returned_iff _ _ _ _ _).mp run
  apply (buildCode_returned_iff _ _ _ _ _).mpr
  refine ⟨name, part.set before afterName, message, part.set before afterMessage, ?_, ?_, ?_⟩
  · exact part.lift_returned ops.copyLiteral before code.name name afterName copied
  · have called := part.lift_returned ops.formatLiteral (part.set before afterName)
      code.message message afterMessage (by simpa only [part.get_set] using formatted)
    simpa only [Ops.focus, part.set_set] using called
  · have called := part.lift_returned ops.newBox (part.set before afterMessage)
      (.anchor ⟨name, code.number, message, none, none⟩) error.resource after
      (by simpa only [part.get_set] using allocated)
    simpa only [Ops.focus, part.set_set] using called

/-- Change only the representation of a terminal reason, preserving every value
and every actual finite post-state. -/
def mapTerminalOutcome {Value Target : Type} (convert : Terminal → Target) :
    Outcome State Value Empty Terminal → Outcome State Value Empty Target
  | .returned value after => .returned value after
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => .terminated (convert reason)

/-- Embed an existing dependency in a chosen terminal-reason vocabulary. -/
def mapTerminal {Args Value Target : Type} (convert : Terminal → Target)
    (run : Callback.Run State Args Value Empty Terminal) :
    Callback.Run State Args Value Empty Target :=
  fun before args outcome => ∃ actual, run before args actual ∧ mapTerminalOutcome convert actual =
    outcome

/-- Terminal encoding changes neither resource identities nor primitive stores. -/
def Ops.mapTerminal {Target : Type} (ops : Ops State StringResource BoxResource Terminal)
    (convert : Terminal → Target) : Ops State StringResource BoxResource Target where
  currentString := ops.currentString
  currentBox := ops.currentBox
  copyLiteral := AnchorErrorOwned.mapTerminal convert ops.copyLiteral
  formatLiteral := AnchorErrorOwned.mapTerminal convert ops.formatLiteral
  newBox := AnchorErrorOwned.mapTerminal convert ops.newBox
  writeBox := ops.writeBox
  dropString := AnchorErrorOwned.mapTerminal convert ops.dropString
  freeBox := AnchorErrorOwned.mapTerminal convert ops.freeBox

/-- Normal fixed-code executions survive a terminal-reason encoding unchanged. -/
theorem buildCode_mapTerminal_returned {Target : Type}
    (ops : Ops State StringResource BoxResource Terminal) (convert : Terminal → Target)
    (before : State) (code : Code) (error : Error BoxResource) (after : State)
    (run : buildCode ops before code (.returned error after)) :
    buildCode (ops.mapTerminal convert) before code (.returned error after) := by
  obtain ⟨name, afterName, message, afterMessage, copied, formatted, allocated⟩ :=
    (buildCode_returned_iff _ _ _ _ _).mp run
  apply (buildCode_returned_iff _ _ _ _ _).mpr
  exact ⟨name, afterName, message, afterMessage,
    ⟨.returned name afterName, copied, rfl⟩,
    ⟨.returned message afterMessage, formatted, rfl⟩,
    ⟨.returned error.resource after, allocated, rfl⟩⟩

/-- Normal program-error executions likewise keep the exact allocated Box. -/
theorem fromProgram_mapTerminal_returned {Target : Type}
    (ops : Ops State StringResource BoxResource Terminal) (convert : Terminal → Target)
    (before : State) (program : ProgramError.Value) (error : Error BoxResource) (after : State)
    (run : fromProgram ops before program (.returned error after)) :
    fromProgram (ops.mapTerminal convert) before program (.returned error after) := by
  apply (fromProgram_returned_iff _ _ _ _ _).mpr
  exact ⟨.returned error.resource after, (fromProgram_returned_iff _ _ _ _ _).mp run, rfl⟩

end Solanalib.Specs.Core.AnchorErrorOwned
