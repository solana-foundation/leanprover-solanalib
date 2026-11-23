/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedCollect

private theorem cleanup_unwind_no_return {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (reason : Unwind) (before : State) (value : Value) (after : State) :
    ¬ Owned.cleanup double drops (.unwound reason before) (.returned value after) := by
  induction drops generalizing reason before with
  | nil => intro impossible; cases impossible
  | cons action rest induction =>
    rintro ⟨dropped, _, following⟩
    cases dropped with
    | returned returnedUnit middle =>
      cases returnedUnit
      exact induction reason middle following
    | unwound later middle =>
      obtain ⟨terminal, _, impossible⟩ := following
      cases impossible
    | terminated terminal => cases following

private theorem cleanup_return_value {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (value result : Value) (before after : State)
    (run : Owned.cleanup double drops (.returned value before) (.returned result after)) :
    result = value := by
  induction drops generalizing before with
  | nil => cases run; rfl
  | cons action rest induction =>
    obtain ⟨dropped, _, following⟩ := run
    cases dropped with
    | returned returnedUnit middle =>
      cases returnedUnit
      exact induction middle following
    | unwound reason middle =>
      exact False.elim (cleanup_unwind_no_return double rest reason middle result after following)
    | terminated terminal => cases following

/-- A successful collection invokes every remaining callback, and its current
owned vector contains exactly one element for every successful acquisition,
including the previously acquired prefix. This follows from the trace and the
local finish law; no whole SDK success postcondition is assumed. -/
theorem Trace.success_current {Extra Resource Unwind Terminal : Type}
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal}
    {vectors : Owned.VectorOps (World Extra) Element Resource Unwind Terminal}
    (laws : ResourceLaws protocol vectors)
    {index : Nat} {acquired : List Element} {before : World Extra} {calls : List Nat}
    {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    (trace : Trace protocol iterator callback index acquired before calls final) :
    ∀ resource after, final = .returned (.ok resource) after →
      index + calls.length = iterator.length ∧
      ∃ values, vectors.current after resource = some values ∧
        values.length = acquired.length + calls.length := by
  induction trace with
  | @done index acquired before pending final endOfIterator finished exit =>
    intro resource after returned
    cases pending with
    | returned actual current =>
      change final = .returned (.ok actual) current at exit
      rw [exit] at returned
      cases returned
      exact ⟨by simpa using endOfIterator,
        acquired, laws.finish_current before acquired resource after finished, by simp⟩
    | unwound reason current =>
      rw [returned] at exit
      exact False.elim (cleanup_unwind_no_return protocol.double _ reason current _ after exit.2)
    | terminated reason =>
      change final = .terminated reason at exit
      rw [exit] at returned
      cases returned
  | next within read called tail induction =>
    intro resource after returned
    obtain ⟨complete, values, observed, length⟩ := induction resource after returned
    refine ⟨?_, values, observed, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm 1] using complete
    · simpa [List.length_append, Nat.add_assoc, Nat.add_comm 1] using length
  | error within read called cleaned =>
    intro resource after returned
    rw [returned] at cleaned
    have impossible := cleanup_return_value protocol.double _ _ _ _ after cleaned.2
    cases impossible
  | unwind within read called cleaned =>
    intro resource after returned
    rw [returned] at cleaned
    exact False.elim (cleanup_unwind_no_return protocol.double _ _ _ _ after cleaned.2)
  | terminal within read called => intro resource after impossible; cases impossible
  | internalReturn within stepped tail induction => exact induction
  | internalUnwind within stepped cleaned =>
    intro resource after returned
    rw [returned] at cleaned
    exact False.elim (cleanup_unwind_no_return protocol.double _ _ _ _ after cleaned.2)
  | internalTerminal within stepped => intro resource after impossible; cases impossible

/-- The successful vector returned by a conforming provider has exactly the length of the source
iterator. Its members still retain the actual keys and guard identities tracked
by its trace and resource law. -/
theorem Provider.success_length {Extra Resource Unwind Terminal : Type}
    {provider : Provider Extra Resource Unwind Terminal}
    {protocol : Protocol Extra Resource Unwind Terminal}
    {vectors : Owned.VectorOps (World Extra) Element Resource Unwind Terminal}
    (conforms : provider.Conforms protocol) (laws : ResourceLaws protocol vectors)
    (iterator : Iterator Extra)
    (callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element) Unwind Terminal)
    (before after : World Extra) (resource : Resource)
    (run : provider.run iterator callback before (.returned (.ok resource) after)) :
    ∃ values, vectors.current after resource = some values ∧ values.length = iterator.length := by
  obtain ⟨calls, trace⟩ := conforms iterator callback before _ run
  obtain ⟨complete, values, observed, length⟩ := trace.success_current laws resource after rfl
  refine ⟨values, observed, ?_⟩
  simpa using length.trans complete

end Solanalib.Specs.Core.Token.AllocatedCollect
