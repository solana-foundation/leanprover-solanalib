/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.Token

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedTlv

universe u v w x

/-- The discriminator that ends initialized SPL type-length-value storage.
This is an eight-byte discriminator, distinct from token-extension u16 tags. -/
def emptyDiscriminator : Bytes := List.replicate 8 0

/-- Observe the same borrowed slice in the supplied current state. Its length
is fixed by the source reference; an absent observation or changed length is
a failed representation, not an invented Rust error or panic. A source binding
must justify the observation, stable length, permissions and lifetime. -/
def sliceAt {State : Type u} (observe : State → Option Bytes)
    (byteLength : Nat) (state : State) (bytes : Bytes) : Prop :=
  observe state = some bytes ∧ bytes.length = byteLength

/-- Saturating a computed payload end at `usize::MAX` does not change the
out-of-bounds test for an addressable slice. This includes a payload length
whose natural sum exceeds that maximum. -/
theorem saturating_payload_check (byteLength endIndex usizeMax : Nat)
    (addressable : byteLength < usizeMax) :
    byteLength < min endIndex usizeMax ↔ byteLength < endIndex := by
  omega

/-- The finite exits of the allocation-aware TLV validation loop from
spl-type-length-value 0.9.1. A complete nonzero discriminator and complete
four-byte length slot are checked before `push`. The discriminator is copied
before that call; the length is read from the actual returned state after it.
The retained vector is dropped by `validate`, including after ordinary errors
and unwinds. Every recursive step consumes at least its twelve-byte header.

The source binding requires an addressable Rust slice and at least 32-bit
`usize`. On those inputs the natural-number checks below agree with the saturating additions of the
source, including out-of-bounds u32 payload lengths.
This relation supplies no allocator or Rust body correctness theorem. -/
def validateFrom {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (observe : State → Option Bytes) (resource : Resource)
    (byteLength offset : Nat) (before : State)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) : Prop :=
  ∃ bytes, sliceAt observe byteLength before bytes ∧
    if offset < byteLength then
      if byteLength < offset + 8 then
        outcome = .returned
          (if (bytes.drop offset).all (· == 0) then .ok () else .error .InvalidAccountData)
          before
      else
        let discriminator := Solanalib.Runtime.slice bytes offset 8
        if discriminator = emptyDiscriminator then outcome = .returned (.ok ()) before
        else if byteLength < offset + 12 then
          outcome = .returned (.error .InvalidAccountData) before
        else
          ∃ pushed, ops.push before (resource, discriminator) pushed ∧
            match pushed with
            | .returned () after =>
              ∃ current, sliceAt observe byteLength after current ∧
                let endIndex := offset + 12 + Solanalib.Runtime.leNat (Solanalib.Runtime.slice
                  current (offset + 8) 4)
                if byteLength < endIndex then
                  outcome = .returned (.error .InvalidAccountData) after
                else validateFrom ops observe resource byteLength endIndex after outcome
            | .unwound reason after => outcome = .unwound reason after
            | .terminated reason => outcome = .terminated reason
    else outcome = .returned (.ok ()) before
termination_by byteLength - offset
decreasing_by omega

/-- Validate the entire initialized TLV region as `check_data` does. Empty
construction occurs even for an empty slice. The actual vector identity is
retained through every push and passed to scope cleanup. Cleanup runs before
any ordinary result is exposed to a later selected-entry lookup; a terminal
exit skips cleanup, and a destructor unwind during an existing unwind follows
the explicit double-unwind policy.

The primitive operations and current-state observations are parameters, not
assumptions that validation has returned a desired result. -/
def validate {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) :
    Callback.Run State Unit (Except Error Unit) Unwind Terminal :=
  fun before _ outcome =>
    ∃ bytes, observe before = some bytes ∧
      let allocated := ops.empty before
      ∃ pending, validateFrom ops observe allocated.1 bytes.length 0 allocated.2 pending ∧
        Owned.cleanup double [ops.dropAction allocated.1] pending outcome

/-- The token-interface 3.0.0 Mint extension marker lies after 83 padding
bytes: the common 165-byte account base minus the 82-byte Mint base. -/
def mintPaddingLength : Nat := 83

/-- Finish a successful padding comparison after its temporary vector has
been dropped. Only the saved equality decides whether the marker is read.
On equality, marker and tail are observed in the actual post-drop state.
The Mint marker is 1; TLV bytes remain unvalidated at this parsing stage. -/
def mintAfterPadding {State : Type u} {Unwind : Type w} {Terminal : Type x}
    (observe : State → Option Bytes) (byteLength : Nat) (equal : Bool)
    (before : State) (outcome : Outcome State (Except Error Bytes) Unwind Terminal) : Prop :=
  if equal then
    ∃ bytes, sliceAt observe byteLength before bytes ∧
      outcome = .returned
        (if bytes[mintPaddingLength]? = some 1 then
          .ok (bytes.drop (mintPaddingLength + 1)) else .error .InvalidAccountData) before
  else outcome = .returned (.error .InvalidAccountData) before

/-- Compare the current padding with the current temporary zero vector, then
drop that same resource before branching on the saved Boolean. Neither the
comparison nor cleanup uses a saved pre-allocation contents snapshot. An
unrepresented resource or borrowed slice produces no finite modeled exit. -/
def compareMintPadding {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State UInt8 Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (byteLength : Nat)
    (resource : Resource) (before : State)
    (outcome : Outcome State (Except Error Bytes) Unwind Terminal) : Prop :=
  ∃ bytes zeroes, sliceAt observe byteLength before bytes ∧
    ops.current before resource = some zeroes ∧
    ∃ dropped, Owned.cleanup double [ops.dropAction resource]
        (.returned (bytes.take mintPaddingLength == zeroes) before) dropped ∧
      match dropped with
      | .returned equal after => mintAfterPadding observe byteLength equal after outcome
      | .unwound reason after => outcome = .unwound reason after
      | .terminated reason => outcome = .terminated reason

/-- The allocation-aware Mint tail parser for token-interface 3.0.0. Its caller first performs the
total-length admission and packed Mint parsing of the source. Empty remainder bypasses
allocation; a short nonempty remainder fails before construction. A long enough remainder
constructs exactly the temporary 83-byte zero vector of the source. Construction exits propagate
before ownership is obtained; its provider handles any constructor-internal cleanup. On
successful construction `compareMintPadding` takes over the returned identity and actual state,
and drops the temporary before marker admission. Here `fromList` must be bound to the actual
repeated-zero constructor; this does not assert an equivalence with a different Rust vector
constructor.

This helper models the allocation present in 3.0.0; the 3.1.1 source checks the padding with an
iterator and does not make this allocation. -/
def mintTail {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State UInt8 Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) :
    Callback.Run State Unit (Except Error Bytes) Unwind Terminal :=
  fun before _ outcome =>
    ∃ bytes, observe before = some bytes ∧
      if bytes.isEmpty then outcome = .returned (.ok []) before
      else if bytes.length < mintPaddingLength + 1 then
        outcome = .returned (.error .InvalidAccountData) before
      else Callback.bind ops.fromList
        (fun resource after result =>
          compareMintPadding ops double observe bytes.length resource after result)
        before (List.replicate mintPaddingLength 0) outcome

/-- Missing slice representation cannot be translated into a source result. -/
theorem validate_absent {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (before : State)
    (absent : observe before = none)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) :
    ¬ validate ops double observe before () outcome := by
  rintro ⟨bytes, represented, _⟩
  rw [absent] at represented
  cases represented

/-- A completed validation loop preserves its current state until the
surrounding vector cleanup runs. -/
theorem validateFrom_end {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (observe : State → Option Bytes) (resource : Resource)
    (byteLength offset : Nat) (before : State) (bytes : Bytes)
    (represented : sliceAt observe byteLength before bytes) (ended : byteLength ≤ offset) :
    validateFrom ops observe resource byteLength offset before (.returned (.ok ()) before) := by
  rw [validateFrom]
  exact ⟨bytes, represented, by simp only [Nat.not_lt.mpr ended, ite_false]⟩

/-- A terminal validation exit bypasses the destructor of the retained vector. -/
theorem validate_terminal {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (before : State) (bytes : Bytes)
    (represented : observe before = some bytes) (reason : Terminal)
    (run : validateFrom ops observe (ops.empty before).1 bytes.length 0
      (ops.empty before).2 (.terminated reason)) :
    validate ops double observe before () (.terminated reason) := by
  exact ⟨bytes, represented, .terminated reason, run,
    (Owned.cleanup_terminated double _ reason _).mpr rfl⟩

/-- An ordinary validation error still runs the retained vector destructor
and exposes the actual post-drop state. -/
theorem validate_error_cleanup {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (before during after : State) (bytes : Bytes)
    (represented : observe before = some bytes) (error : Error)
    (run : validateFrom ops observe (ops.empty before).1 bytes.length 0
      (ops.empty before).2 (.returned (.error error) during))
    (drop : ops.drop during (ops.empty before).1 (.returned () after)) :
    validate ops double observe before () (.returned (.error error) after) := by
  exact ⟨bytes, represented, .returned (.error error) during, run,
    .returned () after, drop, rfl⟩

/-- A push unwind keeps its actual state for destructor execution. If that
destructor also unwinds, only the supplied double-unwind policy can finish. -/
theorem validate_double_unwind {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State Bytes Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (before during after : State) (bytes : Bytes)
    (represented : observe before = some bytes) (original later : Unwind) (terminal : Terminal)
    (run : validateFrom ops observe (ops.empty before).1 bytes.length 0
      (ops.empty before).2 (.unwound original during))
    (drop : ops.drop during (ops.empty before).1 (.unwound later after))
    (abort : double after original later terminal) :
    validate ops double observe before () (.terminated terminal) := by
  exact ⟨bytes, represented, .unwound original during, run,
    Owned.cleanup_double_unwind double _ [] during after original later terminal drop abort⟩

/-- An empty Mint remainder performs no temporary-vector operation. -/
theorem mintTail_empty {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State UInt8 Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (before : State)
    (empty : observe before = some []) :
    mintTail ops double observe before () (.returned (.ok []) before) := by
  exact ⟨[], empty, rfl⟩

/-- A short nonempty Mint remainder fails before invoking allocation. -/
theorem mintTail_short {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (ops : Owned.VectorOps State UInt8 Resource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (observe : State → Option Bytes) (before : State) (bytes : Bytes)
    (represented : observe before = some bytes) (nonempty : bytes.isEmpty = false)
    (short : bytes.length < mintPaddingLength + 1) :
    mintTail ops double observe before () (.returned (.error .InvalidAccountData) before) := by
  exact ⟨bytes, represented, by simp only [nonempty, Bool.false_eq_true, ite_false, short,
    ite_true]⟩

/-- The marker-read branch is chosen using the pre-drop comparison result;
a failed comparison does not inspect even a represented post-drop slice. -/
theorem mintAfterPadding_unequal {State : Type u} {Unwind : Type w} {Terminal : Type x}
    (observe : State → Option Bytes) (byteLength : Nat) (before : State)
    (outcome : Outcome State (Except Error Bytes) Unwind Terminal) :
    mintAfterPadding observe byteLength false before outcome ↔
      outcome = .returned (.error .InvalidAccountData) before := Iff.rfl

end Solanalib.Specs.Core.Token.AllocatedTlv
