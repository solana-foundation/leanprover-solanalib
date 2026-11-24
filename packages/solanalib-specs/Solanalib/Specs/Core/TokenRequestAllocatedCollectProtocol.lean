/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedCollect

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedCollect

/-- Internal dependency effects of one collection call. These operations are
not a claimed reserve/push schedule: an implementation binding supplies its
actual finite internal chunks between source callback invocations. The internal owned storage of the
collector is part of `Extra`. -/
structure Protocol (Extra Resource Unwind Terminal : Type) where
  /-- One finite internal chunk, indexed by the next callback and the already
acquired elements. Its actual outcome is threaded into the protocol trace. -/
  internal : Nat → List Element → Owned.DropAction (World Extra) Unwind Terminal
  /-- Transfer the completed owned vector, after every source callback. -/
  finish : Callback.Run (World Extra) (List Element) Resource Unwind Terminal
  /-- Actual partial-cleanup order, selected using the current
storage/pending-element bookkeeping of the collector. Cleanup checks that this order contains
exactly the acquired elements. A newly returned element can still be pending
in a failing insertion and may need to drop before the stored prefix. -/
  partialOrder : World Extra → List Element → List Element := fun _ acquired => acquired
  /-- Retire only collector storage after the element guards have been dropped.
`none` denotes the in-progress collector; `some` identifies a returned vector.
This operation must not drop the already retired guards a second time. -/
  retire : Option Resource → List Element → Owned.DropAction (World Extra) Unwind Terminal
  /-- The explicit terminal policy for a second unwind during cleanup. -/
  double : Owned.DoubleUnwind (World Extra) Unwind Terminal

/-- The guard portion of the destructor of a collector, followed by its separately
supplied storage retirement. This is a primitive collection dependency
obligation; it is not inferred from `VectorOps.Laws`. -/
def Protocol.drops {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) (resource : Option Resource)
    (acquired : List Element) : List (Owned.DropAction (World Extra) Unwind Terminal) :=
  acquired.map (fun element => element.2.drop) ++ [protocol.retire resource acquired]

/-- A partial collector follows its actual chosen element order, then retires
its internal storage. The caller separately checks the exact permutation. -/
def Protocol.partialDrops {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) (before : World Extra)
    (acquired : List Element) : List (Owned.DropAction (World Extra) Unwind Terminal) :=
  (protocol.partialOrder before acquired).map (fun element => element.2.drop) ++
    [protocol.retire none acquired]

/-- Failure cleanup retains the exact acquired prefix, actual failure state,
and error or unwind reason. Its state-dependent order must be a permutation
of exactly those elements; it cannot leak one or drop an unrelated reference.
Terminal outcomes stop before any order check or destructor. -/
def Protocol.cleanup {Extra Resource Unwind Terminal Value : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) (acquired : List Element)
    (pending final : Outcome (World Extra) Value Unwind Terminal) : Prop :=
  match pending with
  | .terminated reason => final = .terminated reason
  | .returned _ before | .unwound _ before =>
    (protocol.partialOrder before acquired).Perm acquired ∧
      Owned.cleanup protocol.double (protocol.partialDrops before acquired) pending final

/-- Successful finalization transfers the owned vector. A failed finalization
cleans the acquired guards and storage; it cannot return a ProgramError. -/
def Protocol.finishExit {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) (acquired : List Element)
    (pending : Outcome (World Extra) Resource Unwind Terminal)
    (final : Outcome (World Extra) (Except Error Resource) Unwind Terminal) : Prop :=
  match pending with
  | .returned resource after => final = .returned (.ok resource) after
  | .unwound reason after => protocol.cleanup acquired (.unwound reason after) final
  | .terminated reason => final = .terminated reason

/-- A finite higher-order dependency trace. Callback indices advance exactly
once and in order; no callback follows an error, unwind or terminal exit.
Internal provider chunks are explicit and may occur between callbacks without
claiming a particular std allocation algorithm. `calls` records only actual
source closure invocations, not allocation events. -/
inductive Trace {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) (iterator : Iterator Extra)
    (callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal) : Nat → List Element → World Extra → List Nat →
      Outcome (World Extra) (Except Error Resource) Unwind Terminal → Prop
  /-- All source elements were acquired; finalize this same sequence. -/
  | done {index : Nat} {acquired : List Element} {before : World Extra}
      {pending : Outcome (World Extra) Resource Unwind Terminal}
      {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
      (endOfIterator : index = iterator.length)
      (finished : protocol.finish before acquired pending)
      (exit : protocol.finishExit acquired pending final) :
      Trace protocol iterator callback index acquired before [] final
  /-- The actual next callback returns an element and only then advances.
The contract of the callback supplies its reference-validity guarantee. -/
  | next {index : Nat} {acquired : List Element} {before after : World Extra}
      {info : AccountInfo.Value} {element : Element} {calls : List Nat}
      {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.returned (.ok element) after))
      (tail : Trace protocol iterator callback (index + 1) (acquired ++ [element]) after calls
        final) :
      Trace protocol iterator callback index acquired before (index :: calls) final
  /-- An ordinary callback error short-circuits and cleans only its predecessors. -/
  | error {index : Nat} {acquired : List Element} {before after : World Extra}
      {info : AccountInfo.Value} {error : Error}
      {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.returned (.error error) after))
      (cleaned : protocol.cleanup acquired (.returned (.error error) after) final) :
      Trace protocol iterator callback index acquired before [index] final
  /-- A callback unwind preserves its actual state before prefix cleanup. -/
  | unwind {index : Nat} {acquired : List Element} {before after : World Extra}
      {info : AccountInfo.Value} {reason : Unwind}
      {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.unwound reason after))
      (cleaned : protocol.cleanup acquired (.unwound reason after) final) :
      Trace protocol iterator callback index acquired before [index] final
  /-- A terminal callback never runs another callback or a destructor. -/
  | terminal {index : Nat} {acquired : List Element} {before : World Extra}
      {info : AccountInfo.Value} {reason : Terminal}
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.terminated reason)) :
      Trace protocol iterator callback index acquired before [index] (.terminated reason)
  /-- A real internal normal effect retains the next callback index. -/
  | internalReturn {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat} {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
      (within : index ≤ iterator.length)
      (stepped : protocol.internal index acquired before (.returned () after))
      (tail : Trace protocol iterator callback index acquired after calls final) :
      Trace protocol iterator callback index acquired before calls final
  /-- An internal unwind cleans the acquired prefix and never calls the closure. -/
  | internalUnwind {index : Nat} {acquired : List Element} {before after : World Extra}
      {reason : Unwind} {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
      (within : index ≤ iterator.length)
      (stepped : protocol.internal index acquired before (.unwound reason after))
      (cleaned : protocol.cleanup acquired (.unwound reason after) final) :
      Trace protocol iterator callback index acquired before [] final
  /-- An internal terminal outcome stops before any further source action. -/
  | internalTerminal {index : Nat} {acquired : List Element} {before : World Extra}
      {reason : Terminal} (within : index ≤ iterator.length)
      (stepped : protocol.internal index acquired before (.terminated reason)) :
      Trace protocol iterator callback index acquired before [] (.terminated reason)

/-- Callback invocations form a prefix starting at the next iterator index.
This excludes repetition, reordering and skipped source callbacks in a trace. -/
theorem Trace.calls_prefix {Extra Resource Unwind Terminal : Type}
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {index : Nat} {acquired : List Element} {before : World Extra}
    {calls : List Nat} {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    (trace : Trace protocol iterator callback index acquired before calls final) :
    calls = List.range' index calls.length := by
  induction trace with
  | done => simp
  | next within read called tail induction =>
    simpa only [List.length_cons, List.range'_succ] using congrArg (List.cons _) induction
  | error => simp
  | unwind => simp
  | terminal => simp
  | internalReturn within stepped tail induction => exact induction
  | internalUnwind => simp
  | internalTerminal => simp

/-- A collection trace never invokes more callbacks than the captured source
iterator contains, including on an internal early exit. -/
theorem Trace.calls_bound {Extra Resource Unwind Terminal : Type}
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {index : Nat} {acquired : List Element} {before : World Extra}
    {calls : List Nat} {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    (trace : Trace protocol iterator callback index acquired before calls final) :
    index + calls.length ≤ iterator.length := by
  induction trace with
  | done endOfIterator => simp [endOfIterator]
  | next within read called tail induction => simpa [Nat.add_assoc, Nat.add_comm 1] using induction
  | error within => simpa using Nat.succ_le_of_lt within
  | unwind within => simpa using Nat.succ_le_of_lt within
  | terminal within => simpa using Nat.succ_le_of_lt within
  | internalReturn within stepped tail induction => exact induction
  | internalUnwind within => simpa using within
  | internalTerminal within => simpa using within

/-- Local higher-order dependency correctness, separate from the enclosing SDK
model: every admitted collection result must have an actual protocol trace.
It does not imply progress; a sample execution is checked independently. -/
def Provider.Conforms {Extra Resource Unwind Terminal : Type}
    (provider : Provider Extra Resource Unwind Terminal)
    (protocol : Protocol Extra Resource Unwind Terminal) : Prop :=
  ∀ iterator callback before final, provider.run iterator callback before final →
    ∃ calls, Trace protocol iterator callback 0 [] before calls final

/-- A mathematical provider whose finite behavior is precisely the protocol.
Selecting it is a reference interpretation, not a proof about Rust collect. -/
def protocolProvider {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) : Provider Extra Resource Unwind Terminal
      :=
  ⟨fun iterator callback before final =>
    ∃ calls, Trace protocol iterator callback 0 [] before calls final⟩

/-- Every finite behavior of the reference interpretation obeys its protocol. -/
theorem protocolProvider_conforms {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal) :
    (protocolProvider protocol).Conforms protocol := fun _ _ _ _ trace => trace

/-- Successful collection transfers the same ordered acquired elements into
the current observation of the returned vector. This is the resource fact used by
`Trace.success_current` and `Provider.success_length`. Element destruction and
storage retirement remain the behavior of the supplied cleanup operations;
this record imposes no additional law on the later drop of a returned vector. -/
structure ResourceLaws {Extra Resource Unwind Terminal : Type}
    (protocol : Protocol Extra Resource Unwind Terminal)
    (vectors : Owned.VectorOps (World Extra) Element Resource Unwind Terminal) : Prop where
  /-- Successful transfer preserves every acquired element and its order. -/
  finish_current : ∀ before acquired resource after,
    protocol.finish before acquired (.returned resource after) →
      vectors.current after resource = some acquired

end Solanalib.Specs.Core.Token.AllocatedCollect
