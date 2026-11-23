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

variable {Extra Resource Unwind Terminal : Type}

/-- The actual forward portion of a collection call, before any failure or
finalization. It begins at index zero with no acquired references. Only an
actual successful callback appends an element; an internal return keeps the
same next index. No complete trace or cleanup outcome is assumed. -/
inductive ForwardPrefix (protocol : Protocol Extra Resource Unwind Terminal)
    (iterator : Iterator Extra)
    (callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal) (entry : World Extra) :
    Nat → List Element → World Extra → List Nat → Prop
  /-- The unchanged collection entry has no callback or acquired element. -/
  | start : ForwardPrefix protocol iterator callback entry 0 [] entry []
  /-- A successful current callback appends its actual element and call index. -/
  | next {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat} {info : AccountInfo.Value} {element : Element}
      (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.returned (.ok element) after)) :
      ForwardPrefix protocol iterator callback entry (index + 1) (acquired ++ [element])
        after (calls ++ [index])
  /-- A returned internal chunk changes only the recorded current state. -/
  | internalReturn {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat}
      (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
      (within : index ≤ iterator.length)
      (stepped : protocol.internal index acquired before (.returned () after)) :
      ForwardPrefix protocol iterator callback entry index acquired after calls

/-- An actual suffix extends this same forward prefix into the original
collection relation, retaining the exact callback list and final outcome. -/
theorem ForwardPrefix.extend
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry before : World Extra} {index : Nat}
    {acquired : List Element} {calls suffix : List Nat}
    {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
    (tail : Trace protocol iterator callback index acquired before suffix final) :
    Trace protocol iterator callback 0 [] entry (calls ++ suffix) final := by
  induction reached generalizing suffix with
  | start => exact tail
  | next reached within read called induction =>
      have extended := induction (Trace.next within read called tail)
      simpa only [List.append_assoc, List.singleton_append] using extended
  | internalReturn reached within stepped induction =>
      exact induction (Trace.internalReturn within stepped tail)

/-- One actual failure immediately after a forward prefix, including the
state in which cleanup begins. The newly returned but pending element from a successful callback is
already part of `acquired`. Terminal exits are not cleanup
sites and therefore impose no partial-order requirement. -/
inductive CleanupSite (protocol : Protocol Extra Resource Unwind Terminal)
    (iterator : Iterator Extra)
    (callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal) (entry : World Extra) :
    List Element → World Extra →
      Outcome (World Extra) (Except Error Resource) Unwind Terminal → List Nat → Prop
  /-- A real callback error cleans the previously acquired elements. -/
  | error {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat} {info : AccountInfo.Value} {error : Error}
      (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.returned (.error error) after)) :
      CleanupSite protocol iterator callback entry acquired after
        (.returned (.error error) after) (calls ++ [index])
  /-- A generic callback unwind starts cleanup in its actual unwind state. -/
  | callbackUnwind {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat} {info : AccountInfo.Value} {reason : Unwind}
      (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
      (within : index < iterator.length) (read : iterator.elementAt before index = some info)
      (called : callback before info (.unwound reason after)) :
      CleanupSite protocol iterator callback entry acquired after (.unwound reason after)
        (calls ++ [index])
  /-- A real internal unwind includes any element awaiting insertion. -/
  | internalUnwind {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat} {reason : Unwind}
      (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
      (within : index ≤ iterator.length)
      (stepped : protocol.internal index acquired before (.unwound reason after)) :
      CleanupSite protocol iterator callback entry acquired after (.unwound reason after) calls
  /-- A failed transfer cleans the complete actual acquisition list. -/
  | finishUnwind {index : Nat} {acquired : List Element} {before after : World Extra}
      {calls : List Nat} {reason : Unwind}
      (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
      (finishedAll : index = iterator.length)
      (finished : protocol.finish before acquired (.unwound reason after)) :
      CleanupSite protocol iterator callback entry acquired after (.unwound reason after) calls

/-- A valid cleanup order is required at each reached finite
failure, before any destructor outcome is considered. This law constrains
only the local permutation check; it assumes no destructor or double-unwind
policy terminates and grants no permissions to malformed references. -/
def CleanupReady (protocol : Protocol Extra Resource Unwind Terminal)
    (iterator : Iterator Extra)
    (callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal) (entry : World Extra) : Prop :=
  ∀ {acquired after pending calls},
    CleanupSite protocol iterator callback entry acquired after pending calls →
      (protocol.partialOrder after acquired).Perm acquired

/-- A provider with a valid order at every state also satisfies the weaker
actual-prefix admission, independently of its allocation schedule. -/
theorem CleanupReady.of_order
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry : World Extra}
    (order : ∀ after acquired, (protocol.partialOrder after acquired).Perm acquired) :
    CleanupReady protocol iterator callback entry := fun _ => order _ _

/-- At an admitted cleanup site, the protocol retains every actual destructor
outcome, rather than selecting only an exit that passes its local order check. -/
theorem CleanupSite.cleanup_iff
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry after : World Extra} {acquired : List Element}
    {pending final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    {calls : List Nat}
    (site : CleanupSite protocol iterator callback entry acquired after pending calls)
    (ready : CleanupReady protocol iterator callback entry) :
    protocol.cleanup acquired pending final ↔
      Owned.cleanup protocol.double (protocol.partialDrops after acquired) pending final := by
  have order := ready site
  cases site <;> exact ⟨And.right, fun cleaned => ⟨order, cleaned⟩⟩

/-- Each actual cleanup exit extends the recorded forward prefix to a complete
trace with the same final value/reason and state. No complete Trace is used in
the admission, and no exit of retirement or double-unwind is invented. -/
theorem CleanupSite.extend
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry after : World Extra} {acquired : List Element}
    {pending final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    {calls : List Nat}
    (site : CleanupSite protocol iterator callback entry acquired after pending calls)
    (ready : CleanupReady protocol iterator callback entry)
    (cleaned : Owned.cleanup protocol.double (protocol.partialDrops after acquired) pending final) :
    Trace protocol iterator callback 0 [] entry calls final := by
  have admitted := (site.cleanup_iff ready).2 cleaned
  cases site with
  | error reached within read called =>
      exact reached.extend (Trace.error within read called admitted)
  | callbackUnwind reached within read called =>
      exact reached.extend (Trace.unwind within read called admitted)
  | internalUnwind reached within stepped =>
      simpa only [List.append_nil] using
        reached.extend (Trace.internalUnwind within stepped admitted)
  | finishUnwind reached finishedAll finished =>
      simpa only [List.append_nil] using
        reached.extend (Trace.done finishedAll finished admitted)

/-- The reference provider accepts each retained finite cleanup. A different
provider needs its own trace-completeness interpretation; Conforms alone is
only the converse direction. -/
theorem CleanupSite.provider
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry after : World Extra} {acquired : List Element}
    {pending final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    {calls : List Nat}
    (site : CleanupSite protocol iterator callback entry acquired after pending calls)
    (ready : CleanupReady protocol iterator callback entry)
    (cleaned : Owned.cleanup protocol.double (protocol.partialDrops after acquired) pending final) :
    (protocolProvider protocol).run iterator callback entry final :=
  ⟨calls, site.extend ready cleaned⟩

/-- Internal termination bypasses the cleanup-order gate entirely, including
when the acquired prefix is nonempty. -/
theorem ForwardPrefix.internal_terminal
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry before : World Extra} {index : Nat}
    {acquired : List Element} {calls : List Nat} {reason : Terminal}
    (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
    (within : index ≤ iterator.length)
    (stopped : protocol.internal index acquired before (.terminated reason)) :
    Trace protocol iterator callback 0 [] entry calls (.terminated reason) := by
  simpa only [List.append_nil] using
    reached.extend (Trace.internalTerminal within stopped)

/-- Successful finalization transfers its actual resource and state without
checking a partial-cleanup order. -/
theorem ForwardPrefix.finish_returned
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {callback : Callback.Run (World Extra) AccountInfo.Value (Except Error Element)
      Unwind Terminal} {entry before after : World Extra} {index : Nat}
    {acquired : List Element} {calls : List Nat} {resource : Resource}
    (reached : ForwardPrefix protocol iterator callback entry index acquired before calls)
    (finishedAll : index = iterator.length)
    (finished : protocol.finish before acquired (.returned resource after)) :
    Trace protocol iterator callback 0 [] entry calls (.returned (.ok resource) after) := by
  simpa only [List.append_nil] using
    reached.extend (Trace.done finishedAll finished rfl)

/-- The source collection closure uses a checked borrow, so it cannot call the
panic provider. A malformed mathematical input still has no invented exit. -/
theorem borrowElement_no_unwind
    (raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal)
    (before after : World Extra) (info : AccountInfo.Value) (reason : Unwind) :
    ¬ borrowElement raise before info (.unwound reason after) := by
  rintro ⟨pending, borrowed, forwarded⟩
  cases acquired : AccountInfo.tryBorrow .shared info.data before.1 with
  | mk result during =>
      cases result with
      | error error =>
          simp only [AllocatedControl.borrow, AllocatedControl.fromStep,
            Onchain.borrowData, acquired, ↓reduceIte] at borrowed
          cases borrowed
          cases forwarded
      | ok guard =>
          cases current : Borrow.current during guard with
          | error error =>
              simp only [AllocatedControl.borrow, AllocatedControl.fromStep,
                Onchain.borrowData, acquired, current] at borrowed
          | ok contents =>
              obtain ⟨view, content⟩ := contents
              cases content with
              | lamports amount =>
                  simp only [AllocatedControl.borrow, AllocatedControl.fromStep,
                    Onchain.borrowData, acquired, current] at borrowed
              | data bytes =>
                  simp only [AllocatedControl.borrow, AllocatedControl.fromStep,
                    Onchain.borrowData, acquired, current] at borrowed
                  cases borrowed
                  cases forwarded

/-- The actual checked-borrow closure needs only callback-error, internal-
unwind and finish-unwind order laws. Its impossible callback-unwind case adds
no provider obligation. Every premise is at a reached forward prefix. -/
theorem CleanupReady.of_borrowElement
    {protocol : Protocol Extra Resource Unwind Terminal} {iterator : Iterator Extra}
    {raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal}
    {entry : World Extra}
    (onError : ∀ {index acquired before after calls info error},
      ForwardPrefix protocol iterator (borrowElement raise) entry index acquired before calls →
      index < iterator.length → iterator.elementAt before index = some info →
      borrowElement raise before info (.returned (.error error) after) →
        (protocol.partialOrder after acquired).Perm acquired)
    (onInternalUnwind : ∀ {index acquired before after calls reason},
      ForwardPrefix protocol iterator (borrowElement raise) entry index acquired before calls →
      index ≤ iterator.length → protocol.internal index acquired before (.unwound reason after) →
        (protocol.partialOrder after acquired).Perm acquired)
    (onFinishUnwind : ∀ {index acquired before after calls reason},
      ForwardPrefix protocol iterator (borrowElement raise) entry index acquired before calls →
      index = iterator.length → protocol.finish before acquired (.unwound reason after) →
        (protocol.partialOrder after acquired).Perm acquired) :
    CleanupReady protocol iterator (borrowElement raise) entry := by
  intro acquired after pending calls site
  cases site with
  | error reached within read called => exact onError reached within read called
  | callbackUnwind reached within read called =>
      exact False.elim (borrowElement_no_unwind raise _ _ _ _ called)
  | internalUnwind reached within stepped => exact onInternalUnwind reached within stepped
  | finishUnwind reached finishedAll finished => exact onFinishUnwind reached finishedAll finished

end Solanalib.Specs.Core.Token.AllocatedCollect
