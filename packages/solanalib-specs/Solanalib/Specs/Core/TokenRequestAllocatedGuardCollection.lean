/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuardPrimitives
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardBorrow

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

open AccountInfo.GuardCallback

/-- the current cleanup permutation of Collection can release only its acquired
elements. Each real release and the final storage callback frame every other
held guard; the proof keeps the actual error/unwind/terminal outcome. -/
theorem collection_cleanup {Extra Resource Value Unwind Terminal : Type}
    {protocol : AllocatedCollect.Protocol Extra Resource Unwind Terminal}
    {acquired : List AllocatedCollect.Element}
    (retireLaw : Preserves (fun state (_ : Unit) => protocol.retire none acquired state))
    {before : World Extra}
    {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    (live : before.1.resolve guard = some slot)
    (outside : ∀ element ∈ acquired, element.2.guard ≠ guard)
    {pending final : Outcome (World Extra) Value Unwind Terminal}
    (framed : Frame before guard pending) (cleaned : protocol.cleanup acquired pending final) :
    Frame before guard final := by
  have pointwise (order : List AllocatedCollect.Element)
      (permutation : order.Perm acquired) :
      ∀ action ∈ order.map (fun element => element.2.drop) ++ [protocol.retire none acquired],
        ∀ current, current.1.Valid → ∀ currentSlot,
          current.1.resolve guard = some currentSlot →
            Admissible guard (fun actual (_ : Unit) => action actual) current () := by
    intro action member current valid currentSlot currentLive
    rcases List.mem_append.mp member with inElements | inRetire
    · obtain ⟨element, selectedMember, same⟩ := List.mem_map.mp inElements
      cases same
      have distinct := outside element (permutation.mem_iff.mp selectedMember)
      exact data_drop_frames element.2 current () valid guard currentSlot currentLive
        (by simpa only [List.mem_singleton] using Ne.symm distinct)
    · have same := List.mem_singleton.mp inRetire
      cases same
      exact retireLaw current () valid guard currentSlot currentLive (by simp)
  cases pending with
  | returned value state =>
    exact cleanup_frame live protocol.double _ (pointwise _ cleaned.1) framed cleaned.2
  | unwound reason state =>
    exact cleanup_frame live protocol.double _ (pointwise _ cleaned.1) framed cleaned.2
  | terminated reason => cases cleaned; trivial

/-- Every finite collection trace preserves an outer live data guard. The
induction follows the existing operational trace: each actual borrow issues a
fresh distinct token; each internal primitive has its own admission before
the next iterator read; failure cleanup consumes only acquired inner guards. -/
theorem CollectionFrames.trace {Extra Resource Unwind Terminal : Type}
    {protocol : AllocatedCollect.Protocol Extra Resource Unwind Terminal}
    (laws : CollectionFrames protocol)
    {raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal}
    (raiseLaw : Preserves raise) {iterator : AllocatedCollect.Iterator Extra}
    {index : Nat} {acquired : List AllocatedCollect.Element} {before : World Extra}
    {calls : List Nat} {final : Outcome (World Extra) (Except Error Resource) Unwind Terminal}
    (trace : AllocatedCollect.Trace protocol iterator (AllocatedCollect.borrowElement raise)
      index acquired before calls final) :
    ∀ {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}, before.1.Valid →
      before.1.resolve guard = some slot →
      (∀ element ∈ acquired, element.2.guard ≠ guard) → Frame before guard final := by
  induction trace with
  | @done index acquired before pending final complete finished exit =>
    intro guard slot valid live outside
    have frame := laws.finish _ _ valid guard slot live (by simp) _ finished
    cases pending with
    | returned _ _ => cases exit; exact frame
    | unwound reason after =>
      exact collection_cleanup (laws.retire _) (pending := .unwound reason after)
        live outside frame exit
    | terminated _ => cases exit; trivial
  | next within read called tail induction =>
    intro guard slot valid live outside
    have frame := borrowElement_preserves raiseLaw _ _ valid guard slot live (by simp) _ called
    have distinct := borrowElement_fresh live called
    apply Frame.prepend frame
    apply induction frame.valid (frame.resolve live)
    intro element member
    rcases List.mem_append.mp member with prior | last
    · exact outside element prior
    · cases List.mem_singleton.mp last
      exact distinct
  | error within read called cleaned =>
    intro guard slot valid live outside
    have frame := borrowElement_preserves raiseLaw _ _ valid guard slot live (by simp) _ called
    exact collection_cleanup (laws.retire _) live outside frame cleaned
  | unwind within read called cleaned =>
    intro guard slot valid live outside
    have frame := borrowElement_preserves raiseLaw _ _ valid guard slot live (by simp) _ called
    exact collection_cleanup (laws.retire _) live outside frame cleaned
  | terminal => intro _ _ _ _ _; trivial
  | internalReturn within stepped tail induction =>
    intro guard slot valid live outside
    have frame := laws.internal _ _ _ () valid guard slot live (by simp) _ stepped
    exact Frame.prepend frame (induction frame.valid (frame.resolve live) outside)
  | internalUnwind within stepped cleaned =>
    intro guard slot valid live outside
    have frame := laws.internal _ _ _ () valid guard slot live (by simp) _ stepped
    exact collection_cleanup (laws.retire _) live outside frame cleaned
  | internalTerminal => intro _ _ _ _ _; trivial

/-- The required collector protocol and primitive frame laws imply its actual
callback-composed effect frames every previously held guard. No successful
collection, complete token body or assumed final frame appears in admission. -/
theorem collection_preserves {types : OnchainAllocated.Types}
    {provider : AllocatedCollect.Provider types.Extra types.GuardResource
      types.Unwind types.Terminal}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (conforms : provider.Conforms protocol) (frames : CollectionFrames protocol)
    (raiseLaw : Preserves types.raise)
    (iterator : AllocatedCollect.Iterator types.Extra) :
    Preserves (fun state (_ : Unit) =>
      provider.run iterator (AllocatedCollect.borrowElement types.raise) state) := by
  intro before _ valid guard slot live _ outcome called
  obtain ⟨calls, actual⟩ := conforms iterator _ before outcome called
  exact frames.trace raiseLaw actual valid live (by simp)

/-- Internal collection work cannot erase a current read before a later
iterator or source callback. Unlike a complete trace theorem, this conclusion
needs only the particular primitive exit already reached. -/
theorem collection_internal_read {Extra Resource Unwind Terminal : Type}
    {protocol : AllocatedCollect.Protocol Extra Resource Unwind Terminal}
    {index : Nat} {acquired : List AllocatedCollect.Element}
    (law : Preserves (fun state (_ : Unit) => protocol.internal index acquired state))
    {before after : World Extra} {reference : AllocatedControl.DataRef} {bytes : Bytes}
    (valid : before.1.Valid)
    (read : reference.read before = some bytes)
    (called : protocol.internal index acquired before (.returned () after)) :
    reference.read after = some bytes :=
  law.read_returned (args := ()) valid read called

end Solanalib.Specs.Core.Token.AllocatedGuard
