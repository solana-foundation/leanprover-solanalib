/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionListCurrent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

open Owned

/-- An explicit dependency law preserving the shared source bytes across a
normally returning push. It imposes no frame condition on unwinds, terminal
exits or cleanup, and is not built into the operational collector. -/
def ExtensionReadFrame {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (length : Nat) (byteAt : State → Fin length → UInt8) : Prop :=
  ∀ before resource kind after,
    ops.push before (resource, kind) (.returned () after) →
      ∀ index, byteAt after index = byteAt before index

/-- The read-frame law preserves the complete observed slice after a normal
push, while leaving all other changes to the actual state unconstrained. -/
theorem currentExtensionBytes_eq_of_push {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (length : Nat) (byteAt : State → Fin length → UInt8)
    (frame : ExtensionReadFrame ops length byteAt)
    (before after : State) (resource : Resource) (kind : ExtensionType)
    (pushed : ops.push before (resource, kind) (.returned () after)) :
    currentExtensionBytes length byteAt after = currentExtensionBytes length byteAt before :=
  congrArg List.ofFn (funext (frame before resource kind after pushed))

/-- Scope cleanup of an ordinary parse error cannot create a successful list. -/
private theorem extensionCleanup_error_no_success {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource result : Resource)
    (before after : State) :
    ¬ cleanup double [ops.dropAction resource]
      (.returned (.error .InvalidAccountData) before :
        Outcome State (Except Error Resource) Unwind Terminal)
      (.returned (.ok result) after) := by
  rintro ⟨dropped, called, finished⟩
  cases dropped <;> simp_all [cleanup]

/-- Scope cleanup of an unwind cannot manufacture a successful list return. -/
private theorem extensionCleanup_unwind_no_success {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource result : Resource)
    (before after : State) (reason : Unwind) :
    ¬ cleanup double [ops.dropAction resource]
      (.unwound reason before : Outcome State (Except Error Resource) Unwind Terminal)
      (.returned (.ok result) after) := by
  rintro ⟨dropped, called, finished⟩
  cases dropped <;> simp_all [cleanup]

/-- The successful-push content law and the explicit read-frame law recover the pure
ordered fold from a successful live-slice collection. The returned owner is the
same resource, and its actual final contents supply the pure result. -/
theorem collectCurrentExtensionTypes_success {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (push_current : ∀ before resource value values after,
      ops.current before resource = some values →
      ops.push before (resource, value) (.returned () after) →
        ops.current after resource = some (values ++ [value]))
    (double : DoubleUnwind State Unwind Terminal)
    (resource result : Resource) (length : Nat) (byteAt : State → Fin length → UInt8)
    (frame : ExtensionReadFrame ops length byteAt) (offset : Nat)
    (before after : State) (values : List ExtensionType)
    (current : ops.current before resource = some values)
    (run : collectCurrentExtensionTypes ops double resource length byteAt offset before
      (.returned (.ok result) after)) :
    ∃ finalValues used,
      result = resource ∧ ops.current after result = some finalValues ∧
      foldExtensionTypes (fun prior kind => .ok (prior ++ [kind])) values offset
        ((currentExtensionBytes length byteAt before).drop offset) = .ok (finalValues, used) := by
  rw [collectCurrentExtensionTypes] at run
  split at run
  · rename_i scanned
    cases run
    exact ⟨values, offset, rfl, current, by rw [foldExtensionTypes_scan, scanned]⟩
  · exact False.elim (extensionCleanup_error_no_success ops double resource result before after run)
  · rename_i kind consumed tail scanned
    obtain ⟨pushed, method, continued⟩ := run
    cases pushed with
    | returned returnedUnit middle =>
      cases returnedUnit
      have middleCurrent := push_current before resource kind values middle current method
      obtain ⟨finalValues, used, same, currentAfter, pureFold⟩ :=
        collectCurrentExtensionTypes_success ops push_current double resource result length byteAt
          frame
          (offset + consumed) middle after (values ++ [kind]) middleCurrent continued
      have bytesSame := currentExtensionBytes_eq_of_push ops length byteAt frame before middle
        resource kind method
      have tailSame := nextExtension_next_tail_eq _ kind consumed tail scanned
      have remainingSame :
          (currentExtensionBytes length byteAt middle).drop (offset + consumed) = tail := by
        rw [bytesSame, tailSame, List.drop_drop]
      refine ⟨finalValues, used, same, currentAfter, ?_⟩
      rw [foldExtensionTypes_scan, scanned]
      simpa only [remainingSame, Except.bind] using pureFold
    | unwound reason middle =>
      exact False.elim (extensionCleanup_unwind_no_success ops double resource result middle after
        reason continued)
    | terminated reason => cases continued
termination_by length - offset
decreasing_by
  have geometry := nextExtension_next_geometry _ _ _ _ (by assumption)
  simp only [List.length_drop, currentExtensionBytes_length] at geometry
  omega

end Solanalib.Specs.Core.Token
