/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionGetter
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The transfer-hook and permanent-delegate convenience functions call the
actual resolved get_extension method, then copy one nullable key field. Their
Result::ok consumes an ordinary error, including its owned payload and drop. -/
structure ExtensionKeyGetter where
  /-- Actual interpretation state. -/
  State : Type
  /-- Identity of the returned borrowed extension. -/
  Reference : Type
  /-- Dependency unwind reasons. -/
  Unwind : Type
  /-- Dependency terminal reasons. -/
  Terminal : Type
  /-- The actual get_extension call specialized to the fixed Pod of the helper. -/
  getExtension : State → Outcome State (Except Error Reference) Unwind Terminal → Prop
  /-- Destruction of the actual returned error. Its owned payload remains in
  State even when Error records only the error variant. -/
  dropError : Callback.Run State Error Unit Unwind Terminal
  /-- The exact nullable key field read through the returned reference. -/
  key : State → Reference → Solanalib.Runtime.Pubkey

/-- Copying an OptionalNonZeroPubkey maps only the all-zero key to None. -/
def nullableKey (key : Solanalib.Runtime.Pubkey) : Option Solanalib.Runtime.Pubkey :=
  if key = .zero then none else some key

/-- Copy a successful key, or consume an ordinary error before returning None.
No error-drop return, unwind, or terminal state is invented. -/
def finishKey (getter : ExtensionKeyGetter) :
    Outcome getter.State (Except Error getter.Reference) getter.Unwind getter.Terminal →
      Outcome getter.State (Option Solanalib.Runtime.Pubkey) getter.Unwind getter.Terminal → Prop
  | .returned (.ok reference) after, final =>
      final = .returned (nullableKey (getter.key after reference)) after
  | .returned (.error error) after, final =>
      ∃ dropped, getter.dropError after error dropped ∧
        final = Outcome.map (fun _ => none) dropped
  | .unwound reason after, final => final = .unwound reason after
  | .terminated reason, final => final = .terminated reason

/-- Complete wrapper control flow, with no guessed default trait method. -/
def getExtensionKey (getter : ExtensionKeyGetter) (before : getter.State)
    (final : Outcome getter.State (Option Solanalib.Runtime.Pubkey) getter.Unwind getter.Terminal)
      : Prop :=
  ∃ called, getter.getExtension before called ∧ finishKey getter called final

/-- Returned dependency errors are masked only after their actual drop returns;
both the getter and error-destructor state changes survive. -/
theorem getExtensionKey_error (getter : ExtensionKeyGetter) (before middle after : getter.State)
    (error : Error) (called : getter.getExtension before (.returned (.error error) middle))
    (dropped : getter.dropError middle error (.returned () after)) :
    getExtensionKey getter before (.returned none after) :=
  ⟨.returned (.error error) middle, called, .returned () after, dropped, rfl⟩

/-- Abnormal finite error-drop exits are forwarded, rather than hidden by ok. -/
theorem getExtensionKey_error_exit (getter : ExtensionKeyGetter) (before middle : getter.State)
    (error : Error) (called : getter.getExtension before (.returned (.error error) middle))
    (dropped : Outcome getter.State Unit getter.Unwind getter.Terminal)
    (ran : getter.dropError middle error dropped) :
    getExtensionKey getter before (Outcome.map (fun _ => none) dropped) :=
  ⟨.returned (.error error) middle, called, dropped, ran, rfl⟩

/-- The helper does not turn an unwind into an absent optional key. -/
theorem getExtensionKey_unwind (getter : ExtensionKeyGetter) (before after : getter.State)
    (reason : getter.Unwind) (called : getter.getExtension before (.unwound reason after)) :
    getExtensionKey getter before (.unwound reason after) :=
  ⟨.unwound reason after, called, rfl⟩

/-- A nonreturning extension getter gives the convenience wrapper no invented
None return, unwind, or terminal exit. -/
theorem getExtensionKey_no_exit (getter : ExtensionKeyGetter) (before : getter.State)
    (noExit : ∀ outcome, ¬ getter.getExtension before outcome) :
    ∀ final, ¬ getExtensionKey getter before final := by
  rintro final ⟨called, ran, _⟩
  exact noExit called ran

/-- The generic typed getter can be composed with a concrete field decoder;
reference identity and actual get_extension states remain unchanged. -/
def keyGetterOf (getter : ExtensionGetter)
    (field : getter.representation.Value → Solanalib.Runtime.Pubkey)
    (dropError : Callback.Run getter.provider.State Error Unit
      getter.provider.Unwind getter.provider.Terminal) : ExtensionKeyGetter where
  State := getter.provider.State
  Reference := TypedExtensionReference getter.provider.Reference getter.representation.Value
  Unwind := getter.provider.Unwind
  Terminal := getter.provider.Terminal
  getExtension := getExtensionOperational getter.provider getter.representation
  dropError := dropError
  key := fun _ reference => field reference.value

end Solanalib.Specs.Core.Token
