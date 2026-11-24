/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Wrappers

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- A returned error is observed through its actual box, when present, and
through every currently owned String in declaration order. -/
def errorContents (resources : Resources) (profile : Profile) (state : resources.State)
    (error : Error resources profile) :
    Option (AnchorErrorOperations.Payload resources.ProgramError resources.StringResource × List
      String) := do
  let payload ← AnchorErrorOperations.currentPayload profile.storage resources.errors state error
  let strings ← (payload.strings resources.errors.programStrings).mapM
    (resources.errors.currentString state)
  pure (payload, strings)

/-- Only these destructors follow an invocation return in the selected
wrappers. Keys, serialization temporaries and DataV2 fields have already left
scope and therefore impose no returned-error frame obligation. -/
inductive ReturnDrop (resources : Resources) where
  | metas (resource : resources.MetaResource)
  | bytes (resource : resources.ByteResource)
  | infos (resource : resources.InfoResource)
  | account (value : AccountInfo.Value)

def ReturnDrop.action {resources : Resources} : ReturnDrop resources →
    Owned.DropAction resources.State resources.Unwind resources.Terminal
  | .metas resource => resources.metas.dropAction resource
  | .bytes resource => resources.bytes.dropAction resource
  | .infos resource => resources.infos.dropAction resource
  | .account value => infoDrop resources value

/-- The exact resource obligations of converting and retaining a program
error. A boxed release initializes the actual returned box and retains the
moved error Strings. Final local destruction preserves the current
contents of this error. No successful allocation or destructor exit is required. -/
structure ErrorResources (resources : Resources) (profile : Profile) : Prop where
  allocation : match profile.storage with
    | .inline => True
    | .boxed => ∀ before program box after,
        resources.errors.newBox before (.program ⟨program, none, none⟩) (.returned box after) →
        resources.errors.currentBox after box = some (.program ⟨program, none, none⟩) ∧
          (resources.errors.programStrings program).mapM (resources.errors.currentString after) =
            (resources.errors.programStrings program).mapM (resources.errors.currentString before)
  cleanup : ∀ (drop : ReturnDrop resources) before after error contents,
    errorContents resources profile before error = some contents →
    drop.action before (.returned () after) →
    errorContents resources profile after error = some contents

/-- A finite conversion returns the complete dependency error and the same
owned string contents; the selected allocation supplies its actual box. -/
theorem ErrorResources.converted {resources : Resources} {profile : Profile}
    (ready : ErrorResources resources profile) (before after : resources.State)
    (program : resources.ProgramError) (strings : List String) (error : Error resources profile)
    (live : (resources.errors.programStrings program).mapM
      (resources.errors.currentString before) = some strings)
    (converted : AnchorErrorOperations.fromProgram profile.storage resources.errors
      before program (.returned error after)) :
    errorContents resources profile after error =
      some (.program ⟨program, none, none⟩, strings) := by
  cases profile with
  | legacyInline =>
    cases converted
    simp [errorContents, Profile.storage, AnchorErrorOperations.currentPayload, Option.bind,
      AnchorErrorOperations.Payload.strings, AnchorErrorOwned.originStrings,
      AnchorErrorOwned.comparedStrings, live]
  | legacyBoxed | modern =>
    obtain ⟨produced, called, returned⟩ := converted
    cases produced with
    | unwound impossible _ => nomatch impossible
    | terminated reason => cases returned
    | returned box final =>
      cases returned
      obtain ⟨current, retained⟩ := ready.allocation before program box after called
      simp [errorContents, Profile.storage, AnchorErrorOperations.currentPayload, current,
        AnchorErrorOperations.Payload.strings, AnchorErrorOwned.originStrings,
        AnchorErrorOwned.comparedStrings, retained, live]

/-- Every actual returning cleanup step retains the same live error. The
list records source order and includes repeated AccountInfo owners. -/
theorem ErrorResources.cleaned {resources : Resources} {profile : Profile}
    (ready : ErrorResources resources profile) (drops : List (ReturnDrop resources))
    (before after : resources.State) (error : Error resources profile)
    (contents : AnchorErrorOperations.Payload resources.ProgramError resources.StringResource ×
      List String)
    (current : errorContents resources profile before error = some contents)
    (cleaned : Owned.DropReturns (drops.map ReturnDrop.action) before after) :
    errorContents resources profile after error = some contents ∧
      Owned.cleanup resources.doubleUnwind (drops.map ReturnDrop.action)
        (.returned (.error error : Except (Error resources profile) Unit) before)
        (.returned (.error error) after) := by
  constructor
  · induction drops generalizing before with
    | nil => cases cleaned; exact current
    | cons drop rest induction =>
      cases cleaned with
      | cons _ _ _ middle _ head tail =>
        exact induction middle (ready.cleanup drop before middle error contents current head) tail
  · exact cleaned.cleanup_returned resources.doubleUnwind
      (.error error : Except (Error resources profile) Unit)

end Solanalib.Specs.Core.AnchorSplSupport
