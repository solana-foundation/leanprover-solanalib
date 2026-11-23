/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperations
public import Solanalib.Specs.Core.ProgramErrorOwnedValues

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- the only observations of PartialEq are current boxes and the current Strings of the legacy
dependency. Diagnostic origin/name/message fields are intentionally unused. -/
structure EqualityTypes where
  State : Type
  StringResource : Type
  BoxResource : Type
  currentString : State → StringResource → Option String
  currentBox : State → BoxResource →
    Option (Payload (ProgramErrorOwned.Value StringResource) StringResource)

/-- The exact derived Error equality: variant first, the code-only Anchor
PartialEq second, or the full legacy ProgramError PartialEq. -/
def equalPayload {State S : Type} (currentString : State → S → Option String)
    (state : State) :
    Payload (ProgramErrorOwned.Value S) S → Payload (ProgramErrorOwned.Value S) S → Option Bool
  | .anchor left, .anchor right => some (decide (left.number = right.number))
  | .program left, .program right => ProgramErrorOwned.equal currentString state left.error
    right.error
  | .anchor _, .program _ | .program _, .anchor _ => some false

def equalityRun (types : EqualityTypes) : Callback.Run types.State
    (AnchorErrorOwned.Error types.BoxResource × AnchorErrorOwned.Error types.BoxResource)
    Bool Empty Empty :=
  fun before args outcome => ∃ left right result,
    types.currentBox before args.1.resource = some left ∧
    types.currentBox before args.2.resource = some right ∧
    equalPayload types.currentString before left right = some result ∧
    outcome = .returned result before

/-- Equality neither clones, formats, mutates nor frees either borrowed error. -/
def equalityFamily : Family where
  Index := EqualityTypes
  State := EqualityTypes.State
  Args := fun types =>
    AnchorErrorOwned.Error types.BoxResource × AnchorErrorOwned.Error types.BoxResource
  Value := fun _ => Bool
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun types => { requires := fun _ _ => True, post := equalityRun types }

theorem equality_reference : FamilyReference equalityFamily equalityRun := fun _ _ _ _ _ run => run

/-- The sample deliberately uses two same-status Borsh errors with different
text. A status-code comparison cannot satisfy this execution. -/
abbrev equalitySample : EqualityTypes where
  State := Unit
  StringResource := String
  BoxResource := Bool
  currentString := fun _ text => some text
  currentBox := fun _ box => some (.program ⟨.borshIoError (if box then "a" else "b"), none, none⟩)

theorem equality_hasExecution : FamilyHasExecution equalityFamily equalityRun equalitySample :=
  ⟨(), (⟨true⟩, ⟨false⟩), .returned false (), trivial,
    ⟨_, _, false, rfl, rfl, rfl, rfl⟩⟩

theorem equality_satisfiable : FamilySatisfiable equalityFamily equalitySample :=
  equality_hasExecution.satisfiable

/-- Names and messages need no readable representation for code-only equality:
they are never observed by AnchorError::eq. -/
theorem equalPayload_anchor {State S : Type}
    (currentString : State → S → Option String) (state : State)
    (left right : AnchorPayload S) :
    equalPayload currentString state (.anchor left) (.anchor right) =
      some (decide (left.number = right.number)) := rfl

end Solanalib.Specs.Core.AnchorErrorOperations
