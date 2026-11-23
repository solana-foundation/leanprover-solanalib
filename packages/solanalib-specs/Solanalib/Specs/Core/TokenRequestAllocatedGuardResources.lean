/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuard
public import Solanalib.Specs.Core.TokenRequestAllocatedTypes
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol
public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedGuard

/-- A retained resource observation in an actual finite exit. Terminal exits
have no state to observe and do not manufacture a resource or cleanup. -/
def ObservationOutcome {Extra Resource Value Result Unwind Terminal : Type}
    (observe : World Extra → Resource → Option Value) (resource : Resource) (value : Value) :
    Outcome (World Extra) Result Unwind Terminal → Prop
  | .returned _ after | .unwound _ after => observe after resource = some value
  | .terminated _ => True

/-- A primitive cannot replace or erase another retained resource between
source reads. This law quantifies its exits independently of a later read or
completed SDK body. It constrains only the supplied observation footprint. -/
def Retains {Extra Resource Value Args Result Unwind Terminal : Type}
    (observe : World Extra → Resource → Option Value)
    (call : Callback.Run (World Extra) Args Result Unwind Terminal) : Prop :=
  ∀ before args resource value, observe before resource = some value →
    ∀ outcome, call before args outcome → ObservationOutcome observe resource value outcome

/-- An unavailable primitive has no invented finite exit. -/
theorem Retains.empty {Extra Resource Value Args Result Unwind Terminal : Type}
    (observe : World Extra → Resource → Option Value) :
    Retains observe (fun (_ : World Extra) (_ : Args)
      (_ : Outcome (World Extra) Result Unwind Terminal) => False) := by
  intro _ _ _ _ _ _ impossible
  exact False.elim impossible

/-- A mathematical focus on disjoint auxiliary storage preserves every
retained observation on both returns and unwinds. -/
theorem Retains.focus {Extra Inner Resource Value Args Result Unwind Terminal : Type}
    (observe : World Extra → Resource → Option Value)
    (part : Owned.Focus (World Extra) Inner)
    (outside : ∀ before inner resource, observe (part.set before inner) resource =
      observe before resource)
    (call : Callback.Run Inner Args Result Unwind Terminal) : Retains observe (part.lift call) := by
  rintro before args resource value current _ ⟨produced, _, rfl⟩
  cases produced with
  | returned _ inner => exact (outside before inner resource).trans current
  | unwound _ inner => exact (outside before inner resource).trans current
  | terminated _ => trivial

/-- Selecting primitive inputs changes no retained observation obligation. -/
theorem Retains.arguments {Extra Resource Value Args Selected Result Unwind Terminal : Type}
    {observe : World Extra → Resource → Option Value}
    {call : Callback.Run (World Extra) Args Result Unwind Terminal}
    (law : Retains observe call) (select : Selected → Args) :
    Retains observe (fun before selected => call before (select selected)) := by
  intro before selected
  exact law before (select selected)

/-- Mapping a return value keeps the actual post-state of the primitive. -/
theorem Retains.map {Extra Resource Value Args Result Next Unwind Terminal : Type}
    {observe : World Extra → Resource → Option Value}
    {call : Callback.Run (World Extra) Args Result Unwind Terminal}
    (law : Retains observe call) (f : Result → Next) : Retains observe (Callback.map f call) := by
  rintro before args resource value current _ ⟨produced, called, rfl⟩
  have frame := law before args resource value current produced called
  cases produced <;> exact frame

/-- Sequential retention consumes each actual primitive exit, with first-call
admission required even when the continuation has no finite outcome. -/
theorem Retains.bind {Extra Resource Value Args Result Next Unwind Terminal : Type}
    {observe : World Extra → Resource → Option Value}
    {first : Callback.Run (World Extra) Args Result Unwind Terminal}
    {next : Result → World Extra → Outcome (World Extra) Next Unwind Terminal → Prop}
    (firstLaw : Retains observe first)
    (nextLaw : ∀ value, Retains observe (fun state (_ : Unit) => next value state)) :
    Retains observe (Callback.bind first next) := by
  rintro before args resource value current outcome ⟨produced, called, continued⟩
  have kept := firstLaw before args resource value current produced called
  cases produced with
  | returned result after => exact nextLaw result after () resource value kept outcome continued
  | unwound _ _ => cases continued; exact kept
  | terminated _ => cases continued; trivial

/-- A resource observer does not treat a borrow-store update as a vector
mutation. AccountInfo acquisition/release leave auxiliary storage unchanged;
the independent resource binding must justify this observer property. -/
def CurrentOnAux {Extra Resource Value : Type}
    (observe : World Extra → Resource → Option Value) : Prop :=
  ∀ accounts next extra resource, observe (accounts, extra) resource =
    observe (next, extra) resource

/-- Equal auxiliary stores suffice for equality of a resource observation. -/
theorem CurrentOnAux.same {Extra Resource Value : Type}
    {observe : World Extra → Resource → Option Value} (law : CurrentOnAux observe)
    {before after : World Extra} (same : after.2 = before.2) (resource : Resource) :
    observe after resource = observe before resource := by
  rcases before with ⟨accounts, extra⟩
  rcases after with ⟨next, other⟩
  cases same
  exact law next accounts extra resource

end Solanalib.Specs.Core.Token.AllocatedGuard
