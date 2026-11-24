/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoGuardCallback
public import Solanalib.Specs.Core.AnchorErrorOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorGuardEffects

open AccountInfo.GuardCallback (World Admissible Frame)

/-- A dependency focused into auxiliary state preserves the held borrow store
on every finite exit, independently of its effects or termination behavior. -/
theorem focused_admissible {Aux Args Value Unwind Terminal : Type}
    (run : Callback.Run Aux Args Value Unwind Terminal) (before : World Aux)
    (args : Args) (guard : Borrow.Guard) (valid : before.1.Valid) :
    Admissible guard (Owned.Focus.snd.lift run) before args := by
  rintro _ ⟨produced, _, rfl⟩
  cases produced with
  | returned _ _ => exact AccountInfo.GuardCallback.StateFrame.refl before.1 guard valid
  | unwound _ _ => exact AccountInfo.GuardCallback.StateFrame.refl before.1 guard valid
  | terminated _ => trivial

/-- Primitive guard obligations for the selected fixed-code factory. Each
obligation applies at its actual source-ordered input, including a first
allocation that returns even if a later dependency has no finite exit. -/
structure BuildCodeAdmissible {Aux StringResource BoxResource Terminal : Type}
    (ops : AnchorErrorOwned.Ops (World Aux) StringResource BoxResource Terminal)
    (before : World Aux) (guard : Borrow.Guard) (code : AnchorErrorOwned.Code) : Prop where
  /-- The name allocation frames every one of its actual exits. -/
  name : Admissible guard ops.copyLiteral before code.name
  /-- The message allocation is checked at every reached name-return state. -/
  message : ∀ name afterName, ops.copyLiteral before code.name (.returned name afterName) →
    Admissible guard ops.formatLiteral afterName code.message
  /-- Box allocation is checked after each actual name/message return pair. -/
  boxed : ∀ name afterName, ops.copyLiteral before code.name (.returned name afterName) →
    ∀ message afterMessage, ops.formatLiteral afterName code.message (.returned message
      afterMessage) →
      Admissible guard ops.newBox afterMessage
        (.anchor ⟨name, code.number, message, none, none⟩)

/-- Primitive reached-site admission composes to the whole relation of the factory.
The premise is stronger than framing only completed factory exits. -/
theorem BuildCodeAdmissible.admissible {Aux StringResource BoxResource Terminal : Type}
    {ops : AnchorErrorOwned.Ops (World Aux) StringResource BoxResource Terminal}
    {before : World Aux} {guard : Borrow.Guard} {code : AnchorErrorOwned.Code}
    (admitted : BuildCodeAdmissible ops before guard code) :
    Admissible guard (AnchorErrorOwned.buildCode ops) before code := by
  apply AccountInfo.GuardCallback.Admissible.bind admitted.name
  intro name afterName copied
  apply AccountInfo.GuardCallback.Admissible.bind (admitted.message name afterName copied)
  intro message afterMessage formatted
  exact (admitted.boxed name afterName copied message afterMessage formatted).map
    AnchorErrorOwned.Error.mk

/-- The shared independent error heap meets all three primitive guard laws;
it can still exhaust its modeled allocation supply and terminate. -/
theorem BuildCodeAdmissible.focused {Aux StringResource BoxResource Terminal : Type}
    (ops : AnchorErrorOwned.Ops Aux StringResource BoxResource Terminal)
    (before : World Aux) (guard : Borrow.Guard) (code : AnchorErrorOwned.Code)
    (valid : before.1.Valid) :
    BuildCodeAdmissible (ops.focus Owned.Focus.snd) before guard code := by
  have name := focused_admissible ops.copyLiteral before code.name guard valid
  refine ⟨name, ?_, ?_⟩
  · intro resource after called
    exact focused_admissible ops.formatLiteral after code.message guard (name _ called).valid
  · intro nameResource afterName copied messageResource afterMessage formatted
    have message := focused_admissible ops.formatLiteral afterName code.message guard
      (name _ copied).valid
    exact focused_admissible ops.newBox afterMessage
      (.anchor ⟨nameResource, code.number, messageResource, none, none⟩) guard
      (message _ formatted).valid

end Solanalib.Specs.Core.AnchorGuardEffects
