/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecyclePayload

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

private theorem resultBind_success {State Args Error First Last Unwind Terminal : Type}
    {first : Callback.Run State Args (Except Error First) Unwind Terminal}
    {next : First → State → Outcome State (Except Error Last) Unwind Terminal → Prop}
    {before after : State} {args : Args} {result : Last}
    (called : AnchorEffects.resultBind first next before args (.returned (.ok result) after)) :
    ∃ value middle, first before args (.returned (.ok value) middle) ∧
      next value middle (.returned (.ok result) after) := by
  obtain ⟨produced, initial, continued⟩ := called
  cases produced with
  | unwound _ _ => cases continued
  | terminated _ => cases continued
  | returned value middle =>
    cases value with
    | error _ => cases continued
    | ok value => exact ⟨value, middle, initial, continued⟩

/-- A returned Account contains the original AccountInfo and exactly the
payload produced by the reached decoder. The intermediate states come from
the actual initialization and Owner calls; no admission premise is needed. -/
theorem construct_account_success {storage : InfoStorage} {types : PayloadTypes}
    {before after : World types.Aux} {args : AccountInfo.Args}
    {result : AnchorAccount.Account types.Payload}
    (called : construct .account storage types before args (.returned (.ok result) after)) :
    ∃ started checked,
      initialized types before args (.returned (.ok ()) started) ∧
      ownerCheck types started args (.returned (.ok ()) checked) ∧
      decodePayload storage types checked args (.returned (.ok result.value) after) ∧
      result.info = args.info := by
  obtain ⟨ignored, started, initializedCall, next⟩ := resultBind_success called
  cases ignored
  obtain ⟨ignored, checked, ownerCall, next⟩ := resultBind_success next
  cases ignored
  obtain ⟨produced, decodedCall, wrapped⟩ := next
  cases produced with
  | unwound _ _ => cases wrapped
  | terminated _ => cases wrapped
  | returned decoded final =>
    cases decoded with
    | error _ => cases wrapped
    | ok payload =>
      cases wrapped
      exact ⟨started, checked, initializedCall, ownerCall, decodedCall, rfl⟩

/-- InterfaceAccount takes its saved owner from the final decoder state.
The CheckOwner callback and decoder remain the actually reached calls, with
all their state effects retained in that final state. -/
theorem construct_interface_success {storage : InfoStorage} {types : PayloadTypes}
    {before after : World types.Aux} {args : AccountInfo.Args}
    {result : AnchorAccount.InterfaceAccount types.Payload}
    (called : construct .interfaceAccount storage types before args (.returned (.ok result) after))
      :
    ∃ started checked,
      initialized types before args (.returned (.ok ()) started) ∧
      AnchorAccount.widenCallback types.checkOwner started args.info.ownerRef
        (.returned (.ok ()) checked) ∧
      decodePayload storage types checked args (.returned (.ok result.account.value) after) ∧
      result.account.info = args.info ∧ result.owner = types.ownerAt after.2 args.info.ownerRef :=
        by
  obtain ⟨ignored, started, initializedCall, next⟩ := resultBind_success called
  cases ignored
  obtain ⟨ignored, checked, checkOwnerCall, next⟩ := resultBind_success next
  cases ignored
  obtain ⟨produced, decodedCall, wrapped⟩ := next
  cases produced with
  | unwound _ _ => cases wrapped
  | terminated _ => cases wrapped
  | returned decoded final =>
    cases decoded with
    | error _ => cases wrapped
    | ok payload =>
      cases wrapped
      exact ⟨started, checked, initializedCall, checkOwnerCall, decodedCall, rfl, rfl⟩

/-- Successful constructor inversion, uniform in the two wrapper kinds.
It exposes the real reached prefix and exact returned aggregate without
assuming that any unexecuted trait or allocator call succeeds. -/
theorem construct_success_trace {kind : PayloadKind} {storage : InfoStorage} {types : PayloadTypes}
    {before after : World types.Aux} {args : AccountInfo.Args}
    {result : kind.constructor.Result types.Payload}
    (called : construct kind storage types before args (.returned (.ok result) after)) :
    ∃ started checked payload,
      initialized types before args (.returned (.ok ()) started) ∧
      (match kind with
        | .account => ownerCheck types
        | .interfaceAccount => fun state input =>
            AnchorAccount.widenCallback types.checkOwner state input.info.ownerRef)
        started args (.returned (.ok ()) checked) ∧
      decodePayload storage types checked args (.returned (.ok payload) after) ∧
      (match kind, result with
        | .account, value => value = ⟨payload, args.info⟩
        | .interfaceAccount, value =>
            value = ⟨⟨payload, args.info⟩, types.ownerAt after.2 args.info.ownerRef⟩) := by
  cases kind with
  | account =>
    obtain ⟨started, checked, initial, owner, decoded, info⟩ := construct_account_success called
    refine ⟨started, checked, result.value, initial, owner, decoded, ?_⟩
    cases result
    cases info
    rfl
  | interfaceAccount =>
    obtain ⟨started, checked, initial, owner, decoded, info, saved⟩ := construct_interface_success
      called
    refine ⟨started, checked, result.account.value, initial, owner, decoded, ?_⟩
    cases result with
    | mk account savedOwner =>
      cases account
      cases info
      cases saved
      rfl

/-- Both constructors preserve the original input record value; source record identity and pointer
provenance require separate source-binding proofs. -/
theorem construct_success_info {kind : PayloadKind} {storage : InfoStorage} {types : PayloadTypes}
    {before after : World types.Aux} {args : AccountInfo.Args}
    {result : kind.constructor.Result types.Payload}
    (called : construct kind storage types before args (.returned (.ok result) after)) :
    (match kind, result with
      | .account, value => value.info
      | .interfaceAccount, value => value.account.info) = args.info := by
  cases kind with
  | account =>
    obtain ⟨_, _, _, _, _, info⟩ := construct_account_success called
    exact info
  | interfaceAccount =>
    obtain ⟨_, _, _, _, _, info, _⟩ := construct_interface_success called
    exact info

end Solanalib.Specs.Core.AnchorLifecycle
