/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.AnchorLifecycleValidation

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleCollections

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

theorem leaf_error_keeps_consumed_tail {types : ValidationAccountsTypes}
    {kind : ValidationKind} {storage : InfoStorage}
    {before after : AnchorAccount.World types.Aux} {args : AccountsArgs}
    {head : AccountReference} {tail : List AccountReference} {bumps : types.Bumps}
    {reallocs : List Solanalib.Runtime.Pubkey} {error : types.toValidationTypes.toBase.Error}
    (failed : validate kind storage types.toValidationTypes before ⟨args.profile, head⟩
      (.returned (.error error) after)) :
    validationAccountsRun kind storage types (before, ⟨head :: tail, bumps, reallocs⟩) args
      (.returned (.error error) (after, ⟨tail, bumps, reallocs⟩)) :=
  ⟨.returned (.error error) after, failed, rfl⟩

theorem leaf_unwind_keeps_consumed_tail {types : ValidationAccountsTypes}
    {kind : ValidationKind} {storage : InfoStorage}
    {before after : AnchorAccount.World types.Aux} {args : AccountsArgs}
    {head : AccountReference} {tail : List AccountReference} {bumps : types.Bumps}
    {reallocs : List Solanalib.Runtime.Pubkey} {reason : types.toValidationTypes.toBase.Unw}
    (failed : validate kind storage types.toValidationTypes before ⟨args.profile, head⟩
      (.unwound reason after)) :
    validationAccountsRun kind storage types (before, ⟨head :: tail, bumps, reallocs⟩) args
      (.unwound reason (after, ⟨tail, bumps, reallocs⟩)) :=
  ⟨.unwound reason after, failed, rfl⟩

theorem box_inner_error_retains_state {types : AccountCollectionTypes}
    {before after : AnchorAccount.World types.Aux × AccountsState types.Bumps}
    {args : AccountsArgs} {error : types.toBase.Error}
    (failed : types.inner before args (.returned (.error error) after)) :
    collectionBoxedRun types before args (.returned (.error error) after) :=
  ⟨.returned (.error error) after, failed, rfl⟩

theorem box_inner_unwind_skips_allocator {types : AccountCollectionTypes}
    {before after : AnchorAccount.World types.Aux × AccountsState types.Bumps}
    {args : AccountsArgs} {reason : types.toBase.Unw}
    (failed : types.inner before args (.unwound reason after)) :
    collectionBoxedRun types before args (.unwound reason after) :=
  ⟨.unwound reason after, failed, rfl⟩

/-- The inner constructor can terminate even when no allocator continuation
is available. The terminal outcome carries no returned account state. -/
abbrev terminalCollection : AccountCollectionTypes where
  toBase := (AnchorLifecycleValidation.validation .boxed).toBase
  Bumps := Nat
  Payload := Nat
  PayloadBox := Nat
  inner := Callback.ofFunction fun _ _ => .terminated (.inr "inner abort")
  newBox := fun _ _ _ => False

def terminalBefore : AnchorAccount.World (List Nat) × AccountsState Nat :=
  (AnchorLifecycleValidation.before, ⟨[validationArgs.reference], 2, []⟩)

theorem box_inner_terminal_skips_allocator :
    collectionBoxedRun terminalCollection terminalBefore collectionArgs
      (.terminated (.inr "inner abort")) :=
  ⟨.terminated (.inr "inner abort"), rfl, rfl⟩

def afterInner : AnchorAccount.World (List Nat) × AccountsState Nat :=
  ((terminalBefore.1.1, [51]), ⟨[], 3, [payloadSampleOwner]⟩)

/-- This allocator accepts only the payload and complete successor state
actually produced by the inner call, then terminates. -/
def exhaustedCollection : AccountCollectionTypes :=
  { terminalCollection with
    inner := Callback.ofFunction fun _ _ => .returned (.ok 9) afterInner
    newBox := fun before value outcome =>
      before = afterInner ∧ value = 9 ∧ outcome = .terminated "allocation abort" }

theorem box_allocation_terminal_after_inner_effects :
    collectionBoxedRun exhaustedCollection terminalBefore collectionArgs
      (.terminated (.inr "allocation abort")) := by
  refine ⟨.returned (.ok (9 : Nat)) afterInner, rfl, .terminated (.inr "allocation abort"), ?_, rfl⟩
  exact ⟨.terminated (.inr "allocation abort"),
    ⟨.terminated "allocation abort", ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩

theorem option_marker_consumes_one (types : AccountCollectionTypes) (allowMissing : Bool)
    (before : AnchorAccount.World types.Aux) (args : AccountsArgs)
    (tail : List AccountReference) (bumps : types.Bumps) (reallocs : List Solanalib.Runtime.Pubkey)
      :
    collectionOptionRun allowMissing types
      (before, ⟨⟨19, { AccountInfo.sampleInfo with key := args.programId }⟩ :: tail, bumps,
        reallocs⟩)
      args (.returned (.ok none) (before, ⟨tail, bumps, reallocs⟩)) := by
  simp only [collectionOptionRun, optionAccounts, ↓reduceIte]
  rfl

theorem option_empty_feature_preserves_slice (types : AccountCollectionTypes)
    (before : AnchorAccount.World types.Aux) (args : AccountsArgs)
    (bumps : types.Bumps) (reallocs : List Solanalib.Runtime.Pubkey) :
    collectionOptionRun true types (before, ⟨[], bumps, reallocs⟩) args
      (.returned (.ok none) (before, ⟨[], bumps, reallocs⟩)) := rfl

theorem option_absent_feature_calls_error_factory {types : AccountCollectionTypes}
    {before after : AnchorAccount.World types.Aux} {args : AccountsArgs}
    {bumps : types.Bumps} {reallocs : List Solanalib.Runtime.Pubkey} {error : types.toBase.Error}
    (built : code types.toBase .notEnoughKeys before () (.returned error after)) :
    collectionOptionRun false types (before, ⟨[], bumps, reallocs⟩) args
      (.returned (.error error) (after, ⟨[], bumps, reallocs⟩)) :=
  ⟨.returned error (after, ⟨[], bumps, reallocs⟩), ⟨.returned error after, built, rfl⟩, rfl⟩

def noneClose : OptionCloseTypes where
  toBase := (AnchorLifecycleValidation.validation .boxed).toBase
  Payload := Nat
  rc := (AnchorLifecycleValidation.validation .boxed).rc
  close := fun _ _ _ => False

theorem none_close_drops_moved_destination :
    optionClose noneClose AnchorLifecycleValidation.before (none, AccountInfo.sampleInfo)
      (.returned (.ok ()) (AccountInfo.sampleState, [400, 401])) := by
  exact ⟨.returned () (AccountInfo.sampleState, [400, 401]),
    ⟨_, ⟨_, ⟨.returned () (AccountInfo.sampleState, [400]), rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

def liveBox : DispatchTypes where
  State := Nat
  Payload := Nat
  BoxResource := Unit
  Arg := Solanalib.Runtime.Pubkey
  Error := Empty
  Unwind := Empty
  Terminal := Empty
  current := fun state _ => some state
  call := Callback.ofFunction fun state (payload, _) => .returned (.ok ()) (state + payload)

theorem box_dispatch_reads_current_payload :
    boxedDispatch liveBox (7 : Nat) ((), .zero) (.returned (.ok ()) (14 : Nat)) := ⟨(7 : Nat), rfl,
      rfl⟩

theorem box_dispatch_rejects_stale_payload :
    ¬ boxedDispatch liveBox (7 : Nat) ((), .zero) (.returned (.ok ()) (9 : Nat)) := by
  rintro ⟨value, current, called⟩
  cases current
  cases called

theorem default_exit_leaves_state :
    defaultExitRun ⟨Nat, Nat, Empty⟩ (7 : Nat) ((9 : Nat), .zero) (.returned (.ok ()) (7 : Nat)) :=
      rfl

end SolanalibTest.Specs.Core.AnchorLifecycleCollections
