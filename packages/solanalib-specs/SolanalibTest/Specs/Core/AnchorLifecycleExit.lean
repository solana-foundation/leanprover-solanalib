/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleProfiles
public import Solanalib.Specs.Core.AnchorLifecycleExitFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleExit

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

inductive Mode where
  | success
  | error
  | unwind
  deriving DecidableEq

def serializer (mode : Mode) : ExitTypes where
  toBase := Base.ofConstructor AnchorOwnedSamples.constructor
  Payload := Nat
  ownerAt := fun _ _ => payloadSampleOwner
  owner := Callback.ofFunction fun state _ => .returned payloadSampleOwner state
  serialize := Callback.ofFunction fun state args =>
    let after := ((Borrow.write state.1 args.guard (.data [99, 20, 30])).2, state.2)
    match mode with
    | .success => .returned (.ok ()) after
    | .error => .returned (.error ⟨(⟨0⟩ : AnchorErrorOwned.Reference.BoxId)⟩) after
    | .unwind => .unwound "partial serializer" after
  rc := sampleRc

/-- The error of the serializer is an already owned, represented program-error Box.
It moves out on error; its identity is not reconstructed from a status. -/
def heap : AnchorErrorOwned.Reference.State :=
  ⟨[], [some (.program ⟨.invalidAccountData, none, none⟩)], 6, []⟩

def before : AnchorAccount.World AnchorErrorOwned.Reference.State := (AccountInfo.sampleState, heap)
def during : AccountInfo.State := (AccountInfo.tryBorrowMutData AccountInfo.sampleState
  AccountInfo.sampleArgs).2
def written : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [99, 20, 30], AccountInfo.sampleProfile.policy⟩],
    [some ⟨⟨1⟩, .exclusive, 0, .whole⟩]⟩
def after : AnchorAccount.World AnchorErrorOwned.Reference.State :=
  (⟨written.cells, [none]⟩, heap)

def args : ExitArgs .account Nat :=
  ⟨AccountInfo.sampleProfile, ⟨7, AccountInfo.sampleInfo⟩, payloadSampleOwner⟩

def result (mode : Mode) (state : AnchorAccount.World AnchorErrorOwned.Reference.State) :
    Outcome (AnchorAccount.World AnchorErrorOwned.Reference.State) (Except (serializer
      mode).toBase.Error Unit)
      (serializer mode).toBase.Unw (serializer mode).toBase.Term :=
  match mode with
  | .success => .returned (.ok ()) state
  | .error => .returned (.error ⟨(⟨0⟩ : AnchorErrorOwned.Reference.BoxId)⟩) state
  | .unwind => .unwound (.inr "partial serializer") state

theorem serializer_admitted (mode : Mode) :
    SerializeReady (serializer mode) before args.wrapper args.profile := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard state acquired view bytes current
  change (Except.ok (⟨0, 0⟩ : Borrow.Guard), during) = (.ok guard, state) at acquired
  cases acquired
  have valid : during.Valid := AccountInfo.GuardCallback.tryBorrow_valid
    AccountInfo.sample_valid.2.1 _ _
  have frame : Borrow.CallbackFrame mutableDataFootprint during written ⟨0, 0⟩ :=
    mutable_write_frame valid (guard := ⟨0, 0⟩) (bytes := [99, 20, 30]) (slot := ⟨⟨1⟩, .exclusive,
      0, .whole⟩) rfl rfl
      (old := [10, 20, 30]) (policy := AccountInfo.sampleProfile.policy) rfl rfl
  rintro outcome ⟨raw, called, widened⟩
  cases mode <;> cases called <;> cases widened <;> exact frame

theorem exit_admitted (mode : Mode) : ExitReady .account false (serializer mode) before args := by
  rintro expected checked ⟨_, called, widened⟩ equal
  cases called; cases widened
  refine ⟨?_, ?_⟩
  · intro impossible
    exact False.elim (payloadSampleOwner_ne impossible)
  intro state openAccount
  simp only [isClosed, serializer, payloadSampleOwner_ne, ↓reduceIte] at openAccount
  cases openAccount
  exact serializer_admitted mode

theorem exit_retains_partial_writes (mode : Mode) :
    exit .account false (serializer mode) before args (result mode after) := by
  refine ⟨.returned payloadSampleOwner before, ⟨_, rfl, rfl⟩, ?_⟩
  change exitExpected false (serializer mode) args.wrapper args.profile args.programId
    payloadSampleOwner before () (result mode after)
  simp only [exitExpected, args, ↓reduceIte]
  refine ⟨.returned false before, ?_, ?_⟩
  · simp only [isClosed, serializer, payloadSampleOwner_ne, ↓reduceIte]
  · refine ⟨result mode (written, heap), ?_, ?_⟩
    · cases mode <;> exact ⟨_, rfl, rfl⟩
    · cases mode <;> rfl

theorem data_and_guard_after_error :
    (after.1.lookupCell AccountInfo.sampleInfo.data).map Borrow.Cell.value = some (.data [99, 20,
      30]) ∧
    after.1.resolve ⟨0, 0⟩ = none ∧
    AnchorErrorOwned.Reference.currentBox after.2 ⟨0⟩ =
      some (.program ⟨.invalidAccountData, none, none⟩) := ⟨rfl, rfl, rfl⟩

theorem interface_exit_uses_saved_owner :
    exit .interfaceAccount false (serializer .success) before
      ⟨AccountInfo.sampleProfile, ⟨⟨(7 : Nat), AccountInfo.sampleInfo⟩, .zero⟩, .zero⟩
      (.returned (.ok ()) after) := by
  change exitExpected false (serializer .success) ⟨(7 : Nat), AccountInfo.sampleInfo⟩
    AccountInfo.sampleProfile .zero .zero before () (.returned (.ok ()) after)
  simp only [exitExpected, ↓reduceIte]
  refine ⟨.returned false before, ?_, ?_⟩
  · simp only [isClosed, serializer, payloadSampleOwner_ne, ↓reduceIte]
  · exact ⟨.returned (.ok ()) (written, heap), ⟨_, rfl, rfl⟩, rfl⟩

end SolanalibTest.Specs.Core.AnchorLifecycleExit
