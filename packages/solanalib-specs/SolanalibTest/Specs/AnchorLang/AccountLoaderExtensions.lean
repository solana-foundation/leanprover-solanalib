/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.account_loader
public import Solanalib.Specs.AnchorLang.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core

def stateWith (bytes : Solanalib.Runtime.Bytes) : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data bytes, AccountInfo.sampleProfile.policy⟩], []⟩

def acquire (bytes : Solanalib.Runtime.Bytes) : AccountInfo.State :=
  (AccountInfo.tryBorrow .exclusive AccountInfo.sampleInfo.data (stateWith bytes)).2

def release (bytes : Solanalib.Runtime.Bytes) : AccountInfo.State := (Borrow.release (acquire
  bytes) ⟨0, 0⟩).2

theorem init_preserves_zero_discriminator :
    AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith [0, 20, 30])
      AnchorLoaderInit.sampleArgs =
      some (.returned (.ok ⟨⟨0, 1⟩⟩)
        (Borrow.transfer (acquire [0, 20, 30]) ⟨0, 0⟩ (.bytesRange 1 2)).2) := rfl

theorem init_mapped_view_is_current :
    Borrow.deref AccountInfo.projectBytes
      (Borrow.transfer (acquire [0, 20, 30]) ⟨0, 0⟩ (.bytesRange 1 2)).2 ⟨0, 1⟩ =
        (.ok (.ok [20, 30]), (Borrow.transfer (acquire [0, 20, 30]) ⟨0, 0⟩ (.bytesRange 1 2)).2) :=
          rfl

theorem init_short_prefix_panics_and_releases :
    AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith []) AnchorLoaderInit.sampleArgs =
      some (.unwound .sliceBounds (release [])) := rfl

theorem init_payload_bounds_panics_and_releases :
    AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith [0, 20]) AnchorLoaderInit.sampleArgs =
      some (.unwound .sliceBounds (release [0, 20])) := rfl

theorem init_short_prefix_abort_has_no_state :
    AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith [])
      { AnchorLoaderInit.sampleArgs with profile := ⟨64, true⟩ } = some (.terminated .sliceBounds)
        := rfl

theorem nonzero_prefix_is_error_not_panic :
    AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith [10, 20, 30])
      AnchorLoaderInit.sampleArgs =
      some (.returned (.error AnchorLoaderInit.alreadySet) (release [10, 20, 30])) := rfl

theorem writable_rejection_precedes_conflict :
    AnchorLoaderInit.run AnchorLoaderInit.sample (acquire [0, 20, 30])
      { AnchorLoaderInit.sampleArgs with loader := ⟨AccountInfo.sampleInfo⟩ } =
        some (.returned (.error (AnchorAccount.error .notMutable)) (acquire [0, 20, 30])) := rfl

theorem init_does_not_check_owner :
    AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith [0, 20, 30])
      { AnchorLoaderInit.sampleArgs with loader :=
          ⟨{ AnchorLoaderInit.sampleArgs.loader.info with ownerRef := ⟨1234⟩ }⟩ } =
        AnchorLoaderInit.run AnchorLoaderInit.sample (stateWith [0, 20, 30])
          AnchorLoaderInit.sampleArgs := rfl

theorem init_remains_possible_until_exit :
    AnchorLoaderInit.run AnchorLoaderInit.sample
      (Borrow.release (Borrow.transfer (acquire [0, 20, 30]) ⟨0, 0⟩ (.bytesRange 1 2)).2 ⟨0, 1⟩).2
      AnchorLoaderInit.sampleArgs =
        some (.returned (.ok ⟨⟨1, 1⟩⟩)
          ⟨(stateWith [0, 20, 30]).cells,
            [none, some ⟨⟨1⟩, .exclusive, 1, .bytesRange 1 2⟩]⟩) := rfl

theorem clone_preserves_record_and_cell_identity :
    AnchorLoader.clone AnchorLoader.sampleValue = AnchorLoader.sampleValue ∧
      AnchorLoader.asRef (AnchorLoader.clone AnchorLoader.sampleValue) =
        AnchorLoader.sampleReference :=
  ⟨rfl, rfl⟩

theorem equal_metadata_does_not_identify_records :
    AnchorLoader.asRef (⟨⟨8, AccountInfo.sampleInfo⟩⟩ : AnchorLoader.Value Nat) ≠
      AnchorLoader.asRef AnchorLoader.sampleValue := by decide

theorem unchecked_ignores_empty_missing_data :
    AnchorLoader.unchecked AnchorLoader.constructorSample
      (Borrow.State.empty, AnchorOwnedSamples.auxiliary) AnchorLoader.uncheckedSampleArgs
      (.returned (.ok AnchorLoader.sampleValue) (Borrow.State.empty, AnchorOwnedSamples.auxiliary))
        :=
  AnchorLoader.unchecked_matching rfl rfl

theorem exit_writer_preserves_partial_bytes :
    AnchorLoaderExit.writeDiscriminator
      { AnchorLoaderExit.sample with discriminator := [10, 11, 12, 13] }
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩
      (acquire [0, 0], AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ [0, 0]
      (.unwound (.inl .writeZero)
        (⟨(stateWith [10, 11]).cells, [none]⟩, AnchorOwnedSamples.auxiliary)) := by
  apply AnchorLoaderExit.write_short_unwound rfl (by decide) ?_ rfl
  exact ⟨.returned Borsh.writeZeroError _, rfl,
    .unwound (.inl .writeZero) _, rfl, .returned () _, rfl, rfl⟩

theorem exit_writer_abort_has_no_state :
    AnchorLoaderExit.writeDiscriminator
      { AnchorLoaderExit.sample with discriminator := [10, 11, 12, 13] }
      ⟨⟨64, true⟩, AnchorLoader.sampleValue, .zero⟩
      (acquire [0, 0], AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ [0, 0]
      (.terminated (.inl .writeZero)) := by
  apply AnchorLoaderExit.write_short_terminal rfl (by decide) ?_
  exact ⟨.returned Borsh.writeZeroError _, rfl, .terminated (.inl .writeZero), rfl, rfl⟩

theorem exit_write_occurs_after_initialization :
    AnchorLoaderExit.writeDiscriminator AnchorLoaderExit.sample AnchorLoaderExit.sampleArgs
      (acquire [0, 20, 30], AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ [0, 20, 30]
      (.returned (.ok ()) (⟨(stateWith [10, 20, 30]).cells, [none]⟩, AnchorOwnedSamples.auxiliary))
        := rfl

theorem old_guard_is_consumed_by_mapping :
    (Borrow.transfer (acquire [0, 20, 30]) ⟨0, 0⟩ (.bytesRange 1 2)).2.resolve ⟨0, 0⟩ = none := rfl

/-- The primary owned error path allocates the exact name/message/Box while
holding its exclusive guard, then releases that same guard before returning. -/
def alreadySetResult := AnchorErrorOwned.Reference.buildCodeResult
  AnchorOwnedSamples.auxiliary AnchorLoaderInitOwned.alreadySet

theorem owned_init_already_set_releases :
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_init_run
      AnchorLoaderInitOwned.sample (stateWith [10, 20, 30], AnchorOwnedSamples.auxiliary)
      AnchorLoaderInit.sampleArgs
      (.returned (.error alreadySetResult.1) (release [10, 20, 30], alreadySetResult.2)) := by
  refine ⟨.returned (.error alreadySetResult.1) (acquire [10, 20, 30], alreadySetResult.2), ?_, rfl⟩
  refine ⟨.returned alreadySetResult.1 (acquire [10, 20, 30], alreadySetResult.2), ?_, rfl⟩
  refine ⟨.returned alreadySetResult.1 (acquire [10, 20, 30], alreadySetResult.2), ?_, rfl⟩
  exact ⟨.returned ⟨0⟩ (acquire [10, 20, 30],
    (AnchorErrorOwned.Reference.stringResult false AnchorOwnedSamples.auxiliary
      AnchorLoaderInitOwned.alreadySet.name).2),
    ⟨.returned ⟨0⟩ _, rfl, rfl⟩,
    .returned ⟨1⟩ (acquire [10, 20, 30],
      (AnchorErrorOwned.Reference.stringResult true
        (AnchorErrorOwned.Reference.stringResult false AnchorOwnedSamples.auxiliary
          AnchorLoaderInitOwned.alreadySet.name).2
        AnchorLoaderInitOwned.alreadySet.message).2),
    ⟨.returned ⟨1⟩ _, rfl, rfl⟩,
    .returned ⟨0⟩ (acquire [10, 20, 30], alreadySetResult.2),
    ⟨.returned ⟨0⟩ _, rfl, rfl⟩, rfl⟩

theorem owned_init_error_payload_and_cleanup :
    AnchorErrorOwned.current (AnchorLoaderInitOwned.sample.errors)
      (release [10, 20, 30], alreadySetResult.2) alreadySetResult.1 = some
        AnchorLoaderInit.alreadySet ∧
      (release [10, 20, 30]).resolve ⟨0, 0⟩ = none ∧ alreadySetResult.2.remaining = 3 :=
  ⟨rfl, rfl, rfl⟩

theorem exit_closed_skips_writer :
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.exit_run
      AnchorLoaderExit.sample
      (stateWith [], AnchorOwnedSamples.auxiliary) AnchorLoaderExit.sampleArgs
      (.returned (.ok ())
        (⟨(stateWith []).cells, [none]⟩, AnchorOwnedSamples.auxiliary)) := by
  refine ⟨.returned .zero _, ⟨.returned .zero _, ⟨.returned .zero _, rfl, rfl⟩, rfl⟩, ?_⟩
  refine ⟨.returned true _, ?_, rfl⟩
  exact ⟨.returned true _, ⟨.returned 0 _, rfl, rfl⟩, rfl⟩

theorem exit_closed_read_conflict_is_panic :
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.exit_run
      AnchorLoaderExit.sample
      (acquire [], AnchorOwnedSamples.auxiliary) AnchorLoaderExit.sampleArgs
      (.unwound (.inl .borrowFailed) (acquire [], AnchorOwnedSamples.auxiliary)) := by
  refine ⟨.returned .zero _, ⟨.returned .zero _, ⟨.returned .zero _, rfl, rfl⟩, rfl⟩, ?_⟩
  refine ⟨.unwound (.inl .borrowFailed) _, ?_, rfl⟩
  exact ⟨.unwound (.inl .borrowFailed) _, ⟨.unwound (.inl .borrowFailed) _, rfl, rfl⟩, rfl⟩

def ownerUnwinds : AnchorLoader.ConstructorTypes :=
  { AnchorLoader.constructorSample with
    owner := Callback.ofFunction fun before _ => .unwound "owner" before }

def unwindingAccounts : AnchorLoader.AccountsTypes := ⟨ownerUnwinds, Nat, [10]⟩
def unwindingAccountsBefore : AnchorLoader.AccountsState unwindingAccounts :=
  ⟨(AccountInfo.sampleState, AnchorOwnedSamples.auxiliary),
    [AnchorLoader.sampleReference, ⟨8, AccountInfo.sampleInfo⟩], (17 : Nat), [.zero]⟩

theorem try_accounts_pop_before_owner_unwind :
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_accounts_run
      unwindingAccounts
      unwindingAccountsBefore AnchorLoader.accountsSampleArgs
      (.unwound (.inr "owner") { unwindingAccountsBefore with remaining := [⟨8,
        AccountInfo.sampleInfo⟩] }) := by
  refine AnchorLoader.tryAccounts_retain (types := unwindingAccounts)
    (before := unwindingAccountsBefore) (args := AnchorLoader.accountsSampleArgs)
    (account := AnchorLoader.sampleReference) (rest := [⟨8, AccountInfo.sampleInfo⟩])
    (produced := .unwound (.inr "owner") unwindingAccountsBefore.world) rfl ?_
  exact ⟨.unwound (.inr "owner") _,
    ⟨.unwound (.inr "owner") _, ⟨.unwound "owner" _, rfl, rfl⟩, rfl⟩, rfl⟩

namespace WriteZeroEffects

open AnchorErrorOwned.Reference

/-- A nontrivial interpretation of the diagnostic owner and unwind state.
Its String token is an abstract owner, not a native allocation-count claim. -/
def make (before : State) (error : Borsh.IoError) :
    Outcome State StringId Empty Failure :=
  let result := stringResult false before error.message
  .returned result.1 result.2

def format (before : State) (args : Bool × StringId) :
    Outcome State Empty (AnchorLoaderExit.Unwind AnchorLoaderExit.sample)
      (AnchorLoaderExit.Terminal AnchorLoaderExit.sample) → Prop :=
  fun outcome => currentString before args.2 = some Borsh.writeZeroError.message ∧
    outcome = if args.1 then .terminated (.inl .writeZero)
      else .unwound (.inl .writeZero) (stringResult true before "unwrap panic payload").2

def drop (before : State) (error : StringId) :
    Outcome State Unit (AnchorLoaderExit.Unwind AnchorLoaderExit.sample)
      (AnchorLoaderExit.Terminal AnchorLoaderExit.sample) → Prop :=
  fun outcome => ∃ text, currentString before error = some text ∧
    outcome = .returned () { before with
      strings := before.strings.set error.index none
      events := before.events ++ [.dropString error text] }

def types : AnchorLoaderExit.Types :=
  { AnchorLoaderExit.sample with
    discriminator := [10, 11, 12, 13]
    IoError := StringId
    makeError := Callback.ofFunction make
    unwrapError := format
    dropError := drop }

def args : AnchorLoaderExit.Args types :=
  ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩
def before : AnchorAccount.World types.Aux := (acquire [0, 0], AnchorOwnedSamples.auxiliary)
def written : AccountInfo.State :=
  (Borrow.write before.1 ⟨0, 0⟩ (.data [10, 11])).2

def made : StringId × State := stringResult false before.2 Borsh.writeZeroError.message
def formatted : StringId × State := stringResult true made.2 "unwrap panic payload"
def dropped : State :=
  { formatted.2 with
    strings := formatted.2.strings.set made.1.index none
    events := formatted.2.events ++ [.dropString made.1 Borsh.writeZeroError.message] }

theorem reached_diagnostic_trace :
    AnchorLoaderExit.writeZero types before.2 false (.unwound (.inl .writeZero) dropped) := by
  refine ⟨.returned made.1 made.2, rfl,
    .unwound (.inl .writeZero) formatted.2, ⟨rfl, rfl⟩, .returned () dropped, ?_, rfl⟩
  exact ⟨Borsh.writeZeroError.message, rfl, rfl⟩

/-- Construction, borrowed formatting and destruction use the same error
identity while the exclusive guard and partial bytes of the caller remain current. -/
theorem guard_and_owner_survive_until_error_drop :
    written.resolve ⟨0, 0⟩ = some ⟨⟨1⟩, .exclusive, 0, .whole⟩ ∧
    Borrow.current written ⟨0, 0⟩ = .ok (.whole, .data [10, 11]) ∧
    (Owned.Focus.snd.lift types.makeError) (written, before.2) Borsh.writeZeroError
      (.returned made.1 (written, made.2)) ∧
    (Owned.Focus.snd.lift types.unwrapError) (written, made.2) (false, made.1)
      (.unwound (.inl .writeZero) (written, formatted.2)) ∧
    (Owned.Focus.snd.lift types.dropError) (written, formatted.2) made.1
      (.returned () (written, dropped)) ∧
    currentString made.2 made.1 = some Borsh.writeZeroError.message ∧
    currentString formatted.2 made.1 = some Borsh.writeZeroError.message ∧
    currentString dropped made.1 = none := by
  refine ⟨rfl, rfl, ⟨.returned made.1 made.2, rfl, rfl⟩,
    ⟨.unwound (.inl .writeZero) formatted.2, ⟨rfl, rfl⟩, rfl⟩,
    ⟨.returned () dropped, ?_, rfl⟩, rfl, rfl, rfl⟩
  exact ⟨Borsh.writeZeroError.message, rfl, rfl⟩

theorem final_unwind_keeps_effects_and_releases_guard :
    AnchorLoaderExit.writeDiscriminator types args before ⟨0, 0⟩ [0, 0]
      (.unwound (.inl .writeZero) ((Borrow.release written ⟨0, 0⟩).2, dropped)) ∧
    (Borrow.release written ⟨0, 0⟩).2.resolve ⟨0, 0⟩ = none ∧
    dropped.events = [.name ⟨0⟩ Borsh.writeZeroError.message,
      .message ⟨1⟩ "unwrap panic payload", .dropString ⟨0⟩ Borsh.writeZeroError.message] ∧
    dropped ≠ before.2 := by
  refine ⟨AnchorLoaderExit.write_short_unwound rfl (by decide) reached_diagnostic_trace rfl,
    rfl, rfl, ?_⟩
  intro unchanged
  have lengthEq : (3 : Nat) = 0 :=
    congrArg (fun state : State => state.events.length) unchanged
  cases lengthEq

theorem diagnostic_unwind_exact
    {outcome : Outcome State Empty (AnchorLoaderExit.Unwind types) (AnchorLoaderExit.Terminal
      types)}
    (called : AnchorLoaderExit.writeZero types before.2 false outcome) :
    outcome = .unwound (.inl .writeZero) dropped := by
  obtain ⟨created, madeEq, continued⟩ := called
  change make before.2 Borsh.writeZeroError = created at madeEq
  cases madeEq
  obtain ⟨pending, ⟨_, panicEq⟩, cleaned⟩ := continued
  cases panicEq
  obtain ⟨finished, ⟨text, current, dropEq⟩, finalEq⟩ := cleaned
  change some Borsh.writeZeroError.message = some text at current
  have textEq := Option.some.inj current
  cases textEq
  cases dropEq
  exact finalEq

theorem old_auxiliary_state_is_rejected :
    ¬ AnchorLoaderExit.writeZero types before.2 false (.unwound (.inl .writeZero) before.2) := by
  intro called
  have stateEq := (Outcome.unwound.inj (diagnostic_unwind_exact called)).2
  exact final_unwind_keeps_effects_and_releases_guard.2.2.2 stateEq.symm

/-- A callback has no finite exit unless the relation supplies one. -/
def noConstructor : AnchorLoaderExit.Types :=
  { types with makeError := fun _ _ _ => False }

theorem absent_constructor_has_no_diagnostic_exit
    (outcome : Outcome State Empty (AnchorLoaderExit.Unwind noConstructor)
      (AnchorLoaderExit.Terminal noConstructor)) :
    ¬ AnchorLoaderExit.writeZero noConstructor before.2 false outcome := by
  rintro ⟨_, impossible, _⟩
  exact impossible

def noUnwrap : AnchorLoaderExit.Types := { types with unwrapError := fun _ _ _ => False }

theorem absent_unwrap_has_no_diagnostic_exit
    (outcome : Outcome State Empty (AnchorLoaderExit.Unwind noUnwrap)
      (AnchorLoaderExit.Terminal noUnwrap)) :
    ¬ AnchorLoaderExit.writeZero noUnwrap before.2 false outcome := by
  rintro ⟨created, madeEq, continued⟩
  change make before.2 Borsh.writeZeroError = created at madeEq
  cases madeEq
  obtain ⟨_, impossible, _⟩ := continued
  exact impossible

def noDrop : AnchorLoaderExit.Types := { types with dropError := fun _ _ _ => False }

theorem absent_drop_does_not_finish_unwind
    (outcome : Outcome State Empty (AnchorLoaderExit.Unwind noDrop)
      (AnchorLoaderExit.Terminal noDrop)) :
    ¬ AnchorLoaderExit.writeZero noDrop before.2 false outcome := by
  rintro ⟨created, madeEq, continued⟩
  change make before.2 Borsh.writeZeroError = created at madeEq
  cases madeEq
  obtain ⟨pending, ⟨_, panicEq⟩, cleaned⟩ := continued
  cases panicEq
  obtain ⟨_, impossible, _⟩ := cleaned
  exact impossible

/-- Panic-abort does not run a later error destructor or release a guard. -/
theorem terminal_unwrap_does_not_require_drop :
    AnchorLoaderExit.writeDiscriminator noDrop ⟨⟨64, true⟩, AnchorLoader.sampleValue, .zero⟩
      before ⟨0, 0⟩ [0, 0] (.terminated (.inl .writeZero)) := by
  apply AnchorLoaderExit.write_short_terminal rfl (by decide) ?_
  exact ⟨.returned made.1 made.2, rfl, .terminated (.inl .writeZero), ⟨rfl, rfl⟩, rfl⟩

def dropUnwindState : State := { formatted.2 with remaining := 19 }
/-- These are generic dependency outcomes, not a claim that a concrete
String destructor or GlobalAlloc implementation may legally unwind. -/
def secondUnwind : AnchorLoaderExit.Types :=
  { types with
    dropError := Callback.ofFunction (fun _ _ => .unwound (.inr "error drop") dropUnwindState)
    doubleUnwind := fun state first second terminal => state = dropUnwindState ∧
      first = .inl .writeZero ∧ second = .inr "error drop" ∧ terminal = .inl .writeZero }

theorem destructor_unwind_uses_actual_state_and_two_reasons :
    AnchorLoaderExit.writeDiscriminator secondUnwind
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩ before ⟨0, 0⟩ [0, 0]
      (.terminated (.inl .writeZero)) := by
  apply AnchorLoaderExit.write_short_terminal rfl (by decide) ?_
  exact ⟨.returned made.1 made.2, rfl,
    .unwound (.inl .writeZero) formatted.2, ⟨rfl, rfl⟩,
    .unwound (.inr "error drop") dropUnwindState, rfl,
    .inl .writeZero, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The successful local writer still works when every diagnostic relation
is empty; no new diagnostic readiness is imposed on that branch. -/
def noDiagnostics : AnchorLoaderExit.Types :=
  { AnchorLoaderExit.sample with
    makeError := fun _ _ _ => False
    unwrapError := fun _ _ _ => False
    dropError := fun _ _ _ => False
    doubleUnwind := fun _ _ _ _ => False }

theorem nonshort_needs_no_diagnostic_outcome :
    AnchorLoaderExit.writeDiscriminator noDiagnostics
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩
      (acquire [0, 20, 30], AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ [0, 20, 30]
      (.returned (.ok ()) (⟨(stateWith [10, 20, 30]).cells, [none]⟩, AnchorOwnedSamples.auxiliary))
        := rfl

theorem borrow_error_keeps_the_original_dependency :
    AnchorLoaderExit.persist noDiagnostics (acquire [0, 20, 30], AnchorOwnedSamples.auxiliary)
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩ =
    AnchorLoaderExit.persist AnchorLoaderExit.sample (acquire [0, 20, 30],
      AnchorOwnedSamples.auxiliary)
      AnchorLoaderExit.sampleArgs := by
  have blocked :
      AccountInfo.tryBorrow .exclusive AccountInfo.sampleInfo.data (acquire [0, 20, 30]) =
        (.error .accountBorrowFailed, acquire [0, 20, 30]) := rfl
  funext outcome
  simp only [AnchorLoaderExit.persist, AnchorLoaderExit.sampleArgs,
    AnchorLoader.sampleValue, AnchorLoader.sampleReference, blocked,
    AnchorLoaderExit.lift]
  apply propext
  constructor
  all_goals
    rintro ⟨produced, observed, widened⟩
    refine ⟨produced, observed, ?_⟩
    cases produced with
    | returned _ _ => exact widened
    | unwound reason _ => cases reason <;> exact widened
    | terminated reason => cases reason <;> exact widened

theorem closed_skip_needs_no_diagnostic_outcome :
    AnchorLoaderExit.run noDiagnostics (stateWith [], AnchorOwnedSamples.auxiliary)
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩ (.returned (.ok ())
        (⟨(stateWith []).cells, [none]⟩, AnchorOwnedSamples.auxiliary)) := by
  refine ⟨.returned .zero _, ⟨.returned .zero _, ⟨.returned .zero _, rfl, rfl⟩, rfl⟩, ?_⟩
  refine ⟨.returned true _, ?_, rfl⟩
  exact ⟨.returned true _, ⟨.returned 0 _, rfl, rfl⟩, rfl⟩

/-- These terminal labels exercise generic dependency composition. They do
not admit source error-construction allocation failure or claim that a
concrete standard-library destructor may unwind. -/
def constructorTerminal : AnchorLoaderExit.Types :=
  { types with
    makeError := Callback.ofFunction (fun _ _ => .terminated (.allocation .name))
    unwrapError := fun _ _ _ => False
    dropError := fun _ _ _ => False
    doubleUnwind := fun _ _ _ _ => False }

theorem constructor_terminal_needs_no_later_callback :
    AnchorLoaderExit.writeDiscriminator constructorTerminal
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩ before ⟨0, 0⟩ [0, 0]
      (.terminated (.inr (.allocation .name))) := by
  apply AnchorLoaderExit.write_short_terminal rfl (by decide) ?_
  exact ⟨.terminated (.allocation .name), rfl, rfl⟩

def dropTerminal : AnchorLoaderExit.Types :=
  { types with
    dropError := Callback.ofFunction (fun _ _ => .terminated (.inr (.allocation .box)))
    doubleUnwind := fun _ _ _ _ => False }

theorem error_drop_terminal_needs_no_double_unwind :
    AnchorLoaderExit.writeDiscriminator dropTerminal
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩ before ⟨0, 0⟩ [0, 0]
      (.terminated (.inr (.allocation .box))) := by
  apply AnchorLoaderExit.write_short_terminal rfl (by decide) ?_
  exact ⟨.returned made.1 made.2, rfl,
    .unwound (.inl .writeZero) formatted.2, ⟨rfl, rfl⟩,
    .terminated (.inr (.allocation .box)), rfl, rfl⟩

/-- A formatting dependency can supply its own unwind reason and state;
the same error is still dropped before the guard of the caller is released. -/
def formattingUnwind : AnchorLoaderExit.Types :=
  { types with
    unwrapError := Callback.ofFunction (fun _ _ => .unwound (.inr "formatting") formatted.2) }

theorem formatting_unwind_keeps_its_reason_and_cleanup_state :
    AnchorLoaderExit.writeDiscriminator formattingUnwind
      ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, .zero⟩ before ⟨0, 0⟩ [0, 0]
      (.unwound (.inr "formatting") ((Borrow.release written ⟨0, 0⟩).2, dropped)) := by
  apply AnchorLoaderExit.write_short_unwound rfl (by decide) ?_ rfl
  exact ⟨.returned made.1 made.2, rfl,
    .unwound (.inr "formatting") formatted.2, rfl,
    .returned () dropped, ⟨Borsh.writeZeroError.message, rfl, rfl⟩, rfl⟩

end WriteZeroEffects

end SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions

namespace SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions.StableProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.AnchorLang.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_loader_AccountLoader_as_ref,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("core::convert::AsRef::as_ref",
        "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
          core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref")]),
    (.accounts_account_loader_AccountLoader_try_accounts,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("anchor_lang::Accounts::try_accounts",
        "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
          anchor_lang::Accounts<'info, B>>::try_accounts")]),
    (.accounts_account_loader_AccountLoader_try_from_unchecked,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("anchor_lang::accounts::account_loader::AccountLoader::<'info, \
        T>::try_from_unchecked",
        "anchor_lang::accounts::account_loader::AccountLoader::<'info, \
          T>::try_from_unchecked")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"anchor-lang", build.version, item, implementation⟩))

def members : List Key := [.accounts_account_loader_AccountLoader_as_ref,
  .accounts_account_loader_AccountLoader_try_accounts,
  .accounts_account_loader_AccountLoader_try_from_unchecked]

theorem every_member_has_a_literal_case :
    members.length = 3 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.1.1",
      "1.1.2",
      "1.2.0", "1.2.1", "1.2.2"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.32.4", "1.0.4", "1.9.99+fixture"].all (fun version => fixtures.all (fun (key, build,
      expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.31.99", "0.33.0", "2.0.0", "1.2.0-rc.1"].all (fun version => fixtures.all (fun (key, build,
      _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "1.0.0", "1.0.1",
          "1.0.2", "1.0.3", "1.1.1", "1.1.2", "1.2.0", "1.2.1", "1.2.2"] ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩, ⟨"1.0.0", "2.0.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions.StableProfiles

namespace SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions.InitializationExitProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.AnchorLang.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.accounts_account_loader_AccountLoader_exit,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("anchor_lang::AccountsExit::exit",
        "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
          anchor_lang::AccountsExit<'info>>::exit")]),
    (.accounts_account_loader_AccountLoader_load_init,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry },
      [("anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_init",
        "anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_init")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"anchor-lang", build.version, item, implementation⟩))

def members : List Key := [.accounts_account_loader_AccountLoader_exit,
  .accounts_account_loader_AccountLoader_load_init]

theorem every_member_has_a_literal_case :
    members.length = 2 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.1.1",
      "1.1.2"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.32.4", "1.0.4", "1.1.99+fixture"].all (fun version => fixtures.all (fun (key, build,
      expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.31.99", "0.33.0", "1.2.0", "1.2.1", "1.2.2", "1.1.2-rc.1"].all (fun version => fixtures.all
      (fun (key, build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["0.32.0", "0.32.1", "0.32.2", "0.32.3", "1.0.0", "1.0.1",
          "1.0.2", "1.0.3", "1.1.1", "1.1.2"] ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩, ⟨"1.0.0", "1.2.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions.InitializationExitProfiles

namespace SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions.ObservationProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

def build (version : String) : Versioning.Build :=
  {
    package := "anchor-lang", version := version,
    source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩ }

/-- Matching the partial mathematical observation never manufactures a
source-call identity or replaces the complete owned diagnostic protocol. -/
theorem partial_observation_remains_noncallable :
    Solanalib.Specs.AnchorLang.Capabilities.catalog.sourceCallRegistered
      .accounts_account_loader_AccountLoader_load_init_observation = false ∧
    Solanalib.Specs.AnchorLang.Capabilities.catalog.kind
      .accounts_account_loader_AccountLoader_load_init_observation = .partialModel ∧
    ["0.32.0", "0.32.1", "0.32.3", "0.32.4", "1.0.0", "1.1.2", "1.1.99"].all
      (fun version =>
        !(Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability
          .accounts_account_loader_AccountLoader_load_init_observation).isEmpty &&
        (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability
          .accounts_account_loader_AccountLoader_load_init_observation).all
          (fun profile => profile.matches (build version)) &&
        ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild (build version)).identities
          .accounts_account_loader_AccountLoader_load_init_observation).isEmpty) = true := by
  decide +kernel

/-- The 1.2 size check changes the panic/error order of the observation too.
Check profile matching directly; empty call identities alone would be vacuous. -/
theorem the_observation_also_excludes_the_size_check_change :
    ["1.2.0", "1.2.1", "1.2.2", "1.1.2-rc.1"].all (fun version =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability
        .accounts_account_loader_AccountLoader_load_init_observation).all
        (fun profile => !profile.matches (build version))) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions.ObservationProfiles

namespace SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem self_close_zeroes_after_credit :
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.close_run
      AnchorLoaderClose.sample
      AnchorLifecycle.closeSampleBefore AnchorLoaderClose.sampleArgs
      (.returned (.ok ()) AnchorLifecycle.closeSampleAfter) :=
  AnchorLifecycle.closeSample_wrapper false .legacy .boxed

theorem self_close_releases_all_guards :
    AnchorLifecycle.closeSampleAfter.1.slots = List.replicate 5 none ∧
      AnchorLifecycle.closeSampleAfter.1.lookupCell AccountInfo.sampleInfo.lamports =
        some ⟨.lamports 0, AccountInfo.sampleProfile.policy⟩ ∧
      AnchorLifecycle.closeSampleAfter.1.lookupCell AccountInfo.sampleInfo.data =
        some ⟨.data [], AccountInfo.sampleProfile.policy⟩ := ⟨rfl, rfl, rfl⟩

end SolanalibTest.Specs.AnchorLang.AccountLoaderExtensions

@[expose] public section

namespace SolanalibTest.Specs.AnchorLang.V1_0_2AccountLoaderExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.AnchorLang.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.1.1", "1.1.2", "1.2.0", "1.2.1", "1.2.2", "1.3.\
      0"].all
      (fun version =>
      decide (((selectedProfile "anchor-loader-reviewed").forBuild
        { build0 with version := version }).identities .accounts_account_loader_AccountLoader_clone
          =
          [⟨"anchor-lang", version, "core::clone::Clone::clone",
            "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
              core::clone::Clone>::clone"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "core::clone::Clone::clone",
            "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
              core::clone::Clone>::clone"⟩] : List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build0).identities .accounts_account_loader_AccountLoader_clone)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "anchor-loader-reviewed").applicability
      .accounts_account_loader_AccountLoader_clone).length = 1 ∧
    ["0.999.999", "2.0.0", "1.3.0-rc.1"].all (fun version =>
      (((selectedProfile "anchor-loader-reviewed").forBuild { build0 with version := version
        }).identities
        .accounts_account_loader_AccountLoader_clone).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-lang-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "anchor-loader-reviewed").forBuild build).identities
        .accounts_account_loader_AccountLoader_clone).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "anchor-lang"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := none
  targetFeatures := none
  dependencies := []

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-loader-close-reviewed").forBuild
        { build1 with version := version }).identities .accounts_account_loader_AccountLoader_close
          =
          [⟨"anchor-lang", version, "anchor_lang::AccountsClose::close",
            "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
              anchor_lang::AccountsClose<'info>>::close"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"anchor-lang", "1.0.2", "anchor_lang::AccountsClose::close",
            "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
              anchor_lang::AccountsClose<'info>>::close"⟩] : List Capabilities.RustIdentity).all
                (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild
        build1).identities .accounts_account_loader_AccountLoader_close)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "anchor-loader-close-reviewed").applicability
      .accounts_account_loader_AccountLoader_close).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-loader-close-reviewed").forBuild { build1 with version := version
        }).identities
        .accounts_account_loader_AccountLoader_close).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "anchor-lang-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ } ] : List Versioning.Build).all
      (fun build => (((selectedProfile "anchor-loader-close-reviewed").forBuild build).identities
        .accounts_account_loader_AccountLoader_close).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.V1_0_2AccountLoaderExtensions
