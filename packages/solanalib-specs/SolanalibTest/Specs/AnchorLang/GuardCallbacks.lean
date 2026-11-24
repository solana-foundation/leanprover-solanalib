/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.construct
public import Solanalib.Specs.AnchorLang.loading

@[expose] public section

open Solanalib.Specs

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.GuardCallbacks

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev World := AnchorAccount.World AnchorErrorOwned.Reference.State
abbrev Error := AnchorErrorOwned.Error AnchorErrorOwned.Reference.BoxId
abbrev Decoded := AnchorConstructOwned.Decoded Error Nat
abbrev Decoder := Callback.Run World AnchorAccount.DecodeArgs Decoded String
  AnchorErrorOwned.Reference.Failure

/-- A real modeled error Box is available to the ordinary-error callback. -/
def errorBuilt := AnchorErrorOwned.Reference.fromProgramResult AnchorOwnedSamples.auxiliary
  (.custom 77)
def auxiliary := errorBuilt.2
def before : World := (AccountInfo.sampleState, auxiliary)
def afterInit : World := (AnchorAccount.sampleAfterInit, auxiliary)
def during : World := (AnchorAccount.sampleDataDuring, auxiliary)
def guard : Borrow.Guard := ⟨1, 0⟩
def decodeArgs : AnchorAccount.DecodeArgs := ⟨AccountInfo.sampleInfo, guard, [10, 20, 30]⟩

/-- Vary only the supplied decoder; all error primitives use the shared heap. -/
def interpretation (decoder : Decoder) : AnchorConstructOwned.Types where
  Aux := AnchorErrorOwned.Reference.State
  Payload := Nat
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorOwnedSamples.constructor.errors
  discriminator := [10]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned .zero state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := decoder

theorem owner_ready (decoder : Decoder) (state : World) (args : AccountInfo.Args) :
    AnchorConstructOwned.OwnerCheckReady (interpretation decoder) state args := by
  intro expected after called mismatch
  cases called
  exact False.elim (mismatch rfl)

def mutateHeld (state : World) : World :=
  ((Borrow.replaceCell state.1 AccountInfo.sampleInfo.data (.data [99])).2, state.2)

def mutateOther (state : World) : World :=
  ((Borrow.replaceCell state.1 AccountInfo.sampleInfo.lamports (.lamports 77)).2, state.2)

def release (state : World) : World := ((Borrow.release state.1 guard).2, state.2)

def badReturn : Decoder := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩ (mutateHeld
  state)
def badUnwind : Decoder := Callback.ofFunction fun state _ => .unwound "decode" (mutateHeld state)
def goodReturn : Decoder := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩ (mutateOther
  state)
def goodError : Decoder := Callback.ofFunction fun state _ => .returned ⟨.error errorBuilt.1, []⟩
  (mutateOther state)
def goodUnwind : Decoder := Callback.ofFunction fun state _ => .unwound "decode" (mutateOther state)
def terminal : Decoder := Callback.ofFunction fun _ _ => .terminated (.allocation .name)
def killed : Decoder := Callback.ofFunction fun state args =>
  .returned ⟨.ok 7, []⟩ ((Borrow.release state.1 args.guard).2, state.2)

/-- The counterexample callback has a real finite exit and a live guard even
though its bytes violate the held shared footprint. -/
theorem bad_callback_is_real : badReturn during decodeArgs (.returned ⟨.ok 7, []⟩ (mutateHeld
  during)) ∧
    (mutateHeld during).1.resolve guard = some ⟨AccountInfo.sampleInfo.data, .shared, 0, .whole⟩ :=
  ⟨rfl, rfl⟩

/-- The raw decoder now retains that formerly erased returned outcome, with
the actual mutation and checked cleanup, independently of admission. -/
theorem unframed_return_is_retained : AnchorConstructOwned.decodeAccount (interpretation badReturn)
    afterInit AccountInfo.sampleArgs (.returned (.ok (7 : Nat)) (release (mutateHeld during))) := by
  exact ⟨.returned (.ok (7 : Nat)) (mutateHeld during),
    ⟨.returned ⟨.ok (7 : Nat), []⟩ (mutateHeld during),
      ⟨.returned ⟨.ok (7 : Nat), []⟩ (mutateHeld during), rfl, rfl⟩, rfl⟩, rfl⟩

/-- Unwinding footprint violations with live guards are retained as well;
the state is not rolled back and the original unwind reason survives. -/
theorem unframed_unwind_is_retained : AnchorConstructOwned.decodeAccount (interpretation badUnwind)
    afterInit AccountInfo.sampleArgs (.unwound (.inr "decode") (release (mutateHeld during))) := by
  exact ⟨.unwound (.inr "decode") (mutateHeld during),
    ⟨.unwound (.inr "decode") (mutateHeld during),
      ⟨.unwound "decode" (mutateHeld during), rfl, rfl⟩, rfl⟩, rfl⟩

/-- The finite callback is rejected by the universal frame premise, rather
than erased from the operational relation. -/
theorem bad_callback_not_admitted : ¬ AccountInfo.GuardCallback.Admissible guard badReturn during
  decodeArgs := by
  intro admitted
  have frame := admitted _ bad_callback_is_real.1
  have changed := frame.changes
    ⟨AccountInfo.sampleInfo.data, .shared, 0, .whole⟩
    ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩
    ⟨.data [99], AccountInfo.sampleProfile.policy⟩ rfl rfl rfl
  have impossible : ([99] : _root_.Solanalib.Runtime.Bytes) = [10, 20, 30] := by injection changed
  exact (by decide : ([99] : _root_.Solanalib.Runtime.Bytes) ≠ [10, 20, 30]) impossible

/-- The destructive decoder fails the local cleanup premise.
Its finite outcome remains available in the raw operational relation. -/
theorem decoder_admission_rejects_bad_callback :
    ¬ AnchorConstructOwned.DecodeReady (interpretation badReturn) afterInit AccountInfo.sampleArgs
      := by
  intro ready
  exact bad_callback_not_admitted (ready.2 guard during.1 rfl .whole [10, 20, 30] rfl)

/-- Raw retention extends through the complete primary constructor, so the
old counterexample no longer proves every postcondition vacuously. -/
theorem primary_retains_bad_return :
    AnchorLang.accounts.account.Account.try_from_run (interpretation badReturn)
      before AccountInfo.sampleArgs
      (.returned (.ok (AnchorAccount.Account.mk (7 : Nat) AccountInfo.sampleInfo))
        (release (mutateHeld during))) := by
  refine ⟨.returned (.ok ()) afterInit, rfl, ?_⟩
  refine ⟨.returned (.ok ()) afterInit,
    ⟨.returned .zero afterInit, ⟨.returned .zero afterInit, rfl, rfl⟩, rfl⟩, ?_⟩
  exact ⟨.returned (.ok (7 : Nat)) (release (mutateHeld during)), unframed_return_is_retained, rfl⟩

/-- The complete raw constructor retains the bad return, but the reached-call admission of the exact
registered family rejects this interpretation. -/
theorem raw_family_retains_unframed_return :
    AnchorLang.accounts.account.Account.try_from_run (interpretation badReturn)
      before AccountInfo.sampleArgs
      (.returned (.ok (AnchorAccount.Account.mk (7 : Nat) AccountInfo.sampleInfo))
        (release (mutateHeld during))) ∧
    ¬ (AnchorLang.accounts.account.Account.try_from_contract.contract
      (interpretation badReturn)).requires before AccountInfo.sampleArgs := by
  refine ⟨primary_retains_bad_return, ?_⟩
  intro ready
  apply decoder_admission_rejects_bad_callback
  exact (ready.2 afterInit rfl).2 afterInit
    ⟨.returned .zero afterInit, ⟨.returned .zero afterInit, rfl, rfl⟩, rfl⟩

def mixed : Decoder := fun state args outcome => goodReturn state args outcome ∨ badReturn state
  args outcome

/-- A valid alternative does not excuse another finite exit of the same
callback. Admission is universal, even though both raw returns are retained. -/
theorem mixed_callback_not_admitted : ¬ AccountInfo.GuardCallback.Admissible guard mixed during
  decodeArgs := by
  intro admitted
  apply bad_callback_not_admitted
  intro outcome called
  exact admitted outcome (Or.inr called)

/-- Permitted effects may mutate a different identified cell. The frame keeps
the held data guard and its bytes, and validates the actual changed store. -/
theorem other_cell_frame : AccountInfo.GuardCallback.StateFrame during.1 (mutateOther during).1
  guard := by
  apply Borrow.CallbackFrame.of_slots
    (Borrow.replaceCell_valid AnchorAccount.sampleDataDuring_valid _ _)
    (Borrow.replaceCell_slots _ _ _) (fun query => Borrow.replaceCell_policy _ _ query _)
  intro slot old next live oldFound nextFound
  change some (⟨AccountInfo.sampleInfo.data, .shared, 0, .whole⟩ : Borrow.Slot AccountInfo.View) =
    some slot at live
  cases live
  change some (⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩ : Borrow.Cell
    AccountInfo.Content) = some old at oldFound
  cases oldFound
  change some (⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩ : Borrow.Cell
    AccountInfo.Content) = some next at nextFound
  cases nextFound
  rfl

theorem good_return_admitted : AccountInfo.GuardCallback.Admissible guard goodReturn during
  decodeArgs := by
  intro produced called
  cases called
  exact other_cell_frame

/-- Admission quantifies over all exits at the data scope reached by the
actual initialization and Owner prefixes, before any guard cleanup. -/
theorem primary_ready {decoder : Decoder}
    (admitted : AccountInfo.GuardCallback.Admissible guard decoder during decodeArgs) :
    (AnchorLang.accounts.account.Account.try_from_contract.contract
      (interpretation decoder)).requires before AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro _ impossible
    cases impossible
  intro after started
  refine ⟨owner_ready decoder after _, ?_⟩
  intro checked owned
  have same : after = afterInit := (Outcome.returned.inj started).2
  cases same
  obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
    AnchorConstructOwned.ownerCheck_returned_ok owned
  change .returned .zero afterInit = produced at called
  cases called
  cases widened
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro next store acquired view bytes current
  change (Except.ok guard, during.1) = (.ok next, store) at acquired
  cases acquired
  change Except.ok (AccountInfo.View.whole, AccountInfo.Content.data [10, 20, 30]) =
    .ok (view, .data bytes) at current
  cases current
  exact admitted

theorem owner_check (decoder : Decoder) :
    AnchorConstructOwned.ownerCheck (interpretation decoder) afterInit AccountInfo.sampleArgs
      (.returned (.ok ()) afterInit) :=
  ⟨.returned .zero afterInit, ⟨.returned .zero afterInit, rfl, rfl⟩, rfl⟩

/-- Both ordinary errors and unwinds meet the same actual-state frame, while
the owned error Box still denotes the original ProgramError value. -/
theorem other_cell_error_unwind_admitted :
    AccountInfo.GuardCallback.Admissible guard goodError during decodeArgs ∧
    AccountInfo.GuardCallback.Admissible guard goodUnwind during decodeArgs ∧
    AnchorErrorOwned.current AnchorOwnedSamples.constructor.errors during errorBuilt.1 =
      some (.program ⟨.custom 77, none, none⟩) := by
  refine ⟨?_, ?_, rfl⟩
  · intro produced called; cases called; exact other_cell_frame
  · intro produced called; cases called; exact other_cell_frame

/-- Every admitted state-bearing exit keeps the mutation of the other cell
and releases the held data guard exactly once. -/
theorem admitted_error_and_unwind_retained :
    AnchorConstructOwned.decodeAccount (interpretation goodError) afterInit AccountInfo.sampleArgs
      (.returned (.error errorBuilt.1) (release (mutateOther during))) ∧
    AnchorConstructOwned.decodeAccount (interpretation goodUnwind) afterInit AccountInfo.sampleArgs
      (.unwound (.inr "decode") (release (mutateOther during))) ∧
    (release (mutateOther during)).1.lookupCell AccountInfo.sampleInfo.lamports =
      some ⟨.lamports 77, AccountInfo.sampleProfile.policy⟩ ∧
    Borrow.current (release (mutateOther during)).1 guard = .error .invalidGuard := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact ⟨.returned (.error errorBuilt.1) (mutateOther during),
      ⟨.returned ⟨.error errorBuilt.1, []⟩ (mutateOther during),
        ⟨.returned ⟨.error errorBuilt.1, []⟩ (mutateOther during), rfl, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨.unwound (.inr "decode") (mutateOther during),
      ⟨.unwound (.inr "decode") (mutateOther during),
        ⟨.unwound "decode" (mutateOther during), rfl, rfl⟩, rfl⟩, rfl⟩

/-- A terminal callback is admitted and forwarded exactly, with no post-state
or fabricated guard-release event. -/
theorem terminal_retained : AccountInfo.GuardCallback.Admissible guard terminal during decodeArgs ∧
    AnchorConstructOwned.decodeAccount (interpretation terminal) afterInit AccountInfo.sampleArgs
      (.terminated (.inr (.allocation .name))) := by
  constructor
  · intro produced called; cases called; trivial
  · exact ⟨.terminated (.inr (.allocation .name)),
      ⟨.terminated (.inr (.allocation .name)),
        ⟨.terminated (.allocation .name), rfl, rfl⟩, rfl⟩, rfl⟩

/-- A callback that destroys the guard still has its explicit finite exit,
but cannot meet the universal guard-identity premise of the caller. -/
theorem killed_guard_not_admitted : killed during decodeArgs (.returned ⟨.ok 7, []⟩ (release
  during)) ∧
    ¬ AccountInfo.GuardCallback.Admissible guard killed during decodeArgs := by
  refine ⟨rfl, ?_⟩
  intro admitted
  have held := (admitted _ (show killed during decodeArgs (.returned ⟨.ok 7, []⟩ (release during))
    from rfl)).held
  change (none : Option (Borrow.Slot AccountInfo.View)) = some _ at held
  cases held

/-- The invalid representation does not manufacture a second destructor. Its
partial cleanup boundary is explicit and its call is outside admission. -/
theorem killed_guard_no_fabricated_cleanup :
    AnchorAccount.releaseOutcome guard
      (.returned (.ok (7 : Nat)) (release during) : Outcome World (Except Error Nat) String
        AnchorErrorOwned.Reference.Failure) = none := rfl

/-- A finite guard-destroying codec is rejected by the primary registered
family at its reached input, even though cleanup has no raw result. -/
theorem killed_guard_rejected_by_primary_family :
    ¬ (AnchorLang.accounts.account.Account.try_from_contract.contract
      (interpretation killed)).requires before AccountInfo.sampleArgs := by
  intro ready
  exact killed_guard_not_admitted.2
    (((ready.2 afterInit rfl).2 afterInit (owner_check killed)).2
      guard during.1 rfl .whole [10, 20, 30] rfl)

def observationKilled : AnchorAccount.ConstructorIndex where
  Aux := AnchorErrorOwned.Reference.State
  Payload := Nat
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  discriminator := [10]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned .zero state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state args =>
    .returned ⟨.ok 7, []⟩ ((Borrow.release state.1 args.guard).2, state.2)

/-- The observation family rejects the same finite invalidating exit. Its
unchanged raw release relation also refuses to invent a second destructor. -/
theorem killed_guard_rejected_by_observation_family :
    observationKilled.deserialize during decodeArgs (.returned ⟨.ok (7 : Nat), []⟩ (release
      during)) ∧
    AnchorAccount.releaseOutcome guard
      (.returned (.ok (7 : Nat)) (release during) : Outcome World
        (Except AnchorAccount.Error Nat) String AnchorErrorOwned.Reference.Failure) = none ∧
    ¬ ((AnchorAccount.constructorFamily .account).contract observationKilled).requires
      before AccountInfo.sampleArgs := by
  refine ⟨rfl, rfl, ?_⟩
  intro ready
  have localReady := ready.2 afterInit rfl afterInit
    ⟨.returned .zero afterInit, ⟨.returned .zero afterInit, rfl, rfl⟩, rfl⟩
  have held := (localReady.2 guard during.1 rfl .whole [10, 20, 30] rfl _
    (show observationKilled.deserialize during decodeArgs
      (.returned ⟨.ok (7 : Nat), []⟩ (release during)) from rfl)).held
  change (none : Option (Borrow.Slot AccountInfo.View)) = some _ at held
  cases held

/-- Universal admission plus the actual live acquisition rules out empty
scope behavior for the concrete permitted callback. -/
theorem admitted_scope_nonempty : ∃ outcome,
    AccountInfo.GuardCallback.withGuard guard goodReturn during decodeArgs outcome := by
  apply (good_return_admitted.hasOutcome_iff
    (show during.1.resolve guard = some ⟨AccountInfo.sampleInfo.data, .shared, 0, .whole⟩ from
      rfl)).mpr
  exact ⟨.returned ⟨.ok 7, []⟩ (mutateOther during), rfl⟩

/-- This complete primary execution observes the permitted other-cell write
after the initialization of the source, Owner call, decoding, and actual release. -/
theorem admitted_primary_execution : FamilyHasExecution
    AnchorLang.accounts.account.Account.try_from_contract
    AnchorLang.accounts.account.Account.try_from_run (interpretation goodReturn) :=
      by
  refine ⟨before, AccountInfo.sampleArgs,
    .returned (.ok (AnchorAccount.Account.mk (7 : Nat) AccountInfo.sampleInfo))
      (release (mutateOther during)),
    primary_ready good_return_admitted, ?_⟩
  obtain ⟨decoded, released, retained⟩ := AnchorConstructOwned.account_retain
    (primary_ready good_return_admitted) rfl (owner_check goodReturn) rfl rfl
    (show goodReturn during decodeArgs (.returned ⟨.ok 7, []⟩ (mutateOther during)) from rfl)
  change some (Outcome.returned (Except.ok (7 : Nat)) (release (mutateOther during))) =
    some decoded at released
  cases released
  exact retained

/-- One nondeterministic provider has all four finite exit forms. Admission
must frame both state-bearing return alternatives and its unwind. -/
def permitted : Decoder := fun state args outcome =>
  goodReturn state args outcome ∨ goodError state args outcome ∨
    goodUnwind state args outcome ∨ terminal state args outcome

theorem permitted_admitted : AccountInfo.GuardCallback.Admissible guard permitted during decodeArgs
  := by
  intro produced called
  rcases called with called | called | called | called
  · exact good_return_admitted produced called
  · exact other_cell_error_unwind_admitted.1 produced called
  · exact other_cell_error_unwind_admitted.2.1 produced called
  · exact terminal_retained.1 produced called

/-- Every actual finite exit of this admitted provider extends through the
complete primary constructor. This consumes the callback exit and derives
cleanup; it assumes neither a completed constructor result nor totality. -/
theorem permitted_exit_continues {produced : Outcome World Decoded String
    AnchorErrorOwned.Reference.Failure}
    (called : permitted during decodeArgs produced) :
    ∃ decoded, AnchorAccount.releaseOutcome guard
        (Outcome.map AnchorConstructOwned.Decoded.result (AnchorAccount.widen produced)) = some
          decoded ∧
      AnchorLang.accounts.account.Account.try_from_run (interpretation permitted)
        before AccountInfo.sampleArgs
        (Outcome.map (Except.map fun value => AnchorAccount.Account.mk value AccountInfo.sampleInfo)
          decoded) :=
  AnchorConstructOwned.account_retain (primary_ready permitted_admitted) rfl
    (owner_check permitted) rfl rfl called

/-- Success, the owned ordinary error, unwind and terminal all survive the
registered constructor. Only the state-bearing exits perform guard release. -/
theorem admitted_primary_all_exits :
    (AnchorLang.accounts.account.Account.try_from_contract.contract
      (interpretation permitted)).requires before AccountInfo.sampleArgs ∧
    AnchorLang.accounts.account.Account.try_from_run (interpretation permitted)
      before AccountInfo.sampleArgs
      (.returned (.ok (AnchorAccount.Account.mk (7 : Nat) AccountInfo.sampleInfo))
        (release (mutateOther during))) ∧
    AnchorLang.accounts.account.Account.try_from_run (interpretation permitted)
      before AccountInfo.sampleArgs (.returned (.error errorBuilt.1) (release (mutateOther
        during))) ∧
    AnchorLang.accounts.account.Account.try_from_run (interpretation permitted)
      before AccountInfo.sampleArgs (.unwound (.inr "decode") (release (mutateOther during))) ∧
    AnchorLang.accounts.account.Account.try_from_run (interpretation permitted)
      before AccountInfo.sampleArgs (.terminated (.inr (.allocation .name))) := by
  refine ⟨primary_ready permitted_admitted, ?_, ?_, ?_, ?_⟩
  · obtain ⟨decoded, released, retained⟩ := permitted_exit_continues
      (show permitted during decodeArgs (.returned ⟨.ok 7, []⟩ (mutateOther during)) from Or.inl
        rfl)
    change some (Outcome.returned (Except.ok (7 : Nat)) (release (mutateOther during))) =
      some decoded at released
    cases released
    exact retained
  · obtain ⟨decoded, released, retained⟩ := permitted_exit_continues
      (show permitted during decodeArgs (.returned ⟨.error errorBuilt.1, []⟩ (mutateOther during))
        from
        Or.inr (Or.inl rfl))
    change some (Outcome.returned (Except.error errorBuilt.1) (release (mutateOther during))) =
      some decoded at released
    cases released
    exact retained
  · obtain ⟨decoded, released, retained⟩ := permitted_exit_continues
      (show permitted during decodeArgs (.unwound "decode" (mutateOther during)) from
        Or.inr (Or.inr (Or.inl rfl)))
    change some (Outcome.unwound (.inr "decode") (release (mutateOther during))) = some decoded
      at released
    cases released
    exact retained
  · obtain ⟨decoded, released, retained⟩ := permitted_exit_continues
      (show permitted during decodeArgs (.terminated (.allocation .name)) from
        Or.inr (Or.inr (Or.inr rfl)))
    change some (Outcome.terminated (.inr (.allocation .name))) = some decoded at released
    cases released
    exact retained

/-- This malicious primitive preserves its String/Box observations but kills
the guard of the caller. Its next primitive has no finite outcomes. -/
def prefixOps : AnchorErrorOwned.Ops World AnchorErrorOwned.Reference.StringId
    AnchorErrorOwned.Reference.BoxId AnchorErrorOwned.Reference.Failure :=
  { AnchorOwnedSamples.constructor.errors with
    copyLiteral := Callback.bind AnchorOwnedSamples.constructor.errors.copyLiteral
      (fun resource after outcome => outcome = .returned resource (release after))
    formatLiteral := fun _ _ _ => False }

def prefixCode : AnchorErrorOwned.Code :=
  let payload := AnchorAccount.Code.discriminatorMismatch.payload
  ⟨payload.name, payload.code, payload.message⟩
def nameResult := AnchorErrorOwned.Reference.stringResult false auxiliary prefixCode.name
def afterName : World := release (during.1, nameResult.2)

/-- The first primitive really returns with the guard already invalidated. -/
theorem invalidating_name_prefix : prefixOps.copyLiteral during prefixCode.name
    (.returned nameResult.1 afterName) ∧ afterName.1.resolve guard = none := by
  refine ⟨?_, rfl⟩
  exact ⟨.returned nameResult.1 (during.1, nameResult.2),
    ⟨.returned nameResult.1 nameResult.2, rfl, rfl⟩, rfl⟩

/-- No alternate name outcome is invented by the malformed provider. -/
theorem name_prefix_only {outcome : Outcome World AnchorErrorOwned.Reference.StringId
    Empty AnchorErrorOwned.Reference.Failure}
    (called : prefixOps.copyLiteral during prefixCode.name outcome) :
    outcome = .returned nameResult.1 afterName := by
  obtain ⟨first, ⟨raw, copied, focused⟩, next⟩ := called
  change Outcome.returned nameResult.1 nameResult.2 = raw at copied
  cases copied
  cases focused
  exact next

/-- The whole factory has no result, despite its real invalidating prefix.
An admission predicate over only completed factory exits would miss this. -/
theorem invalidating_prefix_factory_empty : ¬ ∃ outcome,
    AnchorErrorOwned.buildCode prefixOps during prefixCode outcome := by
  rintro ⟨outcome, named, copied, rest⟩
  have same := name_prefix_only copied
  cases same
  obtain ⟨_, impossible, _⟩ := rest
  exact impossible

/-- Primitive admission rejects the invalidating prefix before any dependent
operation can make the complete factory relation empty. -/
theorem invalidating_prefix_not_admitted :
    ¬ AnchorGuardEffects.BuildCodeAdmissible prefixOps during guard prefixCode := by
  intro admitted
  have frame := admitted.name _ invalidating_name_prefix.1
  have held := frame.held
  change (none : Option (Borrow.Slot AccountInfo.View)) = some _ at held
  cases held

/-- Merely framing completed exits of that factory would be vacuous. The
selected Loader precondition instead demands the rejected primitive law. -/
theorem whole_factory_admission_is_insufficient :
    AccountInfo.GuardCallback.Admissible guard (AnchorErrorOwned.buildCode prefixOps) during
      prefixCode := by
  intro outcome called
  exact False.elim (invalidating_prefix_factory_empty ⟨outcome, called⟩)

/-- The bad provider still obeys the separate heap observations on returned
name allocation; that does not imply its held-guard premise. -/
theorem prefix_copy_heap {before after : World} {text : String}
    {resource : AnchorErrorOwned.Reference.StringId}
    (called : prefixOps.copyLiteral before text (.returned resource after)) :
    AnchorErrorOwned.Reference.ops.copyLiteral before.2 text (.returned resource after.2) := by
  obtain ⟨produced, copied, next⟩ := called
  cases produced with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases next
  | returned value middle =>
    cases next
    exact AnchorErrorOwned.focus_returned_inner Owned.Focus.snd copied

/-- Existing String/Box laws alone did not exclude the guard-destroying
provider. The new primitive guard admission is an independent requirement. -/
theorem invalidating_prefix_heap_laws : prefixOps.Laws := by
  refine { AnchorErrorOwned.Reference.ops.focus_laws
    AnchorErrorOwned.Reference.ops_laws Owned.Focus.snd with
    copy := ?_, format := ?_, copy_boxes := ?_, format_boxes := ?_ }
  · exact {
      current := fun _ _ _ _ called =>
        AnchorErrorOwned.Reference.ops_laws.copy.current _ _ _ _ (prefix_copy_heap called)
      fresh := fun _ _ _ _ called =>
        AnchorErrorOwned.Reference.ops_laws.copy.fresh _ _ _ _ (prefix_copy_heap called)
      other := fun _ _ _ _ called =>
        AnchorErrorOwned.Reference.ops_laws.copy.other _ _ _ _ (prefix_copy_heap called) }
  · exact {
      current := fun _ _ _ _ impossible => False.elim impossible
      fresh := fun _ _ _ _ impossible => False.elim impossible
      other := fun _ _ _ _ impossible => False.elim impossible }
  · exact fun _ _ _ _ called =>
      AnchorErrorOwned.Reference.ops_laws.copy_boxes _ _ _ _ (prefix_copy_heap called)
  · exact fun _ _ _ _ impossible => False.elim impossible

/-- The error factory is reached under exactly the guard used by the prefix
counterexample, after the earlier lamport-guard tombstone of the initial state. -/
def prefixTypes : AnchorConstructOwned.Types where
  Aux := AnchorErrorOwned.Reference.State
  Payload := Nat
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := prefixOps
  discriminator := [99]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned .zero state
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := goodReturn

/-- The separate Loader cleanup premise rejects the hidden invalidating
prefix even when its heap laws hold and the complete factory is empty. -/
theorem loader_admission_rejects_invalidating_prefix :
    ¬ AnchorConstructOwned.LoaderReady prefixTypes afterInit AccountInfo.sampleArgs := by
  intro ready
  exact invalidating_prefix_not_admitted
    (ready.2 guard during.1 rfl .whole [10, 20, 30] rfl .discriminatorMismatch rfl)

/-- The same primitive prefix is rejected by the exact registered Loader
family, without waiting for a complete factory or constructor exit. -/
theorem registered_loader_rejects_invalidating_prefix :
    ¬ (AnchorLang.accounts.account_loader.AccountLoader.try_from_contract.contract
      prefixTypes).requires afterInit AccountInfo.sampleArgs := by
  intro ready
  exact loader_admission_rejects_invalidating_prefix
    (ready.2 afterInit
      ⟨.returned .zero afterInit, ⟨.returned .zero afterInit, rfl, rfl⟩, rfl⟩).2

def offPath : Decoder := fun state args outcome =>
  if args.guard = guard then goodReturn state args outcome else badReturn state args outcome

/-- Admission checks the callback at the actual acquired guard. It imposes no
unrelated global input restriction on a callback branch that is not reached. -/
theorem unrelated_callback_input_is_unconstrained :
    AnchorConstructOwned.DecodeReady (interpretation offPath) afterInit AccountInfo.sampleArgs ∧
      offPath during { decodeArgs with guard := ⟨9, 0⟩ }
        (.returned ⟨.ok 7, []⟩ (mutateHeld during)) := by
  refine ⟨?_, rfl⟩
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro next store acquired view bytes current produced called
  change (Except.ok guard, during.1) = (.ok next, store) at acquired
  cases acquired
  change goodReturn during ⟨AccountInfo.sampleInfo, guard, bytes⟩ produced at called
  cases called
  exact other_cell_frame

namespace SelectedData

/-- These abstract inputs have current data but no designated lamports cell.
The zero-width profile also disagrees with the actual borrow policy of the cell. -/
def args : AccountInfo.Args :=
  { AccountInfo.sampleArgs with
    profile := ⟨0, false⟩
    info := { AccountInfo.sampleInfo with lamports := ⟨99⟩ } }

def initial : World := (AnchorAccount.sampleAfterInit, AnchorOwnedSamples.auxiliary)
def active : World := (AnchorAccount.sampleDataDuring, AnchorOwnedSamples.auxiliary)
def afterDecode : World := (AnchorAccount.sampleAfterDecode, AnchorOwnedSamples.auxiliary)

/-- A non-system current owner skips the unrelated initialization read. -/
def types : AnchorConstructOwned.Types :=
  { AnchorOwnedSamples.constructor with
    ownerAt := fun _ _ => .ofNat 1
    owner := Callback.ofFunction fun state _ => .returned (.ofNat 1) state }

theorem outside_whole_representation :
    ¬ AccountInfo.Valid args.profile initial.1 args.info ∧
      initial.1.lookupCell args.info.lamports = none := by
  refine ⟨?_, rfl⟩
  intro valid
  exact (by decide : ¬ 2 ≤ 0) valid.1

/-- The narrowed decoder domain reuses the existing callback frame proof. -/
theorem owned_decode_ready : AnchorConstructOwned.DecodeReady types initial args :=
  AnchorOwnedSamples.decode_ready

theorem owner_check : AnchorConstructOwned.ownerCheck types initial args (.returned (.ok ())
  initial) :=
  ⟨.returned (.ofNat 1) initial, ⟨.returned (.ofNat 1) initial, rfl, rfl⟩, rfl⟩

theorem owner_ready (state : World) : AnchorConstructOwned.OwnerCheckReady types state args := by
  intro expected after called mismatch
  cases called
  exact False.elim (mismatch rfl)

/-- Reached-prefix admission needs only the selected data cell and its codec
frame, even for this input outside the full AccountInfo representation. -/
theorem primary_ready :
    (AnchorLang.accounts.account.Account.try_from_contract.contract types).requires
      initial args := by
  refine ⟨?_, ?_⟩
  · intro impossible
    exact False.elim ((by decide : _root_.Solanalib.Runtime.Pubkey.ofNat 1 ≠ .zero) impossible)
  intro after started
  refine ⟨owner_ready after, ?_⟩
  intro checked owned
  have same : after = initial := (Outcome.returned.inj started).2
  cases same
  obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
    AnchorConstructOwned.ownerCheck_returned_ok owned
  change .returned (.ofNat 1) initial = produced at called
  cases called
  cases widened
  exact owned_decode_ready

/-- Both selected-cell typing and the callback frame are consumed: the former
supplies a real codec input, and the latter derives its exact checked cleanup. -/
theorem typed_data_reaches_owned_decoder :
    (∃ bytes, Borrow.current active.1 guard = .ok (.whole, .data bytes) ∧
      types.deserialize active ⟨args.info, guard, bytes⟩ (.returned ⟨.ok (7 : Nat), []⟩ active)) ∧
    AnchorConstructOwned.decodeAccount types initial args (.returned (.ok (7 : Nat)) afterDecode) ∧
    Borrow.current afterDecode.1 guard = .error .invalidGuard := by
  have acquired : AccountInfo.tryBorrowData initial.1 args = (.ok guard, active.1) := rfl
  obtain ⟨bytes, current, _⟩ := owned_decode_ready.callback_input acquired
  have called : types.deserialize active ⟨args.info, guard, bytes⟩
      (.returned ⟨.ok (7 : Nat), []⟩ active) := rfl
  obtain ⟨outcome, released, retained⟩ := owned_decode_ready.retain acquired current called
  change some (Outcome.returned (Except.ok (7 : Nat)) afterDecode) = some outcome at released
  cases released
  exact ⟨⟨bytes, current, called⟩, retained, rfl⟩

/-- The observation decoder uses the same selected-data premise and cleanup
law, without reinstating unrelated representation conditions. -/
theorem typed_data_reaches_observation_decoder :
    AnchorAccount.decodeAccount AnchorAccount.constructorSample
      (initial.1, ()) args (.returned (.ok (7 : Nat)) (afterDecode.1, ())) := by
  have ready : AnchorAccount.DecodeReady AnchorAccount.constructorSample (initial.1, ()) args :=
    AnchorAccount.decode_sample_ready
  have acquired : AccountInfo.tryBorrowData initial.1 args = (.ok guard, active.1) := rfl
  obtain ⟨bytes, current, _⟩ := ready.callback_input acquired
  have called : AnchorAccount.constructorSample.deserialize (active.1, ())
      ⟨args.info, guard, bytes⟩ (.returned ⟨.ok (7 : Nat), []⟩ (active.1, ())) := rfl
  obtain ⟨outcome, released, retained⟩ := ready.retain acquired current called
  change some (Outcome.returned (Except.ok (7 : Nat)) (afterDecode.1, ())) = some outcome
    at released
  cases released
  exact retained

/-- This broader mathematical input reaches initialization, Owner, the actual
decoder and cleanup in the registered primary family. -/
theorem typed_data_primary_execution : FamilyHasExecution
    AnchorLang.accounts.account.Account.try_from_contract
    AnchorLang.accounts.account.Account.try_from_run types := by
  refine ⟨initial, args, .returned (.ok (AnchorAccount.Account.mk (7 : Nat) args.info))
    afterDecode, primary_ready, ?_⟩
  obtain ⟨decoded, released, retained⟩ := AnchorConstructOwned.account_retain
    primary_ready rfl owner_check rfl rfl
    (show types.deserialize active ⟨args.info, guard, [10, 20, 30]⟩
      (.returned ⟨.ok (7 : Nat), []⟩ active) from rfl)
  change some (Outcome.returned (Except.ok (7 : Nat)) afterDecode) = some decoded at released
  cases released
  exact retained

theorem loader_ready : AnchorConstructOwned.LoaderReady types initial args := by
  refine ⟨AnchorAccount.sampleAfterInit_valid, ?_⟩
  intro next store acquired view bytes current failure selected
  change (Except.ok guard, active.1) = (.ok next, store) at acquired
  cases acquired
  change Except.ok (AccountInfo.View.whole, AccountInfo.Content.data [10, 20, 30]) =
    .ok (view, .data bytes) at current
  cases current
  change none = some failure at selected
  cases selected

/-- On success, protocol validity supplies the unchanged callback frame used
to derive real cleanup; the absent lamports field and source bounds play no role. -/
theorem protocol_validity_retains_loader_success :
    AnchorConstructOwned.checkLoaderData types initial args (.returned (.ok ()) afterDecode) ∧
      Borrow.current afterDecode.1 guard = .error .invalidGuard := by
  have acquired : AccountInfo.tryBorrowData initial.1 args = (.ok guard, active.1) := rfl
  have current : Borrow.current active.1 guard = .ok (.whole, .data [10, 20, 30]) := rfl
  have called : AnchorConstructOwned.loaderCheck types [10, 20, 30] active ()
      (.returned (.ok ()) active) := rfl
  obtain ⟨outcome, released, retained⟩ := loader_ready.retain acquired current called
  change some (Outcome.returned (Except.ok ()) afterDecode) = some outcome at released
  cases released
  exact ⟨retained, rfl⟩

/-- The owned Loader combines selected-data typing with its existing protocol
and reached-factory admission; it does not require full AccountInfo.Valid. -/
theorem primary_loader_ready :
    (AnchorLang.accounts.account_loader.AccountLoader.try_from_contract.contract
      types).requires initial args := by
  refine ⟨owner_ready initial, ?_⟩
  intro checked owned
  obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
    AnchorConstructOwned.ownerCheck_returned_ok owned
  change .returned (.ofNat 1) initial = produced at called
  cases called
  cases widened
  exact ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, loader_ready⟩

theorem typed_data_primary_loader_execution : FamilyHasExecution
    AnchorLang.accounts.account_loader.AccountLoader.try_from_contract
    AnchorLang.accounts.account_loader.AccountLoader.try_from_run types := by
  refine ⟨initial, args, .returned (.ok (AnchorAccount.Loader.mk (Payload := Nat) args.info))
    afterDecode, primary_loader_ready, ?_⟩
  obtain ⟨decoded, released, retained⟩ := AnchorConstructOwned.loader_retain
    primary_loader_ready owner_check rfl rfl
    (show AnchorConstructOwned.loaderCheck types [10, 20, 30] active ()
      (.returned (.ok ()) active) from rfl)
  change some (Outcome.returned (Except.ok ()) afterDecode) = some decoded at released
  cases released
  exact retained

theorem observation_loader_ready :
    (AnchorLang.accounts.account_loader.AccountLoader.try_from_observation_contract.contract
      AnchorAccount.constructorSample).requires (initial.1, ()) args := by
  intro checked owned
  have same : checked = (initial.1, ()) := by
    simp [AnchorAccount.ownerCheck, AnchorAccount.constructorSample, AnchorAccount.widenCallback,
      Callback.ofFunction, Callback.bind, AnchorAccount.widen] at owned
    exact (Outcome.returned.inj owned).2
  cases same
  exact ⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩

/-- The observation-only Loader records its actual successful check and guard
release without the unused whole-AccountInfo admission gate. -/
theorem observation_loader_execution : FamilyHasExecution
    AnchorLang.accounts.account_loader.AccountLoader.try_from_observation_contract
    AnchorLang.accounts.account_loader.AccountLoader.try_from_observation_run
    AnchorAccount.constructorSample := by
  refine ⟨(initial.1, ()), args,
    .returned (.ok (AnchorAccount.Loader.mk (Payload := Nat) args.info)) (afterDecode.1, ()),
    observation_loader_ready, ?_⟩
  refine ⟨.returned (.ok ()) (initial.1, ()),
    ⟨.returned .zero (initial.1, ()), ⟨.returned .zero (initial.1, ()), rfl, rfl⟩, rfl⟩, ?_⟩
  exact ⟨.returned (.ok ()) (afterDecode.1, ()), rfl, rfl⟩

end SelectedData

namespace Initialization

def malformedArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with
    info := { AccountInfo.sampleInfo with lamports := AccountInfo.sampleInfo.data } }

/-- Both exact primary families reject a system-owned entry whose actual
lamports projection is malformed. The lower-level operation remains empty. -/
theorem malformed_entry_rejected :
    ¬ (AnchorLang.accounts.account.Account.try_from_contract.contract
      AnchorOwnedSamples.constructor).requires before malformedArgs ∧
    ¬ (AnchorLang.accounts.interface_account.InterfaceAccount.try_from_contract.contract
      AnchorOwnedSamples.constructor).requires before malformedArgs := by
  constructor <;> intro ready <;> exact ready.1 rfl rfl

theorem malformed_raw_initialization_empty
    (outcome : Outcome World (Except Error Unit) (AnchorAccount.ConstructorUnwind String)
      (AnchorAccount.ConstructorTerminal AnchorErrorOwned.Reference.Failure)) :
    ¬ AnchorConstructOwned.initialized AnchorOwnedSamples.constructor before malformedArgs outcome
      := by
  intro impossible
  exact impossible

def busy : World :=
  ((AccountInfo.tryBorrowMutData before.1 AccountInfo.sampleArgs).2, before.2)

def busyArgs (aborts : Bool) : AccountInfo.Args :=
  { malformedArgs with profile := ⟨0, aborts⟩ }

/-- Checked borrow failure precedes the projection and does not allocate an
error. Its actual unwind/abort is admitted even with unrelated invalid widths. -/
theorem borrow_failure_admitted (aborts : Bool) :
    (AnchorLang.accounts.account.Account.try_from_contract.contract
      AnchorOwnedSamples.constructor).requires busy (busyArgs aborts) ∧
    (AnchorLang.accounts.interface_account.InterfaceAccount.try_from_contract.contract
      AnchorOwnedSamples.constructor).requires busy (busyArgs aborts) := by
  have domain : AnchorAccount.InitReady AnchorOwnedSamples.constructor.ownerAt busy (busyArgs
    aborts) := by
    intro _ impossible
    cases impossible
  have noSuccess : ∀ after, AnchorConstructOwned.initialized AnchorOwnedSamples.constructor
      busy (busyArgs aborts) (.returned (.ok ()) after) → False := by
    intro after called
    cases aborts <;> cases called
  exact ⟨⟨domain, fun after called => False.elim (noSuccess after called)⟩,
    ⟨domain, fun after called => False.elim (noSuccess after called)⟩⟩

theorem borrow_failure_retains_unwind_and_abort :
    AnchorConstructOwned.run .account AnchorOwnedSamples.constructor busy (busyArgs false)
      (.unwound (.inl .borrowFailed) busy) ∧
    AnchorConstructOwned.run .interfaceAccount AnchorOwnedSamples.constructor busy (busyArgs true)
      (.terminated (.inl .borrowFailed)) := by
  constructor
  · exact ⟨.unwound (.inl .borrowFailed) busy, rfl, rfl⟩
  · exact ⟨.terminated (.inl .borrowFailed), rfl, rfl⟩

def zeroBefore : World :=
  ((Borrow.replaceCell AccountInfo.sampleState AccountInfo.sampleInfo.lamports (.lamports 0)).2,
    AnchorOwnedSamples.auxiliary)

def zeroRead : World :=
  ((AccountInfo.observe .lamports zeroBefore.1 AccountInfo.sampleInfo).2, zeroBefore.2)

def zeroCode : AnchorErrorOwned.Code :=
  ⟨AnchorAccount.Code.notInitialized.payload.name, AnchorAccount.Code.notInitialized.payload.code,
    AnchorAccount.Code.notInitialized.payload.message⟩

def zeroBuilt := AnchorErrorOwned.Reference.buildCodeResult zeroRead.2 zeroCode
def zeroAfter : World := (zeroRead.1, zeroBuilt.2)

theorem zero_balance_admitted :
    (AnchorLang.accounts.account.Account.try_from_contract.contract
      AnchorOwnedSamples.constructor).requires zeroBefore AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro _ impossible
    cases impossible
  rintro after ⟨produced, _, mapped⟩
  cases produced <;> cases mapped

/-- The zero-balance branch executes the real three-allocation factory. The
continuation lemma retains its returned Box and exact allocation effects. -/
theorem zero_balance_retains_actual_factory :
    AnchorConstructOwned.run .account AnchorOwnedSamples.constructor zeroBefore
      AccountInfo.sampleArgs
      (.returned (.error zeroBuilt.1) zeroAfter) := by
  have built : AnchorErrorOwned.buildCode AnchorOwnedSamples.constructor.errors zeroRead zeroCode
      (.returned zeroBuilt.1 zeroAfter) :=
    AnchorErrorOwned.buildCode_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
      zeroRead zeroCode zeroBuilt.1 zeroBuilt.2
      (AnchorErrorOwned.Reference.buildCode_returns zeroRead.2 zeroCode (by decide))
  have factory : AnchorConstructOwned.code AnchorOwnedSamples.constructor .notInitialized zeroRead
    ()
      (.returned zeroBuilt.1 zeroAfter) :=
    ⟨.returned zeroBuilt.1 zeroAfter, ⟨.returned zeroBuilt.1 zeroAfter, built, rfl⟩, rfl⟩
  refine ⟨.returned (.error zeroBuilt.1) zeroAfter, ?_, rfl⟩
  exact AnchorConstructOwned.initialized_zero_retain rfl rfl factory

def exhausted : World := (zeroBefore.1, AnchorErrorOwned.Reference.initial 0)
def exhaustedRead : World := (zeroRead.1, AnchorErrorOwned.Reference.initial 0)

/-- The same zero branch admits an actual allocation terminal. It does not
require a successful error return or invent a terminal post-state. -/
theorem zero_balance_retains_actual_allocation_terminal :
    (AnchorLang.accounts.account.Account.try_from_contract.contract
      AnchorOwnedSamples.constructor).requires exhausted AccountInfo.sampleArgs ∧
    AnchorConstructOwned.run .account AnchorOwnedSamples.constructor exhausted
      AccountInfo.sampleArgs
      (.terminated (.inr (.allocation .name))) := by
  refine ⟨⟨?_, ?_⟩, .terminated (.inr (.allocation .name)), ?_, rfl⟩
  · intro _ impossible
    cases impossible
  · rintro after ⟨produced, _, mapped⟩
    cases produced <;> cases mapped
  · have called : AnchorOwnedSamples.constructor.errors.copyLiteral exhaustedRead zeroCode.name
        (.terminated (.allocation .name)) :=
      ⟨.terminated (.allocation .name), rfl, rfl⟩
    exact AnchorConstructOwned.initialized_zero_retain rfl rfl
      (AnchorConstructOwned.code_from_name_terminal called)

end Initialization

end SolanalibTest.Specs.AnchorLang.GuardCallbacks
