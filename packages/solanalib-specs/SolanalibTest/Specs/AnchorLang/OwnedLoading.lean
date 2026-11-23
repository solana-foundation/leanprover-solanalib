/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.loading

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.OwnedLoading

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- A mismatch fixture using the existing focused String/Box reference heap. -/
def types : AnchorLoadingOwned.Types :=
  { AnchorOwnedSamples.loading with
    layout := { AnchorAccount.loadSample with discriminator := [99] } }
/-- The sample writable loader selects the real nonempty data cell. -/
def args : AnchorAccount.LoadArgs types.layout :=
  ⟨AccountInfo.sampleProfile, AnchorAccount.loadSampleArgs.loader, 8⟩
/-- The actual state after acquiring the sample shared data guard. -/
def during := (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2
/-- The actual state after releasing the acquired generation. -/
def released := (Borrow.release during ⟨0, 0⟩).2
/-- The exact discriminator-mismatch error payload fields. -/
def code : AnchorErrorOwned.Code :=
  let payload := AnchorAccount.Code.discriminatorMismatch.payload
  ⟨payload.name, payload.code, payload.message⟩
/-- The three reference allocations and their final owned error. -/
def built := AnchorErrorOwned.Reference.buildCodeResult AnchorOwnedSamples.auxiliary code

/-- The focused reference factory leaves the guard held throughout allocation. -/
theorem error_built_while_borrowed : AnchorLoadingOwned.code types .discriminatorMismatch
    (during, AnchorOwnedSamples.auxiliary) () (.returned built.1 (during, built.2)) := by
  refine ⟨.returned built.1 (during, built.2), ?_, rfl⟩
  exact AnchorErrorOwned.buildCode_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
    (during, AnchorOwnedSamples.auxiliary) code built.1 built.2
    (AnchorErrorOwned.Reference.buildCode_returns AnchorOwnedSamples.auxiliary code (by decide))

/-- The mismatch path allocates its two Strings and Box with the shared guard
still held. Returning the owned error then releases that exact guard. -/
theorem discriminator_error_releases_guard :
    (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_contract.contract
      types).post
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) args
      (.returned (.error built.1) (released, built.2)) := by
  change AnchorEffects.withGuard ⟨0, 0⟩
    (Callback.map Except.error (AnchorLoadingOwned.code types .discriminatorMismatch))
    (during, AnchorOwnedSamples.auxiliary) () (.returned (.error built.1) (released, built.2))
  exact ⟨.returned (.error built.1) (during, built.2),
    ⟨.returned built.1 (during, built.2), error_built_while_borrowed, rfl⟩, rfl⟩

/-- The error stays readable after cleanup and the old guard cannot be reused. -/
theorem owned_error_and_no_guard :
    AnchorErrorOwned.current types.errors (released, built.2) built.1 =
      some (AnchorAccount.error .discriminatorMismatch) ∧
    Borrow.current released ⟨0, 0⟩ = .error .invalidGuard ∧
    released.lookupCell AccountInfo.sampleInfo.data =
      AccountInfo.sampleState.lookupCell AccountInfo.sampleInfo.data := ⟨rfl, rfl, rfl⟩

/-- A concrete reference heap with no remaining allocation. -/
def exhausted := AnchorErrorOwned.Reference.initial 0

/-- The first actual name allocation terminates with its recorded reason. -/
theorem error_name_terminal : AnchorLoadingOwned.code types .discriminatorMismatch
    (during, exhausted) () (.terminated (.inr (.allocation .name))) := by
  refine ⟨.terminated (.allocation .name), ?_, rfl⟩
  refine ⟨.terminated (.allocation .name), ?_, rfl⟩
  exact ⟨.terminated (.allocation .name), rfl, rfl⟩

/-- A terminal error dependency has no invented post-state or release event.
The branch remains distinct from the local mapping panic vocabulary. -/
theorem held_error_allocation_terminal :
    AnchorLoadingOwned.run .shared types (AccountInfo.sampleState, exhausted) args
      (.terminated (.inr (.allocation .name))) := by
  change AnchorEffects.withGuard ⟨0, 0⟩
    (Callback.map Except.error (AnchorLoadingOwned.code types .discriminatorMismatch))
    (during, exhausted) () (.terminated (.inr (.allocation .name)))
  apply AnchorEffects.withGuard_terminal
  exact ⟨.terminated (.inr (.allocation .name)), error_name_terminal, rfl⟩

/-- Writable metadata rejects this input before using its abstract address. -/
def rejectedArgs : AnchorAccount.LoadArgs types.layout :=
  ⟨AccountInfo.sampleProfile, ⟨AccountInfo.sampleInfo⟩, 0⟩
/-- The exact writable-rejection error payload fields. -/
def notMutableCode : AnchorErrorOwned.Code :=
  let payload := AnchorAccount.Code.notMutable.payload
  ⟨payload.name, payload.code, payload.message⟩
/-- The completed writable-rejection allocations in the reference heap. -/
def notMutableBuilt :=
  AnchorErrorOwned.Reference.buildCodeResult AnchorOwnedSamples.auxiliary notMutableCode

/-- The zero abstract address is outside the Rust data-pointer binding. The
writable rejection precedes its use, and still performs the actual three error
allocations with no acquired guard or invented cleanup. -/
theorem abstract_address_retains_writable_error :
    rejectedArgs.dataAddress = 0 ∧
    (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_mut_contract.contract
      types).requires
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) rejectedArgs ∧
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_mut_run types
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) rejectedArgs
      (.returned (.error notMutableBuilt.1) (AccountInfo.sampleState, notMutableBuilt.2)) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨trivial, trivial⟩
  · refine ⟨.returned notMutableBuilt.1 (AccountInfo.sampleState, notMutableBuilt.2), ?_, rfl⟩
    refine ⟨.returned notMutableBuilt.1 (AccountInfo.sampleState, notMutableBuilt.2), ?_, rfl⟩
    exact AnchorErrorOwned.buildCode_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary)
      notMutableCode notMutableBuilt.1 notMutableBuilt.2
      (AnchorErrorOwned.Reference.buildCode_returns AnchorOwnedSamples.auxiliary notMutableCode (by
        decide))

/-- The normal result of the actual name allocation, before the deliberately bad cleanup. -/
def nameBuilt := AnchorErrorOwned.Reference.stringResult false AnchorOwnedSamples.auxiliary
  code.name

/-- The actual message allocation continues from the preceding name heap. -/
def messageBuilt := AnchorErrorOwned.Reference.stringResult true nameBuilt.2 code.message

/-- The ordinary finite reference factory satisfies all three reached guard checkpoints. -/
theorem discriminator_error_is_admitted :
    AnchorLoadingOwned.Admission .shared types
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) args := by
  change True ∧ AnchorLoadingOwned.FactoryReady types
    (during, AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ .discriminatorMismatch
  refine ⟨trivial, ?_⟩
  constructor
  · rintro outcome ⟨inner, called, inserted⟩
    change .returned nameBuilt.1 nameBuilt.2 = inner at called
    cases called
    cases inserted
    exact ⟨_, rfl⟩
  · rintro name afterName ⟨inner, called, inserted⟩
    change .returned nameBuilt.1 nameBuilt.2 = inner at called
    cases called
    cases inserted
    rintro outcome ⟨message, formatted, inserted⟩
    change .returned messageBuilt.1 messageBuilt.2 = message at formatted
    cases formatted
    cases inserted
    exact ⟨_, rfl⟩
  · rintro name afterName ⟨inner, called, inserted⟩
    change .returned nameBuilt.1 nameBuilt.2 = inner at called
    cases called
    cases inserted
    rintro message afterMessage ⟨innerMessage, formatted, inserted⟩
    change .returned messageBuilt.1 messageBuilt.2 = innerMessage at formatted
    cases formatted
    cases inserted
    rintro outcome ⟨box, allocated, inserted⟩
    change .returned built.1.resource built.2 = box at allocated
    cases allocated
    cases inserted
    exact ⟨_, rfl⟩

/-- A focused reference allocation followed by an illicit release of the guard of the caller.
The message and Box providers remain the original reference providers. -/
def consumingCopy : Callback.Run (AnchorAccount.World AnchorErrorOwned.Reference.State)
    String AnchorErrorOwned.Reference.StringId Empty AnchorErrorOwned.Reference.Failure :=
  Callback.ofFunction fun before text =>
    match AnchorErrorOwned.Reference.allocateString false before.2 text with
    | .returned value after => .returned value ((Borrow.release before.1 ⟨0, 0⟩).2, after)
    | .unwound impossible _ => nomatch impossible
    | .terminated reason => .terminated reason

/-- Only the name provider is changed; the remaining real allocations can finish. -/
def consumingTypes : AnchorLoadingOwned.Types :=
  { types with errors := { types.errors with copyLiteral := consumingCopy } }

/-- The bad provider has a finite normal return with an allocated String and retired token. -/
theorem consuming_name_has_finite_return :
    consumingCopy (during, AnchorOwnedSamples.auxiliary) code.name
      (.returned nameBuilt.1 (released, nameBuilt.2)) ∧
      released.resolve ⟨0, 0⟩ = none := ⟨rfl, rfl⟩

/-- Message and Box allocation actually finish after the guard-consuming name return. -/
theorem consuming_factory_finishes :
    AnchorLoadingOwned.code consumingTypes .discriminatorMismatch
      (during, AnchorOwnedSamples.auxiliary) () (.returned built.1 (released, built.2)) := by
  refine ⟨.returned built.1 (released, built.2), ?_, rfl⟩
  apply (AnchorErrorOwned.buildCode_returned_iff _ _ _ _ _).2
  exact ⟨nameBuilt.1, (released, nameBuilt.2), messageBuilt.1, (released, messageBuilt.2),
    rfl, ⟨.returned messageBuilt.1 messageBuilt.2, rfl, rfl⟩,
    ⟨.returned built.1.resource built.2, rfl, rfl⟩⟩

/-- Every finite factory exit in this concrete fixture is that completed owned error. -/
theorem consuming_factory_unique
    (outcome : Outcome (AnchorAccount.World consumingTypes.Aux)
      (AnchorLoadingOwned.Error consumingTypes) AnchorAccount.LoadPanic
      (AnchorLoadingOwned.Terminal consumingTypes))
    (called : AnchorLoadingOwned.code consumingTypes .discriminatorMismatch
      (during, AnchorOwnedSamples.auxiliary) () outcome) :
    outcome = .returned built.1 (released, built.2) := by
  obtain ⟨original, ⟨first, copied, rest⟩, lifted⟩ := called
  change .returned nameBuilt.1 (released, nameBuilt.2) = first at copied
  cases copied
  obtain ⟨second, ⟨inner, formatted, inserted⟩, last⟩ := rest
  change .returned messageBuilt.1 messageBuilt.2 = inner at formatted
  cases formatted
  cases inserted
  obtain ⟨third, ⟨innerBox, allocated, inserted⟩, mapped⟩ := last
  change .returned built.1.resource built.2 = innerBox at allocated
  cases allocated
  cases inserted
  cases mapped
  exact lifted

/-- The full raw factory exists, but its real checked cleanup has no finite load outcome. -/
theorem consuming_factory_has_no_load
    (outcome : Outcome (AnchorAccount.World consumingTypes.Aux)
      (AnchorLoadingOwned.Result consumingTypes) AnchorAccount.LoadPanic
      (AnchorLoadingOwned.Terminal consumingTypes)) :
    ¬ AnchorLoadingOwned.run .shared consumingTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) args outcome := by
  intro called
  change AnchorEffects.withGuard ⟨0, 0⟩
    (Callback.map Except.error (AnchorLoadingOwned.code consumingTypes .discriminatorMismatch))
    (during, AnchorOwnedSamples.auxiliary) () outcome at called
  obtain ⟨pending, ⟨factoryExit, factory, mapped⟩, cleanup⟩ := called
  have equal := consuming_factory_unique factoryExit factory
  cases equal
  cases mapped
  change none = some outcome at cleanup
  cases cleanup

/-- Admission sees the bad name return directly instead of losing it at later cleanup. -/
theorem consuming_factory_rejected :
    ¬ AnchorLoadingOwned.Admission .shared consumingTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) args := by
  intro admitted
  have factory : AnchorLoadingOwned.FactoryReady consumingTypes
      (during, AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ .discriminatorMismatch := admitted.2
  obtain ⟨slot, live⟩ := factory.name (.returned nameBuilt.1 (released, nameBuilt.2)) rfl
  change none = some slot at live
  cases live

/-- The same actual call may preserve or consume the held guard. -/
def alternativeTypes : AnchorLoadingOwned.Types :=
  { types with
    errors := { types.errors with
      copyLiteral := fun before text outcome =>
        types.errors.copyLiteral before text outcome ∨ consumingCopy before text outcome } }

/-- The good alternative still supplies a complete raw load and actual final cleanup. -/
theorem alternative_good_load_retained :
    AnchorLoadingOwned.run .shared alternativeTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) args
      (.returned (.error built.1) (released, built.2)) := by
  change AnchorEffects.withGuard ⟨0, 0⟩
    (Callback.map Except.error (AnchorLoadingOwned.code alternativeTypes .discriminatorMismatch))
    (during, AnchorOwnedSamples.auxiliary) () (.returned (.error built.1) (released, built.2))
  refine ⟨.returned (.error built.1) (during, built.2), ?_, rfl⟩
  refine ⟨.returned built.1 (during, built.2), ?_, rfl⟩
  refine ⟨.returned built.1 (during, built.2), ?_, rfl⟩
  apply (AnchorErrorOwned.buildCode_returned_iff _ _ _ _ _).2
  exact ⟨nameBuilt.1, (during, nameBuilt.2), messageBuilt.1, (during, messageBuilt.2),
    Or.inl ⟨.returned nameBuilt.1 nameBuilt.2, rfl, rfl⟩,
    ⟨.returned messageBuilt.1 messageBuilt.2, rfl, rfl⟩,
    ⟨.returned built.1.resource built.2, rfl, rfl⟩⟩

/-- One good raw load does not discharge universal admission of the bad alternative. -/
theorem alternative_bad_return_rejects_admission :
    ¬ AnchorLoadingOwned.Admission .shared alternativeTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) args := by
  intro admitted
  have factory : AnchorLoadingOwned.FactoryReady alternativeTypes
      (during, AnchorOwnedSamples.auxiliary) ⟨0, 0⟩ .discriminatorMismatch := admitted.2
  obtain ⟨slot, live⟩ := factory.name (.returned nameBuilt.1 (released, nameBuilt.2)) (Or.inr rfl)
  change none = some slot at live
  cases live

/-- A reached terminal name allocation is admitted without a fictitious post-state. -/
theorem held_allocation_terminal_admitted :
    AnchorLoadingOwned.Admission .shared types (AccountInfo.sampleState, exhausted) args ∧
      AnchorLoadingOwned.run .shared types (AccountInfo.sampleState, exhausted) args
        (.terminated (.inr (.allocation .name))) := by
  refine ⟨?_, held_error_allocation_terminal⟩
  change True ∧ AnchorLoadingOwned.FactoryReady types (during, exhausted)
    ⟨0, 0⟩ .discriminatorMismatch
  refine ⟨trivial, ?_⟩
  constructor
  · rintro outcome ⟨inner, called, lifted⟩
    change .terminated (.allocation .name) = inner at called
    cases called
    cases lifted
    trivial
  · rintro name afterName ⟨inner, called, lifted⟩
    change .terminated (.allocation .name) = inner at called
    cases called
    cases lifted
  · rintro name afterName ⟨inner, called, lifted⟩
    change .terminated (.allocation .name) = inner at called
    cases called
    cases lifted

/-- Deliberately unusable mapping parameters are irrelevant to an earlier rejection. -/
def unusedLayoutTypes : AnchorLoadingOwned.Types :=
  { types with layout := { types.layout with byteSize := 2^64, alignment := 0 } }

/-- This input selects actual lamports as data and has an unrelated zero-width profile. -/
def wrongDataArgs : AnchorAccount.LoadArgs unusedLayoutTypes.layout :=
  ⟨⟨0, false⟩, ⟨{ AccountInfo.sampleInfo with data := AccountInfo.sampleInfo.lamports }⟩, 0⟩

/-- A successful borrow of lamports is rejected by both loading admissions and raw reads. -/
theorem selected_lamports_success_rejected :
    (AccountInfo.tryBorrow .shared wrongDataArgs.loader.info.data AccountInfo.sampleState).1 =
      .ok ⟨0, 0⟩ ∧
    ¬ AnchorAccount.LoadReady .shared AccountInfo.sampleState wrongDataArgs ∧
    ¬ AnchorLoadingOwned.Admission .shared unusedLayoutTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) wrongDataArgs ∧
    AnchorAccount.load .shared unusedLayoutTypes.layout AccountInfo.sampleState wrongDataArgs =
      none ∧
    ∀ outcome, ¬ AnchorLoadingOwned.run .shared unusedLayoutTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) wrongDataArgs outcome :=
  ⟨rfl, (fun impossible => impossible), (fun impossible => impossible.1), rfl,
    fun _ impossible => impossible⟩

/-- Writable rejection precedes the wrong-content read and every invalid mapping parameter. -/
theorem wrong_data_writable_error_retained :
    AnchorLoadingOwned.Admission .exclusive unusedLayoutTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) wrongDataArgs ∧
    AnchorLoadingOwned.run .exclusive unusedLayoutTypes
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) wrongDataArgs
      (.returned (.error notMutableBuilt.1) (AccountInfo.sampleState, notMutableBuilt.2)) := by
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  refine ⟨.returned notMutableBuilt.1 (AccountInfo.sampleState, notMutableBuilt.2), ?_, rfl⟩
  refine ⟨.returned notMutableBuilt.1 (AccountInfo.sampleState, notMutableBuilt.2), ?_, rfl⟩
  exact AnchorErrorOwned.buildCode_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
    (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary)
    notMutableCode notMutableBuilt.1 notMutableBuilt.2
    (AnchorErrorOwned.Reference.buildCode_returns AnchorOwnedSamples.auxiliary
      notMutableCode (by decide))

/-- An actual exclusive lease conflicts with the forthcoming shared acquisition. -/
def lamportsBusy :=
  (AccountInfo.tryBorrow .exclusive AccountInfo.sampleInfo.lamports AccountInfo.sampleState).2

/-- Borrow failure still constructs its real owned ProgramError Box. -/
def borrowFailureBuilt :=
  AnchorErrorOwned.Reference.fromProgramResult AnchorOwnedSamples.auxiliary .accountBorrowFailed

/-- The same wrong-content selection is admitted when its actual borrow already fails. -/
theorem conflicting_borrow_error_retained :
    AccountInfo.tryBorrow .shared wrongDataArgs.loader.info.data lamportsBusy =
      (.error .accountBorrowFailed, lamportsBusy) ∧
    AnchorAccount.LoadReady .shared lamportsBusy wrongDataArgs ∧
    AnchorLoadingOwned.Admission .shared unusedLayoutTypes
      (lamportsBusy, AnchorOwnedSamples.auxiliary) wrongDataArgs ∧
    AnchorLoadingOwned.run .shared unusedLayoutTypes
      (lamportsBusy, AnchorOwnedSamples.auxiliary) wrongDataArgs
      (.returned (.error borrowFailureBuilt.1) (lamportsBusy, borrowFailureBuilt.2)) := by
  refine ⟨rfl, trivial, ⟨trivial, trivial⟩, ?_⟩
  refine ⟨.returned borrowFailureBuilt.1 (lamportsBusy, borrowFailureBuilt.2), ?_, rfl⟩
  refine ⟨.returned borrowFailureBuilt.1 (lamportsBusy, borrowFailureBuilt.2), ?_, rfl⟩
  exact AnchorErrorOwned.fromProgram_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
    (lamportsBusy, AnchorOwnedSamples.auxiliary) .accountBorrowFailed
    borrowFailureBuilt.1 borrowFailureBuilt.2
    (AnchorErrorOwned.Reference.fromProgram_returns AnchorOwnedSamples.auxiliary
      .accountBorrowFailed (by decide))

/-- The successful mapping transfers the actual data guard to its bounded projection. -/
def mappedState := (Borrow.transfer during ⟨0, 0⟩ (.bytesRange 1 2)).2

/-- The mapped result reads real bytes and the input generation has been consumed. -/
theorem mapped_success_reads_current_bytes :
    AnchorLoadingOwned.Admission .shared AnchorOwnedSamples.loading
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AnchorAccount.loadSampleArgs ∧
    AnchorLoadingOwned.run .shared AnchorOwnedSamples.loading
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AnchorAccount.loadSampleArgs
      (.returned (.ok ⟨⟨0, 1⟩⟩) (mappedState, AnchorOwnedSamples.auxiliary)) ∧
    mappedState.resolve ⟨0, 0⟩ = none ∧
    Borrow.deref AccountInfo.projectBytes mappedState ⟨0, 1⟩ =
      (.ok (.ok [20, 30]), mappedState) := ⟨⟨trivial, trivial⟩, rfl, rfl, rfl⟩

/-- Each existing mapping-panic cause has a concrete fixture after a matching prefix. -/
def panicTypes (reason : AnchorAccount.LoadPanic) : AnchorLoadingOwned.Types :=
  { AnchorOwnedSamples.loading with layout := match reason with
    | .lengthOverflow => { AnchorAccount.loadSample with byteSize := 2^64 }
    | .sliceBounds => { AnchorAccount.loadSample with byteSize := 3 }
    | .castAlignment => { AnchorAccount.loadSample with alignment := 2 } }

/-- The profile selects the existing unwind or abort path at the reached local panic. -/
def panicArgs (reason : AnchorAccount.LoadPanic) (aborts : Bool) :
    AnchorAccount.LoadArgs (panicTypes reason).layout :=
  ⟨{ AccountInfo.sampleProfile with aborts }, ⟨AnchorAccount.loadSampleArgs.loader.info⟩, 8⟩

/-- Overflow, slice and alignment panics remain admitted: unwind cleans up, abort has no state. -/
theorem mapping_panics_remain_outcomes (reason : AnchorAccount.LoadPanic) (aborts : Bool) :
    AnchorLoadingOwned.Admission .shared (panicTypes reason)
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) (panicArgs reason aborts) ∧
    AnchorLoadingOwned.run .shared (panicTypes reason)
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) (panicArgs reason aborts)
      (if aborts then .terminated (.inl reason)
       else .unwound reason (released, AnchorOwnedSamples.auxiliary)) := by
  cases reason <;> cases aborts <;> exact ⟨⟨trivial, trivial⟩, rfl⟩

end SolanalibTest.Specs.AnchorLang.OwnedLoading
