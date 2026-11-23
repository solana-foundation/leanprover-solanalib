/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.TokenAllocatedGuards
public import SolanalibTest.Specs.Core.TokenAllocatedCollect
public import SolanalibTest.Specs.Core.TokenAllocatedPdaAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedInputs

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.AllocatedGuard

/-- Before the first guard, an allocator can corrupt the source cell kind
without violating a law that quantifies only already live guards. -/
def corruptState {Extra : Type} (before : World Extra) : World Extra :=
  if before.1.slots = [] then
    ((Borrow.replaceCell before.1 ⟨1⟩ (.lamports 77)).2, before.2)
  else before

/-- The bad primitive has an actual finite return, rather than an empty relation. -/
def corrupt {Extra Args Value : Type} (value : Value) :
    Callback.Run (World Extra) Args Value Nat Nat :=
  fun before _ outcome => outcome = .returned value (corruptState before)

/-- Live-guard-only admission misses this entire zero-guard corruption class. -/
theorem corrupt_passes_guard_only {Extra Args Value : Type} (value : Value) :
    Preserves (corrupt (Extra := Extra) (Args := Args) value) := by
  intro before args valid guard slot live absent outcome called
  by_cases empty : before.1.slots = []
  · have impossible : before.1.resolve guard = none := by
      simp [Borrow.State.resolve, Borrow.State.lookupSlot, empty]
    rw [impossible] at live
    cases live
  · change outcome = .returned value (corruptState before) at called
    simp only [corruptState, empty, ↓reduceIte] at called
    cases called
    exact AccountInfo.GuardCallback.StateFrame.refl _ _ valid

/-- The actual corrupted world still has a data-cell identity but wrong type. -/
def corrupted : World Nat :=
  ((Borrow.replaceCell AccountInfo.sampleState ⟨1⟩ (.lamports 77)).2, 0)

/-- The ordinary return of the bad allocation occurs before any data guard exists. -/
theorem corrupt_returns : corrupt () ((AccountInfo.sampleState, 0) : World Nat) ()
    (.returned () corrupted) := rfl

/-- Input preservation rejects that actual exit independently of future code. -/
theorem corrupt_input_rejected : ¬ InputPreserves 64 (corrupt (Extra := Nat) (Args := Unit) ()) :=
  by
  intro law
  have frame := law (AccountInfo.sampleState, 0) () AccountInfo.sample_valid.2.1 _ corrupt_returns
  obtain ⟨next, found, _, shape⟩ := frame.cells ⟨1⟩
    ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩ rfl
  change some ⟨.lamports 77, AccountInfo.sampleProfile.policy⟩ = some next at found
  cases found
  exact shape

/-- A malformed cell does not produce a fabricated local borrow error or value. -/
theorem corrupt_next_borrow_disappears : ∀ outcome,
    ¬ AllocatedControl.borrow (fun (_ : World Nat) (_ : Onchain.Panic)
      (_ : Outcome (World Nat) Empty Nat Nat) => False) true AccountInfo.sampleInfo corrupted
        outcome := by
  intro _ impossible
  exact False.elim impossible

/-- Replace the actually called instruction capacity allocator by that provider. -/
def badTypes : OnchainAllocated.Types :=
  { OnchainAllocated.Witness.sampleTypes with
    bytes := { OnchainAllocated.Witness.sampleTypes.bytes with
      withCapacity := corrupt (0 : Nat) } }

/-- The same collector and opaque invocation interpretations fit the index
whose capacity callback was changed; no source readiness is assumed here. -/
def badDependencies : OnchainAllocated.Dependencies badTypes :=
  { collect := OnchainAllocated.Witness.sampleDependencies.collect
    invoke := OnchainAllocated.Witness.sampleDependencies.invoke }

/-- The family rejects this actual corrupting return before its later borrow.
Only selected data typing is needed; no scalar or length bound is restored. -/
theorem corrupt_family_entry_rejected :
    ¬ (OnchainAllocated.family.contract ⟨badTypes, badDependencies⟩).requires
      OnchainAllocated.Witness.initialState Onchain.witnessArgs := by
  rintro ⟨_, ready, _⟩
  have preserved := (ready.primitive .bytesCapacity).2
    ((AccountInfo.sampleState, {}) : OnchainAllocated.Witness.State) 0
    AccountInfo.sample_valid.2.1 _ (by rfl)
  obtain ⟨bytes, policy, found⟩ := preserved.2 ⟨1⟩
    ⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩
  change some (⟨.lamports 77, AccountInfo.sampleProfile.policy⟩ : Borrow.Cell AccountInfo.Content) =
    some ⟨.data bytes, policy⟩ at found
  cases found

/-- The admitted family also rejects a real successful PDA reply whose
address output is absent, before the unchanged decoder reads it. -/
theorem pda_family_entry_rejected :
    ¬ (OnchainAllocated.family.contract
      ⟨TokenAllocatedPdaAdmission.badTypes,
        ⟨OnchainAllocated.Witness.sampleDependencies.collect,
          OnchainAllocated.Witness.sampleDependencies.invoke⟩⟩).requires
      OnchainAllocated.Witness.initialState Onchain.witnessArgs := by
  rintro ⟨_, ready, _⟩
  exact TokenAllocatedPdaAdmission.uninitialized_success_rejected.2 ready.pdaReady

/-- A permitted current data change also grows the unborrowed slice. -/
def grownAccounts : AccountInfo.State :=
  (Borrow.replaceCell AccountInfo.sampleState ⟨1⟩ (.data [2, 4, 6, 8])).2

/-- An actual stateful callback interpretation on that represented input. -/
def grows : Callback.Run (World Nat) Unit Unit Nat Nat := fun before _ outcome =>
  before.1 = AccountInfo.sampleState ∧
    outcome = .returned () (grownAccounts, before.2 + 7)

/-- The new typing law permits changed unborrowed values and bounded lengths. -/
theorem grows_input_admitted : InputPreserves 64 grows := by
  rintro before args valid outcome ⟨same, returned⟩
  cases returned
  change InputFrame 64 before.1 grownAccounts
  rw [same]
  exact InputFrame.replace AccountInfo.sample_valid.2.1
    (show AccountInfo.sampleState.lookupCell ⟨1⟩ =
      some ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩ from rfl)
    (.data [2, 4, 6, 8]) ⟨fun _ => by decide, fun _ => by decide⟩

/-- No guard is live on the admitted input of this provider, so the independent
held-footprint law does not prohibit its current unborrowed mutation. -/
theorem grows_guard_admitted : Preserves grows := by
  rintro before args valid guard slot live absent outcome ⟨same, _⟩
  have impossible : before.1.resolve guard = none := by
    rw [same]
    simp [Borrow.State.resolve, Borrow.State.lookupSlot, AccountInfo.sampleState]
  rw [impossible] at live
  cases live

/-- Both the data change and auxiliary effect are realized by a finite exit. -/
theorem grows_returns : grows (AccountInfo.sampleState, 0) ()
    (.returned () (grownAccounts, 7)) := ⟨rfl, rfl⟩

/-- Local primitive admission yields a next real checked-borrow result, without
assuming a complete function exit or termination of any other provider. -/
theorem grows_keeps_next_borrow : ∃ result after,
    AllocatedControl.borrow (fun (_ : World Nat) (_ : Onchain.Panic)
      (_ : Outcome (World Nat) Empty Nat Nat) => False) true AccountInfo.sampleInfo
      (grownAccounts, 7) (.returned result after) :=
  grows_input_admitted.borrow_after _ rfl AccountInfo.sample_valid grows_returns

/-- The next source borrow observes the new data and new length exactly. -/
theorem grows_next_borrow_exact : AllocatedControl.borrow
    (fun (_ : World Nat) (_ : Onchain.Panic)
      (_ : Outcome (World Nat) Empty Nat Nat) => False) true AccountInfo.sampleInfo
    (grownAccounts, 7)
    (.returned (.ok ⟨⟨0, 0⟩, 4⟩)
      ({ grownAccounts with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] }, 7)) := rfl

open AllocatedCollect

/-- Erasing only the guard-vector ledger leaves every AccountInfo cell and
guard intact, but would hide a later resource read or destructor. -/
def erasesLedger : Callback.Run ReferenceWorld Unit Unit Nat Nat :=
  fun before _ outcome => outcome = .returned () (before.1, [])

/-- Guard frames alone admit a pure auxiliary-ledger erasure. -/
theorem erasure_passes_guard_frames : Preserves erasesLedger := by
  apply Preserves.of_accounts
  intro _ _ _ called
  cases called
  rfl

/-- Input typing alone also admits that erasure. -/
theorem erasure_passes_input_frames : InputPreserves 64 erasesLedger := by
  apply InputPreserves.of_accounts
  intro _ _ _ called
  cases called
  rfl

/-- The preceding nonempty vector comes from two actual source acquisitions. -/
theorem before_erasure_collected : referenceProvider.run TokenAllocatedCollect.iterator
    (borrowElement TokenAllocatedCollect.noPanic) (TokenAllocatedCollect.accounts, [])
    (.returned (.ok 0) (TokenAllocatedCollect.afterBoth, [some TokenAllocatedCollect.elements])) :=
  TokenAllocatedCollect.successful_execution

/-- The actual erasure occurs while both acquired reference identities are live. -/
theorem erasure_returns : erasesLedger
    (TokenAllocatedCollect.afterBoth, [some TokenAllocatedCollect.elements]) ()
    (.returned () (TokenAllocatedCollect.afterBoth, [])) := rfl

/-- The unmodified resource destructor has no outcome after storage is erased. -/
theorem erased_vector_cannot_drop : ∀ outcome,
    ¬ referenceVectors.drop (TokenAllocatedCollect.afterBoth, []) 0 outcome := by
  rintro _ ⟨values, impossible, _⟩
  cases impossible

/-- The independent observation law rejects this exact corrupting prefix. -/
theorem erasure_resource_rejected : ¬ Retains referenceVectors.current erasesLedger := by
  intro law
  have impossible := law
    (TokenAllocatedCollect.afterBoth, [some TokenAllocatedCollect.elements]) () 0
    TokenAllocatedCollect.elements rfl _ erasure_returns
  cases impossible

/-- The actual reference collector satisfies the weaker pointwise guard laws,
without fixing the allocation schedule or termination of an arbitrary provider. -/
theorem nonempty_collection_frames : CollectionFrames referenceProtocol := by
  refine ⟨fun _ _ => Preserves.empty, ?_, ?_⟩
  · exact Preserves.focus Owned.Focus.snd (fun _ _ => rfl) Owned.vectorReference.fromList
  · intro acquired
    apply Preserves.of_accounts
    intro _ _ _ called
    cases called
    rfl

/-- Nonempty collection has real element/storage cleanup independently of
removed input-provider gates: both guards retire before the vector slot. -/
theorem nonempty_collection_drop_executes : referenceVectors.drop
    (TokenAllocatedCollect.afterBoth, [some TokenAllocatedCollect.elements]) 0
    (.returned () ({ TokenAllocatedCollect.accounts with slots := [none, none] }, [none])) :=
  TokenAllocatedCollect.successful_vector_drop

/-- Current-value linkage alone also holds for the existing storage-only
vector interpretation, whose destructor does not own the element guards. -/
theorem storage_only_collection_linkage : ResourceLaws referenceProtocol referenceStorage :=
  ⟨reference_resource_laws.finish_current⟩

/-- The storage-only destructor has a real finite exit and retires its slot. -/
theorem storage_only_drop_returns : referenceStorage.drop
    (TokenAllocatedCollect.afterBoth, [some TokenAllocatedCollect.elements]) 0
    (.returned () (TokenAllocatedCollect.afterBoth, [none])) :=
  ⟨.returned () [none], ⟨TokenAllocatedCollect.elements, rfl, rfl⟩, rfl⟩

/-- Unlike the actual owning reference-vector destructor above, storage-only
cleanup leaves both references readable. The finish law does not assert their release. -/
theorem storage_only_keeps_elements :
    TokenAllocatedCollect.firstRef.read
      ((TokenAllocatedCollect.afterBoth, [none]) : ReferenceWorld) = some [37] ∧
    TokenAllocatedCollect.secondRef.read
      ((TokenAllocatedCollect.afterBoth, [none]) : ReferenceWorld) = some [19, 23] := ⟨rfl, rfl⟩

end SolanalibTest.Specs.Core.TokenAllocatedInputs
