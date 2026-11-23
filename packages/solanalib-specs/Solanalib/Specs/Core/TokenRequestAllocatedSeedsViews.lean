/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsFailures

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds.Witness

/-- A packed seed requesting two instruction bytes from the one-byte control input. -/
def boundsConfig : Solanalib.Runtime.Pubkey := .ofBytes [2, 0, 2]
/-- The initial state of the instruction-data bounds-error control. -/
def boundsInitial : State := start boundsConfig
/-- The bounds-error control after empty seed-vector construction. -/
def boundsEmpty : State := afterEmpty boundsInitial
/-- The bounds-error control with its decoded instruction-data seed in the owning vector. -/
def boundsSeed : State := seedsHook (.push 0 (.instructionData 0 2)) boundsEmpty
  (seedsFocus.set boundsEmpty [some [.instructionData 0 2]])
/-- The bounds-error control after empty borrowed-view vector construction. -/
def boundsRefs : State := afterRefsEmpty boundsSeed
/-- The bounds-error state after retiring the borrowed-view vector. -/
def boundsRefsCleaned : State := afterRefsDrop boundsRefs
/-- The ordinary bounds-error state after both vector owners have been retired. -/
def boundsFinal : State := afterSeedsDrop boundsRefsCleaned [.instructionData 0 2]

theorem bounds_unpack_full :
    unpack ops double (fun state => (args.extraAt state).map (·.configuration)) boundsInitial ()
      (.returned (.ok 0) boundsSeed) := by
  refine ⟨boundsConfig, rfl, .returned (.ok ()) boundsSeed, ?_, rfl⟩
  rw [unpackFrom]
  refine ⟨boundsConfig, rfl, .returned (.ok (.instructionData 0 2)) boundsEmpty, rfl, 3, rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  refine ⟨.returned () boundsSeed, ⟨[], rfl, rfl⟩, ?_⟩
  change unpackFrom ops (fun state => (args.extraAt state).map (·.configuration))
    0 3 boundsSeed (.returned (.ok ()) boundsSeed)
  rw [unpackFrom]
  exact ⟨boundsConfig, rfl, .returned (.ok .uninitialized) boundsSeed, rfl, 0, rfl, rfl⟩

theorem bounds_reference_loop : pushViewsFrom ops args instructionView 0 0 1 0 boundsRefs
    (.returned (.error Hook.instructionDataTooSmall) boundsRefs) := by
  rw [pushViewsFrom]
  refine ⟨[.instructionData 0 2], rfl, rfl, .instructionData 0 2, rfl, ?_⟩
  exact ⟨.returned (.error Hook.instructionDataTooSmall) boundsRefs, ⟨[4], rfl, rfl⟩, rfl⟩

theorem bounds_pda_full : resolvePda ops double (pureFind crypto panic) args instructionView
  args.programAt
    0 boundsSeed () (.returned (.error Hook.instructionDataTooSmall) boundsRefsCleaned) := by
  refine ⟨[.instructionData 0 2], rfl,
    .returned (.error Hook.instructionDataTooSmall) boundsRefs, ?_, ?_⟩
  · exact ⟨.returned (.error Hook.instructionDataTooSmall) boundsRefs, bounds_reference_loop, rfl⟩
  · exact ⟨.returned () boundsRefsCleaned, ⟨[], rfl, rfl⟩, rfl⟩

/-- An ordinary error inside the PDA helper cleans its own reference vector
and then the outer seed vector; the search and final metadata copy are skipped. -/
theorem bounds_resolve_full : resolve ops double (pureFind crypto panic) args boundsInitial ()
    (.returned (.error Hook.instructionDataTooSmall) boundsFinal) := by
  refine ⟨boundsInitial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt boundsInitial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt boundsInitial = some instruction ∧ _
  refine ⟨[4], rfl, .returned (.ok 0) boundsSeed, bounds_unpack_full, ?_⟩
  refine ⟨.returned (.error Hook.instructionDataTooSmall) boundsRefsCleaned, ?_, ?_⟩
  · exact ⟨.returned (.error Hook.instructionDataTooSmall) boundsRefsCleaned, bounds_pda_full, rfl⟩
  · exact ⟨.returned () boundsFinal, ⟨[.instructionData 0 2], rfl, rfl⟩, rfl⟩

theorem bounds_cleanup_order :
    boundsFinal.1.bytes = [] ∧ boundsFinal.1.seeds = [none] ∧ boundsFinal.2 = [none] ∧
    boundsFinal.1.events = [.seedsEmpty, .seedPushed (.instructionData 0 2), .refsEmpty,
      .refsDropped, .seedsDropped] := ⟨rfl, rfl, rfl, rfl⟩

/-- A retained one-byte instruction-data subslice in the data component. -/
def instructionBorrow : BytesView Data :=
  (⟨1, fun data => some data.instruction⟩ : BytesView Data).slice 0 1

/-- The state after pushing the instruction view and applying the reference-hook effects. -/
def instructionAfterPush : State := refsHook (.push 0 instructionBorrow) refsState
  (refsState.1, refsState.2.set 0 (some [instructionBorrow]))

theorem instruction_view_created : seedView ops args instructionView (.instructionData 0 1)
    refsState () (.returned (.ok (some (liftView instructionBorrow))) refsState) :=
  ⟨[4], rfl, rfl⟩

theorem instruction_view_pushed : ops.refs.push refsState (0, liftView instructionBorrow)
    (.returned () instructionAfterPush) := ⟨instructionBorrow, rfl, [], rfl, rfl⟩

/-- The slice extent is retained but its bytes come from the actual state
returned by the checked push callback, rather than the earlier value 4. -/
theorem instruction_view_live :
    readViews refsState [liftView instructionBorrow] = some [[4]] ∧
    readViews instructionAfterPush [liftView instructionBorrow] = some [[6]] := ⟨rfl, rfl⟩

/-- An account-view control with one present key, two data bytes and an empty reference vector. -/
def accountBefore : State :=
  ({ extra := ⟨1, .zero, false, false⟩, accounts := [(repeatedKey 3, some [1, 2])] }, [some []])

/-- A retained one-byte subslice whose account-data parent retains its two-byte extent. -/
def accountDataBorrow : BytesView Data :=
  (⟨2, fun data => data.accounts[0]?.bind (·.2)⟩ : BytesView Data).slice 0 1

/-- A retained full-width view of the first account key. -/
def accountKeyBorrow : BytesView Data :=
  ⟨32, fun data => (data.accounts[0]?.bind (fun account => some account.1)).map (·.bytes)⟩

/-- A sample push hook that changes current account observations to test state-sensitive reads. -/
def accountHook (step : Step (BytesView Data)) (_ : State) (after : State) : State :=
  match step with
  | .push _ _ => record .refPushed
      ({ after.1 with accounts := [(repeatedKey 4, some [8, 9])] }, after.2)
  | _ => after

/-- The normal borrowed-view provider with the account-observation hook. -/
def accountRefsOps : Owned.VectorOps State (BytesView State) Nat Unwind Terminal :=
  mapElements (ledger Owned.Focus.snd accountHook) liftView

theorem accountRefsOps_laws : accountRefsOps.Laws := by
  apply mapElements_laws
  apply ledger_laws
  intro step before after
  cases step <;> rfl

/-- The actual sample state after pushing the retained account-data view. -/
def accountDataAfter : State := accountHook (.push 0 accountDataBorrow) accountBefore
  (accountBefore.1, [some [accountDataBorrow]])

/-- The actual sample state after pushing the retained account-key view. -/
def accountKeyAfter : State := accountHook (.push 0 accountKeyBorrow) accountBefore
  (accountBefore.1, [some [accountKeyBorrow]])

theorem account_data_view_created : seedView ops args instructionView (.accountData 0 0 1)
    accountBefore () (.returned (.ok (some (liftView accountDataBorrow))) accountBefore) :=
  ⟨[(repeatedKey 3, some [1, 2])], rfl, rfl⟩

theorem account_key_view_created : seedView ops args instructionView (.accountKey 0)
    accountBefore () (.returned (.ok (some (liftView accountKeyBorrow))) accountBefore) :=
  ⟨[(repeatedKey 3, some [1, 2])], rfl, rfl⟩

theorem account_data_view_pushed : accountRefsOps.push accountBefore (0, liftView accountDataBorrow)
    (.returned () accountDataAfter) := ⟨accountDataBorrow, rfl, [], rfl, rfl⟩

theorem account_key_view_pushed : accountRefsOps.push accountBefore (0, liftView accountKeyBorrow)
    (.returned () accountKeyAfter) := ⟨accountKeyBorrow, rfl, [], rfl, rfl⟩

/-- Both account references follow the actual provider state while preserving
their selected index and slice extent. Rust reference identity is an explicit
source-binding obligation beyond this mathematical state-sensitivity check. -/
theorem account_views_live :
    readViews accountBefore [liftView accountDataBorrow] = some [[1]] ∧
    readViews accountDataAfter [liftView accountDataBorrow] = some [[8]] ∧
    readViews accountBefore [liftView accountKeyBorrow] = some [(repeatedKey 3).bytes] ∧
    readViews accountKeyAfter [liftView accountKeyBorrow] = some [(repeatedKey 4).bytes] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The account-selection control with a present key but absent data observation. -/
def missingData : State :=
  ({ accountBefore.1 with accounts := [(repeatedKey 3, none)] }, accountBefore.2)

/-- The account-selection control with present but empty data. -/
def shortData : State :=
  ({ accountBefore.1 with accounts := [(repeatedKey 3, some [])] }, accountBefore.2)

theorem account_selection_errors :
    seedView ops args instructionView (.accountKey 0) initial ()
      (.returned (.error Hook.accountNotFound) initial) ∧
    seedView ops args instructionView (.accountData 0 0 1) initial ()
      (.returned (.error Hook.accountNotFound) initial) ∧
    seedView ops args instructionView (.accountData 0 0 1) missingData ()
      (.returned (.error Hook.accountDataNotFound) missingData) ∧
    seedView ops args instructionView (.accountData 0 0 1) shortData ()
      (.returned (.error Hook.accountDataTooSmall) shortData) :=
  ⟨⟨[], rfl, rfl⟩, ⟨[], rfl, rfl⟩,
    ⟨[(repeatedKey 3, none)], rfl, rfl⟩, ⟨[(repeatedKey 3, some [])], rfl, rfl⟩⟩

/-- Absent or length-changing retained views reject a source representation;
they never become a new ordinary ProgramError or a search panic. -/
theorem search_no_exit_without_views (before : State) (views : List (BytesView State))
    (current : ops.refs.current before 0 = some views) (missing : readViews before views = none) :
    ∀ outcome, ¬ searchPda ops (pureFind crypto panic) args.programAt 0 before () outcome := by
  rintro outcome ⟨actual, values, program, observed, read, programObserved, result⟩
  have same : actual = views := Option.some.inj (observed.symm.trans current)
  subst actual
  rw [missing] at read
  cases read

/-- A state whose retained literal reference no longer has represented contents. -/
def missingLiteral : State :=
  ({ pushedState.1 with bytes := [none] }, pushedState.2)

/-- A state whose literal contents no longer match the retained slice extent. -/
def resizedLiteral : State :=
  ({ pushedState.1 with bytes := [some [9, 10]] }, pushedState.2)

theorem missing_literal_has_no_search_exit :
    ∀ outcome, ¬ searchPda ops (pureFind crypto panic) args.programAt 0 missingLiteral () outcome :=
  search_no_exit_without_views missingLiteral [liftView literalView] rfl rfl

theorem resized_literal_has_no_search_exit :
    ∀ outcome, ¬ searchPda ops (pureFind crypto panic) args.programAt 0 resizedLiteral () outcome :=
  search_no_exit_without_views resizedLiteral [liftView literalView] rfl rfl

/-- The remaining pure tag decoders retain exact byte fields and error codes. -/
theorem ordinary_seed_decoders :
    unpackOne ops.bytes [2, 4, 5] initial () (.returned (.ok (.instructionData 4 5)) initial) ∧
    unpackOne ops.bytes [3, 6] initial () (.returned (.ok (.accountKey 6)) initial) ∧
    unpackOne ops.bytes [4, 7, 8, 9] initial () (.returned (.ok (.accountData 7 8 9)) initial) ∧
    unpackOne ops.bytes [1, 2, 7] initial () (.returned (.error Hook.invalidSeedBytes) initial) ∧
    unpackOne ops.bytes [2, 4] initial () (.returned (.error Hook.invalidSeedBytes) initial) ∧
    unpackOne ops.bytes [3] initial () (.returned (.error Hook.invalidSeedBytes) initial) ∧
    unpackOne ops.bytes [4, 7, 8] initial () (.returned (.error Hook.invalidSeedBytes) initial) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solanalib.Specs.Core.Token.AllocatedSeeds.Witness
