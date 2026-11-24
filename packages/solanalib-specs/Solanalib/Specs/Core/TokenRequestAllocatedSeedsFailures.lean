/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds.Witness

/-- An actual unpacking error propagates through the selected outer source
branch without constructing a reference vector. This is a composition lemma,
not an assumption used by the closed controls below. -/
theorem resolve_unpack_error (providers : Ops State Nat Nat Nat Unwind Terminal)
    (configuration : Solanalib.Runtime.Pubkey) (error : Error) (after : State)
    (called : unpack providers double (fun state => (args.extraAt state).map (·.configuration))
      (start configuration) () (.returned (.error error) after)) :
    resolve providers double (pureFind crypto panic) args (start configuration) ()
      (.returned (.error error) after) := by
  refine ⟨_, rfl, ?_⟩
  change ∃ program, args.programAt (start configuration) = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt (start configuration) = some instruction ∧ _
  refine ⟨[4], rfl, ?_⟩
  exact ⟨.returned (.error error) after, called, rfl⟩

theorem resolve_unpack_unwind (providers : Ops State Nat Nat Nat Unwind Terminal)
    (reason : Unwind) (after : State)
    (called : unpack providers double (fun state => (args.extraAt state).map (·.configuration))
      initial () (.unwound reason after)) :
    resolve providers double (pureFind crypto panic) args initial () (.unwound reason after) := by
  refine ⟨_, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, ?_⟩
  exact ⟨.unwound reason after, called, rfl⟩

theorem resolve_unpack_terminal (providers : Ops State Nat Nat Nat Unwind Terminal)
    (reason : Terminal)
    (called : unpack providers double (fun state => (args.extraAt state).map (·.configuration))
      initial () (.terminated reason)) :
    resolve providers double (pureFind crypto panic) args initial () (.terminated reason) := by
  refine ⟨_, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, ?_⟩
  exact ⟨.terminated reason, called, rfl⟩

/-- A valid literal seed followed by an invalid seed tag. -/
def badConfig : Solanalib.Runtime.Pubkey := .ofBytes [1, 1, 7, 255]
/-- The initial state of the malformed-later-seed control. -/
def badInitial : State := start badConfig
/-- The malformed configuration control after empty seed-vector construction. -/
def badEmpty : State := afterEmpty badInitial
/-- The malformed configuration control after constructing its first literal. -/
def badLiteral : State := afterLiteral badEmpty
/-- The malformed configuration control with the first literal owned by the seed vector. -/
def badSeed : State := afterSeedPush badLiteral
/-- The ordinary malformed-seed error state after recursive seed-vector cleanup. -/
def badFinal : State := afterSeedsDrop badSeed [.literal 0]

theorem malformed_unpack_loop :
    unpackFrom ops (fun state => (args.extraAt state).map (·.configuration)) 0 0 badEmpty
      (.returned (.error .InvalidAccountData) badSeed) := by
  rw [unpackFrom]
  refine ⟨badConfig, rfl, .returned (.ok (.literal 0)) badLiteral, ?_, ?_⟩
  · change Callback.map _ _ _ _ _
    exact ⟨.returned 0 badLiteral, rfl, rfl⟩
  · refine ⟨3, rfl, ?_⟩
    change Callback.bind _ _ _ _ _
    refine ⟨.returned () badSeed, ⟨[], rfl, rfl⟩, ?_⟩
    change unpackFrom ops (fun state => (args.extraAt state).map (·.configuration))
      0 3 badSeed (.returned (.error .InvalidAccountData) badSeed)
    rw [unpackFrom]
    exact ⟨badConfig, rfl, .returned (.error .InvalidAccountData) badSeed, rfl, rfl⟩

/-- A later malformed seed drops the previously constructed owning literal
before returning the exact ordinary source error. -/
theorem malformed_unpack_full :
    unpack ops double (fun state => (args.extraAt state).map (·.configuration)) badInitial ()
      (.returned (.error .InvalidAccountData) badFinal) := by
  refine ⟨badConfig, rfl, .returned (.error .InvalidAccountData) badSeed,
    malformed_unpack_loop, ?_⟩
  exact ⟨.returned () badFinal, ⟨[.literal 0], rfl, rfl⟩, rfl⟩

theorem malformed_resolve_full : resolve ops double (pureFind crypto panic) args badInitial ()
    (.returned (.error .InvalidAccountData) badFinal) :=
  resolve_unpack_error ops badConfig .InvalidAccountData badFinal malformed_unpack_full

theorem malformed_cleanup_exact :
    ops.bytes.current badFinal 0 = none ∧ ops.seeds.current badFinal 0 = none ∧
    badFinal.2 = [] ∧
    badFinal.1.events = [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0),
      .literalDropped 0, .seedsDropped] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A provider whose literal construction records an independent unwind. -/
def allocationUnwindOps : Ops State Nat Nat Nat Unwind Terminal :=
  { ops with
    bytes := { ops.bytes with
      fromList := fun before _ outcome =>
        outcome = .unwound .allocation (record .allocationUnwind before) } }

theorem allocationUnwindOps_laws : allocationUnwindOps.Laws := by
  refine ⟨?_, ops_laws.seeds, ops_laws.refs⟩
  refine { ops_laws.bytes with list_current := ?_, list_fresh := ?_ }
  · intro before values resource after impossible
    cases impossible
  · intro before values resource after impossible
    cases impossible

/-- The actual state exposed by the literal-construction unwind. -/
def allocationFailed : State := record .allocationUnwind emptyState
/-- The literal-construction unwind state after cleanup of the still-empty seed vector. -/
def allocationCleaned : State := afterSeedsDrop allocationFailed []

theorem allocation_unpack_loop :
    unpackFrom allocationUnwindOps (fun state => (args.extraAt state).map (·.configuration))
      0 0 emptyState (.unwound .allocation allocationFailed) := by
  rw [unpackFrom]
  refine ⟨literalConfig, rfl, .unwound .allocation allocationFailed, ?_, rfl⟩
  change Callback.map _ _ _ _ _
  exact ⟨.unwound .allocation allocationFailed, rfl, rfl⟩

theorem allocation_unpack_full :
    unpack allocationUnwindOps double (fun state => (args.extraAt state).map (·.configuration))
      initial () (.unwound .allocation allocationCleaned) := by
  refine ⟨literalConfig, rfl, .unwound .allocation allocationFailed, allocation_unpack_loop, ?_⟩
  exact ⟨.returned () allocationCleaned, ⟨[], rfl, rfl⟩, rfl⟩

/-- Literal construction can unwind before seed push. The actual unwind state
is passed to the still-empty seed-vector destructor. -/
theorem allocation_resolve_unwinds : resolve allocationUnwindOps double (pureFind crypto panic) args
    initial () (.unwound .allocation allocationCleaned) :=
  resolve_unpack_unwind allocationUnwindOps .allocation allocationCleaned allocation_unpack_full

theorem allocation_unwind_cleanup_exact :
    allocationCleaned.1.bytes = [] ∧ allocationCleaned.1.seeds = [none] ∧
    allocationCleaned.2 = [] ∧
    allocationCleaned.1.events = [.seedsEmpty, .allocationUnwind, .seedsDropped] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A provider whose literal construction terminates with the current event trace. -/
def allocationTerminalOps : Ops State Nat Nat Nat Unwind Terminal :=
  { ops with
    bytes := { ops.bytes with
      fromList := fun before _ outcome =>
        outcome = .terminated (.abort (before.1.events ++ [.allocationTerminal])) } }

theorem allocationTerminalOps_laws : allocationTerminalOps.Laws := by
  refine ⟨?_, ops_laws.seeds, ops_laws.refs⟩
  refine { ops_laws.bytes with list_current := ?_, list_fresh := ?_ }
  · intro before values resource after impossible
    cases impossible
  · intro before values resource after impossible
    cases impossible

/-- A terminal allocation exit bypasses cleanup, without manufacturing a
post-state or appending destructor events to the supplied terminal reason. -/
theorem allocation_resolve_terminates : resolve allocationTerminalOps double (pureFind crypto
  panic) args
    initial () (.terminated (.abort [.seedsEmpty, .allocationTerminal])) := by
  apply resolve_unpack_terminal
  refine ⟨literalConfig, rfl,
    .terminated (.abort [.seedsEmpty, .allocationTerminal]), ?_, rfl⟩
  rw [unpackFrom]
  refine ⟨literalConfig, rfl, .terminated (.abort [.seedsEmpty, .allocationTerminal]), ?_, rfl⟩
  change Callback.map _ _ _ _ _
  exact ⟨.terminated (.abort [.seedsEmpty, .allocationTerminal]), rfl, rfl⟩

/-- The failing push owns its moved literal argument. It consumes that owner
before exposing its actual unwind state, while leaving the seed vector live. -/
def seedPushUnwindOps : Ops State Nat Nat Nat Unwind Terminal :=
  { ops with
    seeds := { ops.seeds with
      push := fun before (resource, value) outcome =>
        ∃ values, ops.seeds.current before resource = some values ∧
          outcome = .unwound .seedPush (dropLiterals [value] (record .pushUnwind before)) } }

theorem seedPushUnwindOps_laws : seedPushUnwindOps.Laws := by
  refine ⟨ops_laws.bytes, ?_, ops_laws.refs⟩
  refine { ops_laws.seeds with push_current := ?_, push_unwind_live := ?_ }
  · rintro before resource value values after current ⟨actual, observed, impossible⟩
    cases impossible
  · rintro before resource value reason after ⟨values, current⟩ ⟨actual, observed, equal⟩
    cases equal
    refine ⟨values, ?_⟩
    change (dropLiterals [value] (record .pushUnwind before)).1.seeds.current resource = some values
    rw [dropLiterals_seeds]
    exact current

/-- The failed seed push has consumed its moved literal before exposing this unwind state. -/
def pushFailed : State := dropLiterals [.literal 0] (record .pushUnwind literalState)
/-- The seed-push unwind state after cleanup of the remaining empty seed vector. -/
def pushCleaned : State := afterSeedsDrop pushFailed []

theorem moved_literal_unpack_loop :
    unpackFrom seedPushUnwindOps (fun state => (args.extraAt state).map (·.configuration))
      0 0 emptyState (.unwound .seedPush pushFailed) := by
  rw [unpackFrom]
  refine ⟨literalConfig, rfl, .returned (.ok (.literal 0)) literalState, literal_unpack, 3, rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  exact ⟨.unwound .seedPush pushFailed, ⟨[], rfl, rfl⟩, rfl⟩

theorem moved_literal_unpack_full :
    unpack seedPushUnwindOps double (fun state => (args.extraAt state).map (·.configuration))
      initial () (.unwound .seedPush pushCleaned) := by
  refine ⟨literalConfig, rfl, .unwound .seedPush pushFailed, moved_literal_unpack_loop, ?_⟩
  exact ⟨.returned () pushCleaned, ⟨[], rfl, rfl⟩, rfl⟩

theorem moved_literal_resolve_unwinds : resolve seedPushUnwindOps double (pureFind crypto panic)
  args
    initial () (.unwound .seedPush pushCleaned) :=
  resolve_unpack_unwind seedPushUnwindOps .seedPush pushCleaned moved_literal_unpack_full

/-- Cleanup does not redrop the literal moved into the failed push. -/
theorem moved_literal_cleanup_exact :
    pushCleaned.1.bytes = [none] ∧ pushCleaned.1.seeds = [none] ∧ pushCleaned.2 = [] ∧
    pushCleaned.1.events = [.seedsEmpty, .literalAllocated [7], .pushUnwind,
      .literalDropped 0, .seedsDropped] := ⟨rfl, rfl, rfl, rfl⟩

/-- A supporting mathematical interpretation that rejects every candidate address as on-curve. -/
def exhaustedCrypto : Address.Crypto where
  primitives := { sha256 := fun _ => List.replicate 32 0, onCurve := fun _ => true }

set_option maxRecDepth 4096 in
theorem search_exhausted : Address.tryFind ⟨exhaustedCrypto, [[9]], repeatedKey 2⟩ = none := by
  decide

/-- The actual state after the exhausted-search panic has recorded its call. -/
def searchFailed : State := record .searchPanic pushedState
/-- The search-panic unwind state after borrowed-view vector cleanup. -/
def searchRefsCleaned : State := afterRefsDrop searchFailed
/-- The search-panic unwind state after both vector owners and the literal are retired. -/
def searchAllCleaned : State := afterSeedsDrop searchRefsCleaned [.literal 0]

theorem search_unwinds : searchPda ops (pureFind exhaustedCrypto panic) args.programAt 0
  pushedState ()
    (.unwound .search searchFailed) := by
  refine ⟨[liftView literalView], [[9]], repeatedKey 2, rfl, rfl, rfl,
    .unwound .search searchFailed, ?_, rfl⟩
  unfold pureFind
  rw [search_exhausted]
  exact ⟨.unwound .search searchFailed, rfl, rfl⟩

theorem exhausted_pda_full : resolvePda ops double (pureFind exhaustedCrypto panic) args
  instructionView
    args.programAt 0 seedState () (.unwound .search searchRefsCleaned) := by
  refine ⟨[.literal 0], rfl, .unwound .search searchFailed, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, literal_reference_loop, search_unwinds⟩
  · exact ⟨.returned () searchRefsCleaned, ⟨[literalView], rfl, rfl⟩, rfl⟩

/-- Exhaustion is an actual panic dependency call. Its unwind cleans reference
and owning seed vectors in source order and retains the original reason. -/
theorem exhausted_resolve_unwinds : resolve ops double (pureFind exhaustedCrypto panic) args
  initial ()
    (.unwound .search searchAllCleaned) := by
  refine ⟨initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, ?_⟩
  refine ⟨.returned (.ok 0) seedState, literal_unpack_full, ?_⟩
  refine ⟨.unwound .search searchRefsCleaned, ?_, ?_⟩
  · exact ⟨.unwound .search searchRefsCleaned, exhausted_pda_full, rfl⟩
  · exact ⟨.returned () searchAllCleaned, ⟨[.literal 0], rfl, rfl⟩, rfl⟩

theorem search_unwind_cleanup_exact :
    searchAllCleaned.1.bytes = [none] ∧ searchAllCleaned.1.seeds = [none] ∧
    searchAllCleaned.2 = [none] ∧
    searchAllCleaned.1.events = [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0),
      .refsEmpty, .refPushed, .searchPanic, .refsDropped, .literalDropped 0, .seedsDropped] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A provider whose borrowed-view destructor consumes its owner before unwinding. -/
def refsDropUnwindOps : Ops State Nat Nat Nat Unwind Terminal :=
  { ops with
    refs := { ops.refs with
      drop := fun before resource outcome =>
        ∃ after, ops.refs.drop before resource (.returned () after) ∧
          outcome = .unwound .refsDrop after } }

theorem refsDropUnwindOps_laws : refsDropUnwindOps.Laws := by
  refine ⟨ops_laws.bytes, ops_laws.seeds, ?_⟩
  refine { ops_laws.refs with drop_current := ?_, drop_unwind_consumed := ?_ }
  · rintro before resource after live ⟨actual, dropped, impossible⟩
    cases impossible
  · rintro before resource reason after live ⟨actual, dropped, equal⟩
    cases equal
    exact ops_laws.refs.drop_current before resource _ live dropped

theorem double_fixture_unpack_full :
    unpack refsDropUnwindOps double (fun state => (args.extraAt state).map (·.configuration))
      initial () (.returned (.ok 0) seedState) := by
  refine ⟨literalConfig, rfl, .returned (.ok ()) seedState, ?_, rfl⟩
  rw [unpackFrom]
  refine ⟨literalConfig, rfl, .returned (.ok (.literal 0)) literalState, literal_unpack, 3, rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  refine ⟨.returned () seedState, literal_seed_push, ?_⟩
  change unpackFrom refsDropUnwindOps (fun state => (args.extraAt state).map (·.configuration))
    0 3 seedState (.returned (.ok ()) seedState)
  rw [unpackFrom]
  exact ⟨literalConfig, rfl, .returned (.ok .uninitialized) seedState, rfl, 0, rfl, rfl⟩

theorem double_fixture_reference_loop : pushViewsFrom refsDropUnwindOps args instructionView
    0 0 1 0 refsState (.returned (.ok ()) pushedState) := by
  rw [pushViewsFrom]
  refine ⟨[.literal 0], rfl, rfl, .literal 0, rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  refine ⟨.returned (.ok (some (liftView literalView))) refsState, literal_view, ?_⟩
  refine ⟨.returned () pushedState, literal_ref_push, ?_⟩
  change pushViewsFrom refsDropUnwindOps args instructionView 0 0 1 1 pushedState
    (.returned (.ok ()) pushedState)
  rw [pushViewsFrom]
  rfl

/-- The terminal trace and reasons when reference cleanup unwinds during search-panic
unwinding. -/
def doubleReason : Terminal := .double
  [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0), .refsEmpty, .refPushed,
    .searchPanic, .refsDropped] .search .refsDrop

theorem exhausted_pda_double_unwind : resolvePda refsDropUnwindOps double (pureFind exhaustedCrypto
  panic)
    args instructionView args.programAt 0 seedState () (.terminated doubleReason) := by
  refine ⟨[.literal 0], rfl, .unwound .search searchFailed, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, double_fixture_reference_loop, search_unwinds⟩
  · refine ⟨.unwound .refsDrop searchRefsCleaned, ?_, doubleReason, rfl, rfl⟩
    exact ⟨searchRefsCleaned, ⟨[literalView], rfl, rfl⟩, rfl⟩

/-- The second unwind uses the supplied terminal policy with the actual
post-destructor state. The terminal helper result skips the outer seed drop. -/
theorem exhausted_resolve_double_unwind :
    resolve refsDropUnwindOps double (pureFind exhaustedCrypto panic) args initial () (.terminated
      doubleReason) := by
  refine ⟨initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, ?_⟩
  refine ⟨.returned (.ok 0) seedState, double_fixture_unpack_full, ?_⟩
  refine ⟨.terminated doubleReason, ?_, rfl⟩
  exact ⟨.terminated doubleReason, exhausted_pda_double_unwind, rfl⟩

/-- These are observations at the input to the terminal policy, not an
invented post-state of the terminal outcome. Only the reference owner has
been consumed when the second unwind terminates cleanup. -/
theorem double_unwind_policy_input :
    ops.refs.current searchRefsCleaned 0 = none ∧
    ops.bytes.current searchRefsCleaned 0 = some [9] ∧
    ops.seeds.current searchRefsCleaned 0 = some [.literal 0] ∧
    double searchRefsCleaned .search .refsDrop doubleReason := ⟨rfl, rfl, rfl, rfl⟩

end Solanalib.Specs.Core.Token.AllocatedSeeds.Witness
