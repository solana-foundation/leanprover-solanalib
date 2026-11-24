/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsLedger

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds.Witness

/-- Observable calls in the closed mathematical controls. -/
inductive Event where
  /-- The control has constructed the empty owning seed vector. -/
  | seedsEmpty
  /-- The literal-byte dependency has constructed the recorded bytes. -/
  | literalAllocated (bytes : Bytes)
  /-- The owning seed vector has received the recorded seed. -/
  | seedPushed (seed : Seed Nat)
  /-- The control has constructed the empty vector of borrowed views. -/
  | refsEmpty
  /-- The borrowed-view vector has received one retained view. -/
  | refPushed
  /-- Recursive seed cleanup has retired the recorded literal resource. -/
  | literalDropped (resource : Nat)
  /-- The borrowed-view vector has been retired. -/
  | refsDropped
  /-- The owning seed vector has been retired. -/
  | seedsDropped
  /-- Literal construction has entered the unwind control. -/
  | allocationUnwind
  /-- Literal construction has produced the terminal control outcome. -/
  | allocationTerminal
  /-- The owning seed push has entered the unwind control. -/
  | pushUnwind
  /-- The selected address wrapper has invoked the local search panic. -/
  | searchPanic
  /-- The sample address syscall has returned an ordinary reply. -/
  | pdaReturned
  /-- The sample address syscall has unwound independently of mathematical search. -/
  | pdaUnwind
  /-- The sample address syscall has produced a terminal outcome. -/
  | pdaTerminal
  deriving DecidableEq, Repr

/-- Distinct finite unwind reasons used by the closed lifecycle controls. -/
inductive Unwind where
  /-- Unwind during literal-byte construction. -/
  | allocation
  /-- Unwind while transferring a seed into its owning vector. -/
  | seedPush
  /-- Unwind from the local address-search panic callback. -/
  | search
  /-- Unwind after consuming the vector of borrowed views. -/
  | refsDrop
  /-- Unwind from cleanup of the owning seed vector. -/
  | seedsDrop
  /-- An independent unwind from the address syscall dependency. -/
  | syscall
  deriving DecidableEq, Repr

/-- Terminal reasons retain the observed event trace without inventing a final state. -/
inductive Terminal where
  /-- A dependency aborts with the supplied event trace. -/
  | abort (events : List Event)
  /-- A second unwind terminates cleanup, preserving the trace and both unwind reasons. -/
  | double (events : List Event) (original later : Unwind)
  deriving DecidableEq, Repr

/-- Data and owned vectors contain no readers of the complete recursive state. -/
structure Data where
  /-- The sample ledger of owned literal-byte vectors. -/
  bytes : Owned.VectorState UInt8 := []
  /-- The sample ledger of owning seed vectors. -/
  seeds : Owned.VectorState (Seed Nat) := []
  /-- The current extra-account metadata observed by the resolver. -/
  extra : Hook.ExtraMeta
  /-- The current instruction bytes observed by retained views. -/
  instruction : Bytes := []
  /-- The current program key observed at address search. -/
  program : Solanalib.Runtime.Pubkey := .zero
  /-- The current account-key and account-data observations. -/
  accounts : Hook.Observations := []
  /-- The ordered dependency and cleanup events recorded by the control. -/
  events : List Event := []

/-- The reference ledger holds live views of the separate data component. -/
abbrev State := Data × Owned.VectorState (BytesView Data)

/-- Project the literal-byte ledger while retaining the other state components. -/
def bytesFocus : Owned.Focus State (Owned.VectorState UInt8) where
  get := fun state => state.1.bytes
  set := fun state bytes => ({ state.1 with bytes := bytes }, state.2)
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Project the owning seed ledger while retaining the other state components. -/
def seedsFocus : Owned.Focus State (Owned.VectorState (Seed Nat)) where
  get := fun state => state.1.seeds
  set := fun state seeds => ({ state.1 with seeds := seeds }, state.2)
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Append one observable event to the sample state. -/
def record (event : Event) (state : State) : State :=
  ({ state.1 with events := state.1.events ++ [event] }, state.2)

/-- Record literal construction after the byte ledger has been updated. -/
def bytesHook (step : Step UInt8) (_ : State) (after : State) : State :=
  match step with
  | .fromList values => record (.literalAllocated values) after
  | _ => after

/-- Normal recursive element destruction in this sample retires the actual
literal handles contained in the parent. Only the parent calls this function. -/
def dropLiterals : List (Seed Nat) → State → State
  | [], state => state
  | .literal resource :: rest, state =>
    dropLiterals rest (record (.literalDropped resource)
      ({ state.1 with bytes := state.1.bytes.set resource none }, state.2))
  | _ :: rest, state => dropLiterals rest state

theorem dropLiterals_seeds (values : List (Seed Nat)) (state : State) :
    (dropLiterals values state).1.seeds = state.1.seeds := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest induction =>
    cases value <;> simp only [dropLiterals, induction, record]

/-- Record seed operations and recursively retire literal owners during seed-vector cleanup. -/
def seedsHook (step : Step (Seed Nat)) (_ : State) (after : State) : State :=
  match step with
  | .empty => record .seedsEmpty after
  | .push _ value => record (.seedPushed value) after
  | .drop _ values =>
    let cleaned := dropLiterals values after
    record .seedsDropped
      ({ cleaned.1 with extra := { cleaned.1.extra with isSigner := false, isWritable := false } },
        cleaned.2)
  | _ => after

/-- Lift a view of the data component to the full state without copying its bytes. -/
def liftView (view : BytesView Data) : BytesView State :=
  ⟨view.length, fun state => view.read state.1⟩

/-- A full-width sample key containing one repeated byte. -/
def repeatedKey (byte : UInt8) : Solanalib.Runtime.Pubkey := .ofBytes (List.replicate 32 byte)

/-- The sample deliberately changes other observations after reference push.
This tests actual-state reads in the resolver, without asserting these effects
are possible for a concrete Rust allocator. Each source binding must justify
which observations its dependencies may change. -/
def refsHook (step : Step (BytesView Data)) (_ : State) (after : State) : State :=
  match step with
  | .empty => record .refsEmpty after
  | .push _ _ => record .refPushed
      ({ after.1 with
          bytes := after.1.bytes.set 0 (some [9])
          instruction := [6]
          program := repeatedKey 2 }, after.2)
  | .drop _ _ => record .refsDropped
      ({ after.1 with extra := { after.1.extra with isSigner := true, isWritable := true } },
        after.2)
  | _ => after

/-- The eventful normal provider for sample literal-byte vectors. -/
def bytesOps : Owned.VectorOps State UInt8 Nat Unwind Terminal :=
  ledger bytesFocus bytesHook

/-- The eventful normal provider for sample owning seed vectors. -/
def seedsOps : Owned.VectorOps State (Seed Nat) Nat Unwind Terminal :=
  ledger seedsFocus seedsHook

/-- The eventful normal ledger of views into the data component. -/
def refsLedger : Owned.VectorOps State (BytesView Data) Nat Unwind Terminal :=
  ledger Owned.Focus.snd refsHook

/-- The three exact vector providers used by the closed resolver controls. -/
def ops : Ops State Nat Nat Nat Unwind Terminal :=
  ⟨bytesOps, seedsOps, mapElements refsLedger liftView⟩

/-- All primitive laws are checked for the exact provider used by the full
resolver witness, including fresh empty owners and permanent drop tombstones. -/
theorem ops_laws : ops.Laws := by
  constructor
  · apply ledger_laws
    intro step before after
    cases step <;> rfl
  · apply ledger_laws
    intro step before after
    cases step with
    | drop resource values => exact dropLiterals_seeds values after
    | _ => rfl
  · apply mapElements_laws
    apply ledger_laws
    intro step before after
    cases step <;> rfl

/-- Current-state observations of the source arguments in the sample resolver. -/
def args : Args State where
  extraAt := fun state => some state.1.extra
  instructionAt := fun state => some state.1.instruction
  programAt := fun state => some state.1.program
  accountsAt := fun state => some state.1.accounts

/-- The sample double-unwind policy retains the actual event trace and both reasons. -/
def double : Owned.DoubleUnwind State Unwind Terminal :=
  fun state original later terminal => terminal = .double state.1.events original later

/-- The sample panic callback records its call before unwinding with the search reason. -/
def panic : Callback.Run State Unit Empty Unwind Terminal :=
  fun before _ outcome => outcome = .unwound .search (record .searchPanic before)

/-- A mathematical hash that reveals both the first seed byte and the first
program byte for the one-byte-literal fixture. It has the required width and
is explicitly not an implementation or property of SHA-256. -/
def crypto : Address.Crypto where
  primitives :=
    { sha256 := fun input => List.replicate 32 (input[0]?.getD 0 + input[2]?.getD 0)
      onCurve := fun _ => false }

/-- Construct an initial sample state with the supplied configuration and resolver tag. -/
def start (configuration : Solanalib.Runtime.Pubkey) (tag : UInt8 := 1) : State :=
  ({ extra := ⟨tag, configuration, false, false⟩, instruction := [4] }, [])

/-- A packed configuration containing one literal seed with byte 7. -/
def literalConfig : Solanalib.Runtime.Pubkey := .ofBytes [1, 1, 7]
/-- The empty-resource initial state of the one-literal resolver control. -/
def initial : State := start literalConfig
/-- The actual state produced by empty seed-vector construction. -/
def afterEmpty (before : State) : State := (ops.seeds.empty before).2

/-- The sample state after constructing the one-byte literal vector. -/
def afterLiteral (before : State) : State :=
  bytesHook (.fromList [7]) before
    (bytesFocus.set before ((bytesFocus.get before).allocate [7]).2)

/-- The sample state after transferring the literal owner into the seed vector. -/
def afterSeedPush (before : State) : State :=
  seedsHook (.push 0 (.literal 0)) before
    (seedsFocus.set before (before.1.seeds.set 0 (some [.literal 0])))

/-- A one-byte retained view of literal resource zero in the data component. -/
def literalView : BytesView Data := ⟨1, fun data => data.bytes.current 0⟩
/-- A one-byte retained view of the current instruction data. -/
def instructionView : BytesView State := ⟨1, args.instructionAt⟩
/-- The actual state produced by empty borrowed-view vector construction. -/
def afterRefsEmpty (before : State) : State := (ops.refs.empty before).2

/-- The sample state after pushing the literal view and applying the reference hook. -/
def afterRefPush (before : State) : State :=
  refsHook (.push 0 literalView) before
    (before.1, before.2.set 0 (some [literalView]))

/-- The sample state after retiring the borrowed-view vector and applying its drop hook. -/
def afterRefsDrop (before : State) : State :=
  refsHook (.drop 0 [literalView]) before (before.1, before.2.set 0 none)

/-- The sample state after retiring the seed vector and recursively cleaning its current
elements. -/
def afterSeedsDrop (before : State) (values : List (Seed Nat)) : State :=
  seedsHook (.drop 0 values) before (seedsFocus.set before (before.1.seeds.set 0 none))

/-- The one-literal control immediately after empty seed-vector construction. -/
def emptyState : State := afterEmpty initial
/-- The one-literal control immediately after literal-byte construction. -/
def literalState : State := afterLiteral emptyState
/-- The one-literal control after transfer of the literal into its owning seed vector. -/
def seedState : State := afterSeedPush literalState
/-- The one-literal control immediately after empty borrowed-view vector construction. -/
def refsState : State := afterRefsEmpty seedState
/-- The one-literal control after pushing its retained view and observing the hook effects. -/
def pushedState : State := afterRefPush refsState
/-- The normal one-literal control after borrowed-view cleanup. -/
def refsDroppedState : State := afterRefsDrop pushedState
/-- The normal one-literal control after both vector owners and the literal have been retired. -/
def finalState : State := afterSeedsDrop refsDroppedState [.literal 0]
/-- The sample search result reflecting the current seed byte and program byte. -/
def derivedKey : Solanalib.Runtime.Pubkey := repeatedKey 11
/-- The resulting account metadata with flags read after borrowed-view cleanup. -/
def finalMeta : Solanalib.Runtime.CpiMeta := Instruction.accountMeta derivedKey true true

/-- Literal allocation runs before its owning seed is pushed. -/
theorem literal_unpack : unpackOne ops.bytes literalConfig.bytes emptyState ()
    (.returned (.ok (.literal 0)) literalState) := by
  change Callback.map _ _ _ _ _
  exact ⟨.returned 0 literalState, rfl, rfl⟩

theorem literal_seed_push : ops.seeds.push literalState (0, .literal 0)
    (.returned () seedState) := ⟨[], rfl, rfl⟩

theorem literal_unpack_loop : unpackFrom ops (fun state => (args.extraAt state).map
  (·.configuration))
    0 0 emptyState (.returned (.ok ()) seedState) := by
  rw [unpackFrom]
  refine ⟨literalConfig, rfl, .returned (.ok (.literal 0)) literalState, literal_unpack, ?_⟩
  refine ⟨3, rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  refine ⟨.returned () seedState, literal_seed_push, ?_⟩
  change unpackFrom ops (fun state => (args.extraAt state).map (·.configuration))
    0 3 seedState (.returned (.ok ()) seedState)
  rw [unpackFrom]
  refine ⟨literalConfig, rfl, .returned (.ok .uninitialized) seedState, rfl, 0, rfl, rfl⟩

/-- This checked unpacking execution starts with no resources and transfers
one live seed-vector token owning the newly created literal. -/
theorem literal_unpack_full :
    unpack ops double (fun state => (args.extraAt state).map (·.configuration)) initial ()
      (.returned (.ok 0) seedState) :=
  ⟨literalConfig, rfl, .returned (.ok ()) seedState, literal_unpack_loop, rfl⟩

theorem literal_view : seedView ops args instructionView (.literal 0) refsState ()
    (.returned (.ok (some (liftView literalView))) refsState) := ⟨[7], rfl, rfl⟩

theorem literal_ref_push : ops.refs.push refsState (0, liftView literalView)
    (.returned () pushedState) := ⟨literalView, rfl, [], rfl, rfl⟩

theorem literal_reference_loop : pushViewsFrom ops args instructionView 0 0 1 0 refsState
    (.returned (.ok ()) pushedState) := by
  rw [pushViewsFrom]
  refine ⟨[.literal 0], rfl, rfl, .literal 0, rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  refine ⟨.returned (.ok (some (liftView literalView))) refsState, literal_view, ?_⟩
  refine ⟨.returned () pushedState, literal_ref_push, ?_⟩
  change pushViewsFrom ops args instructionView 0 0 1 1 pushedState
    (.returned (.ok ()) pushedState)
  rw [pushViewsFrom]
  rfl

/-- The retained reference observes the new byte, while retaining its extent. -/
theorem literal_observed_after_push :
    readViews pushedState [liftView literalView] = some [[9]] := rfl

theorem literal_observed_before_push :
    readViews refsState [liftView literalView] = some [[7]] := rfl

/-- The source search sees both callback changes: 9 + 2, not the entry 7 + 0. -/
theorem search_changed_values : searchPda ops (pureFind crypto panic) args.programAt 0 pushedState
  ()
    (.returned (.ok derivedKey) pushedState) := by
  refine ⟨[liftView literalView], [[9]], repeatedKey 2, rfl, rfl, rfl,
    .returned (derivedKey, 255) pushedState, ?_, rfl⟩
  rfl

theorem entry_values_different :
    Address.tryFind ⟨crypto, [[7]], .zero⟩ = some (repeatedKey 7, 255) ∧
      repeatedKey 7 ≠ derivedKey := by
  constructor
  · rfl
  · decide

theorem reference_drop : ops.refs.drop pushedState 0 (.returned () refsDroppedState) :=
  ⟨[literalView], rfl, rfl⟩

theorem seeds_drop : ops.seeds.drop refsDroppedState 0 (.returned () finalState) :=
  ⟨[.literal 0], rfl, rfl⟩

theorem literal_pda_full : resolvePda ops double (pureFind crypto panic) args instructionView
  args.programAt
    0 seedState () (.returned (.ok derivedKey) refsDroppedState) := by
  refine ⟨[.literal 0], rfl, .returned (.ok derivedKey) pushedState, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, literal_reference_loop, search_changed_values⟩
  · exact ⟨.returned () refsDroppedState, reference_drop, rfl⟩

/-- A closed complete resolver execution: no assumed final execution or
allocator success premise. Flags are copied after reference cleanup and before
seed cleanup, which deliberately changes them again in this control. -/
theorem literal_resolve_full : resolve ops double (pureFind crypto panic) args initial ()
    (.returned (.ok finalMeta) finalState) := by
  refine ⟨initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, ?_⟩
  change Callback.bind _ _ _ _ _
  refine ⟨.returned (.ok 0) seedState, literal_unpack_full, ?_⟩
  refine ⟨.returned (.ok finalMeta) refsDroppedState, ?_, ?_⟩
  · refine ⟨.returned (.ok derivedKey) refsDroppedState, literal_pda_full, ?_⟩
    exact ⟨refsDroppedState.1.extra, rfl, rfl⟩
  · exact ⟨.returned () finalState, seeds_drop, rfl⟩

/-- All three real fixture resources are retired, with literal cleanup owned
by the seed destructor and no duplicate literal drop. -/
theorem final_resources_and_order :
    ops.bytes.current finalState 0 = none ∧
    ops.seeds.current finalState 0 = none ∧
    ops.refs.current finalState 0 = none ∧
    finalState.1.extra.isSigner = false ∧ finalState.1.extra.isWritable = false ∧
    finalMeta.signerByte = 1 ∧ finalMeta.writableByte = 1 ∧
    finalState.1.events = [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0),
      .refsEmpty, .refPushed, .refsDropped, .literalDropped 0, .seedsDropped] := by
  decide

/-- Failed external-program lookup precedes even malformed seed decoding and
empty-vector construction. This source error leaves the initial state exact. -/
theorem external_lookup_precedes_unpack :
    resolve ops double (pureFind crypto panic) args (start (.ofBytes [255]) 128) ()
      (.returned (.error Hook.accountNotFound) (start (.ofBytes [255]) 128)) :=
  ⟨_, rfl, [], rfl, rfl⟩

/-- Static metadata resolution does not construct any owned vector. -/
theorem static_resolve_full : resolve ops double (pureFind crypto panic) args (start literalConfig
  0) ()
    (.returned (.ok (Instruction.accountMeta literalConfig false false)) (start literalConfig 0)) :=
  ⟨_, rfl, rfl⟩

/-- Pubkey-data bounds errors also leave all allocation dependencies unused. -/
theorem key_data_error_full :
    resolve ops double (pureFind crypto panic) args (start (.ofBytes [1, 0]) 2) ()
      (.returned (.error Hook.instructionDataTooSmall) (start (.ofBytes [1, 0]) 2)) := by
  refine ⟨_, rfl, ?_⟩
  simp only [start, show (2 : UInt8).toNat = 2 from rfl,
    show ¬((2 : Nat) = 0) by decide, show ¬((2 : Nat) = 1) by decide,
    show ¬((128 : Nat) ≤ 2) by decide, ite_false, ite_true]
  change Callback.bind _ _ _ _ _
  exact ⟨.returned (.error Hook.instructionDataTooSmall) (start (.ofBytes [1, 0]) 2),
    ⟨[4], rfl, rfl⟩, rfl⟩

end Solanalib.Specs.Core.Token.AllocatedSeeds.Witness
