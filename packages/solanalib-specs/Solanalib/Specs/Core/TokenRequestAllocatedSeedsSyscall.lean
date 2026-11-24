/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsViews

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds.Witness

/-- The exact address-library query made by the one-literal source fixture. -/
def pdaInputs : Address.Syscall.PdaInputs := ⟨[[9]], repeatedKey 2⟩

theorem pda_inputs_bounded : pdaInputs.Bounded := by
  constructor
  · decide
  · intro seed member
    have same : seed = [9] := by simpa [pdaInputs] using member
    subst seed
    decide

/-- The ordinary selected-target model builds the real output-slot request. -/
theorem pda_request_exact : Address.Syscall.pdaRequest pdaInputs =
    ⟨[[9]], 1, repeatedKey 2, none, 255⟩ := rfl

/-- Adapt the existing mathematical panic effect to the shared source panic
site. The shared find wrapper decides whether that site is reached. -/
def sourcePanic : Callback.Run State Address.SearchPanic Empty Unwind Terminal :=
  fun before _ outcome => panic before () outcome

/-- A closed normal syscall interpretation with explicit state effects. Its
replies agree with the mathematical observation; it is not a runtime proof. -/
def returningSyscall :
    Callback.Run State Address.Syscall.PdaRequest Address.Syscall.PdaReply Unwind Terminal :=
  fun before request outcome =>
    match Address.tryFind ⟨crypto, request.seeds, request.programId⟩ with
    | some (key, bump) =>
      outcome = .returned ⟨0, some key, bump⟩ (record .pdaReturned before)
    | none => outcome = .returned ⟨1, none, 255⟩ (record .pdaReturned before)

theorem returningSyscall_agreement : Address.Syscall.NormalPdaAgreement returningSyscall crypto :=
  by
  intro before inputs reply after called
  cases answer : Address.tryFind ⟨crypto, inputs.seeds, inputs.programId⟩ with
  | none =>
    simp only [returningSyscall, Address.Syscall.pdaRequest, answer] at called
    cases called
    constructor
    · intro zero
      exact False.elim ((by decide : (1 : UInt64) ≠ 0) zero)
    · intro _
      rfl
  | some value =>
    obtain ⟨key, bump⟩ := value
    simp only [returningSyscall, Address.Syscall.pdaRequest, answer] at called
    cases called
    constructor
    · intro _ address initialized
      cases initialized
      rfl
    · intro nonzero
      exact False.elim (nonzero rfl)

/-- The callback is the shared ordinary find-program-address body model. -/
def statefulFind : FindPda State Unwind Terminal :=
  Address.Syscall.findRun returningSyscall sourcePanic

theorem statefulFind_agreement : NormalFindAgreement statefulFind crypto :=
  findRun_normal_agreement returningSyscall sourcePanic crypto returningSyscall_agreement

/-- The actual state returned by the successful sample address syscall. -/
def pdaReturnedState : State := record .pdaReturned pushedState
/-- The successful syscall state after borrowed-view vector cleanup. -/
def pdaRefsCleaned : State := afterRefsDrop pdaReturnedState
/-- The successful syscall state after cleanup of both vectors and the owned literal. -/
def pdaAllCleaned : State := afterSeedsDrop pdaRefsCleaned [.literal 0]

theorem stateful_find_returns : statefulFind pushedState pdaInputs
    (.returned (derivedKey, 255) pdaReturnedState) := by
  refine ⟨.returned (some (derivedKey, 255)) pdaReturnedState, ?_, rfl⟩
  exact ⟨.returned ⟨0, some derivedKey, 255⟩ pdaReturnedState,
    rfl, some (derivedKey, 255), ⟨derivedKey, rfl, rfl⟩, rfl⟩

theorem stateful_search_returns : searchPda ops statefulFind args.programAt 0 pushedState ()
    (.returned (.ok derivedKey) pdaReturnedState) :=
  ⟨[liftView literalView], [[9]], repeatedKey 2, rfl, rfl, rfl,
    .returned (derivedKey, 255) pdaReturnedState, stateful_find_returns, rfl⟩

theorem stateful_pda_full : resolvePda ops double statefulFind args instructionView args.programAt
    0 seedState () (.returned (.ok derivedKey) pdaRefsCleaned) := by
  refine ⟨[.literal 0], rfl, .returned (.ok derivedKey) pdaReturnedState, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, literal_reference_loop, stateful_search_returns⟩
  · exact ⟨.returned () pdaRefsCleaned, ⟨[literalView], rfl, rfl⟩, rfl⟩

/-- Full primary execution through the selected address wrapper. Reference
cleanup and flag reads use its actual returned state, including the syscall
event, before the outer seed owner is consumed. -/
theorem stateful_resolve_full : resolve ops double statefulFind args initial ()
    (.returned (.ok finalMeta) pdaAllCleaned) := by
  refine ⟨initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, .returned (.ok 0) seedState, literal_unpack_full, ?_⟩
  refine ⟨.returned (.ok finalMeta) pdaRefsCleaned, ?_, ?_⟩
  · exact ⟨.returned (.ok derivedKey) pdaRefsCleaned, stateful_pda_full,
      ⟨pdaRefsCleaned.1.extra, rfl, rfl⟩⟩
  · exact ⟨.returned () pdaAllCleaned, ⟨[.literal 0], rfl, rfl⟩, rfl⟩

theorem stateful_cleanup_order :
    pdaAllCleaned.1.bytes = [none] ∧ pdaAllCleaned.1.seeds = [none] ∧
    pdaAllCleaned.2 = [none] ∧
    pdaAllCleaned.1.events = [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0),
      .refsEmpty, .refPushed, .pdaReturned, .refsDropped, .literalDropped 0, .seedsDropped] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A nonzero primitive reply leaves the address uninitialized and changes
the bump output. Neither output is read by the selected failure branch. No
cryptographic agreement is asserted for this dependency interpretation. -/
def rejectingSyscall :
    Callback.Run State Address.Syscall.PdaRequest Address.Syscall.PdaReply Unwind Terminal :=
  fun before _ outcome => outcome = .returned ⟨13, none, 3⟩ (record .pdaReturned before)

/-- The selected address wrapper instantiated with the nonzero-reply syscall and local panic. -/
def rejectionFind : FindPda State Unwind Terminal :=
  Address.Syscall.findRun rejectingSyscall sourcePanic

/-- The nonzero syscall reply has reached the local search panic in its actual returned state. -/
def pdaRejectedState : State := record .searchPanic pdaReturnedState
/-- The nonzero-reply panic state after borrowed-view vector cleanup. -/
def pdaRejectionRefsCleaned : State := afterRefsDrop pdaRejectedState
/-- The nonzero-reply panic state after all owned seed resources have been retired. -/
def pdaRejectionAllCleaned : State := afterSeedsDrop pdaRejectionRefsCleaned [.literal 0]

theorem stateful_find_rejects : rejectionFind pushedState pdaInputs
    (.unwound .search pdaRejectedState) := by
  refine ⟨.returned none pdaReturnedState, ?_, ?_⟩
  · exact ⟨.returned ⟨13, none, 3⟩ pdaReturnedState, rfl, none, rfl, rfl⟩
  · exact ⟨.unwound .search pdaRejectedState, rfl, rfl⟩

theorem stateful_search_rejects : searchPda ops rejectionFind args.programAt 0 pushedState ()
    (.unwound .search pdaRejectedState) :=
  ⟨[liftView literalView], [[9]], repeatedKey 2, rfl, rfl, rfl,
    .unwound .search pdaRejectedState, stateful_find_rejects, rfl⟩

theorem stateful_pda_rejects : resolvePda ops double rejectionFind args instructionView
  args.programAt
    0 seedState () (.unwound .search pdaRejectionRefsCleaned) := by
  refine ⟨[.literal 0], rfl, .unwound .search pdaRejectedState, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, literal_reference_loop, stateful_search_rejects⟩
  · exact ⟨.returned () pdaRejectionRefsCleaned, ⟨[literalView], rfl, rfl⟩, rfl⟩

/-- A normal nonzero syscall reply reaches the local panic at the actual
returned state, then both owners are cleaned in source order. The primary
model does not assume the optional mathematical correspondence. -/
theorem stateful_resolve_rejects : resolve ops double rejectionFind args initial ()
    (.unwound .search pdaRejectionAllCleaned) := by
  refine ⟨initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, .returned (.ok 0) seedState, literal_unpack_full, ?_⟩
  refine ⟨.unwound .search pdaRejectionRefsCleaned, ?_, ?_⟩
  · exact ⟨.unwound .search pdaRejectionRefsCleaned, stateful_pda_rejects, rfl⟩
  · exact ⟨.returned () pdaRejectionAllCleaned, ⟨[.literal 0], rfl, rfl⟩, rfl⟩

theorem stateful_rejection_cleanup_order :
    pdaRejectionAllCleaned.1.bytes = [none] ∧ pdaRejectionAllCleaned.1.seeds = [none] ∧
    pdaRejectionAllCleaned.2 = [none] ∧
    pdaRejectionAllCleaned.1.events = [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0),
      .refsEmpty, .refPushed, .pdaReturned, .searchPanic, .refsDropped, .literalDropped 0,
      .seedsDropped] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Primitive failure is independent of a cryptographic answer. -/
def unwindingSyscall :
    Callback.Run State Address.Syscall.PdaRequest Address.Syscall.PdaReply Unwind Terminal :=
  fun before _ outcome => outcome = .unwound .syscall (record .pdaUnwind before)

/-- Even the optional normal agreement cannot exclude independent abnormal
exits: this provider has no ordinary replies, but has a checked unwind below. -/
theorem unwindingSyscall_agreement : Address.Syscall.NormalPdaAgreement unwindingSyscall crypto :=
  by
  intro before inputs reply after impossible
  cases impossible

/-- The selected address wrapper instantiated with the independently unwinding syscall. -/
def unwindFind : FindPda State Unwind Terminal :=
  Address.Syscall.findRun unwindingSyscall sourcePanic

/-- The actual state exposed by the independent syscall unwind. -/
def pdaUnwoundState : State := record .pdaUnwind pushedState
/-- The syscall unwind state after borrowed-view vector cleanup. -/
def pdaUnwindRefsCleaned : State := afterRefsDrop pdaUnwoundState
/-- The syscall unwind state after cleanup of both vectors and the owned literal. -/
def pdaUnwindAllCleaned : State := afterSeedsDrop pdaUnwindRefsCleaned [.literal 0]

theorem stateful_find_unwinds : unwindFind pushedState pdaInputs
    (.unwound .syscall pdaUnwoundState) :=
  ⟨.unwound .syscall pdaUnwoundState, ⟨.unwound .syscall pdaUnwoundState, rfl, rfl⟩, rfl⟩

theorem stateful_search_unwinds : searchPda ops unwindFind args.programAt 0 pushedState ()
    (.unwound .syscall pdaUnwoundState) :=
  ⟨[liftView literalView], [[9]], repeatedKey 2, rfl, rfl, rfl,
    .unwound .syscall pdaUnwoundState, stateful_find_unwinds, rfl⟩

theorem stateful_pda_unwinds : resolvePda ops double unwindFind args instructionView args.programAt
    0 seedState () (.unwound .syscall pdaUnwindRefsCleaned) := by
  refine ⟨[.literal 0], rfl, .unwound .syscall pdaUnwoundState, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, literal_reference_loop, stateful_search_unwinds⟩
  · exact ⟨.returned () pdaUnwindRefsCleaned, ⟨[literalView], rfl, rfl⟩, rfl⟩

/-- A syscall unwind remains a complete primary resolver execution even though
the mathematical search succeeds. Both cleanup phases retain its actual state. -/
theorem stateful_resolve_unwinds :
    Address.tryFind ⟨crypto, pdaInputs.seeds, pdaInputs.programId⟩ = some (derivedKey, 255) ∧
    resolve ops double unwindFind args initial () (.unwound .syscall pdaUnwindAllCleaned) := by
  refine ⟨rfl, initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, .returned (.ok 0) seedState, literal_unpack_full, ?_⟩
  refine ⟨.unwound .syscall pdaUnwindRefsCleaned, ?_, ?_⟩
  · exact ⟨.unwound .syscall pdaUnwindRefsCleaned, stateful_pda_unwinds, rfl⟩
  · exact ⟨.returned () pdaUnwindAllCleaned, ⟨[.literal 0], rfl, rfl⟩, rfl⟩

theorem stateful_unwind_cleanup_order :
    pdaUnwindAllCleaned.1.bytes = [none] ∧ pdaUnwindAllCleaned.1.seeds = [none] ∧
    pdaUnwindAllCleaned.2 = [none] ∧
    pdaUnwindAllCleaned.1.events = [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0),
      .refsEmpty, .refPushed, .pdaUnwind, .refsDropped, .literalDropped 0, .seedsDropped] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A sample syscall that terminates with its observed trace and supplies no final state. -/
def terminatingSyscall :
    Callback.Run State Address.Syscall.PdaRequest Address.Syscall.PdaReply Unwind Terminal :=
  fun before _ outcome => outcome = .terminated (.abort (before.1.events ++ [.pdaTerminal]))

/-- The selected address wrapper instantiated with the terminal syscall dependency. -/
def terminalFind : FindPda State Unwind Terminal :=
  Address.Syscall.findRun terminatingSyscall sourcePanic

/-- The terminal syscall trace before any vector cleanup or local search panic. -/
def pdaTerminalReason : Terminal := .abort
  [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0), .refsEmpty, .refPushed,
    .pdaTerminal]

theorem stateful_search_terminates : searchPda ops terminalFind args.programAt 0 pushedState ()
    (.terminated pdaTerminalReason) := by
  refine ⟨[liftView literalView], [[9]], repeatedKey 2, rfl, rfl, rfl,
    .terminated pdaTerminalReason, ?_, rfl⟩
  exact ⟨.terminated pdaTerminalReason, ⟨.terminated pdaTerminalReason, rfl, rfl⟩, rfl⟩

theorem stateful_pda_terminates : resolvePda ops double terminalFind args instructionView
  args.programAt
    0 seedState () (.terminated pdaTerminalReason) :=
  ⟨[.literal 0], rfl, .terminated pdaTerminalReason,
    ⟨.returned (.ok ()) pushedState, literal_reference_loop, stateful_search_terminates⟩, rfl⟩

/-- An independent syscall terminal exit skips both vector destructors and
the local search-exhaustion panic, even on mathematical success. -/
theorem stateful_resolve_terminates :
    Address.tryFind ⟨crypto, pdaInputs.seeds, pdaInputs.programId⟩ = some (derivedKey, 255) ∧
    resolve ops double terminalFind args initial () (.terminated pdaTerminalReason) := by
  refine ⟨rfl, initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, .returned (.ok 0) seedState, literal_unpack_full, ?_⟩
  exact ⟨.terminated pdaTerminalReason, ⟨.terminated pdaTerminalReason, stateful_pda_terminates,
    rfl⟩, rfl⟩

/-- The terminal trace and reasons when reference cleanup unwinds during a syscall unwind. -/
def syscallDoubleReason : Terminal := .double
  [.seedsEmpty, .literalAllocated [7], .seedPushed (.literal 0), .refsEmpty, .refPushed,
    .pdaUnwind, .refsDropped] .syscall .refsDrop

theorem stateful_pda_double_unwind : resolvePda refsDropUnwindOps double unwindFind
    args instructionView args.programAt 0 seedState () (.terminated syscallDoubleReason) := by
  refine ⟨[.literal 0], rfl, .unwound .syscall pdaUnwoundState, ?_, ?_⟩
  · exact ⟨.returned (.ok ()) pushedState, double_fixture_reference_loop, stateful_search_unwinds⟩
  · refine ⟨.unwound .refsDrop pdaUnwindRefsCleaned, ?_, syscallDoubleReason, rfl, rfl⟩
    exact ⟨pdaUnwindRefsCleaned, ⟨[literalView], rfl, rfl⟩, rfl⟩

/-- Double-unwind cleanup also starts from an independent syscall failure,
without a pure-search failure premise or a synthetic ordinary error. -/
theorem stateful_resolve_double_unwind : resolve refsDropUnwindOps double unwindFind args
    initial () (.terminated syscallDoubleReason) := by
  refine ⟨initial.1.extra, rfl, ?_⟩
  change ∃ program, args.programAt initial = some program ∧ _
  refine ⟨.zero, rfl, ?_⟩
  change ∃ instruction, args.instructionAt initial = some instruction ∧ _
  refine ⟨[4], rfl, .returned (.ok 0) seedState, double_fixture_unpack_full, ?_⟩
  exact ⟨.terminated syscallDoubleReason,
    ⟨.terminated syscallDoubleReason, stateful_pda_double_unwind, rfl⟩, rfl⟩

end Solanalib.Specs.Core.Token.AllocatedSeeds.Witness
