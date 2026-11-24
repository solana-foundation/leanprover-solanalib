/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorSpl.Token

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

set_option maxRecDepth 4096

namespace SolanalibTest.Specs.AnchorSpl.OwnedTransfer

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTransfer

/-- This versioned contract has an actual execution retaining an owned error
while retiring both instruction vectors and the remaining vector of the context. -/
theorem returned_error_contract :
    (Solanalib.Specs.AnchorSpl.token.transfer_contract.contract Sample.types).post Sample.initial
      Sample.args
      (.returned (.error Sample.boxed.1) Sample.finalState) := by
  exact run_after_build Sample.types Sample.args Sample.initial Sample.builtState
    Sample.instruction _ _
    Sample.builder_returns Sample.invocation_returns_error
    (Sample.cleanup_returns.cleanup_returned _ (Except.error Sample.boxed.1))

theorem returned_error_and_retired_vectors :
    AnchorErrorOwned.current Sample.types.errors Sample.finalState Sample.boxed.1 =
      some (AnchorAccount.programError .insufficientFunds) ∧
    Sample.resources.builder.bytes.current Sample.finalState Sample.instruction.data = none ∧
    Sample.resources.builder.metas.current Sample.finalState Sample.instruction.metas = none ∧
    Sample.resources.remaining.current Sample.finalState Sample.args.context.remaining = none :=
  ⟨Sample.final_error_current, Sample.final_vectors_retired⟩

theorem actual_request_order : Sample.finalState.2.calls = [Sample.call] ∧
    Sample.call.instruction.programId = Token.legacyProgramId ∧
    Sample.call.accounts = [Sample.info 1, Sample.info 2, Sample.info 3] ∧
    Sample.call.signers = [[], [[1, 2], []]] := ⟨rfl, rfl, rfl, rfl⟩

def unwindTypes : Types :=
  { Sample.types with
    invoke := Callback.ofFunction fun state call => .unwound (23 : Nat)
      (state.1, { state.2 with calls := state.2.calls ++ [call] }) }

def unwindMetas : Sample.State := ((Sample.afterInvoke.1.1, [none]), Sample.afterInvoke.2)
def unwindBytes : Sample.State := (([none], [none]), Sample.afterInvoke.2)
def unwindAccounts : Sample.State :=
  Sample.afterInfo (Sample.afterInfo (Sample.afterInfo unwindBytes (Sample.info 1))
    (Sample.info 2)) (Sample.info 3)
def unwindFinal : Sample.State :=
  Sample.remainingFocus.set (Sample.afterInfos unwindAccounts [Sample.info 4]) [none]

theorem unwind_cleanup :
    Owned.DropReturns (invocationDrops Sample.args Sample.instruction) Sample.afterInvoke
      unwindFinal := by
  refine .cons _ _ _ unwindMetas unwindFinal ?_ ?_
  · exact ⟨.returned () (Sample.afterInvoke.1.1, [none]),
      Token.InstructionAllocated.Witness.metas_drop _ _, rfl⟩
  refine .cons _ _ _ unwindBytes unwindFinal ?_ ?_
  · exact ⟨.returned () ([none], [none]),
      Token.InstructionAllocated.Witness.bytes_drop _ _, rfl⟩
  refine .cons _ _ _ (Sample.afterInfo unwindBytes (Sample.info 1)) unwindFinal
    (Sample.sdk_info_drop _ _) ?_
  refine .cons _ _ _ (Sample.afterInfo (Sample.afterInfo unwindBytes (Sample.info 1))
    (Sample.info 2)) unwindFinal (Sample.sdk_info_drop _ _) ?_
  refine .cons _ _ _ unwindAccounts unwindFinal (Sample.sdk_info_drop _ _) ?_
  exact .cons _ _ _ unwindFinal unwindFinal
    (Sample.remaining_drop unwindAccounts [Sample.info 4] rfl) (.nil _)

/-- An opaque invocation unwind keeps its recorded request and state effects;
the source scope then drops the instruction, moved array and remaining vector. -/
theorem invocation_unwind_cleanup : run unwindTypes Sample.initial Sample.args
    (.unwound (23 : Nat) unwindFinal) := by
  apply run_after_build unwindTypes Sample.args Sample.initial Sample.builtState Sample.instruction
    (.unwound (23 : Nat) Sample.afterInvoke) (.unwound (23 : Nat) unwindFinal)
      Sample.builder_returns
  · exact ⟨.unwound (23 : Nat) Sample.afterInvoke, rfl, rfl⟩
  · exact unwind_cleanup.cleanup_unwound _ (23 : Nat)

theorem unwind_did_not_box_error : unwindFinal.2.errors.boxes = [] ∧
    unwindFinal.2.calls = [Sample.call] ∧
    unwindFinal.2.rcEvents = Sample.infoEvents (Sample.info 1) ++
      Sample.infoEvents (Sample.info 2) ++ Sample.infoEvents (Sample.info 3) ++
      Sample.infoEvents (Sample.info 4) := ⟨rfl, rfl, rfl⟩

def exhaustedAux : Sample.Aux :=
  { Sample.auxiliary with errors := AnchorErrorOwned.Reference.initial 0 }
def exhaustedInitial : Sample.State := (([], []), exhaustedAux)
def exhaustedBuilt : Sample.State := (Sample.builtState.1, exhaustedAux)
def exhaustedInvoked : Sample.State :=
  (exhaustedBuilt.1, { exhaustedBuilt.2 with calls := [Sample.call] })

theorem exhausted_program_box : AnchorErrorOwned.fromProgram Sample.types.errors exhaustedInvoked
    .insufficientFunds (.terminated (2 : Nat)) := by
  refine ⟨.terminated (2 : Nat), ?_, rfl⟩
  refine ⟨.terminated (2 : Nat), ?_, rfl⟩
  exact ⟨.terminated (.allocation .box), rfl, rfl⟩

/-- Allocation failure in the post-CPI ProgramError conversion is terminal.
It does not invent a normal boxed error or run later scope cleanup. -/
theorem cpi_error_box_terminal : run Sample.types exhaustedInitial Sample.args (.terminated (2 :
  Nat)) := by
  apply run_after_build Sample.types Sample.args exhaustedInitial exhaustedBuilt Sample.instruction
    (.terminated (2 : Nat)) (.terminated (2 : Nat))
  · exact VectorSample.run_returns (plan Sample.args) exhaustedAux (plan_admitted Sample.args)
  · refine ⟨.returned (.error .insufficientFunds) exhaustedInvoked, rfl, ?_⟩
    refine ⟨.terminated (2 : Nat), ?_, rfl⟩
    exact ⟨.terminated (2 : Nat), exhausted_program_box, rfl⟩
  · exact (Owned.cleanup_terminated _ _ _ _).mpr rfl

def earlyBuilder : Token.InstructionAllocated.Types :=
  { Sample.resources.builder with
    bytes := { Sample.resources.builder.bytes with
      withCapacity := Callback.ofFunction fun state _ => .unwound (17 : Nat) state } }

def earlyResources : Resources := { Sample.resources with builder := earlyBuilder }
def earlyTypes : Types :=
  { Sample.types with
    resources := earlyResources
    invoke := fun _ _ _ => False }
def earlyArgs : Args earlyResources := ⟨Sample.args.context, Sample.args.amount⟩
def earlyAccounts : Sample.State :=
  Sample.afterInfo (Sample.afterInfo (Sample.afterInfo Sample.initial (Sample.info 1))
    (Sample.info 2)) (Sample.info 3)
def earlyFinal : Sample.State :=
  Sample.remainingFocus.set (Sample.afterInfos earlyAccounts [Sample.info 4]) [none]

theorem early_context_cleanup :
    Owned.DropReturns (contextDrops earlyArgs) Sample.initial earlyFinal := by
  refine .cons _ _ _ (Sample.afterInfo Sample.initial (Sample.info 1)) earlyFinal
    (Sample.sdk_info_drop _ _) ?_
  refine .cons _ _ _ (Sample.afterInfo (Sample.afterInfo Sample.initial (Sample.info 1))
    (Sample.info 2)) earlyFinal (Sample.sdk_info_drop _ _) ?_
  refine .cons _ _ _ earlyAccounts earlyFinal (Sample.sdk_info_drop _ _) ?_
  exact .cons _ _ _ earlyFinal earlyFinal
    (Sample.remaining_drop earlyAccounts [Sample.info 4] rfl) (.nil _)

/-- This failure-injection interpretation checks the generic source cleanup
branch before any context fields move. It claims no concrete Global allocator
unwind: a Rust binding must separately establish which dependency exits exist. -/
theorem before_move_dependency_unwind :
    run earlyTypes Sample.initial earlyArgs (.unwound (17 : Nat) earlyFinal) := by
  refine ⟨.unwound (17 : Nat) Sample.initial, ?_, ?_⟩
  · exact Token.InstructionAllocated.Witness.run_capacity_unwound (plan_admitted earlyArgs) rfl rfl
  · exact early_context_cleanup.cleanup_unwound _ (17 : Nat)

theorem before_move_no_instruction_or_invocation :
    earlyFinal.1 = ([], []) ∧ earlyFinal.2.calls = [] ∧
    earlyFinal.2.errors = Sample.auxiliary.errors ∧
    earlyFinal.2.rcEvents = Sample.infoEvents (Sample.info 1) ++
      Sample.infoEvents (Sample.info 2) ++ Sample.infoEvents (Sample.info 3) ++
      Sample.infoEvents (Sample.info 4) := ⟨rfl, rfl, rfl, rfl⟩


def terminalBuilder : Token.InstructionAllocated.Types :=
  { Sample.resources.builder with
    bytes := { Sample.resources.builder.bytes with
      withCapacity := Callback.ofFunction fun _ _ => .terminated (29 : Nat) } }
def terminalResources : Resources := { Sample.resources with builder := terminalBuilder }
def terminalTypes : Types := { Sample.types with resources := terminalResources }
def terminalArgs : Args terminalResources := ⟨Sample.args.context, Sample.args.amount⟩
def noRemaining : Sample.State :=
  (Sample.initial.1, { Sample.initial.2 with remaining := [] })

/-- A missing abstract remaining-vector owner is outside the source binding.
A terminal first allocation still exits before that vector, invocation, or
cleanup is used; the mathematical family must retain that actual exit. -/
theorem absent_remaining_retains_builder_terminal :
    ¬ terminalResources.remaining.Live noRemaining terminalArgs.context.remaining ∧
    (Solanalib.Specs.AnchorSpl.token.transfer_contract.contract terminalTypes).requires noRemaining
      terminalArgs ∧
    Solanalib.Specs.AnchorSpl.token.transfer_run terminalTypes noRemaining terminalArgs
      (.terminated (29 : Nat)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨values, current⟩
    cases current
  · change BuildReady terminalResources noRemaining terminalArgs
    intro instruction after built
    unfold Token.InstructionAllocated.run at built
    rw [plan_admitted terminalArgs] at built
    obtain ⟨allocated, equal, next⟩ := built
    change Outcome.terminated (29 : Nat) = allocated at equal
    subst allocated
    cases next
  · apply run_build_terminal
    change Token.InstructionAllocated.run terminalBuilder noRemaining (plan terminalArgs)
      (.terminated (29 : Nat))
    unfold Token.InstructionAllocated.run
    rw [plan_admitted terminalArgs]
    exact ⟨.terminated (29 : Nat), rfl, rfl⟩

namespace Edition2021

/-- This test dependency has an observable terminal exit if an AccountInfo
field drops while either instruction vector is live. It never filters a
callback outcome; the source cleanup sequence determines which exit occurs. -/
def rc : AccountInfoRc.Ops Sample.State Nat :=
  { Sample.rc with
    dropRc := fun before field outcome =>
      match before.1.1[0]?.join, before.1.2[0]?.join with
      | none, none => Sample.rc.dropRc before field outcome
      | _, _ => outcome = .terminated 90 }

def resources : Resources := { Sample.resources with rc := rc }
def types : Types := { Sample.types with resources := resources }
def args : Args resources := ⟨Sample.args.context, Sample.args.amount⟩

/-- Dropping the tail-expression array before ix reaches a different finite
exit in this interpretation. This detects the previous cleanup ordering. -/
theorem premature_array_drop_is_terminal :
    dropInfo resources (Sample.info 1) Sample.afterBox (.terminated (90 : Nat)) :=
  ⟨.terminated (90 : Nat), ⟨.terminated (90 : Nat), rfl, rfl⟩, rfl⟩

private theorem info_drop (aux : Sample.Aux) (value : AccountInfo.Value) :
    dropInfo resources value (([none], [none]), aux)
      (.returned () (Sample.afterInfo (([none], [none]), aux) value)) := by
  refine ⟨.returned () (Sample.afterInfo (([none], [none]), aux) value), ?_, rfl⟩
  refine ⟨.returned () (([none], [none]),
    { aux with rcEvents := aux.rcEvents ++ [.drop .lamports value.lamports] }), rfl, ?_⟩
  simp [resources, rc, Sample.rc, Callback.ofFunction, Sample.afterInfo, Sample.infoEvents,
    List.append_assoc]
  rfl

private theorem cleanup_returns :
    Owned.DropReturns (invocationDrops args Sample.instruction) Sample.afterBox Sample.finalState
      := by
  refine .cons _ _ _ Sample.afterMetas Sample.finalState ?_ ?_
  · exact ⟨.returned () (Sample.afterBox.1.1, [none]),
      Token.InstructionAllocated.Witness.metas_drop _ _, rfl⟩
  refine .cons _ _ _ Sample.afterBytes Sample.finalState ?_ ?_
  · exact ⟨.returned () ([none], [none]),
      Token.InstructionAllocated.Witness.bytes_drop _ _, rfl⟩
  refine .cons _ _ _ (Sample.afterInfo Sample.afterBytes (Sample.info 1)) Sample.finalState ?_ ?_
  · exact info_drop Sample.afterBytes.2 (Sample.info 1)
  refine .cons _ _ _
    (Sample.afterInfo (Sample.afterInfo Sample.afterBytes (Sample.info 1)) (Sample.info 2))
    Sample.finalState ?_ ?_
  · exact info_drop (Sample.afterInfo Sample.afterBytes (Sample.info 1)).2 (Sample.info 2)
  refine .cons _ _ _ Sample.afterAccounts Sample.finalState ?_ ?_
  · exact info_drop
      (Sample.afterInfo (Sample.afterInfo Sample.afterBytes (Sample.info 1)) (Sample.info 2)).2
      (Sample.info 3)
  exact .cons _ _ _ Sample.finalState Sample.finalState
    (Sample.remaining_drop Sample.afterAccounts [Sample.info 4] rfl) (.nil _)

/-- The actual edition-2021 sequence retires ix before the array dependency
observes it, preserves the returned error, and completes all later cleanup. -/
theorem instruction_drops_before_array :
    run types Sample.initial args (.returned (.error Sample.boxed.1) Sample.finalState) :=
  run_after_build types args Sample.initial Sample.builtState Sample.instruction _ _
    Sample.builder_returns Sample.invocation_returns_error
    (cleanup_returns.cleanup_returned _ (Except.error Sample.boxed.1))

/-- The same nonempty error result remains live after the order-sensitive
execution, including the recorded state effects of the invocation. -/
theorem cleanup_order_preserves_error :
    (family.contract types).HasExecution (reference types) := by
  exact ⟨Sample.initial, args, .returned (.error Sample.boxed.1) Sample.finalState,
    Sample.build_ready Sample.auxiliary Sample.args,
    instruction_drops_before_array⟩

end Edition2021

namespace DropCapabilities

private theorem remaining_no_unwind (before : Sample.State) (resource reason : Nat)
    (after : Sample.State) :
    ¬ Sample.remainingOps.drop before resource (.unwound reason after) := by
  rintro ⟨produced, _, equal⟩
  cases produced with
  | returned value state => cases equal
  | unwound impossible state => nomatch impossible
  | terminated reason => cases equal

/-- Concrete mathematical providers discharge the separate cleanup premises.
Their drops cannot replace a pending owned-error return with an unwind. -/
theorem pending_error_cannot_unwind (before after : Sample.State) (reason : Nat) :
    ¬ Owned.cleanup Sample.resources.builder.doubleUnwind
      (invocationDrops Sample.args Sample.instruction)
      (.returned (Except.error Sample.boxed.1 : Except (Error Sample.types) Unit) before)
      (.unwound reason after) := by
  apply cleanup_return_not_unwound
  intro action member current reason final
  exact invocationDrops_no_unwind
    (fun before resource reason after => VectorSample.bytes_no_unwind before after resource reason)
    (fun before resource reason after => VectorSample.metas_no_unwind before after resource reason)
    remaining_no_unwind Sample.args Sample.instruction action member current final reason

/-- This mathematical provider deliberately violates the separate source
drop obligation. The raw family must retain its finite unwind outcome. -/
def resources : Resources :=
  { Sample.resources with
    remaining := { Sample.remainingOps with
      drop := Callback.ofFunction fun before _ => .unwound (73 : Nat) before } }

def types : Types := { Sample.types with resources := resources }
def args : Args resources := ⟨Sample.args.context, Sample.args.amount⟩

theorem remaining_drop_really_unwinds :
    resources.remaining.drop Sample.afterAccounts args.context.remaining
      (.unwound (73 : Nat) Sample.afterAccounts) := rfl

private theorem transfer_unwinds :
    run types Sample.initial args (.unwound (73 : Nat) Sample.afterAccounts) := by
  refine run_after_build types args Sample.initial Sample.builtState Sample.instruction
    (.returned (.error Sample.boxed.1) Sample.afterBox) _ Sample.builder_returns
    Sample.invocation_returns_error ?_
  refine ⟨.returned () Sample.afterMetas, ?_, ?_⟩
  · exact ⟨.returned () (Sample.afterBox.1.1, [none]),
      Token.InstructionAllocated.Witness.metas_drop _ _, rfl⟩
  refine ⟨.returned () Sample.afterBytes, ?_, ?_⟩
  · exact ⟨.returned () ([none], [none]),
      Token.InstructionAllocated.Witness.bytes_drop _ _, rfl⟩
  refine ⟨.returned () (Sample.afterInfo Sample.afterBytes (Sample.info 1)),
    Sample.sdk_info_drop _ _, ?_⟩
  refine ⟨.returned () (Sample.afterInfo (Sample.afterInfo Sample.afterBytes
    (Sample.info 1)) (Sample.info 2)), Sample.sdk_info_drop _ _, ?_⟩
  refine ⟨.returned () Sample.afterAccounts, Sample.sdk_info_drop _ _, ?_⟩
  exact ⟨.unwound (73 : Nat) Sample.afterAccounts, remaining_drop_really_unwinds, rfl⟩

/-- The exact registered raw family admits the provider and keeps its unwind
after actual instruction and moved-account cleanup. This is not a Rust drop
interpretation: the premise of the conditional no-unwind theorem is false here. -/
theorem raw_family_retains_drop_unwind : FamilyHasExecution
    Solanalib.Specs.AnchorSpl.token.transfer_contract Solanalib.Specs.AnchorSpl.token.transfer_run
      types :=
  ⟨Sample.initial, args, .unwound (73 : Nat) Sample.afterAccounts,
    Sample.build_ready Sample.auxiliary Sample.args, transfer_unwinds⟩

theorem unwinding_provider_excluded_by_drop_premise :
    ¬ (∀ before resource reason after,
      ¬ resources.remaining.drop before resource (.unwound reason after)) := by
  intro noUnwind
  exact noUnwind _ _ _ _ remaining_drop_really_unwinds

end DropCapabilities

namespace RequestAdmission

/-- Remove one current observation without changing any allocation or write. -/
def missingTypes (metadata : Bool) : Types :=
  { Sample.types with resources := { Sample.resources with
    builder := { Sample.resources.builder with
      metas := { Sample.resources.builder.metas with
        current := fun state resource =>
          if metadata then none else Sample.resources.builder.metas.current state resource }
      bytes := { Sample.resources.builder.bytes with
        current := fun state resource =>
          if metadata then Sample.resources.builder.bytes.current state resource else none } } } }

/-- Reindex the unchanged transfer arguments at the test interpretation. -/
def missingArgs (metadata : Bool) : Args (missingTypes metadata).resources :=
  ⟨Sample.args.context, Sample.args.amount⟩

private theorem missing_rejected (metadata : Bool) :
    Token.InstructionAllocated.run (missingTypes metadata).resources.builder Sample.initial
      (plan (missingArgs metadata)) (.returned (.ok Sample.instruction) Sample.builtState) ∧
    request (missingTypes metadata) Sample.builtState (missingArgs metadata) Sample.instruction =
      none ∧
    ¬ (family.contract (missingTypes metadata)).requires Sample.initial (missingArgs metadata) := by
  refine ⟨Sample.builder_returns, ?_, ?_⟩
  · cases metadata <;> rfl
  · intro ready
    obtain ⟨call, read⟩ := (buildReady_iff_requests (missingTypes metadata)
      Sample.initial (missingArgs metadata)).mp ready Sample.instruction Sample.builtState
      Sample.builder_returns
    cases metadata <;> cases read

/-- Both missing-current interpretations really finish construction, but the
reached unreadable vector excludes each from the source transfer domain. -/
theorem missing_current_after_real_build_rejected :
    (Token.InstructionAllocated.run (missingTypes true).resources.builder Sample.initial
      (plan (missingArgs true)) (.returned (.ok Sample.instruction) Sample.builtState) ∧
      request (missingTypes true) Sample.builtState (missingArgs true) Sample.instruction = none ∧
      ¬ (family.contract (missingTypes true)).requires Sample.initial (missingArgs true)) ∧
    (Token.InstructionAllocated.run (missingTypes false).resources.builder Sample.initial
      (plan (missingArgs false)) (.returned (.ok Sample.instruction) Sample.builtState) ∧
      request (missingTypes false) Sample.builtState (missingArgs false) Sample.instruction = none ∧
      ¬ (family.contract (missingTypes false)).requires Sample.initial (missingArgs false)) :=
  ⟨missing_rejected true, missing_rejected false⟩

/-- A second allocation exit changes only the auxiliary observation marker. -/
def markedAux : Sample.Aux := { Sample.auxiliary with calls := [Sample.call] }

/-- The first allocation can either preserve or mark the auxiliary state.
All later writes still use the real vector providers. Only the metadata observation of the marked
state is unavailable. -/
def mixedBuilder : Token.InstructionAllocated.Types :=
  { Sample.resources.builder with
    bytes := { Sample.resources.builder.bytes with
      withCapacity := fun before capacity outcome =>
        Sample.resources.builder.bytes.withCapacity before capacity outcome ∨
        ∃ resource after,
          Sample.resources.builder.bytes.withCapacity before capacity (.returned resource after) ∧
          outcome = .returned resource (after.1, { after.2 with calls := [Sample.call] }) }
    metas := { Sample.resources.builder.metas with
      current := fun state resource =>
        if state.2.calls.isEmpty then Sample.resources.builder.metas.current state resource else
          none } }

/-- Other transfer dependencies are unchanged in the mixed interpretation. -/
def mixedTypes : Types :=
  { Sample.types with resources := { Sample.resources with builder := mixedBuilder } }

/-- Both construction paths start from the same transfer input. -/
def mixedArgs : Args mixedTypes.resources := ⟨Sample.args.context, Sample.args.amount⟩

private theorem mixed_builds (aux : Sample.Aux)
    (allocation : mixedBuilder.bytes.withCapacity Sample.initial mixedBuilder.enumSize
      (.returned (0 : Nat) (([some []], []), aux))) :
    Token.InstructionAllocated.run mixedBuilder Sample.initial (plan mixedArgs)
      (.returned (.ok Sample.instruction) (Sample.builtState.1, aux)) := by
  exact Token.InstructionAllocated.Witness.run_from_prepared_data (plan_admitted mixedArgs) rfl
    allocation (VectorSample.write_data_returns (plan mixedArgs).dataSteps [] [] aux)
    (VectorSample.build_metas_returns (plan mixedArgs).metas [some (plan mixedArgs).data] aux) rfl

/-- One readable success cannot discharge universal reached admission: the
same actual builder also returns a constructed but unreadable instruction. -/
theorem one_good_build_does_not_hide_unreadable_success :
    Token.InstructionAllocated.run mixedBuilder Sample.initial (plan mixedArgs)
      (.returned (.ok Sample.instruction) Sample.builtState) ∧
    request mixedTypes Sample.builtState mixedArgs Sample.instruction = some Sample.call ∧
    Token.InstructionAllocated.run mixedBuilder Sample.initial (plan mixedArgs)
      (.returned (.ok Sample.instruction) (Sample.builtState.1, markedAux)) ∧
    request mixedTypes (Sample.builtState.1, markedAux) mixedArgs Sample.instruction = none ∧
    ¬ (family.contract mixedTypes).requires Sample.initial mixedArgs := by
  have good := mixed_builds Sample.auxiliary
    (Or.inl (VectorSample.bytes_capacity [] [] Sample.auxiliary mixedBuilder.enumSize))
  have bad := mixed_builds markedAux (Or.inr ⟨(0 : Nat), (([some []], []), Sample.auxiliary),
    VectorSample.bytes_capacity [] [] Sample.auxiliary mixedBuilder.enumSize, rfl⟩)
  refine ⟨good, rfl, bad, rfl, ?_⟩
  intro ready
  obtain ⟨metas, current⟩ := (ready Sample.instruction (Sample.builtState.1, markedAux) bad).1
  cases current

/-- A callback interpretation may expose no finite CPI exit. -/
def noInvocation : Types := { Sample.types with invoke := fun _ _ _ => False }

/-- Readable construction grants a local request, not an invented invocation
outcome. This provider remains admitted despite having no finite CPI exit. -/
theorem readiness_does_not_require_cpi_execution :
    (family.contract noInvocation).requires Sample.initial Sample.args ∧
    request noInvocation Sample.builtState Sample.args Sample.instruction = some Sample.call ∧
    ¬ ∃ pending, invokeAndConvert noInvocation Sample.args Sample.instruction
      Sample.builtState () pending := by
  refine ⟨Sample.build_ready Sample.auxiliary Sample.args, rfl, ?_⟩
  rintro ⟨pending, invoked, impossible, _⟩
  exact impossible

/-- Admission forms the actual request and the generic continuation consumes
the real failing invocation, owned conversion and source-ordered cleanup. -/
theorem admitted_build_continues_through_error_cleanup :
    run Sample.types Sample.initial Sample.args
      (.returned (.error Sample.boxed.1) Sample.finalState) := by
  obtain ⟨call, read, continuation⟩ :=
    (Sample.build_ready Sample.auxiliary Sample.args).after_build Sample.types Sample.args
      Sample.initial Sample.builtState Sample.instruction Sample.builder_returns
  have same : Sample.call = call := Option.some.inj read
  subst call
  obtain ⟨invoked, called, converted⟩ :=
    (invokeAndConvert_iff Sample.types Sample.args Sample.instruction Sample.builtState
      Sample.call rfl _).mp Sample.invocation_returns_error
  exact continuation invoked _ _ called converted
    (Sample.cleanup_returns.cleanup_returned _ (Except.error Sample.boxed.1))

end RequestAdmission

end SolanalibTest.Specs.AnchorSpl.OwnedTransfer
