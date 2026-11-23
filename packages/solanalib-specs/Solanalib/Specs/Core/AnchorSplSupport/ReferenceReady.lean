/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.ReferenceExecution

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Reference

open Execution

theorem meta_no_unwind : NoUnwind resources.metas.drop := by
  intro before resource reason after called
  dsimp only [resources, metas, vector, Callback.ofFunction] at called
  split at called <;> cases called

theorem byte_no_unwind : NoUnwind resources.bytes.drop := by
  intro before resource reason after called
  dsimp only [resources, bytes, vector, Callback.ofFunction] at called
  split at called <;> cases called

theorem info_no_unwind : NoUnwind resources.infos.drop := by
  intro before resource reason after called
  change (match before.infos.current resource with
    | none => Outcome.terminated "missing info vector"
    | some values => Outcome.returned () { before with
        infos := before.infos.set resource none
        events := before.events ++ infoDropEvents values ++ [Event.retire "infos" resource] }) =
          .unwound reason after at called
  split at called <;> cases called

theorem key_no_unwind : NoUnwind resources.keys.drop := by
  intro before resource reason after called
  dsimp only [resources, keys, vector, Callback.ofFunction] at called
  split at called <;> cases called

theorem serialized_current (before after : State) (input : Serialization)
    (result : Except SerializationError Nat)
    (called : resources.serialize before input (.returned result after)) :
    SerializationResult resources input result after := by
  change serialize before input (.returned result after) at called
  unfold serialize at called
  cases encoded : input.encode with
  | error error =>
    simp only [encoded] at called
    cases called
    simp [SerializationResult, encoded]
  | ok values =>
    simp only [encoded, Callback.map, bytes, vector, returns_exact, Owned.VectorState.allocate,
      exists_eq_left, Outcome.map, Outcome.returned.injEq] at called
    obtain ⟨rfl, rfl⟩ := called
    simpa only [SerializationResult, encoded, resources, bytes, vector, Owned.VectorState.allocate]
      using Owned.VectorState.allocate_current before.bytes values

theorem errors_ready (profile : Profile) : ErrorResources resources profile := by
  constructor
  · cases profile with
    | legacyInline => trivial
    | legacyBoxed | modern =>
      intro before program box after allocated
      change (before.boxes.length, { before with
        boxes := before.boxes ++ [some (.program ⟨program, none, none⟩)]
        events := before.events ++ [Event.allocate "box" before.boxes.length] }) = (box, after)
          at allocated
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj allocated.symm
      constructor
      · simp [errors]
      · rfl
  · intro drop before after error contents current called
    cases drop with
    | metas resource =>
      dsimp only [ReturnDrop.action, Owned.VectorOps.dropAction, resources, metas, vector,
        Callback.ofFunction] at called
      split at called
      · cases called
      · cases called; exact current
    | bytes resource =>
      dsimp only [ReturnDrop.action, Owned.VectorOps.dropAction, resources, bytes, vector,
        Callback.ofFunction] at called
      split at called
      · cases called
      · cases called; exact current
    | infos resource =>
      change (match before.infos.current resource with
        | none => Outcome.terminated "missing info vector"
        | some values => Outcome.returned () { before with
            infos := before.infos.set resource none
            events := before.events ++ infoDropEvents values ++ [Event.retire "infos" resource] })
              = .returned () after at called
      split at called
      · cases called
      · cases called; exact current
    | account value =>
      have same := (drop_exact before value (.returned () after)).mp called
      cases same
      exact current

/-- Evaluate only the earlier prefixes that reach the final local request
read. This check never depends on the completed wrapper or its cleanup. -/
def pointAfterBuildFn (operation : Operation) (before : State) :
    Args resources operation → Built resources → State → Option (CallPoint resources × State) :=
  match operation with
  | .associated _ _ => fun args instruction after =>
      pure (⟨instruction, .array args.context.accounts.owners⟩, after)
  | .deactivate => fun args instruction after =>
      pure (⟨instruction, .array args.context.accounts.moved⟩, after)
  | .memo => fun args instruction after => do
      let remaining ← Reference.infos.current before args.context.remainingAccounts
      pure (⟨instruction, .vector args.context.remainingAccounts remaining⟩, after)
  | .metadata => fun args instruction after => do
      let remaining ← Reference.infos.current before args.context.remainingAccounts
      let .returned infos prepared ← metadataInfosFn functions args.context after | none
      pure (⟨instruction, .vector infos (List.append
        (List.append args.context.accounts.owners remaining) [args.context.program])⟩, prepared)
  | .withdraw => fun args instruction after => do
      let .returned infos prepared ← functions.literal after args.context.accounts | none
      match args.extra.custodian with
      | none => pure (⟨instruction, .vector infos args.context.accounts.moved⟩, prepared)
      | some custodian => do
          let .returned () pushed ← functions.primitive .infoPush prepared (infos, custodian) | none
          pure (⟨instruction, .vector infos (args.context.accounts.moved ++ [custodian])⟩, pushed)

def pointFn (operation : Operation) (before : State) (args : Args resources operation) :
    Option (CallPoint resources × State) := do
  let .returned instruction after ← buildFn functions operation before args | none
  pointAfterBuildFn operation before args instruction after

theorem pointFn_exact {operation : Operation} {before after : State} {args : Args resources
  operation}
    {point : CallPoint resources} (reached : AtCall resources operation before args point after) :
    pointFn operation before args = some (point, after) := by
  refine AtCall.recOn (motive := fun operation before args point after _ =>
    pointFn operation before args = some (point, after)) reached ?_ ?_ ?_ ?_ ?_ ?_
  · intro profile kind before after args instruction built
    simp [pointFn, pointAfterBuildFn, (build_graph functions graphs _ _ _ _).mp built]
  · intro before after args instruction built
    simp [pointFn, pointAfterBuildFn, (build_graph functions graphs _ _ _ _).mp built]
  · intro before after args instruction remaining initial built
    change Reference.infos.current before args.context.remainingAccounts = some remaining at initial
    simp [pointFn, pointAfterBuildFn, (build_graph functions graphs _ _ _ _).mp built, initial]
  · intro before builtState after args instruction infos remaining initial built prepared
    change Reference.infos.current before args.context.remainingAccounts = some remaining at initial
    simp [pointFn, pointAfterBuildFn, (build_graph functions graphs _ _ _ _).mp built, initial,
      (metadataInfos_graph functions graphs _ _ _).mp prepared]
  · intro before builtState after args instruction infos absent built literal
    simp [pointFn, pointAfterBuildFn, (build_graph functions graphs _ _ _ _).mp built, absent,
      (graphs.literal _ _ _).mp literal]
  · intro before builtState preparedState after args instruction infos custodian present built
      literal pushed
    simp [pointFn, pointAfterBuildFn, (build_graph functions graphs _ _ _ _).mp built, present,
      (graphs.literal _ _ _).mp literal, (graphs.primitive .infoPush _ _ _).mp pushed]

/-- The exact current instruction/accounts and owned program-error strings
are checked at the reached call. The invocation is still a whole signature. -/
def callCheck (operation : Operation) (before : State) (args : Args resources operation) : Bool :=
  match pointFn operation before args with
  | none => true
  | some (point, atCall) =>
      decide (observe resources atCall point.instruction = some point.instruction.planned ∧
        point.accounts.read atCall = some point.accounts.expected) &&
      match functions.primitive .invoke atCall
          ⟨point.instruction.planned, point.accounts.expected, args.context.signerSeeds⟩ with
      | some (.returned (.error program) after) =>
          ((errors.programStrings program).mapM (errors.currentString after)).isSome
      | _ => true

def localCheck (operation : Operation) (before : State) (args : Args resources operation) : Bool :=
  match operation with
  | .memo => (Reference.infos.current before args.context.remainingAccounts).isSome
  | .metadata =>
      match args.extra.data.current before, Reference.infos.current before
        args.context.remainingAccounts with
      | some data, some remaining =>
          (match metadataPrefixFn functions args.context.accounts.keys
            args.extra.updateAuthoritySigner before with
          | some (.returned _ after) => decide (args.extra.data.current after = some data)
          | _ => true) &&
          (match buildFn functions .metadata before args with
          | some (.returned _ built) => match metadataFieldsFn functions args.context.accounts
            built with
              | some (.returned _ after) => decide (resources.infos.current after
                args.context.remainingAccounts = some remaining)
              | _ => true
          | _ => true)
      | _, _ => false
  | _ => true

def checked (operation : Operation) (before : State) (args : Args resources operation) : Bool :=
  localCheck operation before args && callCheck operation before args

theorem ready_of_checked (operation : Operation) (before : State) (args : Args resources operation)
    (checked : checked operation before args = true) : Ready types operation before args := by
  obtain ⟨localChecked, callChecked⟩ := Bool.and_eq_true_iff.mp checked
  have callReady : ∀ point after, AtCall resources operation before args point after → point.Ready
    after := by
    intro point after reached
    have current := pointFn_exact reached
    have available : decide (observe resources after point.instruction = some
      point.instruction.planned ∧
        point.accounts.read after = some point.accounts.expected) = true := by
      exact (Bool.and_eq_true_iff.mp (by simpa only [callCheck, current] using callChecked)).1
    change observe resources after point.instruction = some point.instruction.planned ∧ _
    exact of_decide_eq_true available
  refine {
    memo := ?_, metadataData := ?_, metadataRemaining := ?_, call := callReady
    literal := ?_, pda := ?_, serialized := ?_
    metaDrop := meta_no_unwind, byteDrop := byte_no_unwind, infoDrop := info_no_unwind
    keyDrop := ?_, errors := errors_ready operation.profile, invocationError := ?_ }
  · cases operation <;> try trivial
    cases initial : Reference.infos.current before args.context.remainingAccounts with
    | none => simp [localCheck, initial] at localChecked
    | some remaining =>
      refine ⟨remaining, initial, ?_⟩
      intro keys after called
      change (before.keys.length, { before with
        keys := before.keys ++ [some (remaining.map AccountInfo.Value.key)]
        events := before.events ++ [Event.allocate "keys" before.keys.length] }) = (keys, after)
          at called
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj called.symm
      exact Owned.VectorState.allocate_current before.keys (remaining.map AccountInfo.Value.key)
  · cases operation <;> try trivial
    cases initial : args.extra.data.current before with
    | none => simp [localCheck, initial] at localChecked
    | some data =>
      cases remaining : Reference.infos.current before args.context.remainingAccounts with
      | none => simp [localCheck, initial, remaining] at localChecked
      | some values =>
        refine ⟨data, initial, ?_⟩
        intro allocated after prefixRun
        have prefixEq := (metadataPrefix_graph functions graphs _ _ _ _).mp prefixRun
        have same := (Bool.and_eq_true_iff.mp (by simpa only [localCheck, initial, remaining,
          prefixEq] using localChecked)).1
        exact of_decide_eq_true same
  · cases operation <;> try trivial
    cases initial : args.extra.data.current before with
    | none => simp [localCheck, initial] at localChecked
    | some data =>
      cases remaining : Reference.infos.current before args.context.remainingAccounts with
      | none => simp [localCheck, initial, remaining] at localChecked
      | some values =>
        refine ⟨values, remaining, ?_⟩
        intro instruction built infos after builtRun fieldsRun
        have builtEq := (build_graph functions graphs .metadata before args _).mp builtRun
        have fieldsEq := (metadataFields_graph functions graphs _ _ _).mp fieldsRun
        have same := (Bool.and_eq_true_iff.mp
          (by simpa only [localCheck, initial, remaining, builtEq, fieldsEq] using localChecked)).2
        exact of_decide_eq_true same
  · cases operation <;> try trivial
    · exact literal_control 1
    · exact literal_control 5
  · cases operation <;> try trivial
    case associated profile kind =>
      cases profile <;> try trivial
      intro reply after called _
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj called.symm
      exact ⟨.ofNat 77, rfl⟩
  · intro state input result after _ called
    exact serialized_current state after input result called
  · cases operation <;> try trivial
    exact key_no_unwind
  · intro point atCall program after reached invoked
    have pointEq := pointFn_exact reached
    have invokedEq := (graphs.primitive .invoke _ _ _).mp invoked
    have live : ((errors.programStrings program).mapM (errors.currentString after)).isSome = true
      := by
      exact (Bool.and_eq_true_iff.mp (by simpa only [callCheck, pointEq, invokedEq] using
        callChecked)).2
    cases current : (errors.programStrings program).mapM (errors.currentString after) with
    | none => simp [current] at live
    | some strings => exact ⟨strings, rfl⟩

end Solanalib.Specs.Core.AnchorSplSupport.Reference
