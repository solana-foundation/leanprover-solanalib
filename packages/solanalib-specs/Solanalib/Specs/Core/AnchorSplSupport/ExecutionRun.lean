/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.ExecutionBuild

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Execution

variable {types : Types} (fn : Functions types)

def invokeFn (profile : Profile) (instruction : Built types.resources) (infos : List
  AccountInfo.Value)
    (signers : List (List Solanalib.Runtime.Bytes)) (before : types.resources.State) :
    Option (Out types (Except (Error types.resources profile) Unit)) :=
  (observe types.resources before instruction).bind fun value =>
    (fn.primitive .invoke before ⟨value, infos, signers⟩).bind (PGraph.bindK fun result after =>
      match result with
      | .ok () => some (.returned (.ok ()) after)
      | .error error => (fn.primitive (.convert profile) after error).map (Outcome.map
        Except.error))

theorem invoke_graph (graphs : Graph fn) (profile : Profile) (instruction : Built types.resources)
    (infos : List AccountInfo.Value) (signers : List (List Solanalib.Runtime.Bytes)) (before :
      types.resources.State) :
    PGraph (invokeAndConvert types profile instruction infos signers before ())
      (invokeFn fn profile instruction infos signers before) := by
  unfold invokeAndConvert invokeFn
  cases observe types.resources before instruction with
  | none => exact PGraph.false
  | some value =>
    apply PGraph.bind (graphs.primitive .invoke before ⟨value, infos, signers⟩)
    intro result after
    cases result with
    | ok valueUnit => cases valueUnit; exact PGraph.eq_left _
    | error error => exact PGraph.map Except.error (graphs.primitive (.convert profile) after error)

def invokeVectorFn (profile : Profile) (instruction : Built types.resources) (infos :
  types.resources.InfoResource)
    (signers : List (List Solanalib.Runtime.Bytes)) (before : types.resources.State) :
    Option (Out types (Except (Error types.resources profile) Unit)) :=
  (types.resources.infos.current before infos).bind fun values =>
    invokeFn fn profile instruction values signers before

theorem invokeVector_graph (graphs : Graph fn) (profile : Profile) (instruction : Built
  types.resources)
    (infos : types.resources.InfoResource) (signers : List (List Solanalib.Runtime.Bytes)) (before
      : types.resources.State) :
    PGraph (invokeVector types profile instruction infos signers before ())
      (invokeVectorFn fn profile instruction infos signers before) := by
  unfold invokeVector invokeVectorFn
  cases types.resources.infos.current before infos with
  | none => exact PGraph.false
  | some values => exact invoke_graph fn graphs profile instruction values signers before

def withdrawAfterBuildFn (args : Args types.resources .withdraw) (instruction : Built
  types.resources)
    (before : types.resources.State) : Option (Out types (Except (Error types.resources
      .legacyInline) Unit)) :=
  (fn.literal before args.context.accounts).bind fun literal => match literal with
  | .returned infos after =>
      ((match args.extra.custodian with
        | none => some (Outcome.returned () after : Out types Unit)
        | some value => fn.primitive .infoPush after (infos, value)).bind (PGraph.bindK fun _
          pushed =>
          invokeVectorFn fn .legacyInline instruction infos args.context.signerSeeds pushed)).bind
            (PGraph.cleanupFn fn.double (returnDrops fn
              (List.append [ReturnDrop.infos infos] (List.append (instructionDrops instruction)
                (tailDrops args.context)))))
  | .unwound failure after => PGraph.cleanupFn fn.double (returnDrops fn
      (List.append (instructionDrops instruction) (List.append (args.extra.custodian.toList.map
        .account)
        (List.append ((args.context.accounts.unmoved failure.1.completed).map .account) (tailDrops
          args.context)))))
        (.unwound failure.2 after)
  | .terminated reason => some (.terminated reason)

theorem withdrawAfterBuild_graph (graphs : Graph fn) (args : Args types.resources .withdraw)
    (instruction : Built types.resources) (before : types.resources.State) :
    PGraph (withdrawAfterBuild types args instruction before ()) (withdrawAfterBuildFn fn args
      instruction before) := by
  apply PGraph.exists_step (graphs.literal before args.context.accounts)
  intro literal
  cases literal with
  | returned infos after =>
    apply PGraph.scope graphs.double
    · simpa [ReturnDrop.action] using returnDrops_graph fn graphs
        (List.append [.infos infos] (List.append (instructionDrops instruction) (tailDrops
          args.context)))
    · apply PGraph.bind
      · cases args.extra.custodian with
        | none => exact PGraph.eq_left _
        | some value => exact graphs.primitive .infoPush after (infos, value)
      · intro _ pushed
        exact invokeVector_graph fn graphs .legacyInline instruction infos args.context.signerSeeds
          pushed
  | unwound failure after =>
    apply PGraph.cleanup graphs.double
    simpa [List.map_append, List.map_map, List.append_assoc, infoDrops, Function.comp_def,
      ReturnDrop.action] using
      returnDrops_graph fn graphs (List.append (instructionDrops instruction) (List.append
        (args.extra.custodian.toList.map .account)
        (List.append ((args.context.accounts.unmoved failure.1.completed).map .account) (tailDrops
          args.context))))
  | terminated reason => exact PGraph.eq_left _

def afterBuildFn (operation : Operation) (args : Args types.resources operation)
    (instruction : Built types.resources) (before : types.resources.State) :
    Option (Out types (Except (Error types.resources operation.profile) Unit)) :=
  match operation with
  | .associated profile _ =>
      (invokeFn fn profile instruction args.context.accounts.owners args.context.signerSeeds
        before).bind
        (PGraph.cleanupFn fn.double (returnDrops fn
          (List.append (instructionDrops instruction) (List.append
            (args.context.accounts.owners.map .account) (tailDrops args.context)))))
  | .deactivate =>
      (invokeFn fn .legacyInline instruction args.context.accounts.moved args.context.signerSeeds
        before).bind
        (PGraph.cleanupFn fn.double (returnDrops fn
          (List.append (instructionDrops instruction) (List.append (args.context.accounts.moved.map
            .account) (tailDrops args.context)))))
  | .memo =>
      (invokeVectorFn fn .legacyBoxed instruction args.context.remainingAccounts
        args.context.signerSeeds before).bind
        (PGraph.cleanupFn fn.double (returnDrops fn (List.append (instructionDrops instruction)
          (tailDrops args.context))))
  | .metadata => (metadataInfosFn fn args.context before).bind fun prepared => match prepared with
      | .returned infos after =>
          (invokeVectorFn fn .legacyBoxed instruction infos args.context.signerSeeds after).bind
            (PGraph.cleanupFn fn.double (returnDrops fn
              (List.append (instructionDrops instruction) (List.append [.infos infos] (contextDrops
                args.context)))))
      | .unwound reason after =>
          PGraph.cleanupFn fn.double (returnDrops fn (List.append (instructionDrops instruction)
            (contextDrops args.context)))
            (.unwound reason after)
      | .terminated reason => some (.terminated reason)
  | .withdraw => withdrawAfterBuildFn fn args instruction before

theorem afterBuild_graph (graphs : Graph fn) (operation : Operation) (args : Args types.resources
  operation)
    (instruction : Built types.resources) (before : types.resources.State) :
    PGraph (afterBuild types operation args instruction before ()) (afterBuildFn fn operation args
      instruction before) := by
  cases operation with
  | associated profile kind =>
    apply PGraph.scope graphs.double
    · simpa [List.map_append, List.map_map, List.append_assoc, infoDrops, Function.comp_def,
      ReturnDrop.action] using returnDrops_graph fn graphs
        (List.append (instructionDrops instruction) (List.append (args.context.accounts.owners.map
          .account) (tailDrops args.context)))
    · exact invoke_graph fn graphs profile instruction args.context.accounts.owners
        args.context.signerSeeds before
  | deactivate =>
    apply PGraph.scope graphs.double
    · simpa [List.map_append, List.map_map, List.append_assoc, infoDrops, Function.comp_def,
      ReturnDrop.action] using returnDrops_graph fn graphs
        (List.append (instructionDrops instruction) (List.append (args.context.accounts.moved.map
          .account) (tailDrops args.context)))
    · exact invoke_graph fn graphs .legacyInline instruction args.context.accounts.moved
        args.context.signerSeeds before
  | memo =>
    apply PGraph.scope graphs.double
    · simpa using returnDrops_graph fn graphs (List.append (instructionDrops instruction)
        (tailDrops args.context))
    · exact invokeVector_graph fn graphs .legacyBoxed instruction args.context.remainingAccounts
        args.context.signerSeeds before
  | metadata =>
    apply PGraph.exists_step (metadataInfos_graph fn graphs args.context before)
    intro prepared
    cases prepared with
    | returned infos after =>
      apply PGraph.scope graphs.double
      · simpa [List.map_append, List.map_map, List.append_assoc, ReturnDrop.action] using
          returnDrops_graph fn graphs (List.append (instructionDrops instruction) (List.append
            [.infos infos] (contextDrops args.context)))
      · exact invokeVector_graph fn graphs .legacyBoxed instruction infos args.context.signerSeeds
          after
    | unwound reason after =>
      apply PGraph.cleanup graphs.double
      simpa using returnDrops_graph fn graphs (List.append (instructionDrops instruction)
        (contextDrops args.context))
    | terminated reason => exact PGraph.eq_left _
  | withdraw => exact withdrawAfterBuild_graph fn graphs args instruction before

def buildFailureDrops (operation : Operation) (args : Args types.resources operation) :
    List (ReturnDrop types.resources) :=
  (match operation with
    | .withdraw => args.extra.custodian.toList.map .account
    | _ => []) ++ contextDrops args.context

theorem buildFailureDrops_actions (operation : Operation) (args : Args types.resources operation) :
    (buildFailureDrops operation args).map ReturnDrop.action =
      AnchorSplSupport.buildFailureDrops types.resources operation args := by
  cases operation <;>
    simp [buildFailureDrops, AnchorSplSupport.buildFailureDrops, infoDrops, ReturnDrop.action,
      List.map_map]

def runFn (operation : Operation) (before : types.resources.State) (args : Args types.resources
  operation) :
    Option (Out types (Except (Error types.resources operation.profile) Unit)) :=
  (buildFn fn operation before args).bind fun built => match built with
  | .returned instruction after => afterBuildFn fn operation args instruction after
  | .unwound reason after => PGraph.cleanupFn fn.double (returnDrops fn (buildFailureDrops
    operation args))
      (.unwound reason after)
  | .terminated reason => some (.terminated reason)

/-- Exact finite graph of the source-shaped mathematical wrapper relation.
No CPI or SDK implementation is executed or proved by this equivalence. -/
theorem run_graph (graphs : Graph fn) (operation : Operation) (before : types.resources.State)
    (args : Args types.resources operation) :
    PGraph (run types operation before args) (runFn fn operation before args) := by
  apply PGraph.exists_step (build_graph fn graphs operation before args)
  intro built
  cases built with
  | returned instruction after => exact afterBuild_graph fn graphs operation args instruction after
  | unwound reason after =>
    apply PGraph.cleanup graphs.double
    simpa only [buildFailureDrops_actions] using returnDrops_graph fn graphs (buildFailureDrops
      operation args)
  | terminated reason => exact PGraph.eq_left _

end Solanalib.Specs.Core.AnchorSplSupport.Execution
