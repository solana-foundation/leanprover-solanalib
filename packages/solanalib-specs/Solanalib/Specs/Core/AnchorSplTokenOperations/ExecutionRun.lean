/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Execution

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Execution

variable {binding : Binding} {types : Types binding} (fn : Functions types)

theorem drops_append {State Unwind Terminal : Type}
    (last : List (Owned.DropAction State Unwind Terminal))
    (lastFns : List (State → Option (Outcome State Unit Unwind Terminal)))
    (lastGraph : PGraph.DropsGraph last lastFns) :
    ∀ first firstFns, PGraph.DropsGraph first firstFns →
      PGraph.DropsGraph (first ++ last) (firstFns ++ lastFns)
  | [], [], _ => lastGraph
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | _ :: rest, _ :: restFns, ⟨head, tail⟩ =>
      ⟨head, drops_append last lastFns lastGraph rest restFns tail⟩

def dropInfoFn (info : AccountInfo.Value) (state : types.builder.instruction.State) :
    Option (InstructionOut types.builder.instruction Unit) :=
  ((fn.dropRc state (.lamports, info.lamports)).bind
    (PGraph.bindK fun _ after => fn.dropRc after (.data, info.data))).map AccountInfoRc.liftOutcome

theorem dropInfo_graph (graphs : Graph fn) (info : AccountInfo.Value) (state :
  types.builder.instruction.State) :
    PGraph (dropInfo types info state) (dropInfoFn fn info state) :=
  PGraph.exists_eq AccountInfoRc.liftOutcome
    (PGraph.bind (graphs.dropRc state (.lamports, info.lamports))
      fun _ after => graphs.dropRc after (.data, info.data))

def infoDropFns (infos : List AccountInfo.Value) := infos.map (dropInfoFn fn)

theorem infoDrops_graph (graphs : Graph fn) : ∀ infos,
    PGraph.DropsGraph (infoDrops types infos) (infoDropFns fn infos)
  | [] => trivial
  | info :: rest => ⟨dropInfo_graph fn graphs info, infoDrops_graph graphs rest⟩

def contextDropFns (args : Input types) (infos : List AccountInfo.Value) :=
  infoDropFns fn infos ++
    [fun state => (fn.dropRemaining state args.context.remainingAccounts).map
      AccountInfoRc.liftOutcome] ++
    infoDropFns fn (binding.release.programOwners args.context.program)

theorem contextDrops_graph (graphs : Graph fn) (args : Input types) (infos : List
  AccountInfo.Value) :
    PGraph.DropsGraph (contextDrops types args infos) (contextDropFns fn args infos) := by
  apply drops_append _ _ (infoDrops_graph fn graphs (binding.release.programOwners
    args.context.program))
  exact drops_append _ _
    (PGraph.DropsGraph.cons
      (fun state => PGraph.exists_eq AccountInfoRc.liftOutcome (graphs.dropRemaining state
        args.context.remainingAccounts))
      PGraph.DropsGraph.nil) _ _ (infoDrops_graph fn graphs infos)

def instructionDropFns (instruction : InstructionOwner types) :=
  [fun state => fn.instruction.metas.drop state instruction.metas,
    fun state => fn.instruction.bytes.drop state instruction.data]

theorem instructionDrops_graph (graphs : Graph fn) (instruction : InstructionOwner types) :
    PGraph.DropsGraph (Token.InstructionAllocated.drops types.builder.instruction instruction)
      (instructionDropFns fn instruction) :=
  ⟨fun state => graphs.instruction.metas.drop state instruction.metas,
    fun state => graphs.instruction.bytes.drop state instruction.data, trivial⟩

def tailDropFns (args : Input types) (instruction : InstructionOwner types) (infos : List
  AccountInfo.Value) :=
  instructionDropFns fn instruction ++ infoDropFns fn infos ++ contextDropFns fn args
    (retainedAccounts args)

theorem tailDrops_graph (graphs : Graph fn) (args : Input types) (instruction : InstructionOwner
  types)
    (infos : List AccountInfo.Value) :
    PGraph.DropsGraph (tailDrops types args instruction infos) (tailDropFns fn args instruction
      infos) :=
  drops_append _ _ (contextDrops_graph fn graphs args (retainedAccounts args)) _ _
    (drops_append _ _ (infoDrops_graph fn graphs infos) _ _ (instructionDrops_graph fn graphs
      instruction))

def decodeReturnDataFn (expected : Solanalib.Runtime.Pubkey) (state :
  types.builder.instruction.State) :
    Option (Solanalib.Runtime.Pubkey × types.builder.instruction.ByteResource) →
      Option (InstructionOut types.builder.instruction
        (Except (binding.release.ProgramError types.StringResource) Return))
  | none => some (.returned (.error (binding.release.invalidInstructionData types.StringResource))
    state)
  | some (key, data) =>
      if key ≠ expected then PGraph.cleanupFn fn.instruction.double
        [fun after => fn.instruction.bytes.drop after data]
        (.returned (.error (binding.release.incorrectProgramId types.StringResource)) state)
      else (types.builder.instruction.bytes.current state data).bind fun bytes =>
        PGraph.cleanupFn fn.instruction.double [fun after => fn.instruction.bytes.drop after data]
          (.returned (if bytes.length = 8 then .ok (.size (UInt64.ofNat (Solanalib.Runtime.leNat
            bytes)))
            else .error (binding.release.invalidInstructionData types.StringResource)) state)

theorem decodeReturnData_graph (graphs : Graph fn) (expected : Solanalib.Runtime.Pubkey)
    (state : types.builder.instruction.State) (returned : Option (Solanalib.Runtime.Pubkey ×
      types.builder.instruction.ByteResource)) :
    PGraph (decodeReturnData types expected state returned) (decodeReturnDataFn fn expected state
      returned) := by
  cases returned with
  | none => exact PGraph.eq_left _
  | some pair =>
    obtain ⟨key, data⟩ := pair
    unfold decodeReturnData decodeReturnDataFn
    by_cases same : key = expected
    · simp only [same, ne_eq, not_true_eq_false, ↓reduceIte]
      apply PGraph.exists_step (PGraph.ofOption (types.builder.instruction.bytes.current state
        data))
      intro bytes
      exact PGraph.cleanup graphs.instruction.double _ _
        (PGraph.DropsGraph.cons (fun after => graphs.instruction.bytes.drop after data)
          PGraph.DropsGraph.nil) _
    · simp only [same, ne_eq, not_false_eq_true, ↓reduceIte]
      exact PGraph.cleanup graphs.instruction.double _ _
        (PGraph.DropsGraph.cons (fun after => graphs.instruction.bytes.drop after data)
          PGraph.DropsGraph.nil) _

def getSizeFn (expected : Solanalib.Runtime.Pubkey) (state : types.builder.instruction.State) :
  Option (Exit types) :=
  (fn.getReturnData state ()).bind (PGraph.bindK fun returned after =>
    (decodeReturnDataFn fn expected after returned).bind
      (PGraph.bindK fun result current => convertResultFn fn current result))

theorem getSize_graph (graphs : Graph fn) (expected : Solanalib.Runtime.Pubkey) (state :
  types.builder.instruction.State) :
    PGraph (getSize types expected state ()) (getSizeFn fn expected state) :=
  PGraph.bind (graphs.getReturnData state ()) fun returned after =>
    PGraph.bind (decodeReturnData_graph fn graphs expected after returned)
      fun result current => convertResult_graph fn graphs current result

def sizeInvokeFn (args : Input types) (instruction : InstructionOwner types) (infos : List
  AccountInfo.Value)
    (state : types.builder.instruction.State) :
    Option (InstructionOut types.builder.instruction (Except (Error types) Unit)) :=
  (invokeFn fn args instruction infos state).bind (PGraph.cleanupFn fn.instruction.double
    (infoDropFns fn infos))

theorem sizeInvoke_graph (graphs : Graph fn) (args : Input types) (instruction : InstructionOwner
  types)
    (infos : List AccountInfo.Value) (state : types.builder.instruction.State) :
    PGraph (sizeInvoke types args instruction infos state ()) (sizeInvokeFn fn args instruction
      infos state) :=
  PGraph.scope graphs.instruction.double (infoDrops_graph fn graphs infos)
    (invoke_graph fn graphs args instruction infos state)

def afterPreparedFn (args : Input types) (instruction : InstructionOwner types) (infos : List
  AccountInfo.Value)
    (state : types.builder.instruction.State) : Option (Exit types) :=
  if binding.operation = .getAccountDataSize then
    ((sizeInvokeFn fn args instruction infos state).bind (PGraph.bindK fun result after =>
      match result with
      | .error error => some (.returned (.error error) after)
      | .ok () => getSizeFn fn (selectedProgram args) after)).bind
      (PGraph.cleanupFn fn.instruction.double
        (instructionDropFns fn instruction ++ contextDropFns fn args (retainedAccounts args)))
  else ((invokeFn fn args instruction infos state).map
    (Outcome.map (Except.map fun _ => Return.unit))).bind
    (PGraph.cleanupFn fn.instruction.double (tailDropFns fn args instruction infos))

theorem afterPrepared_graph (graphs : Graph fn) (args : Input types) (instruction :
  InstructionOwner types)
    (infos : List AccountInfo.Value) (state : types.builder.instruction.State) :
    PGraph (afterPrepared types args instruction infos state ()) (afterPreparedFn fn args
      instruction infos state) := by
  unfold afterPrepared afterPreparedFn
  by_cases sizing : binding.operation = .getAccountDataSize
  · simp only [sizing, ↓reduceIte]
    apply PGraph.scope graphs.instruction.double
      (drops_append _ _ (contextDrops_graph fn graphs args (retainedAccounts args)) _ _
        (instructionDrops_graph fn graphs instruction))
    apply PGraph.bind (sizeInvoke_graph fn graphs args instruction infos state)
    intro result after
    cases result with
    | error error => exact PGraph.eq_left _
    | ok value => cases value; exact getSize_graph fn graphs (selectedProgram args) after
  · simp only [sizing, ↓reduceIte]
    exact PGraph.scope graphs.instruction.double (tailDrops_graph fn graphs args instruction infos)
      (PGraph.map _ (invoke_graph fn graphs args instruction infos state))

/-- Computation of the full registered relation at the supplied primitive
interpretation. An absent local read produces None, not a manufactured exit. -/
def runFn (state : types.builder.instruction.State) (args : Input types) : Option (Exit types) :=
  (buildFn fn state (argsConstruction args)).bind fun built => match built with
  | .returned (.error error) after =>
      ((convertFn fn after (builderFailure types error)).map (Outcome.map Except.error)).bind
        (PGraph.cleanupFn fn.instruction.double (contextDropFns fn args (allAccounts args)))
  | .returned (.ok instruction) after => (prepareFn fn args after).bind
      (PGraph.bindK fun accounts prepared => afterPreparedFn fn args instruction accounts prepared)
  | .unwound reason after => PGraph.cleanupFn fn.instruction.double
      (contextDropFns fn args (allAccounts args)) (.unwound reason after)
  | .terminated reason => some (.terminated reason)

/-- This is an equivalence with the full model relation, not merely agreement
with a planned wire value or one chosen successful execution. -/
theorem run_graph (graphs : Graph fn) (state : types.builder.instruction.State) (args : Input
  types) :
    PGraph (run types state args) (runFn fn state args) := by
  apply PGraph.exists_step (build_graph fn graphs state (argsConstruction args))
  intro built
  cases built with
  | returned value after =>
    cases value with
    | error error =>
      exact PGraph.scope graphs.instruction.double (contextDrops_graph fn graphs args (allAccounts
        args))
        (PGraph.map Except.error (convert_graph fn graphs after (builderFailure types error)))
    | ok instruction =>
      exact PGraph.bind (prepare_graph fn graphs args after)
        fun accounts prepared => afterPrepared_graph fn graphs args instruction accounts prepared
  | unwound reason after =>
    exact PGraph.cleanup graphs.instruction.double _ _
      (contextDrops_graph fn graphs args (allAccounts args)) _
  | terminated reason => exact PGraph.eq_left _

end Solanalib.Specs.Core.AnchorSplTokenOperations.Execution
