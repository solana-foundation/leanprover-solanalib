/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.ExecutionBuilders
public import Solanalib.Specs.Core.AnchorSplTokenOperations.Continuation

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Execution

/-- Computations used only for a selected explicit dependency interpretation.
The Graph certificate below connects every computation to its actual relation. -/
structure Functions {binding : Binding} (types : Types binding) where
  instruction : InstructionFn types.builder.instruction
  copyExtensions : types.builder.instruction.State → List ExtensionType →
    Option (InstructionOut types.builder.instruction types.builder.ExtensionResource)
  dropExtensions : types.builder.instruction.State → types.builder.ExtensionResource →
    Option (InstructionOut types.builder.instruction Unit)
  cloneRc : types.builder.instruction.State → AccountInfoRc.Field × Borrow.Handle →
    Option (Outcome types.builder.instruction.State Unit Empty types.builder.instruction.Terminal)
  dropRc : types.builder.instruction.State → AccountInfoRc.Field × Borrow.Handle →
    Option (Outcome types.builder.instruction.State Unit Empty types.builder.instruction.Terminal)
  dropRemaining : types.builder.instruction.State → types.RemainingResource →
    Option (Outcome types.builder.instruction.State Unit Empty types.builder.instruction.Terminal)
  newBox : types.builder.instruction.State →
    AnchorErrorOperations.Payload (binding.release.ProgramError types.StringResource)
      types.StringResource →
    Option (Outcome types.builder.instruction.State types.BoxResource Empty
      types.builder.instruction.Terminal)
  invoke : Option types.SeedRef → types.builder.instruction.State → CpiRequest.Request
    AccountInfo.Value →
    Option (InstructionOut types.builder.instruction (Except (binding.release.ProgramError
      types.StringResource) Unit))
  getReturnData : types.builder.instruction.State → Unit →
    Option (InstructionOut types.builder.instruction (Option (Solanalib.Runtime.Pubkey ×
      types.builder.instruction.ByteResource)))

structure Graph {binding : Binding} {types : Types binding} (fn : Functions types) : Prop where
  instruction : InstructionGraph fn.instruction
  copyExtensions : ∀ state values, PGraph (types.builder.extensions.copySlice state values)
    (fn.copyExtensions state values)
  dropExtensions : ∀ state resource, PGraph (types.builder.extensions.drop state resource)
    (fn.dropExtensions state resource)
  cloneRc : ∀ state field, PGraph (types.rc.cloneRc state field) (fn.cloneRc state field)
  dropRc : ∀ state field, PGraph (types.rc.dropRc state field) (fn.dropRc state field)
  dropRemaining : ∀ state resource, PGraph (types.dropRemaining state resource) (fn.dropRemaining
    state resource)
  newBox : ∀ state payload, PGraph (types.errors.newBox state payload) (fn.newBox state payload)
  invoke : ∀ seeds state call, PGraph (types.invoke seeds state call) (fn.invoke seeds state call)
  getReturnData : ∀ state args, PGraph (types.getReturnData state args) (fn.getReturnData state
    args)

variable {binding : Binding} {types : Types binding} (fn : Functions types)

def sizeAfterCopyFn (programId : Solanalib.Runtime.Pubkey) (metas :
  types.builder.instruction.MetaResource)
    (extensions : types.builder.ExtensionResource) (state : types.builder.instruction.State) :
    Option (InstructionOut types.builder.instruction (Except Token.Error (InstructionOwner types)))
      :=
  (types.builder.extensions.current state extensions).bind fun current =>
    ((buildDataFn fn.instruction (sizeSteps current) state).map (Outcome.map fun data =>
      Except.ok ({ programId, metas, data } : InstructionOwner types))).bind
      (PGraph.cleanupFn fn.instruction.double [fun after => fn.dropExtensions after extensions])

theorem sizeAfterCopy_graph (graphs : Graph fn) (programId : Solanalib.Runtime.Pubkey)
    (metas : types.builder.instruction.MetaResource) (extensions : types.builder.ExtensionResource)
    (state : types.builder.instruction.State) :
    PGraph (sizeAfterCopy types.builder programId metas extensions state ())
      (sizeAfterCopyFn fn programId metas extensions state) := by
  apply PGraph.exists_step (PGraph.ofOption (types.builder.extensions.current state extensions))
  intro current
  exact PGraph.scope graphs.instruction.double
    (PGraph.DropsGraph.cons (fun after => graphs.dropExtensions after extensions)
      PGraph.DropsGraph.nil)
    (PGraph.map _ (buildData_graph fn.instruction graphs.instruction (sizeSteps current) state))

def sizeFn (programId mint : Solanalib.Runtime.Pubkey) (extensions : List ExtensionType)
    (state : types.builder.instruction.State) :
    Option (InstructionOut types.builder.instruction (Except Token.Error (InstructionOwner types)))
      :=
  match Token.Instruction.checkProgram .either programId with
  | .error error => some (.returned (.error error) state)
  | .ok () => (fn.instruction.metas.fromList state [Instruction.accountMeta mint false false]).bind
      (PGraph.bindK fun metas allocated =>
        ((fn.copyExtensions allocated extensions).bind (PGraph.bindK fun copied after =>
          sizeAfterCopyFn fn programId metas copied after)).bind
          (PGraph.onUnwindFn fn.instruction.double [fun after => fn.instruction.metas.drop after
            metas]))

theorem size_graph (graphs : Graph fn) (programId mint : Solanalib.Runtime.Pubkey) (extensions :
  List ExtensionType)
    (state : types.builder.instruction.State) :
    PGraph (sizeRun types.builder programId mint extensions state ()) (sizeFn fn programId mint
      extensions state) := by
  unfold sizeRun sizeFn
  cases Token.Instruction.checkProgram .either programId with
  | error error => exact PGraph.eq_left _
  | ok result =>
    cases result
    exact PGraph.bind (graphs.instruction.metas.fromList state [Instruction.accountMeta mint false
      false])
      fun metas allocated => PGraph.protect graphs.instruction.double
        (PGraph.DropsGraph.cons (fun after => graphs.instruction.metas.drop after metas)
          PGraph.DropsGraph.nil)
        (PGraph.bind (graphs.copyExtensions allocated extensions)
          fun copied after => sizeAfterCopy_graph fn graphs programId metas copied after)

def buildFn (state : types.builder.instruction.State) : Construction →
    Option (InstructionOut types.builder.instruction (Except Token.Error (InstructionOwner types)))
  | .ordinary plan => instructionFn fn.instruction state plan
  | .pointer tag args => pointerFn fn.instruction tag args state
  | .size programId mint extensions => sizeFn fn programId mint extensions state

theorem build_graph (graphs : Graph fn) (state : types.builder.instruction.State) (input :
  Construction) :
    PGraph (build types.builder state input) (buildFn fn state input) := by
  cases input with
  | ordinary plan => exact instruction_graph fn.instruction graphs.instruction state plan
  | pointer tag args => exact pointer_graph fn.instruction graphs.instruction tag args state
  | size programId mint extensions => exact size_graph fn graphs programId mint extensions state

def cloneInfoFn (info : AccountInfo.Value) (state : types.builder.instruction.State) :
    Option (Outcome types.builder.instruction.State AccountInfo.Value Empty
      types.builder.instruction.Terminal) :=
  (fn.cloneRc state (.lamports, info.lamports)).bind (PGraph.bindK fun _ after =>
    (fn.cloneRc after (.data, info.data)).map (Outcome.map fun _ => AccountInfo.clone info))

theorem cloneInfo_graph (graphs : Graph fn) (info : AccountInfo.Value) (state :
  types.builder.instruction.State) :
    PGraph (AccountInfoRc.cloneCall types.rc state info) (cloneInfoFn fn info state) :=
  PGraph.bind (graphs.cloneRc state (.lamports, info.lamports)) fun _ after =>
    PGraph.map _ (graphs.cloneRc after (.data, info.data))

def cloneAccountsFn : List AccountInfo.Value → types.builder.instruction.State →
    Option (Outcome types.builder.instruction.State (List AccountInfo.Value) Empty
      types.builder.instruction.Terminal)
  | [], state => some (.returned [] state)
  | info :: rest, state => (cloneInfoFn fn info state).bind
      (PGraph.bindK fun copied after => (cloneAccountsFn rest after).map (Outcome.map (List.cons
        copied)))

theorem cloneAccounts_graph (graphs : Graph fn) : ∀ accounts state,
    PGraph (cloneAccounts types.rc accounts state ()) (cloneAccountsFn fn accounts state)
  | [], _ => PGraph.eq_left _
  | info :: rest, state => PGraph.bind (cloneInfo_graph fn graphs info state)
      fun copied after => PGraph.map (List.cons copied) (cloneAccounts_graph graphs rest after)

def prepareFn (args : Input types) (state : types.builder.instruction.State) :
    Option (InstructionOut types.builder.instruction (List AccountInfo.Value)) :=
  if binding.release.clones then
    (cloneAccountsFn fn (invocationAccounts args) state).map AccountInfoRc.liftOutcome
  else some (.returned (invocationAccounts args) state)

theorem prepare_graph (graphs : Graph fn) (args : Input types) (state :
  types.builder.instruction.State) :
    PGraph (prepareAccounts types args state ()) (prepareFn fn args state) := by
  unfold prepareAccounts prepareFn
  cases binding.release.clones with
  | false => exact PGraph.eq_left _
  | true => exact PGraph.exists_eq AccountInfoRc.liftOutcome (cloneAccounts_graph fn graphs _ state)

def wrapProgramFn {State Program S B Terminal : Type} (storage : AnchorErrorOperations.Storage)
    (allocate : State → AnchorErrorOperations.Payload Program S → Option (Outcome State B Empty
      Terminal))
    (state : State) (error : Program) :
    Option (Outcome State (AnchorErrorOperations.Error storage Program S B) Empty Terminal) :=
  match storage with
  | .inline => some (.returned (.program ⟨error, none, none⟩) state)
  | .boxed => (allocate state (.program ⟨error, none, none⟩)).map (Outcome.map
    AnchorErrorOwned.Error.mk)

theorem wrapProgram_graph {State Program S B Terminal : Type} (storage :
  AnchorErrorOperations.Storage)
    (ops : AnchorErrorOperations.Ops State Program S B Terminal)
    (allocate : State → AnchorErrorOperations.Payload Program S → Option (Outcome State B Empty
      Terminal))
    (graph : ∀ state payload, PGraph (ops.newBox state payload) (allocate state payload))
    (state : State) (error : Program) :
    PGraph (AnchorErrorOperations.fromProgram storage ops state error) (wrapProgramFn storage
      allocate state error) := by
  cases storage with
  | inline => exact PGraph.eq_left _
  | boxed => exact PGraph.map AnchorErrorOwned.Error.mk (graph state (.program ⟨error, none, none⟩))

def convertFn (state : types.builder.instruction.State) (error : binding.release.ProgramError
  types.StringResource) :
    Option (InstructionOut types.builder.instruction (Error types)) :=
  (wrapProgramFn binding.release.storage fn.newBox state error).map AccountInfoRc.liftOutcome

theorem convert_graph (graphs : Graph fn) (state : types.builder.instruction.State)
    (error : binding.release.ProgramError types.StringResource) :
    PGraph (convert types state error) (convertFn fn state error) :=
  PGraph.exists_eq AccountInfoRc.liftOutcome
    (wrapProgram_graph binding.release.storage types.errors fn.newBox graphs.newBox state error)

def convertResultFn {Value : Type} (state : types.builder.instruction.State) :
    Except (binding.release.ProgramError types.StringResource) Value →
      Option (InstructionOut types.builder.instruction (Except (Error types) Value))
  | .ok value => some (.returned (.ok value) state)
  | .error error => (convertFn fn state error).map (Outcome.map Except.error)

theorem convertResult_graph {Value : Type} (graphs : Graph fn) (state :
  types.builder.instruction.State)
    (result : Except (binding.release.ProgramError types.StringResource) Value) :
    PGraph (convertResult types state result) (convertResultFn fn state result) := by
  cases result with
  | error error => exact PGraph.map Except.error (convert_graph fn graphs state error)
  | ok value => exact PGraph.eq_left _

def invokeFn (args : Input types) (instruction : InstructionOwner types) (accounts : List
  AccountInfo.Value)
    (state : types.builder.instruction.State) :
    Option (InstructionOut types.builder.instruction (Except (Error types) Unit)) :=
  (request types state args instruction accounts).bind fun call =>
    (fn.invoke (seedReference args) state call).bind
      (PGraph.bindK fun result after => convertResultFn fn after result)

theorem invoke_graph (graphs : Graph fn) (args : Input types) (instruction : InstructionOwner types)
    (accounts : List AccountInfo.Value) (state : types.builder.instruction.State) :
    PGraph (invokeAndConvert types args instruction accounts state ()) (invokeFn fn args
      instruction accounts state) := by
  apply PGraph.exists_step (PGraph.ofOption (request types state args instruction accounts))
  intro call
  exact PGraph.bind (graphs.invoke (seedReference args) state call)
    fun result after => convertResult_graph fn graphs after result

end Solanalib.Specs.Core.AnchorSplTokenOperations.Execution
