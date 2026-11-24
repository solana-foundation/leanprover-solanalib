/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.ExecutionVectors

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Execution

open Token.InstructionAllocated

/-- Computed forms of an explicit constructor interpretation. These are not
additional postulates: InstructionGraph must prove exact equivalences with
each primitive relation before the computations can certify a model exit. -/
structure InstructionFn (types : Token.InstructionAllocated.Types) where
  bytes : VecFn types.State UInt8 types.ByteResource types.Unwind types.Terminal
  metas : VecFn types.State Solanalib.Runtime.CpiMeta types.MetaResource types.Unwind types.Terminal
  double : types.State → types.Unwind → types.Unwind → Option types.Terminal

structure InstructionGraph {types : Token.InstructionAllocated.Types} (fn : InstructionFn types) :
  Prop where
  bytes : VecGraph types.bytes fn.bytes
  metas : VecGraph types.metas fn.metas
  double : ∀ state first second, PGraph (types.doubleUnwind state first second) (fn.double state
    first second)

variable {types : Token.InstructionAllocated.Types} (fn : InstructionFn types)

abbrev InstructionOut (types : Token.InstructionAllocated.Types) (Value : Type) :=
  Outcome types.State Value types.Unwind types.Terminal

def writeDataFn (resource : types.ByteResource) : List DataStep → types.State → Option
  (InstructionOut types Unit)
  | [], state => some (.returned () state)
  | step :: rest, state =>
    (match step with
      | .push byte => fn.bytes.push state (resource, byte)
      | .extend bytes => fn.bytes.extend state (resource, bytes)).bind
      (PGraph.bindK fun _ after => writeDataFn resource rest after)

theorem writeData_graph (graphs : InstructionGraph fn) (resource : types.ByteResource) :
    ∀ steps state, PGraph (writeData types resource steps state ()) (writeDataFn fn resource steps
      state)
  | [], _ => PGraph.eq_left _
  | step :: rest, state => by
    apply PGraph.bind
    · cases step with
      | push byte => exact graphs.bytes.push state (resource, byte)
      | extend bytes => exact graphs.bytes.extend state (resource, bytes)
    · intro _ after
      exact writeData_graph graphs resource rest after

def pushMetasFn (resource : types.MetaResource) :
    List Solanalib.Runtime.CpiMeta → types.State → Option (InstructionOut types Unit)
  | [], state => some (.returned () state)
  | item :: rest, state => (fn.metas.push state (resource, item)).bind
      (PGraph.bindK fun _ after => pushMetasFn resource rest after)

theorem pushMetas_graph (graphs : InstructionGraph fn) (resource : types.MetaResource) :
    ∀ items state, PGraph (pushMetas types resource items state ()) (pushMetasFn fn resource items
      state)
  | [], _ => PGraph.eq_left _
  | item :: rest, state => PGraph.bind (graphs.metas.push state (resource, item))
      fun _ after => pushMetas_graph graphs resource rest after

def buildMetasFn (plan : MetaPlan) (state : types.State) : Option (InstructionOut types
  types.MetaResource) :=
  match plan with
  | .fromList items => fn.metas.fromList state items
  | .withCapacity capacity items =>
    (fn.metas.withCapacity state capacity).bind (PGraph.bindK fun resource after =>
      ((pushMetasFn fn resource items after).map (Outcome.map fun _ => resource)).bind
        (PGraph.onUnwindFn fn.double [fun current => fn.metas.drop current resource]))
  | .fromListThenPush initial rest =>
    (fn.metas.fromList state initial).bind (PGraph.bindK fun resource after =>
      ((pushMetasFn fn resource rest after).map (Outcome.map fun _ => resource)).bind
        (PGraph.onUnwindFn fn.double [fun current => fn.metas.drop current resource]))

theorem buildMetas_graph (graphs : InstructionGraph fn) (plan : MetaPlan) (state : types.State) :
    PGraph (buildMetas types plan state ()) (buildMetasFn fn plan state) := by
  cases plan with
  | fromList items => exact graphs.metas.fromList state items
  | withCapacity capacity items =>
    exact PGraph.bind (graphs.metas.withCapacity state capacity) fun resource after =>
      PGraph.protect graphs.double
        (PGraph.DropsGraph.cons (fun current => graphs.metas.drop current resource)
          PGraph.DropsGraph.nil)
        (PGraph.map _ (pushMetas_graph fn graphs resource items after))
  | fromListThenPush initial rest =>
    exact PGraph.bind (graphs.metas.fromList state initial) fun resource after =>
      PGraph.protect graphs.double
        (PGraph.DropsGraph.cons (fun current => graphs.metas.drop current resource)
          PGraph.DropsGraph.nil)
        (PGraph.map _ (pushMetas_graph fn graphs resource rest after))

def buildDataFn (steps : List DataStep) (state : types.State) : Option (InstructionOut types
  types.ByteResource) :=
  (fn.bytes.withCapacity state types.enumSize).bind (PGraph.bindK fun resource after =>
    ((writeDataFn fn resource steps after).map (Outcome.map fun _ => resource)).bind
      (PGraph.onUnwindFn fn.double [fun current => fn.bytes.drop current resource]))

theorem buildData_graph (graphs : InstructionGraph fn) (steps : List DataStep) (state :
  types.State) :
    PGraph (buildData types steps state ()) (buildDataFn fn steps state) :=
  PGraph.bind (graphs.bytes.withCapacity state types.enumSize) fun resource after =>
    PGraph.protect graphs.double
      (PGraph.DropsGraph.cons (fun current => graphs.bytes.drop current resource)
        PGraph.DropsGraph.nil)
      (PGraph.map _ (writeData_graph fn graphs resource steps after))

/-- Functional evaluation of the existing allocated constructor relation.
Both allocation orders and all intermediate failure cleanup remain explicit. -/
def instructionFn (state : types.State) (plan : Plan) :
    Option (InstructionOut types (Except Token.Error (Value types))) :=
  match Token.Instruction.checkProgram plan.programs plan.programId with
  | .error error => some (.returned (.error error) state)
  | .ok () =>
    match plan.order with
    | .dataThenMetas =>
      (fn.bytes.withCapacity state types.enumSize).bind (PGraph.bindK fun data after =>
        ((writeDataFn fn data plan.dataSteps after).bind (PGraph.bindK fun _ current =>
          (buildMetasFn fn plan.metas current).map (Outcome.map fun metas => Except.ok
            ({ programId := plan.programId, metas, data } : Value types)))).bind
          (PGraph.onUnwindFn fn.double [fun current => fn.bytes.drop current data]))
    | .metasThenData =>
      (buildMetasFn fn plan.metas state).bind (PGraph.bindK fun metas after =>
        ((buildDataFn fn plan.dataSteps after).map (Outcome.map fun data => Except.ok
          ({ programId := plan.programId, metas, data } : Value types))).bind
          (PGraph.onUnwindFn fn.double [fun current => fn.metas.drop current metas]))

theorem instruction_graph (graphs : InstructionGraph fn) (state : types.State) (plan : Plan) :
    PGraph (Token.InstructionAllocated.run types state plan) (instructionFn fn state plan) := by
  unfold Token.InstructionAllocated.run instructionFn
  cases Token.Instruction.checkProgram plan.programs plan.programId with
  | error error => exact PGraph.eq_left _
  | ok result =>
    cases result
    cases plan.order with
    | dataThenMetas =>
      exact PGraph.bind (graphs.bytes.withCapacity state types.enumSize) fun data after =>
        PGraph.protect graphs.double
          (PGraph.DropsGraph.cons (fun current => graphs.bytes.drop current data)
            PGraph.DropsGraph.nil)
          (PGraph.bind (writeData_graph fn graphs data plan.dataSteps after) fun _ current =>
            PGraph.map _ (buildMetas_graph fn graphs plan.metas current))
    | metasThenData =>
      exact PGraph.bind (buildMetas_graph fn graphs plan.metas state) fun metas after =>
        PGraph.protect graphs.double
          (PGraph.DropsGraph.cons (fun current => graphs.metas.drop current metas)
            PGraph.DropsGraph.nil)
          (PGraph.map _ (buildData_graph fn graphs plan.dataSteps after))

def pointerAfterMetasFn (tag : UInt8) (args : Token.MetadataPointer.Args)
    (metas : types.MetaResource) (state : types.State) :
    Option (InstructionOut types (Except Token.Error (Value types))) :=
  match Token.MetadataPointer.fields args with
  | .error error => PGraph.cleanupFn fn.double [fun current => fn.metas.drop current metas]
      (.returned (.error error) state)
  | .ok encoded => ((buildDataFn fn (Token.MetadataPointer.steps tag encoded) state).map
      (Outcome.map fun data => Except.ok ({ programId := args.programId, metas, data } : Value
        types))).bind
        (PGraph.onUnwindFn fn.double [fun current => fn.metas.drop current metas])

theorem pointerAfterMetas_graph (graphs : InstructionGraph fn) (tag : UInt8) (args :
  Token.MetadataPointer.Args)
    (metas : types.MetaResource) (state : types.State) :
    PGraph (Token.MetadataPointer.afterMetas tag types args metas state)
      (pointerAfterMetasFn fn tag args metas state) := by
  unfold Token.MetadataPointer.afterMetas pointerAfterMetasFn
  cases Token.MetadataPointer.fields args with
  | error error =>
    exact PGraph.cleanup graphs.double _ _
      (PGraph.DropsGraph.cons (fun current => graphs.metas.drop current metas)
        PGraph.DropsGraph.nil) _
  | ok encoded =>
    exact PGraph.protect graphs.double
      (PGraph.DropsGraph.cons (fun current => graphs.metas.drop current metas)
        PGraph.DropsGraph.nil)
      (PGraph.map _ (buildData_graph fn graphs (Token.MetadataPointer.steps tag encoded) state))

def pointerFn (tag : UInt8) (args : Token.MetadataPointer.Args) (state : types.State) :
    Option (InstructionOut types (Except Token.Error (Value types))) :=
  match Token.Instruction.checkProgram .token2022 args.programId with
  | .error error => some (.returned (.error error) state)
  | .ok () => (fn.metas.fromList state (Token.MetadataPointer.metas args)).bind
      (PGraph.bindK fun metas after => pointerAfterMetasFn fn tag args metas after)

theorem pointer_graph (graphs : InstructionGraph fn) (tag : UInt8) (args :
  Token.MetadataPointer.Args)
    (state : types.State) : PGraph (Token.MetadataPointer.run tag types state args) (pointerFn fn
      tag args state) := by
  unfold Token.MetadataPointer.run pointerFn
  cases Token.Instruction.checkProgram .token2022 args.programId with
  | error error => exact PGraph.eq_left _
  | ok result =>
    cases result
    exact PGraph.bind (graphs.metas.fromList state (Token.MetadataPointer.metas args))
      fun metas after => pointerAfterMetas_graph fn graphs tag args metas after

end Solanalib.Specs.Core.AnchorSplTokenOperations.Execution
