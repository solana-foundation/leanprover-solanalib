/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionPlan
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.InstructionAllocated

/-- Dependency interpretations and target layout for the operational builder.
Resource types can distinguish byte and metadata allocations. -/
structure Types where
  /-- The actual state shared by dependency calls. -/
  State : Type
  /-- Stable logical identities for owned byte vectors. -/
  ByteResource : Type
  /-- Stable logical identities for owned metadata vectors. -/
  MetaResource : Type
  /-- Reasons for finite unwinding exits. -/
  Unwind : Type
  /-- Reasons for finite terminal exits, which expose no post-state. -/
  Terminal : Type
  /-- The selected target usize width. -/
  wordBits : Nat
  /-- The selected source TokenInstruction enum size used by Vec::with_capacity. -/
  enumSize : Nat
  /-- Actual instruction byte-vector dependency operations. -/
  bytes : Owned.VectorOps State UInt8 ByteResource Unwind Terminal
  /-- Actual account-metadata vector dependency operations. -/
  metas : Owned.VectorOps State Solanalib.Runtime.CpiMeta MetaResource Unwind Terminal
  /-- The explicit terminal policy for a destructor unwinding during unwind. -/
  doubleUnwind : State → Unwind → Unwind → Terminal → Prop

/-- Returned instruction vectors retain ownership through their resource
identities. Their current contents are observed separately. -/
abbrev Value (types : Types) :=
  Solanalib.Specs.Core.Instruction.OwnedValue types.MetaResource types.ByteResource

/-- Observe both vectors in the current callback state, including any partial
changes a dependency may have made. -/
def observe (types : Types) (state : types.State) (value : Value types) :
    Option Solanalib.Runtime.CpiInstruction :=
  value.observe (types.metas.current state) (types.bytes.current state)

/-- The source writes packed instruction bytes through individual Vec calls.
The state and exceptional exits of the dependency are preserved at every call. -/
def writeData (types : Types) (resource : types.ByteResource) :
    List DataStep → Callback.Run types.State Unit Unit types.Unwind types.Terminal
  | [] => fun state _ outcome => outcome = .returned () state
  | step :: rest =>
    let operation := match step with
      | .push byte => fun state (_ : Unit) => types.bytes.push state (resource, byte)
      | .extend bytes => fun state (_ : Unit) => types.bytes.extend state (resource, bytes)
    Callback.bind operation fun _ state outcome => writeData types resource rest state () outcome

/-- Metadata is pushed in source order, retaining duplicates. -/
def pushMetas (types : Types) (resource : types.MetaResource) :
    List Solanalib.Runtime.CpiMeta → Callback.Run types.State Unit Unit types.Unwind types.Terminal
  | [] => fun state _ outcome => outcome = .returned () state
  | item :: rest =>
    Callback.bind (fun state (_ : Unit) => types.metas.push state (resource, item))
      fun _ state outcome => pushMetas types resource rest state () outcome

/-- A literal vector is one dependency operation. Either subsequently
populated branch owns its resource while pushing and drops that actual
resource on unwind, retaining any partial contents from the failed push. -/
def buildMetas (types : Types) (plan : MetaPlan) :
    Callback.Run types.State Unit types.MetaResource types.Unwind types.Terminal :=
  match plan with
  | .fromList items => fun state _ => types.metas.fromList state items
  | .withCapacity capacity items =>
    Callback.bind (fun state (_ : Unit) => types.metas.withCapacity state capacity)
      fun resource state outcome =>
        Owned.protect types.doubleUnwind
          [fun current => types.metas.drop current resource]
          (Callback.map (fun _ => resource) (pushMetas types resource items))
          state () outcome
  | .fromListThenPush initial rest =>
    Callback.bind (fun state (_ : Unit) => types.metas.fromList state initial)
      fun resource state outcome =>
        Owned.protect types.doubleUnwind
          [fun current => types.metas.drop current resource]
          (Callback.map (fun _ => resource) (pushMetas types resource rest))
          state () outcome

/-- TokenInstruction::pack owns its byte vector across the ordered writes.
Packing unwind cleans this actual byte owner before unwinding into a caller
that may already own metadata. A normal result transfers the byte owner. -/
def buildData (types : Types) (steps : List DataStep) :
    Callback.Run types.State Unit types.ByteResource types.Unwind types.Terminal :=
  Callback.bind (fun state (_ : Unit) => types.bytes.withCapacity state types.enumSize)
    fun resource state outcome =>
      Owned.protect types.doubleUnwind
        [fun current => types.bytes.drop current resource]
        (Callback.map (fun _ => resource) (writeData types resource steps))
        state () outcome

/-- Program rejection allocates nothing. The plan retains the source order
of the two constructions. The earlier owner remains live across the later
construction and its cleanup, so surviving unwind drops the later partial
owner before the earlier one. Normal return transfers both owners. -/
def run (types : Types) (state : types.State) (plan : Plan)
    (outcome : Outcome types.State (Except Error (Value types)) types.Unwind types.Terminal) : Prop
      :=
  match Instruction.checkProgram plan.programs plan.programId with
  | .error error => outcome = .returned (.error error) state
  | .ok () =>
    match plan.order with
    | .dataThenMetas =>
      Callback.bind (fun before (_ : Unit) => types.bytes.withCapacity before types.enumSize)
        (fun data after =>
          Owned.protect types.doubleUnwind
            [fun current => types.bytes.drop current data]
            (Callback.bind (writeData types data plan.dataSteps)
              fun _ current result =>
                Callback.map (fun metas => Except.ok
                  ({ programId := plan.programId, metas, data } : Value types))
                  (buildMetas types plan.metas) current () result)
            after ())
        state () outcome
    | .metasThenData =>
      Callback.bind (buildMetas types plan.metas)
        (fun metas after =>
          Owned.protect types.doubleUnwind
            [fun current => types.metas.drop current metas]
            (Callback.map (fun data => Except.ok
              ({ programId := plan.programId, metas, data } : Value types))
              (buildData types plan.dataSteps))
            after ())
        state () outcome

/-- A Rust Instruction drops its metadata field before its byte-data field. -/
def drops (types : Types) (value : Value types) :
    List (Owned.DropAction types.State types.Unwind types.Terminal) :=
  [fun state => types.metas.drop state value.metas,
    fun state => types.bytes.drop state value.data]


end Solanalib.Specs.Core.Token.InstructionAllocated
