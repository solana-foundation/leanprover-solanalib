/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionBuilder

/-- The two feature-selected serializers used by System interface 3.2.0.
Wincode is selected whenever that feature is present; bincode is the other
enabled branch. The selected source configuration is a separate binding. -/
inductive Format where
  | bincode
  | wincode
  deriving DecidableEq, Repr

structure Types where
  State : Type
  Data : Type
  MetaResource : Type
  ByteResource : Type
  Error : Type
  Unwind : Type
  Terminal : Type

/-- These are dependency operations at their actual source call sites. Their
local laws, codec correctness and any resource frames are separate obligations.
The operational composition below retains every admitted provider outcome. -/
structure Providers (types : Types) where
  metaVec : Owned.VectorOps types.State Instruction.Meta types.MetaResource
    types.Unwind types.Terminal
  byteVec : Owned.VectorOps types.State UInt8 types.ByteResource
    types.Unwind types.Terminal
  serialize : Callback.Run types.State (Format × types.Data)
    (Except types.Error types.ByteResource) types.Unwind types.Terminal
  /-- The actual `Result::unwrap` failure dependency. This includes its
  formatting/panic and owned-error cleanup; its result type excludes a normal
  return. It does not include cleanup of the retained accounts Vec of the caller. -/
  unwrapFailure : Callback.Run types.State types.Error Empty types.Unwind types.Terminal
  doubleUnwind : Owned.DoubleUnwind types.State types.Unwind types.Terminal

structure Args (types : Types) where
  programId : _root_.Solanalib.Runtime.Pubkey
  data : types.Data
  accounts : types.MetaResource
  providers : Providers types

abbrev Value (types : Types) := Instruction.OwnedValue types.MetaResource types.ByteResource

/-- The `Ok` resource of serialization moves into the result with the same accounts
resource. An ordinary serializer error follows the non-returning unwrap path;
it cannot be reinterpreted as a normal constructor return or a returned Err. -/
def rawRun (types : Types) (format : Format) (args : Args types) :
    Callback.Run types.State Unit (Value types) types.Unwind types.Terminal :=
  fun before _ outcome =>
    Callback.bind args.providers.serialize
      (fun result after final =>
        match result with
        | .ok data => final = .returned ⟨args.programId, args.accounts, data⟩ after
        | .error error =>
          Callback.map (fun impossible : Empty => nomatch impossible)
            args.providers.unwrapFailure after error final)
      before (format, args.data) outcome

/-- Retained accounts are dropped once if serialization or unwrap unwinds.
A terminal exit skips cleanup. Success moves both handles into Instruction.
A destructor unwind during an existing unwind uses the explicit terminal-only
policy and the actual state of the destructor. -/
def run (types : Types) (format : Format) (before : types.State) (args : Args types) :
    Outcome types.State (Value types) types.Unwind types.Terminal → Prop :=
  Owned.protect args.providers.doubleUnwind
    [args.providers.metaVec.dropAction args.accounts]
    (rawRun types format args) before ()

structure AllocateArgs (types : Types) where
  programId : _root_.Solanalib.Runtime.Pubkey
  data : types.Data
  accounts : List Instruction.Meta
  providers : Providers types

/-- `vec![...]` constructs metadata before the serializer is called. Only its
normal return supplies an accounts resource owned by the constructor. The
allocation dependency itself handles any partial construction on its exits. -/
def allocateRun (types : Types) (format : Format)
    (before : types.State) (args : AllocateArgs types) :
    Outcome types.State (Value types) types.Unwind types.Terminal → Prop :=
  Callback.bind args.providers.metaVec.fromList
    (fun accounts after => run types format after
      ⟨args.programId, args.data, accounts, args.providers⟩)
    before args.accounts

/-- Returned instruction values are read through both providers at the actual
post-state, rather than rebuilding vectors from input snapshots. -/
def observe (types : Types) (providers : Providers types) (state : types.State)
    (instruction : Value types) : Option Instruction.Value :=
  instruction.observe (providers.metaVec.current state) (providers.byteVec.current state)

/-- The value observation follows once primitive list/codec/frame obligations
establish the two current sequences. This hypothesis is explicitly local; it
does not assume an SDK function postcondition or allocator success. -/
theorem observe_of_current (types : Types) (providers : Providers types)
    (state : types.State) (instruction : Value types)
    (accounts : List Instruction.Meta) (data : _root_.Solanalib.Runtime.Bytes)
    (hm : providers.metaVec.current state instruction.metas = some accounts)
    (hd : providers.byteVec.current state instruction.data = some data) :
    observe types providers state instruction =
      some (Instruction.make instruction.programId accounts data) :=
  Instruction.OwnedValue.observe_of_current _ _ _ _ _ hm hd

/-- A successful serialization moves its exact byte resource and the retained
accounts resource into the result without running a destructor. -/
theorem run_of_serialized (types : Types) (format : Format)
    (before after : types.State) (args : Args types) (data : types.ByteResource)
    (serialized : args.providers.serialize before (format, args.data)
      (.returned (.ok data) after)) :
    run types format before args
      (.returned ⟨args.programId, args.accounts, data⟩ after) := by
  refine ⟨.returned ⟨args.programId, args.accounts, data⟩ after, ?_, rfl⟩
  exact ⟨.returned (.ok data) after, serialized, rfl⟩

/-- The allocation normal return supplies the same retained resource used by
the serializer stage, in the actual state after that allocation. -/
theorem allocateRun_of_returned (types : Types) (format : Format)
    (before middle : types.State) (args : AllocateArgs types)
    (accounts : types.MetaResource)
    (outcome : Outcome types.State (Value types) types.Unwind types.Terminal)
    (allocated : args.providers.metaVec.fromList before args.accounts
      (.returned accounts middle))
    (constructed : run types format middle
      ⟨args.programId, args.data, accounts, args.providers⟩ outcome) :
    allocateRun types format before args outcome :=
  ⟨.returned accounts middle, allocated, constructed⟩

end Solanalib.Specs.Core.InstructionBuilder
