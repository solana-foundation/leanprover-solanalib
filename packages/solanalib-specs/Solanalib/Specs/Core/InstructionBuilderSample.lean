/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionBuilderFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionBuilder.Sample

/-- A finite mathematical provider state. Each vector keeps a stable slot;
retirement clears that slot. These providers are consistency examples, not
implementations of Rust allocation, Vec, bincode or wincode. -/
structure State where
  metas : List (Option (List Instruction.Meta)) := []
  bytes : List (Option _root_.Solanalib.Runtime.Bytes) := []
  events : List Nat := []
  deriving DecidableEq, Repr

def metasAt (state : State) (resource : Nat) : Option (List Instruction.Meta) :=
  match state.metas[resource]? with
  | some values => values
  | none => none

def bytesAt (state : State) (resource : Nat) : Option _root_.Solanalib.Runtime.Bytes :=
  match state.bytes[resource]? with
  | some values => values
  | none => none

def allocateMetas (state : State) (values : List Instruction.Meta) : State :=
  { state with metas := state.metas ++ [some values], events := state.events ++ [10] }

def allocateBytes (state : State) (values : _root_.Solanalib.Runtime.Bytes) : State :=
  { state with bytes := state.bytes ++ [some values], events := state.events ++ [11] }

def retireMetas (state : State) (resource : Nat) : State :=
  { state with metas := state.metas.set resource none, events := state.events ++ [40] }

def retireBytes (state : State) (resource : Nat) : State :=
  { state with bytes := state.bytes.set resource none, events := state.events ++ [41] }

def metaVec : Owned.VectorOps State Instruction.Meta Nat Nat Nat where
  current := metasAt
  empty := fun before => (before.metas.length, allocateMetas before [])
  withCapacity := Callback.ofFunction fun before _ =>
    .returned before.metas.length (allocateMetas before [])
  fromList := Callback.ofFunction fun before values =>
    .returned before.metas.length (allocateMetas before values)
  push := Callback.ofFunction fun before (resource, value) =>
    match metasAt before resource with
    | none => .unwound 404 before
    | some values => .returned ()
      { before with metas := before.metas.set resource (some (values ++ [value])) }
  extend := Callback.ofFunction fun before (resource, extra) =>
    match metasAt before resource with
    | none => .unwound 404 before
    | some values => .returned ()
      { before with metas := before.metas.set resource (some (values ++ extra)) }
  drop := Callback.ofFunction fun before resource => .returned () (retireMetas before resource)

def byteVec : Owned.VectorOps State UInt8 Nat Nat Nat where
  current := bytesAt
  empty := fun before => (before.bytes.length, allocateBytes before [])
  withCapacity := Callback.ofFunction fun before _ =>
    .returned before.bytes.length (allocateBytes before [])
  fromList := Callback.ofFunction fun before values =>
    .returned before.bytes.length (allocateBytes before values)
  push := Callback.ofFunction fun before (resource, value) =>
    match bytesAt before resource with
    | none => .unwound 404 before
    | some values => .returned ()
      { before with bytes := before.bytes.set resource (some (values ++ [value])) }
  extend := Callback.ofFunction fun before (resource, extra) =>
    match bytesAt before resource with
    | none => .unwound 404 before
    | some values => .returned ()
      { before with bytes := before.bytes.set resource (some (values ++ extra)) }
  drop := Callback.ofFunction fun before resource => .returned () (retireBytes before resource)

def types (Data : Type) : Types := ⟨State, Data, Nat, Nat, Nat, Nat, Nat⟩

def afterSerialize {Data : Type} (encode : Data → _root_.Solanalib.Runtime.Bytes)
    (format : Format) (before : State) (data : Data) : State :=
  { before with
    bytes := before.bytes ++ [some (encode data)]
    events := before.events ++ [if format = .bincode then 20 else 21] }

def providers (Data : Type) (encode : Data → _root_.Solanalib.Runtime.Bytes) : Providers (types
  Data) where
  metaVec := metaVec
  byteVec := byteVec
  serialize := Callback.ofFunction fun (before : State) (format, data) =>
    .returned (.ok (before.bytes.length : Nat)) (afterSerialize encode format before data)
  unwrapFailure := Callback.ofFunction fun (before : State) (error : Nat) =>
    .unwound (error + 100) { before with events := before.events ++ [30] }
  doubleUnwind := fun (_ : State) (first later terminal : Nat) =>
    terminal = first + later + 1000

def constructorBefore : State where
  metas := [some [Instruction.accountMeta .zero true true,
    Instruction.accountMeta .zero false true]]
  events := [10]

def constructorArgs : Args (types _root_.Solanalib.Runtime.Bytes) where
  programId := .zero
  data := ([2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0] : _root_.Solanalib.Runtime.Bytes)
  accounts := (0 : Nat)
  providers := providers _root_.Solanalib.Runtime.Bytes id

def constructorAfter (format : Format) : State :=
  afterSerialize id format constructorBefore constructorArgs.data

theorem constructorSuccess (format : Format) :
    run (types _root_.Solanalib.Runtime.Bytes) format constructorBefore constructorArgs
      (.returned ⟨.zero, (0 : Nat), (0 : Nat)⟩ (constructorAfter format)) :=
  run_of_serialized _ _ _ _ _ _ rfl

end Solanalib.Specs.Core.InstructionBuilder.Sample
