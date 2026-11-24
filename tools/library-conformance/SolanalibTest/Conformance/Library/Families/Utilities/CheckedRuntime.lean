/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.Core.InstructionsSysvarChecked
import SolanalibTest.Conformance.Library.Families.Runtime.Common

/-! A deterministic native allocator interpretation used only by conformance.
The graph proofs evaluate the registered model at this explicit provider; they
are not Rust body proofs. Allocation IDs are ordinals of tracked native calls.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.Utilities.CheckedRuntime

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

/-- A graph decider checks the complete registered reference through an explicit
observation of its ghost/resource state, retaining every native field recorded. -/
theorem projected_graph {Input Output : Type} (run : Input → Prop) (computed : Option Input)
    (graph : ∀ actual, run actual ↔ computed = some actual) (project : Input → Option Output)
    (observed : Output) :
    (∃ actual, run actual ∧ project actual = some observed) ↔ computed.bind project = some observed
      := by
  constructor
  · rintro ⟨actual, called, projection⟩
    rw [(graph actual).mp called]
    exact projection
  · intro result
    cases value : computed with
    | none => rw [value] at result; cases result
    | some actual =>
      rw [value] at result
      exact ⟨actual, (graph actual).mpr value, result⟩

end SolanalibTest.Conformance.Library.Families.Utilities.CheckedRuntime

namespace SolanalibTest.Conformance.Library.Families.Utilities.CheckedRuntime

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.InstructionsSysvar
open SolanalibTest.Conformance.Library.Families.Runtime

structure Vector (Element : Type) where
  items : List Element
  capacity : Nat
  allocation : Option Nat
  deriving DecidableEq

structure Pool where
  metas : List (Option (Vector Instruction.Meta)) := []
  bytes : List (Option (Vector UInt8)) := []
  allocations : List Nat := []
  frees : List Nat := []
  live : List Nat := []
  deriving DecidableEq

def allocate (before : Pool) (capacity : Nat) : Option Nat × Pool :=
  if capacity = 0 then (none, before)
  else let id := before.allocations.length
    (some id, { before with allocations := before.allocations ++ [id], live := before.live ++ [id]
      })

def metaNew (before : Pool) (items : List Instruction.Meta) (capacity : Nat) : Nat × Pool :=
  let (allocation, after) := allocate before capacity
  (after.metas.length, { after with metas := after.metas ++ [some ⟨items, capacity, allocation⟩] })

def byteNew (before : Pool) (items : Solanalib.Runtime.Bytes) (capacity : Nat) : Nat × Pool :=
  let (allocation, after) := allocate before capacity
  (after.bytes.length, { after with bytes := after.bytes ++ [some ⟨items, capacity, allocation⟩] })

def metaAt (before : Pool) (id : Nat) : Option (Vector Instruction.Meta) := before.metas[id]?.join
def byteAt (before : Pool) (id : Nat) : Option (Vector UInt8) := before.bytes[id]?.join

def metaPush (before : Pool) (id : Nat) (value : Instruction.Meta) : Pool :=
  match metaAt before id with
  | none => before
  | some vec => { before with metas := before.metas.set id (some { vec with items := vec.items ++
    [value] }) }

def bytePush (before : Pool) (id : Nat) (value : UInt8) : Pool :=
  match byteAt before id with
  | none => before
  | some vec => { before with bytes := before.bytes.set id (some { vec with items := vec.items ++
    [value] }) }

def retire (before : Pool) : Option Nat → Pool
  | none => before
  | some id => { before with frees := before.frees ++ [id], live := before.live.filter (· != id) }

def metaDrop (before : Pool) (id : Nat) : Pool :=
  match metaAt before id with
  | none => before
  | some vec => { retire before vec.allocation with metas := before.metas.set id none }

def byteDrop (before : Pool) (id : Nat) : Pool :=
  match byteAt before id with
  | none => before
  | some vec => { retire before vec.allocation with bytes := before.bytes.set id none }

def metaOps : Owned.VectorOps Pool Instruction.Meta Nat Empty Empty where
  current := fun before id => (metaAt before id).map Vector.items
  empty := fun before => metaNew before [] 0
  withCapacity := Callback.ofFunction fun before capacity =>
    let (id, after) := metaNew before [] capacity
    .returned id after
  fromList := Callback.ofFunction fun before items =>
    let (id, after) := metaNew before items items.length
    .returned id after
  push := Callback.ofFunction fun before (id, item) => .returned () (metaPush before id item)
  extend := Callback.ofFunction fun before (id, items) =>
    .returned () (items.foldl (fun state item => metaPush state id item) before)
  drop := Callback.ofFunction fun before id => .returned () (metaDrop before id)

def byteOps : Owned.VectorOps Pool UInt8 Nat Empty Empty where
  current := fun before id => (byteAt before id).map Vector.items
  empty := fun before => byteNew before [] 0
  withCapacity := Callback.ofFunction fun before capacity =>
    let (id, after) := byteNew before [] capacity
    .returned id after
  fromList := Callback.ofFunction fun before items =>
    let (id, after) := byteNew before items items.length
    .returned id after
  push := Callback.ofFunction fun before (id, item) => .returned () (bytePush before id item)
  extend := Callback.ofFunction fun before (id, items) =>
    .returned () (items.foldl (fun state item => bytePush state id item) before)
  drop := Callback.ofFunction fun before id => .returned () (byteDrop before id)

abbrev index : Checked.Index := {
  Aux := Pool
  MetaResource := Nat
  ByteResource := Nat
  Unwind := Empty
  Terminal := Empty
  metas := metaOps
  bytes := byteOps
  doubleUnwind := fun _ reason _ _ => nomatch reason
}

abbrev Value := Checked.Value index
abbrev DecodeResult := Except ProgramError.Value Value

def metasF (resource : Nat) (data : Solanalib.Runtime.Bytes) : Nat → Nat → Pool → Except
  ProgramError.Value Nat × Pool
  | 0, position, before => (.ok position, before)
  | count + 1, position, before => match Checked.readMeta data position with
    | none => (.error .invalidArgument, before)
    | some (entry, next) => metasF resource data count next (metaPush before resource entry)

theorem metas_graph (resource : Nat) (data : Solanalib.Runtime.Bytes) (count position : Nat)
  (before : Pool)
    (outcome : Outcome Pool (Except ProgramError.Value Nat) Empty Empty) :
    Checked.readMetas index resource data count position before () outcome ↔
      .returned (metasF resource data count position before).1
        (metasF resource data count position before).2 = outcome := by
  induction count generalizing position before with
  | zero => exact eq_comm
  | succ count induction =>
    simp only [Checked.readMetas, metasF]
    cases decoded : Checked.readMeta data position with
    | none => simp only; exact eq_comm
    | some entry =>
      simp only
      change Callback.bind (Callback.ofFunction (fun state (id, item) =>
        Outcome.returned () (metaPush state id item))) _ before (resource, entry.1) outcome ↔ _
      rw [bind_ofFunction_iff]
      exact induction entry.2 (metaPush before resource entry.1)

def tailF (resource : Nat) (data : Solanalib.Runtime.Bytes) (position : Nat) (before : Pool) :
  DecodeResult × Pool :=
  match Checked.key data position with
  | none => (.error .invalidArgument, before)
  | some (program, next) => match Checked.word data next with
    | none => (.error .invalidArgument, before)
    | some (length, next) => match Checked.takeBytes data next length with
      | none => (.error .invalidArgument, before)
      | some (payload, _) =>
        let (bytes, after) := byteNew before payload payload.length
        (.ok ⟨program, resource, bytes⟩, after)

theorem tail_graph (resource : Nat) (data : Solanalib.Runtime.Bytes) (position : Nat) (before :
  Pool)
    (outcome : Outcome Pool DecodeResult Empty Empty) :
    Checked.readTail index resource data position before () outcome ↔
      .returned (tailF resource data position before).1 (tailF resource data position before).2 =
        outcome := by
  unfold Checked.readTail tailF
  cases hfirst : Checked.key data position with
  | none => simp only; exact eq_comm
  | some first =>
    rcases first with ⟨program, next⟩
    simp only
    cases hsecond : Checked.word data next with
    | none => simp only; exact eq_comm
    | some second =>
      rcases second with ⟨length, next⟩
      simp only
      cases hthird : Checked.takeBytes data next length with
      | none => simp only; exact eq_comm
      | some third =>
        exact Callback.map_ofFunction _ _ _ _ _

/-- Account vectors are retired only on a returned Err at this no-unwind native
provider. The underlying registered model still handles all abnormal providers. -/
def protectF (resource : Nat) (pending : DecodeResult × Pool) : DecodeResult × Pool :=
  match pending.1 with
  | .ok value => (.ok value, pending.2)
  | .error error => (.error error, metaDrop pending.2 resource)

theorem protect_graph (resource : Nat)
    (body : Callback.Run Pool Unit DecodeResult Empty Empty)
    (pending : DecodeResult × Pool) (before : Pool)
    (graph : ∀ outcome, body before () outcome ↔ .returned pending.1 pending.2 = outcome)
    (outcome : Outcome Pool DecodeResult Empty Empty) :
    Checked.protectMetas index resource body before () outcome ↔
      .returned (protectF resource pending).1 (protectF resource pending).2 = outcome := by
  rcases pending with ⟨result, after⟩
  unfold Checked.protectMetas
  constructor
  · rintro ⟨middle, called, cleaned⟩
    have same := (graph middle).mp called
    cases same
    cases result with
    | ok value => exact cleaned.symm
    | error error =>
      obtain ⟨dropped, droppedBy, final⟩ := cleaned
      change .returned () (metaDrop after resource) = dropped at droppedBy
      cases droppedBy
      exact final.symm
  · intro same
    refine ⟨.returned result after, (graph _).mpr rfl, ?_⟩
    cases result with
    | ok value => exact same.symm
    | error error =>
      exact ⟨.returned () (metaDrop after resource), rfl, same.symm⟩

def bodyF (resource : Nat) (data : Solanalib.Runtime.Bytes) (count position : Nat) (before : Pool)
  : DecodeResult × Pool :=
  let (result, after) := metasF resource data count position before
  match result with
  | .error error => (.error error, after)
  | .ok next => tailF resource data next after

theorem body_graph (resource : Nat) (data : Solanalib.Runtime.Bytes) (count position : Nat) (before
  : Pool)
    (outcome : Outcome Pool DecodeResult Empty Empty) :
    Callback.bind (Checked.readMetas index resource data count position)
      (fun result after final => match result with
        | .error error => final = .returned (.error error) after
        | .ok next => Checked.readTail index resource data next after () final)
      before () outcome ↔
      .returned (bodyF resource data count position before).1
        (bodyF resource data count position before).2 = outcome := by
  have equal : Checked.readMetas index resource data count position =
      Callback.ofFunction (fun state _ => .returned (metasF resource data count position state).1
        (metasF resource data count position state).2) := by
    funext state args final
    cases args
    exact propext (metas_graph resource data count position state final)
  rw [equal, bind_ofFunction_iff]
  unfold bodyF
  cases computed : metasF resource data count position before with
  | mk result after =>
    cases result with
    | error error => exact eq_comm
    | ok next => exact tail_graph resource data next after outcome

def decodeF (instruction : UInt64) (before : Pool) (data : Solanalib.Runtime.Bytes) : DecodeResult
  × Pool :=
  match Checked.word data 0 with
  | none => (.error .invalidArgument, before)
  | some (count, table) =>
    if instruction.toNat ≥ count then (.error .invalidArgument, before)
    else match Checked.word data (table + 2 * instruction.toNat) with
      | none => (.error .invalidArgument, before)
      | some (start, _) => match Checked.word data start with
        | none => (.error .invalidArgument, before)
        | some (accounts, position) =>
          let (resource, after) := metaNew before [] accounts
          protectF resource (bodyF resource data accounts position after)

theorem decode_graph (instruction : UInt64) (before : Pool) (data : Solanalib.Runtime.Bytes)
    (outcome : Outcome Pool DecodeResult Empty Empty) :
    Checked.decode index instruction before data outcome ↔
      .returned (decodeF instruction before data).1 (decodeF instruction before data).2 = outcome
        := by
  unfold Checked.decode decodeF
  cases hfirst : Checked.word data 0 with
  | none => simp only; exact eq_comm
  | some first =>
    rcases first with ⟨count, table⟩
    simp only
    split
    · exact eq_comm
    · cases hsecond : Checked.word data (table + 2 * instruction.toNat) with
      | none => simp only; exact eq_comm
      | some second =>
        rcases second with ⟨start, ignored⟩
        simp only
        cases hthird : Checked.word data start with
        | none => simp only; exact eq_comm
        | some third =>
          change Callback.bind (Callback.ofFunction (fun state capacity =>
            .returned (metaNew state [] capacity).1 (metaNew state [] capacity).2)) _ before
              third.1 outcome ↔ _
          rw [bind_ofFunction_iff]
          exact protect_graph (metaNew before [] third.1).1 _ _ _
            (body_graph (metaNew before [] third.1).1 data third.1 third.2 (metaNew before []
              third.1).2) outcome

/-- Evaluate the borrow-scoped wrapper. Malformed abstract projections have no
modeled outcome, exactly as in withData; Ready excludes them after a successful
source acquisition. This function invents neither a guard nor a missing cell. -/
def withDataF {Aux Value Unwind Terminal : Type}
    (body : Aux → Solanalib.Runtime.Bytes → Outcome Aux (Except ProgramError.Value Value) Unwind
      Terminal)
    (before : Checked.State Aux) (info : AccountInfo.Value) :
    Option (Outcome (Checked.State Aux) (Except ProgramError.Value Value) Unwind Terminal) :=
  if info.key ≠ Solanalib.Runtime.Ids.sysvarInstructions then
    some (.returned (.error .unsupportedSysvar) before)
  else
    let (acquired, during) := AccountInfo.tryBorrow .shared info.data before.borrows
    match acquired with
    | .error error => some (.returned (.error error) ⟨during, before.aux⟩)
    | .ok guard => match Borrow.current during guard with
      | .ok (.whole, .data bytes) => some (Checked.finish during guard (body before.aux bytes))
      | _ => none

theorem withData_graph {Aux Value Unwind Terminal : Type}
    (body : Aux → Solanalib.Runtime.Bytes → Outcome Aux (Except ProgramError.Value Value) Unwind
      Terminal)
    (before : Checked.State Aux) (info : AccountInfo.Value)
    (outcome : Outcome (Checked.State Aux) (Except ProgramError.Value Value) Unwind Terminal) :
    Checked.withData (Callback.ofFunction body) before info outcome ↔
      withDataF body before info = some outcome := by
  unfold Checked.withData withDataF
  split
  · exact by simp only [Option.some.injEq]; exact eq_comm
  · generalize AccountInfo.tryBorrow Borrow.Mode.shared info.data before.borrows = borrowed
    rcases borrowed with ⟨result, during⟩
    cases result with
    | error error => simp only [Option.some.injEq]; exact eq_comm
    | ok guard =>
      generalize hcurrent : Borrow.current during guard = current
      cases current with
      | error error => simp [hcurrent]
      | ok value =>
        rcases value with ⟨view, content⟩
        cases view <;> cases content <;> simp [hcurrent, Callback.ofFunction, eq_comm]

end SolanalibTest.Conformance.Library.Families.Utilities.CheckedRuntime
