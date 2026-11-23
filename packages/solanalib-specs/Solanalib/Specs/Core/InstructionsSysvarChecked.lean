/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfo
public import Solanalib.Specs.Core.BorrowFacts
public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.SysvarRentArithmetic
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionsSysvar.Checked

/-- Only the data cell reached after the address check needs an interpretation.
No owner, signer, writable, lamport or rent-exemption condition is imposed. -/
def Ready (state : AccountInfo.State) (info : AccountInfo.Value) : Prop :=
  info.key = Solanalib.Runtime.Ids.sysvarInstructions →
    ∃ bytes policy, state.lookupCell info.data = some ⟨.data bytes, policy⟩

/-- A successful acquisition reads the current cell, including through aliases.
This rules out losing a successful borrow to a malformed data projection. -/
theorem acquired_current (state : AccountInfo.State) (info : AccountInfo.Value)
    (ready : Ready state info) (key : info.key = Solanalib.Runtime.Ids.sysvarInstructions)
    (guard : Borrow.Guard) (during : AccountInfo.State)
    (acquired : AccountInfo.tryBorrow .shared info.data state = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) := by
  obtain ⟨bytes, policy, present⟩ := ready key
  unfold AccountInfo.tryBorrow at acquired
  cases step : Borrow.acquire state info.data .shared AccountInfo.View.whole with
  | mk result after =>
    rw [step] at acquired
    cases result with
    | error error => cases acquired
    | ok actual =>
      cases acquired
      exact ⟨bytes, Borrow.acquire_current step present⟩

/-- Resource effects belong to a separate vector/allocator world. The selected
account data is held by a shared Ref throughout decoding; its captured bytes
cannot be changed through a legal source alias during that borrow. -/
structure State (Aux : Type) where
  borrows : AccountInfo.State
  aux : Aux
  deriving DecidableEq, Repr

/-- Release the actual temporary Ref on return or unwind. A terminal exit has
no final world and performs no cleanup. The vector world is retained exactly. -/
def finish {Aux Value Unwind Terminal : Type} (during : AccountInfo.State)
    (guard : Borrow.Guard) :
    Outcome Aux Value Unwind Terminal → Outcome (State Aux) Value Unwind Terminal
  | .returned value after => .returned value ⟨(Borrow.release during guard).2, after⟩
  | .unwound reason after => .unwound reason ⟨(Borrow.release during guard).2, after⟩
  | .terminated reason => .terminated reason

/-- Both checked loaders check the ID before trying a shared borrow. The body
only runs under the actual guard; all of its finite exits are forwarded. -/
def withData {Aux Value Unwind Terminal : Type}
    (body : Callback.Run Aux Solanalib.Runtime.Bytes (Except ProgramError.Value Value) Unwind
      Terminal)
    (before : State Aux) (info : AccountInfo.Value)
    (outcome : Outcome (State Aux) (Except ProgramError.Value Value) Unwind Terminal) : Prop :=
  if info.key ≠ Solanalib.Runtime.Ids.sysvarInstructions then
    outcome = .returned (.error .unsupportedSysvar) before
  else
    let (acquired, during) := AccountInfo.tryBorrow .shared info.data before.borrows
    match acquired with
    | .error error => outcome = .returned (.error error) ⟨during, before.aux⟩
    | .ok guard => ∃ bytes pending,
        Borrow.current during guard = .ok (.whole, .data bytes) ∧
        body before.aux bytes pending ∧ outcome = finish during guard pending

theorem wrong_id_first {Aux Value Unwind Terminal : Type}
    (body : Callback.Run Aux Solanalib.Runtime.Bytes (Except ProgramError.Value Value) Unwind
      Terminal)
    (before : State Aux) (info : AccountInfo.Value)
    (wrong : info.key ≠ Solanalib.Runtime.Ids.sysvarInstructions) :
    withData body before info (.returned (.error .unsupportedSysvar) before) := by
  unfold withData
  split
  · rfl
  · contradiction

theorem acquired_exit_retained {Aux Value Unwind Terminal : Type}
    (body : Callback.Run Aux Solanalib.Runtime.Bytes (Except ProgramError.Value Value) Unwind
      Terminal)
    (before : State Aux) (info : AccountInfo.Value)
    (key : info.key = Solanalib.Runtime.Ids.sysvarInstructions)
    (guard : Borrow.Guard) (during : AccountInfo.State) (bytes : Solanalib.Runtime.Bytes)
    (acquired : AccountInfo.tryBorrow .shared info.data before.borrows = (.ok guard, during))
    (current : Borrow.current during guard = .ok (.whole, .data bytes))
    (pending : Outcome Aux (Except ProgramError.Value Value) Unwind Terminal)
    (called : body before.aux bytes pending) :
    withData body before info (finish during guard pending) := by
  simp only [withData, key, ne_eq, not_true_eq_false, ite_false, acquired]
  exact ⟨bytes, pending, current, called, rfl⟩

inductive Panic where
  | subtractionOverflow
  | sliceRange
  deriving DecidableEq, Repr

/-- Short data panics rather than returning a ProgramError. Checked subtraction
fails first; wrapping subtraction reaches the slice bounds panic instead. -/
def currentBody (profile : Sysvar.ArithmeticProfile) (before : Unit) (bytes :
  Solanalib.Runtime.Bytes) :
    Outcome Unit (Except ProgramError.Value UInt16) Panic Panic :=
  if bytes.length < 2 then
    let reason := if profile.overflowChecks then Panic.subtractionOverflow else Panic.sliceRange
    match profile.panicStrategy with
    | .unwind => .unwound reason before
    | .abort => .terminated reason
  else .returned (.ok (UInt16.ofNat (Solanalib.Runtime.leNat (bytes.drop (bytes.length - 2)))))
    before

def currentFamily : Family where
  Index := ULift Sysvar.ArithmeticProfile
  State := fun _ => State Unit
  Args := fun _ => AccountInfo.Value
  Value := fun _ => Except ProgramError.Value UInt16
  Unwind := fun _ => Panic
  Terminal := fun _ => Panic
  contract := fun profile => {
    requires := fun before info => Ready before.borrows info
    post := withData (Callback.ofFunction (currentBody profile.down))
  }

def currentReference : FamilyRun currentFamily :=
  fun profile => withData (Callback.ofFunction (currentBody profile.down))

theorem current_reference : FamilyReference currentFamily currentReference := by
  intro _ _ _ _ _ called
  exact called

/-- All serializer reads are bounds checked. The source maps their
IndexOutOfBounds errors, including truncated encodings, to InvalidArgument. -/
def takeBytes (data : Solanalib.Runtime.Bytes) (position length : Nat) : Option
  (Solanalib.Runtime.Bytes × Nat) :=
  if position + length ≤ data.length then
    some (Solanalib.Runtime.slice data position length, position + length)
  else none

def word (data : Solanalib.Runtime.Bytes) (position : Nat) : Option (Nat × Nat) := do
  let (bytes, next) ← takeBytes data position 2
  pure (Solanalib.Runtime.leNat bytes, next)

def key (data : Solanalib.Runtime.Bytes) (position : Nat) : Option (Solanalib.Runtime.Pubkey × Nat)
  := do
  let (bytes, next) ← takeBytes data position 32
  pure (Solanalib.Runtime.Pubkey.ofBytes bytes, next)

def readMeta (data : Solanalib.Runtime.Bytes) (position : Nat) : Option (Instruction.Meta × Nat) :=
  do
  let (flag, next) ← takeBytes data position 1
  let (address, next) ← key data next
  let bits := Solanalib.Runtime.leNat flag
  pure (Instruction.accountMeta address (decide (bits % 2 = 1))
    (decide ((bits / 2) % 2 = 1)), next)

structure Index where
  Aux : Type
  MetaResource : Type
  ByteResource : Type
  Unwind : Type
  Terminal : Type
  metas : Owned.VectorOps Aux Instruction.Meta MetaResource Unwind Terminal
  bytes : Owned.VectorOps Aux UInt8 ByteResource Unwind Terminal
  doubleUnwind : Owned.DoubleUnwind Aux Unwind Terminal

abbrev Value (index : Index) := Instruction.OwnedValue index.MetaResource index.ByteResource
abbrev Result (index : Index) := Except ProgramError.Value (Value index)

/-- Preserve one push for each decoded meta, with exact flags, keys and order.
The vector identity does not change across reallocating pushes. -/
def readMetas (index : Index) (resource : index.MetaResource) (data : Solanalib.Runtime.Bytes) :
    Nat → Nat → Callback.Run index.Aux Unit (Except ProgramError.Value Nat)
      index.Unwind index.Terminal
  | 0, position => fun before _ outcome => outcome = .returned (.ok position) before
  | count + 1, position => fun before _ outcome =>
    match readMeta data position with
    | none => outcome = .returned (.error .invalidArgument) before
    | some (entry, next) =>
      Callback.bind index.metas.push
        (fun _ after => readMetas index resource data count next after ())
        before (resource, entry) outcome

/-- Decode the program ID and data length before allocating the returned byte
vector. Every bounds error is local; only the real provider of to_vec may allocate. -/
def readTail (index : Index) (resource : index.MetaResource) (data : Solanalib.Runtime.Bytes)
    (position : Nat) : Callback.Run index.Aux Unit (Result index) index.Unwind index.Terminal :=
  fun before _ outcome =>
    match key data position with
    | none => outcome = .returned (.error .invalidArgument) before
    | some (program, next) => match word data next with
      | none => outcome = .returned (.error .invalidArgument) before
      | some (length, next) => match takeBytes data next length with
        | none => outcome = .returned (.error .invalidArgument) before
        | some (payload, _) =>
          Callback.map (fun bytes => Except.ok (Instruction.OwnedValue.mk program resource bytes))
            index.bytes.fromList before payload outcome

/-- Locally owned accounts are dropped after a parse Err or unwind. Only an
Ok moves them into Instruction; terminal exits do not run a destructor. -/
def protectMetas (index : Index) (resource : index.MetaResource)
    (body : Callback.Run index.Aux Unit (Result index) index.Unwind index.Terminal) :
    Callback.Run index.Aux Unit (Result index) index.Unwind index.Terminal :=
  fun before args outcome => ∃ pending, body before args pending ∧
    match pending with
    | .returned (.ok value) after => outcome = .returned (.ok value) after
    | .returned (.error error) after =>
        Owned.cleanup index.doubleUnwind [index.metas.dropAction resource]
          (.returned (.error error) after) outcome
    | .unwound reason after =>
        Owned.cleanup index.doubleUnwind [index.metas.dropAction resource]
          (.unwound reason after) outcome
    | .terminated reason => outcome = .terminated reason

/-- Source order is count, index bound, offset, account count, with_capacity,
each meta and push, program ID, byte count, and to_vec. No CPI is performed. -/
def decode (index : Index) (instruction : UInt64) :
    Callback.Run index.Aux Solanalib.Runtime.Bytes (Result index) index.Unwind index.Terminal :=
  fun before data outcome => match word data 0 with
  | none => outcome = .returned (.error .invalidArgument) before
  | some (count, table) =>
    if instruction.toNat ≥ count then outcome = .returned (.error .invalidArgument) before
    else match word data (table + 2 * instruction.toNat) with
      | none => outcome = .returned (.error .invalidArgument) before
      | some (start, _) => match word data start with
        | none => outcome = .returned (.error .invalidArgument) before
        | some (accounts, position) =>
          Callback.bind index.metas.withCapacity
            (fun resource after => protectMetas index resource
              (fun current _ final =>
                Callback.bind (readMetas index resource data accounts position)
                  (fun result afterMetas final => match result with
                    | .error error => final = .returned (.error error) afterMetas
                    | .ok next => readTail index resource data next afterMetas () final)
                  current () final) after ())
            before accounts outcome

def instructionFamily : Family where
  Index := Index
  State := fun index => State index.Aux
  Args := fun _ => UInt64 × AccountInfo.Value
  Value := Result
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun before args => Ready before.borrows args.2
    post := fun before args => withData (decode index args.1) before args.2
  }

def instructionReference : FamilyRun instructionFamily :=
  fun index before args => withData (decode index args.1) before args.2

theorem instruction_reference : FamilyReference instructionFamily instructionReference := by
  intro _ _ _ _ _ called
  exact called

/-- The returned vector handles are interpreted in the actual final allocation
world. This projection does not replace provider effects with input snapshots. -/
def observe (index : Index) (state : index.Aux) (value : Value index) : Option Instruction.Value :=
  value.observe (index.metas.current state) (index.bytes.current state)

theorem observe_of_current (index : Index) (state : index.Aux) (value : Value index)
    (metas : List Instruction.Meta) (bytes : Solanalib.Runtime.Bytes)
    (metaContents : index.metas.current state value.metas = some metas)
    (byteContents : index.bytes.current state value.data = some bytes) :
    observe index state value = some (Instruction.make value.programId metas bytes) :=
  Instruction.OwnedValue.observe_of_current _ _ _ _ _ metaContents byteContents

end Solanalib.Specs.Core.InstructionsSysvar.Checked
