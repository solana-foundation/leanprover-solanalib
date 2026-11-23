/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressLookupTable
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AddressLookupTableOwned

open AddressLookupTable

/-- The complete bincode metadata enum, before the SDK rejects Uninitialized. -/
inductive ProgramState where
  | uninitialized
  | lookupTable (metadata : Meta)
  deriving DecidableEq, Repr

def decodeProgram (bytes : Solanalib.Runtime.Bytes) : Option ProgramState :=
  match field bytes 0 4 with
  | none => none
  | some tag =>
    if Solanalib.Runtime.leNat tag = 0 then some .uninitialized
    else if Solanalib.Runtime.leNat tag ≠ 1 then none
    else (decodeMeta bytes).map ProgramState.lookupTable

/-- These later errors construct only the fieldless InstructionError of the SDK.
The metadata decoder has already returned successfully before the size/cast checks. -/
def finish (input : Bytemuck.SliceRef) : ProgramState → Except Error Value
  | .uninitialized => .error .uninitializedAccount
  | .lookupTable metadata =>
    if 56 > input.bytes.length then .error .invalidAccountData
    else
      let suffix : Bytemuck.SliceRef := ⟨input.address + 56, input.bytes.drop 56⟩
      match Bytemuck.tryCastSlice .u8 pubkeyLayout suffix.address suffix.bytes.length with
      | .error _ => .error .invalidAccountData
      | .ok _ => .ok ⟨metadata, suffix⟩

theorem value_facet (input : Bytemuck.SliceRef) :
    (match decodeProgram input.bytes with
      | none => .error .invalidAccountData
      | some state => finish input state) = deserialize input := by
  cases head : field input.bytes 0 4 with
  | none => simp [decodeProgram, deserialize, head]
  | some tag =>
    by_cases zero : Solanalib.Runtime.leNat tag = 0
    · simp [decodeProgram, deserialize, head, zero, finish]
    · by_cases one : Solanalib.Runtime.leNat tag = 1
      · cases metadata : decodeMeta input.bytes <;>
          simp [decodeProgram, deserialize, head, one, metadata, finish] <;> rfl
      · simp [decodeProgram, deserialize, head, zero, one]

/-- A metadata decoding error owns the `Box<ErrorKind>` of bincode, possibly including
an owned diagnostic string. Its construction and destruction may affect the
selected allocator state. The exact successful/error decoding law belongs to
this primitive codec; unwind and terminal effects are not suppressed. -/
structure Index where
  State : Type
  DecodeError : Type
  Unwind : Type
  Terminal : Type
  decode : Callback.Run State Solanalib.Runtime.Bytes (Except DecodeError ProgramState) Unwind
    Terminal
  dropError : Callback.Run State DecodeError Unit Unwind Terminal
  returns_wire : ∀ before bytes result after,
    decode before bytes (.returned result after) →
      match result with
      | .ok state => decodeProgram bytes = some state
      | .error _ => decodeProgram bytes = none

/-- `map_err` destroys the bincode error before `?` returns InvalidAccountData.
Successful bincode decoding does not invoke that cleanup. There is no unwrap
or additional SDK allocation between successful decoding and the borrowed view. -/
def run (index : Index) :
    Callback.Run index.State Bytemuck.SliceRef (Except Error Value) index.Unwind index.Terminal :=
  fun before input => Callback.bind index.decode (fun result state outcome =>
    match result with
    | .ok decoded => outcome = .returned (finish input decoded) state
    | .error error => Callback.map (fun _ => .error .invalidAccountData)
        index.dropError state error outcome) before input.bytes

def family : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Bytemuck.SliceRef
  Value := fun _ => Except Error Value
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := run index }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference :=
  fun _ _ _ _ _ execution => execution

/-- Ordinary values agree with the pure decoder, while the final state still
records reached allocation and cleanup effects. -/
theorem returned_value (index : Index) (before after : index.State) (input : Bytemuck.SliceRef)
    (result : Except Error Value) (execution : run index before input (.returned result after)) :
    result = deserialize input := by
  rcases execution with ⟨decoded, decode, rest⟩
  cases decoded with
  | returned selected middle =>
    have wire := index.returns_wire before input.bytes selected middle decode
    cases selected with
    | ok state =>
      cases rest
      rw [← value_facet input, wire]
    | error error =>
      rcases rest with ⟨dropped, _drop, same⟩
      cases dropped with
      | returned resultUnit last =>
        cases resultUnit
        cases same
        rw [← value_facet input, wire]
      | unwound => cases same
      | terminated => cases same
  | unwound => cases rest
  | terminated => cases rest

theorem returned_alias (index : Index) (before after : index.State) (input : Bytemuck.SliceRef)
    (table : Value) (execution : run index before input (.returned (.ok table) after)) :
    table.addresses = ⟨input.address + 56, input.bytes.drop 56⟩ :=
  success_alias input table (returned_value index before after input (.ok table) execution).symm

structure Executable (index : Index) where
  decode : index.State → Solanalib.Runtime.Bytes →
    Outcome index.State (Except index.DecodeError ProgramState) index.Unwind index.Terminal
  dropError : index.State → index.DecodeError → Outcome index.State Unit index.Unwind index.Terminal
  decode_eq : index.decode = Callback.ofFunction decode
  drop_eq : index.dropError = Callback.ofFunction dropError

def runFn (index : Index) (exec : Executable index) (before : index.State) (input :
  Bytemuck.SliceRef) :
    Outcome index.State (Except Error Value) index.Unwind index.Terminal :=
  Outcome.bind (exec.decode before input.bytes) fun result middle => match result with
    | .ok state => .returned (finish input state) middle
    | .error error => Outcome.map (fun _ => .error .invalidAccountData) (exec.dropError middle
      error)

theorem run_graph (index : Index) (exec : Executable index) (before : index.State)
    (input : Bytemuck.SliceRef) (outcome : Outcome index.State (Except Error Value) index.Unwind
      index.Terminal) :
    run index before input outcome ↔ runFn index exec before input = outcome := by
  unfold run runFn
  rw [exec.decode_eq]
  simp only [Callback.bind, Callback.ofFunction]
  constructor
  · rintro ⟨decoded, rfl, rest⟩
    cases selected : exec.decode before input.bytes with
    | returned result middle =>
      rw [selected] at rest
      cases result with
      | ok state => exact rest.symm
      | error error =>
        rw [exec.drop_eq] at rest
        exact (Callback.map_ofFunction _ _ _ _ _).mp rest
    | unwound reason middle => rw [selected] at rest; exact rest.symm
    | terminated reason => rw [selected] at rest; exact rest.symm
  · intro result
    refine ⟨_, rfl, ?_⟩
    cases selected : exec.decode before input.bytes with
    | returned resultValue middle =>
      rw [selected] at result
      cases resultValue with
      | ok state => exact result.symm
      | error error =>
        rw [exec.drop_eq]
        exact (Callback.map_ofFunction _ _ _ _ _).mpr result
    | unwound reason middle => rw [selected] at result; exact result.symm
    | terminated reason => rw [selected] at result; exact result.symm

/-- A concrete tracking allocator observation: one error construction and one
destruction, with no such events on successful metadata decoding. -/
def sampleDecode (before : Nat) (bytes : Solanalib.Runtime.Bytes) :
    Outcome Nat (Except Unit ProgramState) Nat Nat :=
  match decodeProgram bytes with
  | some state => .returned (.ok state) before
  | none => .returned (.error ()) (before + 1)

def sample : Index where
  State := Nat
  DecodeError := Unit
  Unwind := Nat
  Terminal := Nat
  decode := Callback.ofFunction sampleDecode
  dropError := Callback.ofFunction fun before _ => .returned () (before + 1)
  returns_wire := by
    intro before bytes result after execution
    change sampleDecode before bytes = .returned result after at execution
    unfold sampleDecode at execution
    split at execution <;> cases execution <;> assumption

def sampleExecutable : Executable sample where
  decode := sampleDecode
  dropError := fun (before : Nat) _ => .returned () (before + 1)
  decode_eq := rfl
  drop_eq := rfl

theorem sample_execution : FamilyHasExecution family reference sample := by
  refine ⟨(0 : Nat), ⟨17, []⟩, .returned (.error .invalidAccountData) (2 : Nat), trivial, ?_⟩
  exact (run_graph sample sampleExecutable (0 : Nat) ⟨17, []⟩ _).mpr rfl

theorem sample_satisfiable : FamilySatisfiable family sample := sample_execution.satisfiable

end Solanalib.Specs.Core.AddressLookupTableOwned
