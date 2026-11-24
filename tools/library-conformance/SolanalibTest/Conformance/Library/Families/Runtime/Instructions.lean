/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import Solanalib.Specs.Pinocchio.InstructionsGeneric

/-!
# pinocchio 0.11.1 Instructions sysvar over a generic receiver

The registered generic references (`Instructions.Generic.load_current_index_run`,
`load_instruction_at_run`, `IntrospectedInstruction.Generic.get_program_id_run`,
`get_instruction_data_run`) are decided at one family index each:

* memory: allocations are the recorded buffers, numbered from zero, read from
  the current state; base addresses are disjoint 64 KiB regions (they enter
  only the admission predicates, not the decided runs);
* receiver (`T = ScriptedDeref`): its script, whose k-th entry is the returned slice or panic
message of the k-th `deref`; a missing entry panics with
  `"deref script exhausted"`, as in the driver. The state counts the derefs.

The two receiver runs are relations built with `Callback.bind` over
`Callback.ofFunction` of the scripted deref; `current_graph` and `at_graph`
prove that each is the graph of the corresponding sequence of `Outcome.bind`s.
The two pointer observers are registered as `returnsOf` and decided by `rfl`.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.Pinocchio

namespace SolanalibTest.Conformance.Library.Families.Runtime.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.InstructionsSysvar.Generic
open SolanalibTest.Conformance.Library.Families.Runtime

/-! ## The family index -/

structure ScriptState where
  memory : List Solanalib.Runtime.Bytes
  derefs : Nat
  deriving DecidableEq

def regionBase (k : Nat) : Nat := 65536 * (k + 1)

/-- Allocations of the scripted receiver: the buffers of the current state. -/
abbrev scriptMemory : Memory where
  State := ScriptState
  Allocation := Nat
  bytes := fun s k => s.memory[k]?
  baseAddress := fun _ k => regionBase k

inductive Reply where
  | slice (allocation offset length : Nat)
  | panic (message : String)
  deriving DecidableEq

def exhausted : String := "deref script exhausted"

/-- The k-th deref returns the k-th scripted reply and counts the call. -/
def derefStep (s : ScriptState) (script : List Reply) :
    Outcome ScriptState (Slice Nat) String Empty :=
  let next := { s with derefs := s.derefs + 1 }
  match script[s.derefs]? with
  | some (.slice a o l) => .returned ⟨⟨a, o⟩, l⟩ next
  | some (.panic m) => .unwound m next
  | none => .unwound exhausted next

def scriptIndex : Index where
  memory := scriptMemory
  Receiver := List Reply
  Unwind := String
  Terminal := Empty
  deref := Callback.ofFunction derefStep

/-- Allocations of the pointer observers: the buffers of the state. -/
abbrev bufferMemory : Memory where
  State := List Solanalib.Runtime.Bytes
  Allocation := Nat
  bytes := fun s k => s[k]?
  baseAddress := fun _ k => regionBase k

/-! ## Graph lemmas -/

def currentComputed (before : ScriptState) (script : List Reply) :
    Outcome ScriptState UInt16 String Empty :=
  Outcome.bind (derefStep before script) fun first afterFirst =>
    Outcome.bind (derefStep afterFirst script) fun second afterSecond =>
      .returned (UInt16.ofNat (readWord scriptMemory afterSecond
        (second.pointer.add (first.length - 2)))) afterSecond

theorem current_graph (before : ScriptState) (script : List Reply)
    (o : Outcome ScriptState UInt16 String Empty) :
    currentIndex scriptIndex before script o ↔ currentComputed before script = o := by
  refine (bind_ofFunction_iff (N := UInt16) derefStep _ before script o).trans ?_
  unfold currentComputed
  cases derefStep before script with
  | returned first afterFirst =>
    dsimp only [Outcome.bind]
    refine (bind_ofFunction_iff (N := UInt16) derefStep _ afterFirst script o).trans ?_
    cases derefStep afterFirst script with
    | returned second afterSecond => exact eq_comm
    | unwound m s => exact eq_comm
    | terminated t => exact t.elim
  | unwound m s => exact eq_comm
  | terminated t => exact t.elim

abbrev AtValue := Except ProgramError.Value (Pointer Nat)

def atComputed (before : ScriptState) (args : List Reply × UInt64) :
    Outcome ScriptState AtValue String Empty :=
  Outcome.bind (derefStep before args.1) fun first afterFirst =>
    if readWord scriptMemory afterFirst first.pointer ≤ args.2.toNat then
      .returned (.error .invalidInstructionData) afterFirst
    else
      Outcome.bind (derefStep afterFirst args.1) fun second afterSecond =>
        let offset := readWord scriptMemory afterSecond (second.pointer.add (2 + 2 * args.2.toNat))
        Outcome.bind (derefStep afterSecond args.1) fun third afterThird =>
          .returned (.ok (third.pointer.add offset)) afterThird

theorem at_graph (before : ScriptState) (args : List Reply × UInt64)
    (o : Outcome ScriptState AtValue String Empty) :
    instructionAt scriptIndex before args o ↔ atComputed before args = o := by
  refine (bind_ofFunction_iff (N := AtValue) derefStep _ before args.1 o).trans ?_
  unfold atComputed
  cases derefStep before args.1 with
  | returned first afterFirst =>
    dsimp only [Outcome.bind]
    by_cases count : readWord scriptMemory afterFirst first.pointer ≤ args.2.toNat
    · refine (iff_of_eq (ite_eq_left_of_eq_true _ _ (eq_true count))).trans ?_
      rw [ite_eq_left_of_eq_true _ _ (eq_true count)]
      exact eq_comm
    · refine (iff_of_eq (ite_eq_right_of_eq_false _ _ (eq_false count))).trans ?_
      rw [ite_eq_right_of_eq_false _ _ (eq_false count)]
      refine (bind_ofFunction_iff (N := AtValue) derefStep _ afterFirst args.1 o).trans ?_
      cases derefStep afterFirst args.1 with
      | returned second afterSecond =>
        dsimp only [Outcome.bind]
        refine (bind_ofFunction_iff (N := AtValue) derefStep _ afterSecond args.1 o).trans ?_
        cases derefStep afterSecond args.1 with
        | returned third afterThird => exact eq_comm
        | unwound m s => exact eq_comm
        | terminated t => exact t.elim
      | unwound m s => exact eq_comm
      | terminated t => exact t.elim
  | unwound m s => exact eq_comm
  | terminated t => exact t.elim

/-- The registered pointer observers are `returnsOf` of the raw computations. -/
theorem program_evaluated :
    sysvars.instructions.IntrospectedInstruction.Generic.get_program_id_run
      bufferMemory =
      returnsOf fun before pointer => (programId bufferMemory before pointer, before) := rfl

theorem data_evaluated :
    sysvars.instructions.IntrospectedInstruction.Generic.get_instruction_data_run
        bufferMemory =
      returnsOf fun before pointer => (instructionData bufferMemory before pointer, before) := rfl

theorem current_evaluated :
    sysvars.instructions.Instructions.Generic.load_current_index_run
      scriptIndex =
      currentIndex scriptIndex := rfl

theorem at_evaluated :
    sysvars.instructions.Instructions.Generic.load_instruction_at_run
      scriptIndex =
      instructionAt scriptIndex := rfl

/-! ## Preconditions

The `requires` of the generic families quantify over the returned outcomes of the deref
callback. At the scripted receiver the callback is a function, so each quantifier has exactly
one candidate: `currentReadyB` and `atReadyB` evaluate the conditions on the actual deref
results, and `current_requires_iff` and `at_requires_iff` prove them equivalent to the
registered the `requires` of the contracts. The `requires` of the pointer observers
(`ProgramReady`, `DataReady`) have `Decidable` instances in the models. -/

def currentReadyB (before : ScriptState) (script : List Reply) : Bool :=
  match derefStep before script with
  | .returned first afterFirst =>
    decide (SliceReady scriptMemory afterFirst first) &&
      match derefStep afterFirst script with
      | .returned second afterSecond =>
        decide (SliceReady scriptMemory afterSecond second ∧ 2 ≤ first.length ∧
          first.length ≤ second.length ∧
          AddReady scriptMemory afterSecond second.pointer (first.length - 2) ∧
          RawReady scriptMemory afterSecond (second.pointer.add (first.length - 2)) 2 1)
      | _ => true
  | _ => true

theorem current_requires_iff (before : ScriptState) (script : List Reply) :
    (sysvars.instructions.Instructions.Generic.load_current_index_contract.contract
        scriptIndex).requires before script ↔ currentReadyB before script = true := by
  show CurrentReady scriptIndex before script ↔ _
  unfold CurrentReady currentReadyB
  constructor
  · intro h
    cases h1 : derefStep before script with
    | returned first afterFirst =>
      obtain ⟨s1, rest⟩ := h first afterFirst h1
      dsimp only
      cases h2 : derefStep afterFirst script with
      | returned second afterSecond =>
        dsimp only
        simp only [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨s1, rest second afterSecond h2⟩
      | unwound m s =>
        dsimp only
        simp only [Bool.and_true, decide_eq_true_eq]
        exact s1
      | terminated t => exact t.elim
    | unwound m s => rfl
    | terminated t => exact t.elim
  · intro h first afterFirst h1
    change derefStep before script = _ at h1
    rw [h1] at h
    dsimp only at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, fun second afterSecond h2 => ?_⟩
    change derefStep afterFirst script = _ at h2
    have h' := h.2
    rw [h2] at h'
    dsimp only at h'
    simp only [decide_eq_true_eq] at h'
    exact h'

def atReadyB (before : ScriptState) (args : List Reply × UInt64) : Bool :=
  match derefStep before args.1 with
  | .returned first afterFirst =>
    decide (SliceReady scriptMemory afterFirst first ∧ 2 ≤ first.length ∧
      RawReady scriptMemory afterFirst first.pointer 2 1) &&
    (!decide (args.2.toNat < readWord scriptMemory afterFirst first.pointer) ||
      match derefStep afterFirst args.1 with
      | .returned second afterSecond =>
        decide (SliceReady scriptMemory afterSecond second ∧
          2 + 2 * args.2.toNat + 2 ≤ second.length ∧
          AddReady scriptMemory afterSecond second.pointer (2 + 2 * args.2.toNat) ∧
          RawReady scriptMemory afterSecond (second.pointer.add (2 + 2 * args.2.toNat)) 2 2) &&
        match derefStep afterSecond args.1 with
        | .returned third afterThird =>
          decide (SliceReady scriptMemory afterThird third ∧
            AddReady scriptMemory afterThird third.pointer
              (readWord scriptMemory afterSecond (second.pointer.add (2 + 2 * args.2.toNat))))
        | _ => true
      | _ => true)
  | _ => true

theorem at_requires_iff (before : ScriptState) (args : List Reply × UInt64) :
    (sysvars.instructions.Instructions.Generic.load_instruction_at_contract.contract
        scriptIndex).requires before args ↔ atReadyB before args = true := by
  show AtReady scriptIndex before args ↔ _
  unfold AtReady atReadyB
  constructor
  · intro h
    cases h1 : derefStep before args.1 with
    | returned first afterFirst =>
      obtain ⟨s1, l1, r1, rest⟩ := h first afterFirst h1
      dsimp only
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      refine ⟨⟨s1, l1, r1⟩, ?_⟩
      by_cases count : args.2.toNat < readWord scriptMemory afterFirst first.pointer
      · refine Or.inr ?_
        cases h2 : derefStep afterFirst args.1 with
        | returned second afterSecond =>
          obtain ⟨s2, l2, a2, r2, third⟩ := rest count second afterSecond h2
          dsimp only
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨s2, l2, a2, r2⟩, ?_⟩
          cases h3 : derefStep afterSecond args.1 with
          | returned t afterThird =>
            dsimp only
            simp only [decide_eq_true_eq]
            exact third t afterThird h3
          | unwound m s => rfl
          | terminated x => exact x.elim
        | unwound m s => rfl
        | terminated x => exact x.elim
      · exact Or.inl count
    | unwound m s => rfl
    | terminated x => exact x.elim
  · intro h first afterFirst h1
    change derefStep before args.1 = _ at h1
    rw [h1] at h
    dsimp only at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    obtain ⟨⟨s1, l1, r1⟩, rest⟩ := h
    refine ⟨s1, l1, r1, fun count second afterSecond h2 => ?_⟩
    change derefStep afterFirst args.1 = _ at h2
    rcases rest with outside | inside
    · exact absurd count outside
    rw [h2] at inside
    dsimp only at inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at inside
    obtain ⟨⟨s2, l2, a2, r2⟩, third⟩ := inside
    refine ⟨s2, l2, a2, r2, fun t afterThird h3 => ?_⟩
    change derefStep afterSecond args.1 = _ at h3
    rw [h3] at third
    dsimp only at third
    simp only [decide_eq_true_eq] at third
    exact third

instance (before : ScriptState) (script : List Reply) :
    Decidable
      ((sysvars.instructions.Instructions.Generic.load_current_index_contract.contract
      scriptIndex).requires before script) :=
  decidable_of_iff _ (current_requires_iff before script).symm

instance (before : ScriptState) (args : List Reply × UInt64) :
    Decidable
      ((sysvars.instructions.Instructions.Generic.load_instruction_at_contract.contract
      scriptIndex).requires before args) :=
  decidable_of_iff _ (at_requires_iff before args).symm

instance (before : List Solanalib.Runtime.Bytes) (p : Pointer Nat) :
    Decidable
      ((sysvars.instructions.IntrospectedInstruction.Generic.get_program_id_contract.contract
      bufferMemory).requires before p) :=
  inferInstanceAs (Decidable (ProgramReady bufferMemory before p))

instance (before : List Solanalib.Runtime.Bytes) (p : Pointer Nat) :
    Decidable
      ((sysvars.instructions.IntrospectedInstruction.Generic.get_instruction_data_contract.contract
      bufferMemory).requires before p) :=
  inferInstanceAs (Decidable (DataReady bufferMemory before p))

/-! ## Encodings -/

def memoryOf (j : Json) : Result (List Solanalib.Runtime.Bytes) := do
  (← (← field j "memory").getArr?).toList.mapM asBytes

def memoryJson (m : List Solanalib.Runtime.Bytes) : Json := Json.arr (m.map bytesJson).toArray

def scriptState (j : Json) : Result ScriptState := do
  pure ⟨← memoryOf j, ← nat (← field j "derefs")⟩

def scriptStateJson (s : ScriptState) : Json :=
  Json.mkObj [("memory", memoryJson s.memory), ("derefs", natJson s.derefs)]

def bufferState (j : Json) : Result (List Solanalib.Runtime.Bytes) := memoryOf j

def bufferStateJson (m : List Solanalib.Runtime.Bytes) : Json := Json.mkObj [("memory", memoryJson
  m)]

def reply (j : Json) : Result Reply :=
  match j.getObjVal? "slice", j.getObjVal? "panic" with
  | .ok s, .error _ => do
    pure (.slice (← nat (← field s "allocation")) (← nat (← field s "offset")) (← nat (← field s
      "length")))
  | .error _, .ok m => do pure (.panic (← m.getStr?))
  | _, _ => throw s!"bad deref reply {j.compress}"

def script (j : Json) : Result (List Reply) := do
  (← (← field j "receiver").getArr?).toList.mapM reply

def pointer (j : Json) : Result (Pointer Nat) := do
  pure ⟨← nat (← field j "allocation"), ← nat (← field j "offset")⟩

def pointerJson (p : Pointer Nat) : Json :=
  Json.mkObj [("allocation", natJson p.allocation), ("offset", natJson p.offset)]

def sliceOf (j : Json) : Result (Slice Nat) := do
  pure ⟨← pointer (← field j "pointer"), ← nat (← field j "length")⟩

def sliceJson (s : Slice Nat) : Json :=
  Json.mkObj [("pointer", pointerJson s.pointer), ("length", natJson s.length)]

def someString (s : String) : Option String := some s

/-! ## Checkers -/

def receiver : String := "conformance_runtime_pinocchio_0_11_1::instructions::ScriptedDeref\
  <'_>"

def loadCurrentIndex : Checker where
  function := "pinocchio::sysvars::instructions::Instructions::<T>::load_current_index"
  generics := [("T", receiver)]
  reference :=
    "Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_current_index\
      _run"
  decides :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_current_inde\
      x_run"]
  decidesRequires :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_current_inde\
      x_run"]
  check := fun c => do
    let before ← scriptState c.state
    let r ← script c.args
    let recorded ← parseOutcome u16 scriptState someString noReason c.outcome
    return withRequires "CurrentReady" (decide
      ((sysvars.instructions.Instructions.Generic.load_current_index_contract.contract
        scriptIndex).requires before r)) <| decideGraph (S := ScriptState) (V := UInt16) (U :=
          String) (T := Empty)
      (sysvars.instructions.Instructions.Generic.load_current_index_run
        scriptIndex before r)
      (currentComputed before r) (current_evaluated ▸ current_graph before r) recorded
      (outcomeJson scriptStateJson (fun v => natJson v.toNat) Json.str emptyJson)

def atJson : AtValue → Json := exceptJson programErrorJson pointerJson

def loadInstructionAt : Checker where
  function := "pinocchio::sysvars::instructions::Instructions::<T>::load_instruction_at"
  generics := [("T", receiver)]
  reference :=
    "Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_instruction_a\
      t_run"
  decides :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_instruction_\
      at_run"]
  decidesRequires :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_instruction_\
      at_run"]
  check := fun c => do
    let before ← scriptState c.state
    let args := (← script c.args, ← u64 (← field c.args "index"))
    let recorded ← parseOutcome (asExcept programError pointer) scriptState someString noReason
      c.outcome
    return withRequires "AtReady" (decide
      ((sysvars.instructions.Instructions.Generic.load_instruction_at_contract.contract
        scriptIndex).requires before args)) <| decideGraph (S := ScriptState) (V := AtValue) (U :=
          String) (T := Empty)
      (sysvars.instructions.Instructions.Generic.load_instruction_at_run
        scriptIndex before args)
      (atComputed before args) (at_evaluated ▸ at_graph before args) recorded
      (outcomeJson scriptStateJson atJson Json.str emptyJson)

def getProgramId : Checker where
  function := "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_program\
    _id"
  generics := []
  reference :=
    "Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.Generic.get_pro\
      gram_id_run"
  decides :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.Generic.get_pr\
      ogram_id_run"]
  decidesRequires :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.Generic.get_pr\
      ogram_id_run"]
  check := fun c => do
    let before ← bufferState c.state
    let p ← pointer (← field c.args "instruction")
    return withRequires "ProgramReady" (decide
      ((sysvars.instructions.IntrospectedInstruction.Generic.get_program_id_contract.contract
        bufferMemory).requires before p)) <| ← decideReturns (State := List
          Solanalib.Runtime.Bytes) (Args := Pointer Nat) (Value := Pointer Nat)
      (sysvars.instructions.IntrospectedInstruction.Generic.get_program_id_run
        bufferMemory)
      (fun before pointer => (programId bufferMemory before pointer, before)) program_evaluated
      before p pointer bufferState pointerJson bufferStateJson
      c.outcome

def getInstructionData : Checker where
  function :=
    "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_instruction_data"
  generics := []
  reference :=
    "Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.Generic.get_ins\
      truction_data_run"
  decides :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.Generic.get_in\
      struction_data_run"]
  decidesRequires :=
    ["Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.Generic.get_in\
      struction_data_run"]
  check := fun c => do
    let before ← bufferState c.state
    let p ← pointer (← field c.args "instruction")
    return withRequires "DataReady" (decide
      ((sysvars.instructions.IntrospectedInstruction.Generic.get_instruction_data_contract.contract
        bufferMemory).requires before p)) <| ← decideReturns (State := List
          Solanalib.Runtime.Bytes) (Args := Pointer Nat) (Value := Slice Nat)
      (sysvars.instructions.IntrospectedInstruction.Generic.get_instruction_data_run
        bufferMemory)
      (fun before pointer => (instructionData bufferMemory before pointer, before)) data_evaluated
      before p sliceOf bufferState sliceJson bufferStateJson
      c.outcome

def checkers : List Checker := [loadCurrentIndex, loadInstructionAt, getProgramId,
  getInstructionData]

end SolanalibTest.Conformance.Library.Families.Runtime.Instructions
