/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Heap

/-! Executable callback graphs retain both the protected moved error and the return-place
alternative of the pinned compiler, only on its actual reached path. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

namespace Fn

variable {U : Type}

def moved (types : Types)
    (fn : OpsFn types.State types.Program types.StringResource types.BoxResource types.Terminal)
    (double : types.State → U → U → Option types.Terminal)
    (locals : List (types.State → Option (Outcome types.State Unit U types.Terminal)))
    (original : types.Error) (pending : Outcome types.State types.Error U types.Terminal) :
    List (Outcome types.State types.Error U types.Terminal) :=
  (PGraph.cleanupFn double locals pending).toList.flatMap fun cleaned =>
    let dropValue := fun value => PGraph.onUnwindFn double
      [fun state => (drop types.storage types.ops fn state value).map OwnedFn.liftO] cleaned
    match pending with
    | .returned value _ => (dropValue value).toList ++
        match cleaned with
        | .unwound _ _ => [cleaned]
        | _ => []
    | .unwound _ _ => (dropValue original).toList
    | .terminated _ => [cleaned]

theorem moved_graph (types : Types)
    {fn : OpsFn types.State types.Program types.StringResource types.BoxResource types.Terminal}
    (graph : OpsGraph types.ops fn)
    {double : Owned.DoubleUnwind types.State U types.Terminal}
    {doubleFn : types.State → U → U → Option types.Terminal}
    (doubleGraph : ∀ state left right, PGraph (double state left right) (doubleFn state left right))
    {locals : List (Owned.DropAction types.State U types.Terminal)}
    {localFns : List (types.State → Option (Outcome types.State Unit U types.Terminal))}
    (localGraph : PGraph.DropsGraph locals localFns)
    (original : types.Error) (pending : Outcome types.State types.Error U types.Terminal) :
    LGraph (finishMoved types double locals original pending)
      (moved types fn doubleFn localFns original pending) := by
  apply LGraph.exists_step (PGraph.cleanup doubleGraph _ _ localGraph pending)
  intro cleaned
  have dropGraph (value : types.Error) := PGraph.onUnwind doubleGraph
    (PGraph.DropsGraph.cons
      (d := dropLift types value)
      (fun state => OwnedFn.lift_graph (drop_graph graph types.storage state value))
      PGraph.DropsGraph.nil) cleaned
  cases pending with
  | returned value state =>
    apply LGraph.or (LGraph.ofPGraph (dropGraph value))
    intro final
    cases cleaned <;> simp
  | unwound reason state => exact LGraph.ofPGraph (dropGraph original)
  | terminated reason =>
    intro final
    simp

end Fn

structure Operand where
  label : String
  text : String
  displayPanic : Bool
  dropPanic : Bool

def display (before : Heap) (operand : Operand) : Outcome Heap Nat String String :=
  let after := { before with callbacks := before.callbacks ++ ["display " ++ operand.label] }
  if operand.displayPanic then .unwound ("display " ++ operand.label) after
  else OwnedFn.liftO (newString after operand.text)

def dropOperand (before : Heap) (operand : Operand) : Outcome Heap Unit String String :=
  let after := { before with callbacks := before.callbacks ++ ["drop " ++ operand.label] }
  if operand.dropPanic then .unwound ("drop " ++ operand.label) after else .returned () after

def double : Owned.DoubleUnwind Heap String String := fun _ _ _ terminal => terminal =
  "abort"
def doubleFn : Heap → String → String → Option String := fun _ _ _ => some "abort"

theorem doubleGraph : ∀ state left right, PGraph (double state left right) (doubleFn state left
  right) :=
  fun _ _ _ => PGraph.eq_left _

def valuesTypes (storage : Storage) : ValuesTypes where
  toTypes := heapTypes storage
  Left := Operand
  Right := Operand
  Unwind := String
  callbacks := {
    left := Callback.ofFunction display
    right := Callback.ofFunction display
    dropLeft := Callback.ofFunction dropOperand
    dropRight := Callback.ofFunction dropOperand
    double := double }

abbrev Args (storage : Storage) :=
  ValuesArgs (Error storage (Program Nat) Nat Nat) Operand Operand

def valuesBodyFn (storage : Storage) (before : Heap) (args : Args storage) :=
  (some (display before args.left)).bind (PGraph.bindK fun left middle =>
    ((some (display middle args.right)).bind
      (PGraph.onUnwindFn doubleFn [fun state => (heapFn.dropString state left).map
        OwnedFn.liftO])).bind
      (PGraph.bindK fun right after =>
        (Fn.withCompared storage heapOps heapFn (some (.values left right)) after args.error).map
          OwnedFn.liftO))

theorem valuesBodyGraph (storage : Storage) (before : Heap) (args : Args storage) :
    PGraph (valuesBody (valuesTypes storage) args before ()) (valuesBodyFn storage before args) :=
      by
  apply PGraph.bind (PGraph.ofFunction display before args.left)
  intro left middle
  apply PGraph.bind
  · exact PGraph.protect doubleGraph
      (PGraph.DropsGraph.cons (fun state => OwnedFn.lift_graph (heapGraph.dropString state left))
        PGraph.DropsGraph.nil) (PGraph.ofFunction display middle args.right)
  · intro right after
    exact OwnedFn.lift_graph (Fn.withCompared_graph heapGraph storage (some (.values left right))
      after args.error)

def valueLocals (storage : Storage) (args : Args storage) :
    List (Heap → Option (Outcome Heap Unit String String)) :=
  [fun state => some (dropOperand state args.left), fun state => some (dropOperand state
    args.right)]

theorem valueLocalsGraph (storage : Storage) (args : Args storage) :
    PGraph.DropsGraph
      [fun state result => (valuesTypes storage).callbacks.dropLeft state args.left result,
       fun state result => (valuesTypes storage).callbacks.dropRight state args.right result]
      (valueLocals storage args) :=
  PGraph.DropsGraph.cons (fun state => PGraph.ofFunction dropOperand state args.left)
    (PGraph.DropsGraph.cons (fun state => PGraph.ofFunction dropOperand state args.right)
      PGraph.DropsGraph.nil)

def valuesFn (storage : Storage) (before : Heap) (args : Args storage) :=
  (valuesBodyFn storage before args).toList.flatMap
    (Fn.moved (heapTypes storage) heapFn doubleFn (valueLocals storage args) args.error)

theorem valuesGraph (storage : Storage) (before : Heap) (args : Args storage) :
    LGraph (valuesRun (valuesTypes storage) before args) (valuesFn storage before args) :=
  LGraph.exists_step (valuesBodyGraph storage before args) fun pending =>
    Fn.moved_graph (heapTypes storage) heapGraph doubleGraph (valueLocalsGraph storage args)
      args.error pending

def nameTypes (storage : Storage) : NameTypes where
  toTypes := heapTypes storage
  Name := Operand
  Unwind := String
  toString := Callback.ofFunction display
  dropName := Callback.ofFunction dropOperand
  double := double

def nameBodyFn (storage : Storage) (before : Heap)
    (args : Error storage (Program Nat) Nat Nat × Operand) :=
  (some (display before args.2)).bind (PGraph.bindK fun name after =>
    (Fn.withOrigin storage heapOps heapFn (some (.accountName name)) after args.1).map
      OwnedFn.liftO)

theorem nameBodyGraph (storage : Storage) (before : Heap)
    (args : Error storage (Program Nat) Nat Nat × Operand) :
    PGraph (nameBody (nameTypes storage) args before ()) (nameBodyFn storage before args) :=
  PGraph.bind (PGraph.ofFunction display before args.2) fun name after =>
    OwnedFn.lift_graph (Fn.withOrigin_graph heapGraph storage (some (.accountName name)) after
      args.1)

def nameFn (storage : Storage) (before : Heap)
    (args : Error storage (Program Nat) Nat Nat × Operand) :=
  (nameBodyFn storage before args).toList.flatMap
    (Fn.moved (heapTypes storage) heapFn doubleFn [fun state => some (dropOperand state args.2)]
      args.1)

theorem nameGraph (storage : Storage) (before : Heap)
    (args : Error storage (Program Nat) Nat Nat × Operand) :
    LGraph (nameRun (nameTypes storage) before args) (nameFn storage before args) :=
  LGraph.exists_step (nameBodyGraph storage before args) fun pending =>
    Fn.moved_graph (heapTypes storage) heapGraph doubleGraph
      (PGraph.DropsGraph.cons (fun state => PGraph.ofFunction dropOperand state args.2)
        PGraph.DropsGraph.nil) args.1 pending

/-- The four whole IO conversion scripts retain their own consuming state,
including the formatted String which remains live when the IO drop panics. -/
def ioConvert (before : Heap) (mode : Nat) : Outcome Heap (Program Nat) String String :=
  let displayed := { before with callbacks := before.callbacks ++ ["display io"] }
  let failed := { displayed with callbacks := displayed.callbacks ++ ["drop io"] }
  if mode = 3 then .terminated "abort"
  else if mode = 1 then .unwound "display io" failed
  else
    match newString displayed "payload text" with
    | .returned owner heap =>
      let after := { heap with callbacks := heap.callbacks ++ ["drop io"] }
      if mode = 2 then .unwound "drop io" after
      else .returned (.inl (.borshIoError owner)) after
    | .unwound impossible _ => nomatch impossible
    | .terminated reason => .terminated reason

def ioTypes : IoTypes where
  toTypes := heapTypes .boxed
  IoError := Nat
  Unwind := String
  fromIo := Callback.ofFunction ioConvert

def ioFn (before : Heap) (mode : Nat) :=
  (some (ioConvert before mode)).bind (PGraph.bindK fun program after =>
    (Fn.fromProgram .boxed heapFn after program).map OwnedFn.liftO)

theorem ioGraph (before : Heap) (mode : Nat) :
    PGraph (ioRun ioTypes before mode) (ioFn before mode) :=
  PGraph.bind (PGraph.ofFunction ioConvert before mode) fun program after =>
    OwnedFn.lift_graph (Fn.fromProgram_graph heapGraph .boxed after program)

end SolanalibTest.Conformance.Library.Families.AnchorOperations
