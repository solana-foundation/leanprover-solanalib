/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned.Reference

/-- Logical String slot, distinct from a Box slot and from a machine address. -/
structure StringId where
  /-- Monotonically allocated slot number. -/
  index : Nat
  deriving DecidableEq, Repr

/-- Logical Box slot; retired slot numbers are never allocated again. -/
structure BoxId where
  /-- Monotonically allocated slot number. -/
  index : Nat
  deriving DecidableEq, Repr

/-- The three distinct allocation dependencies in generated error construction. -/
inductive Allocation where
  /-- Generated ErrorCode.name copies its literal. -/
  | name
  /-- Fixed Display formatting constructs the message String. -/
  | message
  /-- Box::new stores the completed error payload. -/
  | box
  deriving DecidableEq, Repr

/-- Explicit terminal allocation exhaustion in this finite reference model. -/
inductive Failure where
  /-- No state is attached to this terminal outcome. -/
  | allocation (site : Allocation)
  deriving DecidableEq, Repr

/-- Events expose source ordering and the current contents actually dropped. -/
inductive Event where
  /-- Literal copying creates this fresh String slot. -/
  | name (resource : StringId) (text : String)
  /-- Fixed-literal formatting creates this fresh String slot. -/
  | message (resource : StringId) (text : String)
  /-- The completed payload enters this fresh Box. -/
  | box (resource : BoxId) (payload : Payload StringId)
  /-- A store retains the Box identity and changes its current payload. -/
  | write (resource : BoxId)
  /-- A String drop observes these contents in its actual input state. -/
  | dropString (resource : StringId) (text : String)
  /-- Final Box allocation retirement. -/
  | freeBox (resource : BoxId)
  deriving DecidableEq, Repr

/-- A finite mathematical heap and an explicit allocation budget. This budget
is a witness/failure provider, not Rust capacity, allocator cost or gas. -/
structure State where
  /-- String tombstones keep all surviving slot identities stable. -/
  strings : List (Option String)
  /-- Box tombstones likewise prevent reuse of retired slots. -/
  boxes : List (Option (Payload StringId))
  /-- Successful allocation dependencies remaining in this interpretation. -/
  remaining : Nat
  /-- Ordered finite dependency events. -/
  events : List Event
  deriving DecidableEq, Repr

/-- An empty heap with the explicitly chosen allocation allowance. -/
def initial (allocations : Nat) : State := ⟨[], [], allocations, []⟩

/-- Only live String slots have an observation. -/
def currentString (state : State) (resource : StringId) : Option String :=
  state.strings[resource.index]?.join

/-- A Box remains represented until its allocation is retired. -/
def currentBox (state : State) (resource : BoxId) : Option (Payload StringId) :=
  state.boxes[resource.index]?.join

/-- State/value result of a successful String dependency. Both source paths
allocate fresh identities; their distinct events remain observable. -/
def stringResult (message : Bool) (before : State) (text : String) : StringId × State :=
  let resource : StringId := ⟨before.strings.length⟩
  let event := if message then Event.message resource text else Event.name resource text
  (resource, ⟨before.strings ++ [some text], before.boxes,
    before.remaining - 1, before.events ++ [event]⟩)

/-- Copy or format one fixed literal, with an actual terminal failure when
the witness provider has no allocation remaining. -/
def allocateString (message : Bool) (before : State) (text : String) :
    Outcome State StringId Empty Failure :=
  if before.remaining = 0 then .terminated (.allocation (if message then .message else .name))
  else let result := stringResult message before text
       .returned result.1 result.2

/-- Successful Box allocation result, retaining resource-bearing fields. -/
def boxResult (before : State) (payload : Payload StringId) : BoxId × State :=
  let resource : BoxId := ⟨before.boxes.length⟩
  (resource, ⟨before.strings, before.boxes ++ [some payload],
    before.remaining - 1, before.events ++ [.box resource payload]⟩)

/-- Box allocation has its own explicit failure point after field evaluation. -/
def allocateBox (before : State) (payload : Payload StringId) :
    Outcome State BoxId Empty Failure :=
  if before.remaining = 0 then .terminated (.allocation .box)
  else let result := boxResult before payload
       .returned result.1 result.2

/-- A live Box update preserves every other slot and the remaining budget. -/
def writeBox (before : State) (resource : BoxId) (payload : Payload StringId) : Option State :=
  match currentBox before resource with
  | none => none
  | some _ => some ⟨before.strings, before.boxes.set resource.index (some payload),
      before.remaining, before.events ++ [.write resource]⟩

/-- A String drop retires its slot and records its actual current text. -/
def retireString (before : State) (resource : StringId)
    (outcome : Outcome State Unit Empty Failure) : Prop :=
  ∃ text, currentString before resource = some text ∧ outcome = .returned ()
    ⟨before.strings.set resource.index none, before.boxes,
      before.remaining, before.events ++ [.dropString resource text]⟩

/-- Retire an existing Box allocation after source-ordered field cleanup. -/
def retireBox (before : State) (resource : BoxId)
    (outcome : Outcome State Unit Empty Failure) : Prop :=
  ∃ payload, currentBox before resource = some payload ∧ outcome = .returned ()
    ⟨before.strings, before.boxes.set resource.index none,
      before.remaining, before.events ++ [.freeBox resource]⟩

/-- The concrete provider has real String/Box identities, current contents,
stores, retirement and terminal allocation failures. It models no Rust heap. -/
def ops : Ops State StringId BoxId Failure where
  currentString := currentString
  currentBox := currentBox
  copyLiteral := Callback.ofFunction (allocateString false)
  formatLiteral := Callback.ofFunction (allocateString true)
  newBox := Callback.ofFunction allocateBox
  writeBox := writeBox
  dropString := retireString
  freeBox := retireBox

/-- The three successful dependency results, kept explicit for composition. -/
def buildCodeResult (before : State) (code : Code) : Error BoxId × State :=
  let name := stringResult false before code.name
  let message := stringResult true name.2 code.message
  let box := boxResult message.2 (.anchor ⟨name.1, code.number, message.1, none, none⟩)
  (⟨box.1⟩, box.2)

/-- Successful ProgramError conversion has only its one Box dependency. -/
def fromProgramResult (before : State) (program : ProgramError.Value) : Error BoxId × State :=
  let box := boxResult before (.program ⟨program, none, none⟩)
  (⟨box.1⟩, box.2)

/-- Sufficient explicit budget gives a real normal model construction. -/
theorem buildCode_returns (before : State) (code : Code) (available : 3 ≤ before.remaining) :
    buildCode ops before code
      (.returned (buildCodeResult before code).1 (buildCodeResult before code).2) := by
  apply (buildCode_returned_iff _ _ _ _ _).mpr
  refine ⟨(stringResult false before code.name).1, (stringResult false before code.name).2,
    (stringResult true (stringResult false before code.name).2 code.message).1,
    (stringResult true (stringResult false before code.name).2 code.message).2, ?_, ?_, ?_⟩
  · change allocateString false before code.name = _
    have positive : before.remaining ≠ 0 := by omega
    simp only [allocateString, positive, ↓reduceIte]
  · change allocateString true (stringResult false before code.name).2 code.message = _
    have positive : (stringResult false before code.name).2.remaining ≠ 0 := by
      change before.remaining - 1 ≠ 0
      omega
    simp only [allocateString, positive, ↓reduceIte]
  · change allocateBox (stringResult true (stringResult false before code.name).2 code.message).2
      (.anchor ⟨(stringResult false before code.name).1, code.number,
        (stringResult true (stringResult false before code.name).2 code.message).1, none, none⟩) = _
    have positive : (stringResult true (stringResult false before code.name).2
      code.message).2.remaining ≠ 0 := by
      change before.remaining - 1 - 1 ≠ 0
      omega
    simp only [allocateBox, positive, ↓reduceIte]
    rfl

/-- One available allocation supplies the program-error Box and its real state. -/
theorem fromProgram_returns (before : State) (program : ProgramError.Value)
    (available : 1 ≤ before.remaining) :
    fromProgram ops before program
      (.returned (fromProgramResult before program).1 (fromProgramResult before program).2) := by
  apply (fromProgram_returned_iff _ _ _ _ _).mpr
  change allocateBox before (.program ⟨program, none, none⟩) = _
  have positive : before.remaining ≠ 0 := by omega
  simp only [allocateBox, positive, ↓reduceIte]
  rfl

/-- Distinct terminal codes for the three allocation sites, solely for
composition with surrounding mathematical Nat-terminal witnesses. -/
def Failure.code : Failure → Nat
  | .allocation .name => 0
  | .allocation .message => 1
  | .allocation .box => 2

/-- The same heap operations, with terminal reasons represented by Nat. -/
def natOps : Ops State StringId BoxId Nat := ops.mapTerminal Failure.code

/-- The Nat-terminal provider has the same normal fixed-code execution. -/
theorem buildCode_returns_nat (before : State) (code : Code) (available : 3 ≤ before.remaining) :
    buildCode natOps before code
      (.returned (buildCodeResult before code).1 (buildCodeResult before code).2) :=
  buildCode_mapTerminal_returned ops Failure.code before code _ _
    (buildCode_returns before code available)

/-- The Nat-terminal provider has the same normal program-error execution. -/
theorem fromProgram_returns_nat (before : State) (program : ProgramError.Value)
    (available : 1 ≤ before.remaining) :
    fromProgram natOps before program
      (.returned (fromProgramResult before program).1 (fromProgramResult before program).2) :=
  fromProgram_mapTerminal_returned ops Failure.code before program _ _
    (fromProgram_returns before program available)

end Solanalib.Specs.Core.AnchorErrorOwned.Reference
