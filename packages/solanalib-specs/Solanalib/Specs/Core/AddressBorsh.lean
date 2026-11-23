/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address
public import Solanalib.Specs.Core.BorshFamily
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-! A fixed address is one `[u8; 32]` field. Writer and reader providers retain
their real state, errors, unwind and terminal exits. The reader boundary is
`R::read_exact`, including an override; no default read loop is substituted. -/

def field (address : Value) : FixedArray UInt8 32 := ⟨address.bytes, address.length_eq⟩

def serializeRun (index : WriterIndex) (before : index.State) (address : Value) :
    Outcome index.State (Except IoError Unit) index.Unwind index.Terminal → Prop :=
  arraySerializeRun ⟨index.State, index.Unwind, index.Terminal, index.writer, 32, .byte⟩
    before (field address)

/-- The byte-specialized array makes one whole-slice write_all. -/
theorem serializeRun_iff (index : WriterIndex) (before : index.State) (address : Value)
    (outcome : Outcome index.State (Except IoError Unit) index.Unwind index.Terminal) :
    serializeRun index before address outcome ↔ index.writer before address.bytes outcome := by
  change (byteArraySerializeProgram (α := Empty) 32 (field address)).Runs
    (writeHandler index.writer noElement) before outcome ↔ _
  rw [show byteArraySerializeProgram (α := Empty) 32 (field address) =
    .call (.writeAll address.bytes) (fun result =>
      match result with
      | .error error => .pure (.error error)
      | .ok () => .pure (.ok ())) from rfl, Program.runs_call]
  constructor
  · rintro ⟨intermediate, step, rest⟩
    cases intermediate with
    | returned result after =>
      cases result with
      | error error => cases rest; exact step
      | ok done => cases done; cases rest; exact step
    | unwound reason after => cases rest; exact step
    | terminated reason => cases rest; exact step
  · intro step
    refine ⟨outcome, step, ?_⟩
    cases outcome with
    | returned result after => cases result with
      | error error => rfl
      | ok done => cases done; rfl
    | unwound reason after => rfl
    | terminated reason => rfl

def serializeFamily : Family where
  Index := WriterIndex
  State := WriterIndex.State
  Args := fun _ => Address.Value
  Value := fun _ => Except IoError Unit
  Unwind := WriterIndex.Unwind
  Terminal := WriterIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before address => index.writer before address.bytes }

def serializeReference : FamilyRun serializeFamily := serializeRun

theorem serializeReference_correct : FamilyReference serializeFamily serializeReference :=
  fun index before address outcome _ step => (serializeRun_iff index before address outcome).mp step

def writeSample : WriterIndex where
  State := Solanalib.Runtime.Bytes
  Unwind := String
  Terminal := String
  writer := Callback.ofFunction fun before bytes => .returned (.ok ()) (before ++ bytes)

theorem writeSample_execution :
    FamilyHasExecution serializeFamily serializeReference writeSample :=
  ⟨[], .zero, .returned (.ok ()) (List.replicate 32 0), trivial,
    (serializeRun_iff writeSample [] .zero _).mpr rfl⟩

structure ReadReply where
  result : Except IoError Unit
  /-- The full initialized local array after read_exact, including unwritten zeros. -/
  buffer : Value

/-- The error value is its kind/message observation. The selected State and
its error-storage interpretation retain the actual tagged word, owned payload,
and allocator state. Each callback below receives the actual preceding state;
none is assumed to have a finite exit or to preserve that state. -/
structure ReadIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  readExact : Callback.Run State Value ReadReply Unwind Terminal
  /-- Construct the selected replacement error, including successful allocation
  effects. An unwind has already cleaned the partial resources of the construction. -/
  constructError : Callback.Run State IoError Unit Unwind Terminal
  /-- Destroy the original returned error and its actual payload. This includes
  state changes, a payload destructor unwind, and terminal exits. -/
  dropError : Callback.Run State IoError Unit Unwind Terminal
  /-- The unwind handling of the selected lowering for the already constructed return
  place. The pinned return-place-retention path is a state-preserving operation;
  a lowering that destroys the replacement supplies its actual cleanup here. -/
  unwindReturnPlace : Callback.Run State IoError Unit Unwind Terminal
  doubleUnwind : Owned.DoubleUnwind State Unwind Terminal

def mapReadError (kind : ErrorKind) (error : IoError) : IoError :=
  if error.kind.debugName = "UnexpectedEof" then ⟨kind, unexpectedLengthMessage⟩ else error

/-- Only the returned observation; this is not the stateful EOF execution. -/
def readResult (kind : ErrorKind) (reply : ReadReply) : Except IoError Value :=
  match reply.result with
  | .ok () => .ok reply.buffer
  | .error error => .error (mapReadError kind error)

/-- Borsh constructs the replacement before dropping the incoming EOF error.
Construction unwind cleans the original error. After successful construction,
an original-error unwind reaches the selected return-place handling; it never
redrops the original owner. A second unwind uses the explicit terminal policy.
Non-EOF errors move out unchanged without any of these callbacks. -/
def mapReadErrorRun (kind : ErrorKind) (index : ReadIndex) :
    Callback.Run index.State IoError IoError index.Unwind index.Terminal :=
  fun before error outcome =>
    if error.kind.debugName = "UnexpectedEof" then
      let replacement : IoError := ⟨kind, unexpectedLengthMessage⟩
      Callback.bind
        (Owned.protect index.doubleUnwind
          [fun state final => index.dropError state error final] index.constructError)
        (fun () after =>
          Owned.protect index.doubleUnwind
            [fun state final => index.unwindReturnPlace state replacement final]
            (Callback.map (fun () => replacement) index.dropError) after error)
        before replacement outcome
    else outcome = .returned error before

def readAfter (kind : ErrorKind) (index : ReadIndex) (reply : ReadReply)
    (before : index.State) :
    Outcome index.State (Except IoError Value) index.Unwind index.Terminal → Prop :=
  match reply.result with
  | .ok () => fun outcome => outcome = .returned (.ok reply.buffer) before
  | .error error => Callback.map Except.error (mapReadErrorRun kind index) before error

def readRun (kind : ErrorKind) (index : ReadIndex) (before : index.State) (_ : Unit) :
    Outcome index.State (Except IoError Value) index.Unwind index.Terminal → Prop :=
  Callback.bind index.readExact (readAfter kind index) before .zero

/-- A concrete reader/error interpretation may have no observable constructor
or original-destructor effects in its selected State. Only those two actual
callback equations are needed: return-place cleanup is then unreachable. -/
theorem mapReadErrorRun_pure_error_steps (kind : ErrorKind) (index : ReadIndex)
    (construct : index.constructError = Callback.ofFunction (fun before _ => .returned () before))
    (destroy : index.dropError = Callback.ofFunction (fun before _ => .returned () before))
    (before : index.State) (error : IoError)
    (outcome : Outcome index.State IoError index.Unwind index.Terminal) :
    mapReadErrorRun kind index before error outcome ↔
      outcome = .returned (mapReadError kind error) before := by
  by_cases eof : error.kind.debugName = "UnexpectedEof"
  · simp [mapReadErrorRun, mapReadError, eof, construct, destroy, Callback.bind,
      Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind, Outcome.map, eq_comm]
  · simp [mapReadErrorRun, mapReadError, eof]

theorem readAfter_pure_error_steps (kind : ErrorKind) (index : ReadIndex)
    (construct : index.constructError = Callback.ofFunction (fun before _ => .returned () before))
    (destroy : index.dropError = Callback.ofFunction (fun before _ => .returned () before))
    (reply : ReadReply) (before : index.State)
    (outcome : Outcome index.State (Except IoError Value) index.Unwind index.Terminal) :
    readAfter kind index reply before outcome ↔
      outcome = .returned (readResult kind reply) before := by
  cases reply with
  | mk result buffer =>
    cases result with
    | ok value => cases value; rfl
    | error error =>
      simp only [readAfter, Callback.map, readResult]
      simp only [mapReadErrorRun_pure_error_steps kind index construct destroy]
      simp [Outcome.map, eq_comm]

theorem readRun_pure_error_steps (kind : ErrorKind) (index : ReadIndex)
    (construct : index.constructError = Callback.ofFunction (fun before _ => .returned () before))
    (destroy : index.dropError = Callback.ofFunction (fun before _ => .returned () before))
    (before : index.State) (args : Unit)
    (outcome : Outcome index.State (Except IoError Value) index.Unwind index.Terminal) :
    readRun kind index before args outcome ↔
      Callback.map (readResult kind) index.readExact before .zero outcome := by
  constructor
  · rintro ⟨actual, called, continued⟩
    refine ⟨actual, called, ?_⟩
    cases actual with
    | returned reply state =>
      exact ((readAfter_pure_error_steps kind index construct destroy reply state outcome).mp
        continued).symm
    | unwound reason state => exact continued.symm
    | terminated reason => exact continued.symm
  · rintro ⟨actual, called, mapped⟩
    refine ⟨actual, called, ?_⟩
    cases actual with
    | returned reply state =>
      exact (readAfter_pure_error_steps kind index construct destroy reply state outcome).mpr
        mapped.symm
    | unwound reason state => exact mapped.symm
    | terminated reason => exact mapped.symm

def readFamily (kind : ErrorKind) : Family where
  Index := ReadIndex
  State := ReadIndex.State
  Args := fun _ => Unit
  Value := fun _ => Except IoError Address.Value
  Unwind := ReadIndex.Unwind
  Terminal := ReadIndex.Terminal
  contract := fun index => { requires := fun _ _ => True, post := readRun kind index }

def readReference (kind : ErrorKind) : FamilyRun (readFamily kind) := readRun kind

theorem readReference_correct (kind : ErrorKind) :
    FamilyReference (readFamily kind) (readReference kind) :=
  fun _ _ _ _ _ execution => execution

/-- This sample records separate read, construction, and destruction effects. -/
def readSample : ReadIndex where
  State := Nat
  Unwind := String
  Terminal := String
  readExact := Callback.ofFunction fun before buffer =>
    .returned ⟨.error ⟨⟨"UnexpectedEof"⟩, "short input"⟩, buffer⟩ (before + 7)
  constructError := Callback.ofFunction fun before _ => .returned () (before + 11)
  dropError := Callback.ofFunction fun before _ => .returned () (before + 13)
  unwindReturnPlace := Callback.ofFunction fun before _ => .returned () before
  doubleUnwind := fun _ _ _ terminal => terminal = "double unwind"

theorem readSample_execution (kind : ErrorKind) :
    FamilyHasExecution (readFamily kind) (readReference kind) readSample := by
  refine ⟨(0 : Nat), (), .returned (.error ⟨kind, unexpectedLengthMessage⟩) (31 : Nat), trivial, ?_⟩
  simp [readReference, readRun, readAfter, mapReadErrorRun, readSample, Callback.bind,
    Callback.map, Callback.ofFunction, Owned.protect, Owned.onUnwind, Outcome.map]
  rfl

/-- A returned wrapper result retains the read reply and its actual intermediate
state, then the reached continuation. The final state need not equal the
read_exact return state because EOF construction and destruction follow it. -/
theorem readRun_returned (kind : ErrorKind) (index : ReadIndex)
    (before after : index.State) (result : Except IoError Value)
    (execution : readRun kind index before () (.returned result after)) :
    ∃ reply middle, index.readExact before .zero (.returned reply middle) ∧
      readAfter kind index reply middle (.returned result after) := by
  obtain ⟨actual, step, continued⟩ := execution
  cases actual with
  | returned reply state => exact ⟨reply, state, step, continued⟩
  | unwound reason state => cases continued
  | terminated reason => cases continued

/-- Borsh 0.9.3 uses copy_from_bytes: a short input fails before modifying the
slice. Both its fixed-array and const-generics source paths have this behavior. -/
def legacyDecode (input : Solanalib.Runtime.Bytes) : Except IoError Value × Solanalib.Runtime.Bytes
  :=
  if enough : 32 ≤ input.length then
    (.ok ⟨input.take 32, by simp [List.length_take, enough]⟩, input.drop 32)
  else (.error ⟨.invalidInput, unexpectedLengthMessage⟩, input)

theorem legacyDecode_short (input : Solanalib.Runtime.Bytes) (short : input.length < 32) :
    legacyDecode input = (.error ⟨.invalidInput, unexpectedLengthMessage⟩, input) := by
  simp [legacyDecode, Nat.not_le_of_gt short]

end Solanalib.Specs.Core.Address.Borsh
