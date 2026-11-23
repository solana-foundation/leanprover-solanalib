/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.SysvarRent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

abbrev Clock := Solanalib.Runtime.Clock

def clockValid (clock : Clock) : Prop :=
  clock.slot < Solanalib.Runtime.U64_LIMIT ∧ clock.epoch < Solanalib.Runtime.U64_LIMIT ∧
    clock.leaderScheduleEpoch < Solanalib.Runtime.U64_LIMIT ∧
    -(2^63 : Int) ≤ clock.epochStartTimestamp ∧ clock.epochStartTimestamp < 2^63 ∧
    -(2^63 : Int) ≤ clock.unixTimestamp ∧ clock.unixTimestamp < 2^63

def zeroClock : Clock := ⟨0, 0, 0, 0, 0⟩

theorem zeroClock_valid : clockValid zeroClock := by
  unfold clockValid zeroClock Solanalib.Runtime.U64_LIMIT
  decide

inductive GetterTarget where
  | solana
  | hostStub
  deriving DecidableEq, Repr

/-- Typed syscalls and generic byte-prefix syscalls remain different requests.
A getter profile supplies its exact byte extent or typed destination. -/
inductive ReadKind where
  | generic (address : Solanalib.Runtime.Pubkey) (offset length : UInt64)
  | typed (kind : Solanalib.Runtime.TypedSysvar)
  deriving DecidableEq, Repr

/-- The initial abstract destination value is `none` for MaybeUninit and
`some default` for the SDK typed macro. This does not claim initialized padding. -/
structure ReadRequest (Value : Type) where
  kind : ReadKind
  initial : Option Value

/-- The callback supplies the actual status and final initialized destination
value, if any. Destination initialization/origin is an explicit primitive
obligation, not an independently selected successful return value. -/
structure ReadReply (Value : Type) where
  status : UInt64
  destination : Option Value

def genericError (status : UInt64) : Option ProgramError.Value :=
  if status = 0 then none
  else if status = 1 then some .invalidArgument else some .unsupportedSysvar

structure GetterConfig (Value : Type) where
  request : ReadRequest Value
  valid : Value → Prop
  error : UInt64 → Option ProgramError.Value

structure GetterIndex (Value : Type) where
  State : Type
  Unwind : Type
  Terminal : Type
  target : GetterTarget
  read : Callback.Run State (GetterTarget × ReadRequest Value) (ReadReply Value) Unwind Terminal

/-- Every actual successful provider reply initializes the destination that
the getter reads. Error statuses and abnormal exits have no such requirement.
This admission is independent of target selection and value validity. -/
def GetterReady {Value : Type} (config : GetterConfig Value) (index : GetterIndex Value)
    (before : index.State) : Prop :=
  ∀ reply after,
    index.read before (index.target, config.request) (.returned reply after) →
    config.error reply.status = none →
    ∃ value, reply.destination = some value

/-- The separate successful-value law used by `get_success_valid`. It does
not establish initialization and is not part of the continuation admission. -/
def GetterValid {Value : Type} (config : GetterConfig Value) (index : GetterIndex Value)
    (before : index.State) : Prop :=
  ∀ reply after value,
    index.read before (index.target, config.request) (.returned reply after) →
    config.error reply.status = none → reply.destination = some value → config.valid value

def forwardGetter {Value State Unwind Terminal : Type} (config : GetterConfig Value)
    (exit : Outcome State (ReadReply Value) Unwind Terminal)
    (outcome : Outcome State (Except ProgramError.Value Value) Unwind Terminal) : Prop :=
  match exit with
  | .returned reply after => match config.error reply.status with
    | some error => outcome = .returned (.error error) after
    | none => ∃ value, reply.destination = some value ∧ outcome = .returned (.ok value) after
  | .unwound reason after => outcome = .unwound reason after
  | .terminated reason => outcome = .terminated reason

def get {Value : Type} (config : GetterConfig Value) (index : GetterIndex Value) :
    Callback.Run index.State Unit (Except ProgramError.Value Value) index.Unwind index.Terminal :=
  fun before _ outcome => ∃ exit,
    index.read before (index.target, config.request) exit ∧ forwardGetter config exit outcome

/-- The local continuation is available exactly when a successful reply has
an initialized destination. Error, unwind and terminal exits always forward. -/
theorem forwardGetter_hasOutcome_iff {Value State Unwind Terminal : Type}
    (config : GetterConfig Value) (exit : Outcome State (ReadReply Value) Unwind Terminal) :
    (∃ outcome, forwardGetter config exit outcome) ↔
      match exit with
      | .returned reply _ => config.error reply.status = none →
          ∃ value, reply.destination = some value
      | .unwound _ _ => True
      | .terminated _ => True := by
  cases exit with
  | returned reply after =>
      cases converted : config.error reply.status with
      | none =>
          constructor
          · rintro ⟨outcome, forwarded⟩ _
            simp only [forwardGetter, converted] at forwarded
            obtain ⟨value, present, _⟩ := forwarded
            exact ⟨value, present⟩
          · intro initialized
            obtain ⟨value, present⟩ := initialized converted
            exact ⟨.returned (.ok value) after, by
              simp only [forwardGetter, converted]
              exact ⟨value, present, rfl⟩⟩
      | some error =>
          constructor
          · intro _ impossible
            simp only [converted, reduceCtorEq] at impossible
          · intro _
            exact ⟨.returned (.error error) after, by simp only [forwardGetter, converted]⟩
  | unwound reason after =>
      exact ⟨fun _ => True.intro, fun _ => ⟨.unwound reason after, rfl⟩⟩
  | terminated reason =>
      exact ⟨fun _ => True.intro, fun _ => ⟨.terminated reason, rfl⟩⟩

/-- Each actual provider exit is retained by the original forwarding relation,
which keeps its value/state or exact abnormal reason. No exit is selected away. -/
theorem get_retains {Value : Type} (config : GetterConfig Value) (index : GetterIndex Value)
    (before : index.State) (ready : GetterReady config index before)
    (exit : Outcome index.State (ReadReply Value) index.Unwind index.Terminal)
    (read : index.read before (index.target, config.request) exit) :
    ∃ outcome, forwardGetter config exit outcome ∧ get config index before () outcome := by
  cases exit with
  | returned reply after =>
      obtain ⟨outcome, forwarded⟩ :=
        (forwardGetter_hasOutcome_iff config (.returned reply after)).2 (ready reply after read)
      exact ⟨outcome, forwarded, .returned reply after, read, forwarded⟩
  | unwound reason after =>
      exact ⟨.unwound reason after, rfl, .unwound reason after, read, rfl⟩
  | terminated reason =>
      exact ⟨.terminated reason, rfl, .terminated reason, read, rfl⟩

/-- With initialization admission, local forwarding neither loses a finite
provider exit nor invents one. Provider termination is not assumed. -/
theorem get_hasOutcome_iff {Value : Type} (config : GetterConfig Value)
    (index : GetterIndex Value) (before : index.State)
    (ready : GetterReady config index before) :
    (∃ outcome, get config index before () outcome) ↔
      ∃ exit, index.read before (index.target, config.request) exit := by
  constructor
  · rintro ⟨_, exit, read, _⟩
    exact ⟨exit, read⟩
  · rintro ⟨exit, read⟩
    obtain ⟨outcome, _, execution⟩ := get_retains config index before ready exit read
    exact ⟨outcome, execution⟩

def getterFamily {Value : Type} (config : GetterConfig Value) : Family where
  Index := GetterIndex Value
  State := GetterIndex.State
  Args := fun _ => Unit
  Value := fun _ => Except ProgramError.Value Value
  Unwind := GetterIndex.Unwind
  Terminal := GetterIndex.Terminal
  contract := fun index => {
    requires := fun before _ => GetterReady config index before
    post := get config index
  }

def getterRun {Value : Type} (config : GetterConfig Value) : FamilyRun (getterFamily config) :=
  fun index => get config index

theorem getter_reference {Value : Type} (config : GetterConfig Value) :
    FamilyReference (getterFamily config) (getterRun config) := by
  intro index before args outcome _ step
  exact step

theorem get_success_valid {Value : Type} (config : GetterConfig Value)
    (index : GetterIndex Value) (before after : index.State) (value : Value)
    (valid : GetterValid config index before)
    (step : get config index before () (.returned (.ok value) after)) : config.valid value := by
  obtain ⟨exit, read, forwarded⟩ := step
  cases exit with
  | returned reply state =>
    unfold forwardGetter at forwarded
    cases status : config.error reply.status with
    | some error => simp only [status] at forwarded; cases forwarded
    | none =>
      simp only [status] at forwarded
      obtain ⟨actual, destination, equal⟩ := forwarded
      cases equal
      exact valid reply after value read status destination
  | unwound reason state => cases forwarded
  | terminated reason => cases forwarded

/-- A concrete inhabited backend used solely for closed model consistency
witnesses. It does not assert that a runtime always succeeds. -/
def getterSample {Value : Type} (value : Value) : GetterIndex Value where
  State := Unit
  Unwind := Empty
  Terminal := Empty
  target := .solana
  read := Callback.ofFunction fun before _ => .returned ⟨0, some value⟩ before

/-- The concrete sample initializes its actual destination independently of
the status converter and the separate value-validity predicate. -/
theorem getterSample_ready {Value : Type} (config : GetterConfig Value) (value : Value)
    (before : Unit) : GetterReady config (getterSample value) before := by
  intro reply after read _
  cases read
  exact ⟨value, rfl⟩

theorem getterSample_hasExecution {Value : Type} (config : GetterConfig Value) (value : Value) :
    FamilyHasExecution (getterFamily config) (getterRun config) (getterSample value) := by
  have ready := getterSample_ready config value ()
  obtain ⟨outcome, execution⟩ := (get_hasOutcome_iff config (getterSample value) () ready).2
    ⟨.returned ⟨0, some value⟩ (), rfl⟩
  exact ⟨(), (), outcome, ready, execution⟩

def pinClockConfig : GetterConfig Clock where
  request := ⟨.generic Solanalib.Runtime.Ids.sysvarClock 0 40, none⟩
  valid := clockValid
  error := genericError


end Solanalib.Specs.Core.Sysvar
