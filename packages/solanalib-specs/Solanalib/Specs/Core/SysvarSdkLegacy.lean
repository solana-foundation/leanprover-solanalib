/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar.Legacy

/-- The three reviewed error tables differ on exact high-word builtin tags.
Unknown words always retain the low u32 as Custom, including truncated zero. -/
inductive ErrorTable where
  | program115
  | program118
  | split222
  deriving DecidableEq, Repr

def ErrorTable.lastTag : ErrorTable → Nat
  | .program115 => 21
  | .program118 => 24
  | .split222 => 26

/-- Older SDK errors carry a string in the Borsh variant. Its exact constant
payload is retained instead of being identified with the newer unit variant.
`plain .borshIoError` is never produced by the decoder. -/
inductive Error where
  | plain (value : ProgramError.Value)
  | borshIoError (message : String)
  deriving DecidableEq, Repr

def statusCode (table : ErrorTable) (status : UInt64) : ProgramError.Value :=
  if status.toNat / 2^32 ≤ table.lastTag then ProgramError.V3_0_1.fromStatus status
  else .custom (UInt32.ofNat status.toNat)

def errorValue : ProgramError.Value → Error
  | .borshIoError => .borshIoError "Unknown"
  | other => .plain other

def fromStatus (table : ErrorTable) (status : UInt64) : Error :=
  errorValue (statusCode table status)

def config {Value : Type} (table : ErrorTable) (request : ReadRequest Value) :
    GetterConfig Value where
  request := request
  valid := fun _ => True
  error := fun status => if status = 0 then none else some (statusCode table status)

/-- A returned old ProgramError owns its String buffer. The value-only `Error`
above remains a separate observation; it is not a resource representation. -/
inductive OwnedError (StringResource : Type) where
  | plain (value : ProgramError.Value)
  | borshIoError (resource : StringResource)
  deriving DecidableEq, Repr

structure Index (Value : Type) where
  getter : GetterIndex Value
  StringResource : Type
  currentString : getter.State → StringResource → Option String
  copyLiteral : Callback.Run getter.State String StringResource getter.Unwind getter.Terminal

/-- Inspect the live owned String in the actual final provider world. -/
def observeError {Value : Type} (index : Index Value) (state : index.getter.State) :
    OwnedError index.StringResource → Option Error
  | .plain value => some (.plain value)
  | .borshIoError resource => Error.borshIoError <$> index.currentString state resource

/-- The allocation is reached only after the typed syscall returned the exact
Borsh tag. Every other value conversion is pure; abnormal read exits bypass it. -/
def next {Value : Type} (index : Index Value) : Except ProgramError.Value Value →
    index.getter.State → Outcome index.getter.State (Except (OwnedError index.StringResource) Value)
      index.getter.Unwind index.getter.Terminal → Prop
  | .ok value, before, outcome => outcome = .returned (.ok value) before
  | .error .borshIoError, before, outcome =>
    Callback.map (fun resource => Except.error (OwnedError.borshIoError resource))
      index.copyLiteral before "Unknown" outcome
  | .error error, before, outcome => outcome = .returned (.error (.plain error)) before

def run {Value : Type} (table : ErrorTable) (request : ReadRequest Value)
    (index : Index Value) : Callback.Run index.getter.State Unit
      (Except (OwnedError index.StringResource) Value) index.getter.Unwind index.getter.Terminal :=
  Callback.bind (get (config table request) index.getter) (next index)

/-- Fresh initialized output storage is required only for actually reached
literal-copy returns. This is independent of successful sysvar initialization,
and neither assumes the copy returns nor constrains its abnormal exits. -/
def StringReady {Value : Type} (table : ErrorTable) (request : ReadRequest Value)
    (index : Index Value) (before : index.getter.State) : Prop :=
  ∀ afterRead, get (config table request) index.getter before ()
      (.returned (.error .borshIoError) afterRead) →
    ∀ resource afterCopy, index.copyLiteral afterRead "Unknown" (.returned resource afterCopy) →
      index.currentString afterRead resource = none ∧
        index.currentString afterCopy resource = some "Unknown"

/-- Every returned owned Borsh error identifies its reached post-read allocation
world, fresh buffer, and exact current literal. This does not claim the buffer
already existed at the after-state of the syscall. -/
def ownedPost {Value : Type} (table : ErrorTable) (request : ReadRequest Value)
    (index : Index Value) (before : index.getter.State) :
    Outcome index.getter.State (Except (OwnedError index.StringResource) Value)
      index.getter.Unwind index.getter.Terminal → Prop
  | .returned (.error (.borshIoError resource)) after =>
    ∃ afterRead, get (config table request) index.getter before ()
        (.returned (.error .borshIoError) afterRead) ∧
      index.currentString afterRead resource = none ∧ index.currentString after resource = some
        "Unknown"
  | _ => True

theorem allocated_returned_iff {Value : Type} (table : ErrorTable) (request : ReadRequest Value)
    (index : Index Value) (before after : index.getter.State) (resource : index.StringResource) :
    run table request index before () (.returned (.error (.borshIoError resource)) after) ↔
      ∃ afterRead, get (config table request) index.getter before ()
          (.returned (.error .borshIoError) afterRead) ∧
        index.copyLiteral afterRead "Unknown" (.returned resource after) := by
  constructor
  · rintro ⟨pending, called, continued⟩
    cases pending with
    | unwound reason state => cases continued
    | terminated reason => cases continued
    | returned result state =>
      cases result with
      | ok value => cases continued
      | error error =>
        cases error <;> try { cases continued }
        obtain ⟨allocation, copied, equal⟩ := continued
        cases allocation with
        | unwound reason final => cases equal
        | terminated reason => cases equal
        | returned actual final =>
          cases equal
          exact ⟨state, called, copied⟩
  · rintro ⟨afterRead, read, copied⟩
    exact ⟨.returned (.error .borshIoError) afterRead, read,
      .returned resource after, copied, rfl⟩

/-- The complete copy exit (including an abrupt exit) is retained after the
actual read that reached it. No allocation outcome is selected away. -/
theorem allocation_exit_retained {Value : Type} (table : ErrorTable) (request : ReadRequest Value)
    (index : Index Value) (before afterRead : index.getter.State)
    (read : get (config table request) index.getter before () (.returned (.error .borshIoError)
      afterRead))
    (exit : Outcome index.getter.State index.StringResource index.getter.Unwind
      index.getter.Terminal)
    (copied : index.copyLiteral afterRead "Unknown" exit) :
    run table request index before ()
      (Outcome.map (fun resource => Except.error (OwnedError.borshIoError resource)) exit) :=
  ⟨.returned (.error .borshIoError) afterRead, read, exit, copied, rfl⟩

/-- Initialization admission retains each finite read exit. The only additional
continuation requirement is an actual finite copy exit when that read returned
the Borsh tag. No copy termination assumption is made for other paths. -/
theorem read_exit_retained {Value : Type} (table : ErrorTable) (request : ReadRequest Value)
    (index : Index Value) (before : index.getter.State)
    (ready : GetterReady (config table request) index.getter before)
    (exit : Outcome index.getter.State (ReadReply Value) index.getter.Unwind index.getter.Terminal)
    (supplied : index.getter.read before (index.getter.target, request) exit)
    (copyExit : match exit with
      | .returned reply after => (config table request).error reply.status = some .borshIoError →
          ∃ copied, index.copyLiteral after "Unknown" copied
      | _ => True) :
    ∃ outcome, run table request index before () outcome := by
  obtain ⟨pending, forwarded, called⟩ :=
    get_retains (config table request) index.getter before ready exit supplied
  cases exit with
  | unwound reason after =>
    cases forwarded
    exact ⟨.unwound reason after, .unwound reason after, called, rfl⟩
  | terminated reason =>
    cases forwarded
    exact ⟨.terminated reason, .terminated reason, called, rfl⟩
  | returned reply after =>
    simp only [forwardGetter] at forwarded
    dsimp only at copyExit
    cases converted : (config table request).error reply.status with
    | none =>
      rw [converted] at forwarded
      obtain ⟨value, _, equal⟩ := forwarded
      cases equal
      exact ⟨.returned (.ok value) after, .returned (.ok value) after, called, rfl⟩
    | some error =>
      rw [converted] at forwarded
      cases forwarded
      cases error <;> try exact
        ⟨.returned (.error (.plain _)) after, .returned (.error _) after, called, rfl⟩
      obtain ⟨copied, allocation⟩ := copyExit converted
      exact ⟨_, allocation_exit_retained table request index before after called copied allocation⟩

def family {Value : Type} (table : ErrorTable) (request : ReadRequest Value) : Family where
  Index := Index Value
  State := fun index => index.getter.State
  Args := fun _ => Unit
  Value := fun index => Except (OwnedError index.StringResource) Value
  Unwind := fun index => index.getter.Unwind
  Terminal := fun index => index.getter.Terminal
  contract := fun index => {
    requires := fun before _ => GetterReady (config table request) index.getter before ∧
      StringReady table request index before
    post := fun before args outcome => run table request index before args outcome ∧
      ownedPost table request index before outcome
  }

def reference {Value : Type} (table : ErrorTable) (request : ReadRequest Value) :
    FamilyRun (family table request) := run table request

theorem reference_correct {Value : Type} (table : ErrorTable) (request : ReadRequest Value) :
    FamilyReference (family table request) (reference table request) := by
  intro index before args outcome ready called
  refine ⟨called, ?_⟩
  cases args
  cases outcome with
  | unwound reason after => trivial
  | terminated reason => trivial
  | returned result after =>
    cases result with
    | ok value => trivial
    | error error =>
      cases error with
      | plain value => trivial
      | borshIoError resource =>
        obtain ⟨afterRead, read, copied⟩ :=
          (allocated_returned_iff table request index before after resource).mp called
        exact ⟨afterRead, read, ready.2 afterRead read resource after copied⟩

/-- The closed witness takes the nonempty owned-error path. The model ledger
records a real new String handle rather than an erased payload. -/
def sample {Value : Type} (value : Value) : Index Value where
  getter := {
    State := List String
    Unwind := Empty
    Terminal := Empty
    target := .solana
    read := Callback.ofFunction fun before _ => .returned ⟨UInt64.ofNat (15 * 2^32), some value⟩
      before
  }
  StringResource := Nat
  currentString := fun before resource => before[resource]?
  copyLiteral := Callback.ofFunction fun before literal => .returned before.length (before ++
    [literal])

theorem sample_hasExecution {Value : Type} (table : ErrorTable)
    (request : ReadRequest Value) (value : Value) :
    FamilyHasExecution (family table request) (reference table request) (sample value) := by
  have code : (config table request).error (UInt64.ofNat (15 * 2^32)) = some .borshIoError := by
    dsimp only [config]
    cases table <;> decide
  have read : get (config table request) (sample value).getter [] ()
      (.returned (.error .borshIoError) []) :=
    ⟨.returned ⟨UInt64.ofNat (15 * 2^32), some value⟩ [], rfl, by simp only [forwardGetter, code]⟩
  refine ⟨[], (), .returned (.error (.borshIoError (0 : Nat))) ["Unknown"], ⟨?_, ?_⟩, ?_⟩
  · intro reply after called _
    cases called
    exact ⟨value, rfl⟩
  · intro afterRead reached resource afterCopy copied
    obtain ⟨exit, supplied, forwarded⟩ := reached
    cases supplied
    simp only [forwardGetter, code] at forwarded
    cases forwarded
    cases copied
    exact ⟨rfl, rfl⟩
  · exact (allocated_returned_iff table request (sample value) [] ["Unknown"] (0 : Nat)).mpr
      ⟨[], read, rfl⟩

end Solanalib.Specs.Core.Sysvar.Legacy
