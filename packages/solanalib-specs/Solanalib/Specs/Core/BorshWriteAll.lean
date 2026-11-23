/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! `Write::write_all`, the provided method of the no-std `Write` trait of borsh
(`src/nostd_io.rs` 545-560 in borsh 1.6.1):

```rust
fn write_all(&mut self, mut buf: &[u8]) -> Result<()> {
    while !buf.is_empty() {
        match self.write(buf) {
            Ok(0) => {
                return Err(Error::new(ErrorKind::WriteZero, "failed to write whole buffer"));
            }
            Ok(n) => buf = &buf[n..],
            Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}
```

The `write` of the writer is a callback. So are the panic of `&buf[n..]` when
`write` reports more bytes than it was offered, whose exits depend on the
panic strategy, and the `String` allocation of the message of `Error::new` on
`Ok(0)`, whose exits depend on the allocator of the program. `WriteAllRuns` is
inductive because an `Interrupted` error retries the same buffer without
bound; a writer that is interrupted forever has no finite outcome. -/

namespace Solanalib.Specs.Core.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core

namespace ErrorKind

/-- `ErrorKind::Interrupted`: `write_all` retries the same buffer. -/
def interrupted : ErrorKind := ⟨"Interrupted"⟩
/-- `ErrorKind::WriteZero`: the kind of the error from `write_all` on `Ok(0)`. -/
def writeZero : ErrorKind := ⟨"WriteZero"⟩

end ErrorKind

/-- `Error::new(ErrorKind::WriteZero, "failed to write whole buffer")`, as its
kind and message. Its `String` allocation is the `allocate` callback of the index. -/
def writeZeroError : IoError := ⟨.writeZero, "failed to write whole buffer"⟩

/-- The `W::write` of the writer as a callback: the bytes offered, and the count it
reports or its error. Its partial effects, unwind state and terminal reason
remain those of the writer. -/
abbrev WriteCallback (State Unwind Terminal : Type) :=
  Callback.Run State Solanalib.Runtime.Bytes (Except IoError Nat) Unwind Terminal

/-- The `write` of the writer as a function, for executable callbacks. -/
abbrev WriteFn (State Unwind Terminal : Type) :=
  State → Solanalib.Runtime.Bytes → Outcome State (Except IoError Nat) Unwind Terminal

/-- The panics that `write_all` raises itself. -/
inductive WriteAllPanic where
  /-- `&buf[n..]` with `n > buf.len()`: the core operation
  `slice_start_index_len_fail(n, buf.len())`. -/
  | sliceStartIndexLenFail (index length : Nat)
  deriving DecidableEq, Repr

/-- A panic as a callback. It never returns; whether it unwinds or terminates
is the choice of the panic strategy. -/
abbrev PanicCallback (State Unwind Terminal : Type) :=
  Callback.Run State WriteAllPanic Empty Unwind Terminal

/-- The slice panic as a function, for executable callbacks. -/
abbrev PanicFn (State Unwind Terminal : Type) :=
  State → WriteAllPanic → Outcome State Empty Unwind Terminal

/-- The allocation that `write_all` makes itself. -/
inductive WriteAllAllocation where
  /-- `String::from(message)` in `Error::new(kind, message)`: a heap buffer for
  the `message.utf8ByteSize` bytes of the message, with alignment 1. -/
  | errorMessage (message : String)
  deriving DecidableEq, Repr

/-- The allocator of the program at the allocation of `write_all`, as a callback. A
return continues in the state after it; whether a failure unwinds or
terminates is determined by the allocator and the panic strategy. -/
abbrev WriteAllAllocate (State Unwind Terminal : Type) :=
  Callback.Run State WriteAllAllocation Unit Unwind Terminal

/-- The allocator as a function, for executable callbacks. -/
abbrev WriteAllAllocateFn (State Unwind Terminal : Type) :=
  State → WriteAllAllocation → Outcome State Unit Unwind Terminal

/-- The allocator that always succeeds and keeps the state. -/
def allocationReturns {State Unwind Terminal : Type} : WriteAllAllocateFn State Unwind Terminal :=
  fun before _ => .returned () before

/-- The writer `W` of `write_all`, by its `write`, and the panic of the slice
index and the allocator in the program using `W`. -/
structure WriteAllIndex where
  State : Type
  Unwind : Type
  Terminal : Type
  write : WriteCallback State Unwind Terminal
  panic : PanicCallback State Unwind Terminal
  allocate : WriteAllAllocate State Unwind Terminal

/-- The finite runs of the loop of `write_all`, with every callback exit retained. -/
inductive WriteAllRuns {State Unwind Terminal : Type}
    (write : WriteCallback State Unwind Terminal) (panic : PanicCallback State Unwind Terminal)
    (allocate : WriteAllAllocate State Unwind Terminal) :
    State → Solanalib.Runtime.Bytes → Outcome State (Except IoError Unit) Unwind Terminal → Prop
      where
  /-- An empty buffer: `Ok(())`, without a call of `write`. -/
  | done (before : State) : WriteAllRuns write panic allocate before [] (.returned (.ok ()) before)
  /-- `Ok(n)` with `0 < n ≤ buf.len()`: continue on `&buf[n..]`. -/
  | advance {before mid : State} {buf : Solanalib.Runtime.Bytes} {n : Nat}
      {outcome : Outcome State (Except IoError Unit) Unwind Terminal}
      (nonempty : buf ≠ []) (step : write before buf (.returned (.ok n) mid))
      (positive : 0 < n) (within : n ≤ buf.length)
      (rest : WriteAllRuns write panic allocate mid (buf.drop n) outcome) :
      WriteAllRuns write panic allocate before buf outcome
  /-- `Ok(0)`: `Error::new` allocates the message of the `WriteZero` error in
  the state `write` left. A return of the allocation gives that error in the
  state after it; every other exit of the allocation is forwarded. -/
  | writeZero {before mid : State} {buf : Solanalib.Runtime.Bytes}
      {outcome : Outcome State (Except IoError Unit) Unwind Terminal}
      (nonempty : buf ≠ []) (step : write before buf (.returned (.ok 0) mid))
      (allocated : Callback.map (fun _ => .error writeZeroError) allocate mid
        (.errorMessage writeZeroError.message) outcome) :
      WriteAllRuns write panic allocate before buf outcome
  /-- `Ok(n)` with `n > buf.len()`: `&buf[n..]` panics, and every exit of the
  panic is forwarded. -/
  | overrun {before mid : State} {buf : Solanalib.Runtime.Bytes} {n : Nat}
      {outcome : Outcome State (Except IoError Unit) Unwind Terminal}
      (nonempty : buf ≠ []) (step : write before buf (.returned (.ok n) mid))
      (over : buf.length < n)
      (panicked : Callback.map Empty.elim panic mid (.sliceStartIndexLenFail n buf.length)
        outcome) :
      WriteAllRuns write panic allocate before buf outcome
  /-- An `Interrupted` error: retry the same buffer. -/
  | interrupted {before mid : State} {buf : Solanalib.Runtime.Bytes} {error : IoError}
      {outcome : Outcome State (Except IoError Unit) Unwind Terminal}
      (nonempty : buf ≠ []) (step : write before buf (.returned (.error error) mid))
      (kind : error.kind = .interrupted)
      (rest : WriteAllRuns write panic allocate mid buf outcome) :
      WriteAllRuns write panic allocate before buf outcome
  /-- Any other error is returned unchanged. -/
  | failed {before after : State} {buf : Solanalib.Runtime.Bytes} {error : IoError}
      (nonempty : buf ≠ []) (step : write before buf (.returned (.error error) after))
      (kind : error.kind ≠ .interrupted) :
      WriteAllRuns write panic allocate before buf (.returned (.error error) after)
  /-- An unwind of `write` is forwarded. -/
  | unwound {before after : State} {buf : Solanalib.Runtime.Bytes} {reason : Unwind}
      (nonempty : buf ≠ []) (step : write before buf (.unwound reason after)) :
      WriteAllRuns write panic allocate before buf (.unwound reason after)
  /-- A terminal exit of `write` is forwarded. -/
  | terminated {before : State} {buf : Solanalib.Runtime.Bytes} {reason : Terminal}
      (nonempty : buf ≠ []) (step : write before buf (.terminated reason)) :
      WriteAllRuns write panic allocate before buf (.terminated reason)

/-! ## The family -/

/-- The reference of the family: the runs of the loop over the index callbacks. -/
def writeAllRun (index : WriteAllIndex) :
    index.State → Solanalib.Runtime.Bytes →
      Outcome index.State (Except IoError Unit) index.Unwind index.Terminal → Prop :=
  WriteAllRuns index.write index.panic index.allocate

/-- `write_all` at every writer: no precondition, and exactly the runs of its
loop over the index callbacks. -/
def writeAllFamily : Family where
  Index := WriteAllIndex
  State := WriteAllIndex.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun _ => Except IoError Unit
  Unwind := WriteAllIndex.Unwind
  Terminal := WriteAllIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := WriteAllRuns index.write index.panic index.allocate }

/-- The contract admits exactly the reference runs. -/
theorem writeAllFamily_reference : FamilyReference writeAllFamily writeAllRun :=
  fun _ _ _ _ _ step => step

/-! ## Execution -/

/-- `write_all` at function callbacks, with at most `fuel` calls of `write`;
`none` when the fuel runs out. -/
def writeAllFuel {State Unwind Terminal : Type} (write : WriteFn State Unwind Terminal)
    (panic : PanicFn State Unwind Terminal) (allocate : WriteAllAllocateFn State Unwind Terminal) :
    Nat → State → Solanalib.Runtime.Bytes → Option (Outcome State (Except IoError Unit) Unwind
      Terminal)
  | _, before, [] => some (.returned (.ok ()) before)
  | 0, _, _ :: _ => none
  | fuel + 1, before, byte :: rest =>
    match write before (byte :: rest) with
    | .returned (.ok n) mid =>
      if n = 0 then some (Outcome.map (fun _ => .error writeZeroError)
        (allocate mid (.errorMessage writeZeroError.message)))
      else if n ≤ (byte :: rest).length then
        writeAllFuel write panic allocate fuel mid ((byte :: rest).drop n)
      else some (Outcome.map Empty.elim
        (panic mid (.sliceStartIndexLenFail n (byte :: rest).length)))
    | .returned (.error error) mid =>
      if error.kind = .interrupted then writeAllFuel write panic allocate fuel mid (byte :: rest)
      else some (.returned (.error error) mid)
    | .unwound reason after => some (.unwound reason after)
    | .terminated reason => some (.terminated reason)

/-- An empty buffer returns `Ok(())` at every fuel, without a call of `write`. -/
@[simp] theorem writeAllFuel_nil {State Unwind Terminal : Type}
    (write : WriteFn State Unwind Terminal) (panic : PanicFn State Unwind Terminal)
    (allocate : WriteAllAllocateFn State Unwind Terminal) (fuel : Nat) (before : State) :
    writeAllFuel write panic allocate fuel before [] = some (.returned (.ok ()) before) := by
  cases fuel <;> rfl

/-- Two runs with enough fuel agree. -/
theorem writeAllFuel_deterministic {State Unwind Terminal : Type}
    {write : WriteFn State Unwind Terminal} {panic : PanicFn State Unwind Terminal}
    {allocate : WriteAllAllocateFn State Unwind Terminal}
    {fuel fuel' : Nat} {before : State} {buf : Solanalib.Runtime.Bytes}
    {outcome outcome' : Outcome State (Except IoError Unit) Unwind Terminal}
    (first : writeAllFuel write panic allocate fuel before buf = some outcome)
    (second : writeAllFuel write panic allocate fuel' before buf = some outcome') :
    outcome = outcome' := by
  induction fuel generalizing fuel' before buf with
  | zero =>
    cases buf with
    | nil =>
      rw [writeAllFuel_nil] at first second
      exact (Option.some.inj first).symm.trans (Option.some.inj second)
    | cons => simp [writeAllFuel] at first
  | succ fuel ih =>
    cases buf with
    | nil =>
      rw [writeAllFuel_nil] at first second
      exact (Option.some.inj first).symm.trans (Option.some.inj second)
    | cons byte rest =>
      cases fuel' with
      | zero => simp [writeAllFuel] at second
      | succ fuel' =>
        simp only [writeAllFuel] at first second
        cases call : write before (byte :: rest) with
        | returned value mid =>
          rw [call] at first second
          cases value with
          | ok n =>
            dsimp only at first second
            by_cases zero : n = 0
            · rw [ite_eq_left zero] at first second
              exact (Option.some.inj first).symm.trans (Option.some.inj second)
            rw [ite_eq_right zero] at first second
            by_cases within : n ≤ (byte :: rest).length
            · rw [ite_eq_left within] at first second
              exact ih first second
            · rw [ite_eq_right within] at first second
              exact (Option.some.inj first).symm.trans (Option.some.inj second)
          | error error =>
            dsimp only at first second
            by_cases kind : error.kind = .interrupted
            · rw [ite_eq_left kind] at first second
              exact ih first second
            · rw [ite_eq_right kind] at first second
              exact (Option.some.inj first).symm.trans (Option.some.inj second)
        | unwound reason after =>
          rw [call] at first second
          exact (Option.some.inj first).symm.trans (Option.some.inj second)
        | terminated reason =>
          rw [call] at first second
          exact (Option.some.inj first).symm.trans (Option.some.inj second)

/-- At function callbacks, the runs of `write_all` are the outcomes of its
executable form with some fuel. -/
theorem writeAllRuns_ofFunction_iff {State Unwind Terminal : Type}
    (write : WriteFn State Unwind Terminal) (panic : PanicFn State Unwind Terminal)
    (allocate : WriteAllAllocateFn State Unwind Terminal)
    (before : State) (buf : Solanalib.Runtime.Bytes)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    WriteAllRuns (Callback.ofFunction write) (Callback.ofFunction panic)
        (Callback.ofFunction allocate) before buf outcome ↔
      ∃ fuel, writeAllFuel write panic allocate fuel before buf = some outcome := by
  constructor
  · intro runs
    induction runs with
    | done before => exact ⟨0, rfl⟩
    | @advance before mid buf n outcome nonempty step positive within _ ih =>
      obtain ⟨fuel, run⟩ := ih
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨fuel + 1, ?_⟩
        change write before (byte :: rest) = .returned (.ok n) mid at step
        simp only [writeAllFuel, step]
        rw [ite_eq_right (Nat.pos_iff_ne_zero.mp positive), ite_eq_left within]
        exact run
    | @writeZero before mid buf outcome nonempty step allocated =>
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨1, ?_⟩
        change write before (byte :: rest) = .returned (.ok 0) mid at step
        obtain ⟨exit, called, mapped⟩ := allocated
        change allocate mid _ = exit at called
        simp only [writeAllFuel, step]
        rw [ite_eq_left trivial, called, mapped]
    | @overrun before mid buf n outcome nonempty step over panicked =>
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨1, ?_⟩
        change write before (byte :: rest) = .returned (.ok n) mid at step
        obtain ⟨exit, called, mapped⟩ := panicked
        change panic mid _ = exit at called
        simp only [writeAllFuel, step]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), called, mapped]
    | @interrupted before mid buf error outcome nonempty step kind _ ih =>
      obtain ⟨fuel, run⟩ := ih
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨fuel + 1, ?_⟩
        change write before (byte :: rest) = .returned (.error error) mid at step
        simp only [writeAllFuel, step]
        rw [ite_eq_left kind]
        exact run
    | @failed before after buf error nonempty step kind =>
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨1, ?_⟩
        change write before (byte :: rest) = .returned (.error error) after at step
        simp only [writeAllFuel, step]
        rw [ite_eq_right kind]
    | @unwound before after buf reason nonempty step =>
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨1, ?_⟩
        change write before (byte :: rest) = .unwound reason after at step
        simp only [writeAllFuel, step]
    | @terminated before buf reason nonempty step =>
      cases buf with
      | nil => exact absurd rfl nonempty
      | cons byte rest =>
        refine ⟨1, ?_⟩
        change write before (byte :: rest) = .terminated reason at step
        simp only [writeAllFuel, step]
  · rintro ⟨fuel, run⟩
    induction fuel generalizing before buf outcome with
    | zero =>
      cases buf with
      | nil =>
        rw [writeAllFuel_nil] at run
        cases run
        exact .done before
      | cons => simp [writeAllFuel] at run
    | succ fuel ih =>
      cases buf with
      | nil =>
        rw [writeAllFuel_nil] at run
        cases run
        exact .done before
      | cons byte rest =>
        have nonempty : byte :: rest ≠ [] := List.cons_ne_nil byte rest
        simp only [writeAllFuel] at run
        cases call : write before (byte :: rest) with
        | returned value mid =>
          rw [call] at run
          cases value with
          | ok n =>
            dsimp only at run
            by_cases zero : n = 0
            · subst zero
              rw [ite_eq_left rfl] at run
              cases run
              exact .writeZero nonempty call ⟨_, rfl, rfl⟩
            rw [ite_eq_right zero] at run
            by_cases within : n ≤ (byte :: rest).length
            · rw [ite_eq_left within] at run
              exact .advance nonempty call (Nat.pos_of_ne_zero zero) within (ih _ _ _ run)
            · rw [ite_eq_right within] at run
              cases run
              exact .overrun nonempty call (by omega) ⟨_, rfl, rfl⟩
          | error error =>
            dsimp only at run
            by_cases kind : error.kind = .interrupted
            · rw [ite_eq_left kind] at run
              exact .interrupted nonempty call kind (ih _ _ _ run)
            · rw [ite_eq_right kind] at run
              cases run
              exact .failed nonempty call kind
        | unwound reason after =>
          rw [call] at run
          cases run
          exact .unwound nonempty call
        | terminated reason =>
          rw [call] at run
          cases run
          exact .terminated nonempty call

/-- Once the executable form returns, it decides the runs at function callbacks:
they are exactly its outcome. -/
theorem writeAllRuns_ofFunction_of_fuel {State Unwind Terminal : Type}
    {write : WriteFn State Unwind Terminal} {panic : PanicFn State Unwind Terminal}
    {allocate : WriteAllAllocateFn State Unwind Terminal}
    {fuel : Nat} {before : State} {buf : Solanalib.Runtime.Bytes}
    {computed : Outcome State (Except IoError Unit) Unwind Terminal}
    (finished : writeAllFuel write panic allocate fuel before buf = some computed)
    (outcome : Outcome State (Except IoError Unit) Unwind Terminal) :
    WriteAllRuns (Callback.ofFunction write) (Callback.ofFunction panic)
        (Callback.ofFunction allocate) before buf outcome ↔
      computed = outcome := by
  rw [writeAllRuns_ofFunction_iff]
  constructor
  · rintro ⟨fuel', run⟩
    exact writeAllFuel_deterministic finished run
  · rintro rfl
    exact ⟨fuel, finished⟩

/-- An empty buffer has exactly one run: `Ok(())` in the same state. -/
theorem writeAllRuns_nil_iff {State Unwind Terminal : Type}
    {write : WriteCallback State Unwind Terminal} {panic : PanicCallback State Unwind Terminal}
    {allocate : WriteAllAllocate State Unwind Terminal}
    {before : State} {outcome : Outcome State (Except IoError Unit) Unwind Terminal} :
    WriteAllRuns write panic allocate before [] outcome ↔
      outcome = .returned (.ok ()) before := by
  constructor
  · intro runs
    cases runs with
    | done => rfl
    | advance nonempty => exact absurd rfl nonempty
    | writeZero nonempty => exact absurd rfl nonempty
    | overrun nonempty => exact absurd rfl nonempty
    | interrupted nonempty => exact absurd rfl nonempty
    | failed nonempty => exact absurd rfl nonempty
    | unwound nonempty => exact absurd rfl nonempty
    | terminated nonempty => exact absurd rfl nonempty
  · rintro rfl
    exact .done before

/-! ## Composition -/

/-- A writer whose `write_all` is this provided method, as the writer index of
the serializers of borsh: they compose over the modeled `write_all`. -/
def WriterIndex.ofWrite (index : WriteAllIndex) : WriterIndex :=
  ⟨index.State, index.Unwind, index.Terminal, writeAllRun index⟩

end Solanalib.Specs.Core.Borsh
