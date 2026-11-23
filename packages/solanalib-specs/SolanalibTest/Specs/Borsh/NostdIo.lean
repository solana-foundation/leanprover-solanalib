/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Borsh.NostdIo
public import Solanalib.Specs.Borsh.Ser

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Borsh.NostdIo

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Borsh Solanalib.Specs.Borsh.nostd_io.Write

abbrev Log := List Solanalib.Runtime.Bytes

/-- A scripted writer: call `k` returns `script[k]`, and every later call
takes the whole buffer. It logs each buffer it is offered. -/
def scripted {Terminal : Type} (script : List (Except IoError Nat)) :
    WriteFn Log WriteAllPanic Terminal :=
  fun log buf => .returned (script.getD log.length (.ok buf.length)) (log ++ [buf])

/-- The slice panic as an unwind that carries its reason. -/
def unwinding {Terminal : Type} : PanicFn Log WriteAllPanic Terminal :=
  fun log reason => .unwound reason log

/-- The scripted writer, the unwinding slice panic and an allocator that succeeds. -/
abbrev scriptedIndex (script : List (Except IoError Nat)) : WriteAllIndex :=
  ⟨Log, WriteAllPanic, Empty, Callback.ofFunction (scripted script), Callback.ofFunction unwinding,
    Callback.ofFunction allocationReturns⟩

/-- At the scripted writer, an outcome of the executable form is the only run. -/
theorem only_run {script : List (Except IoError Nat)} {before : Log} {buf : Solanalib.Runtime.Bytes}
    {computed : Outcome Log (Except IoError Unit) WriteAllPanic Empty} (fuel : Nat)
    (finished : writeAllFuel (scripted script) unwinding allocationReturns fuel before buf =
      some computed)
    (outcome : Outcome Log (Except IoError Unit) WriteAllPanic Empty) :
    write_all_run (scriptedIndex script) before buf outcome ↔ outcome = computed :=
  (writeAllRuns_ofFunction_of_fuel finished outcome).trans eq_comm

/-- An empty buffer returns `Ok(())` without calling `write`, at every writer. -/
theorem empty_buffer_no_call (index : WriteAllIndex) (before : index.State)
    (outcome : Outcome index.State (Except IoError Unit) index.Unwind index.Terminal) :
    write_all_run index before [] outcome ↔ outcome = .returned (.ok ()) before :=
  writeAllRuns_nil_iff

/-- Partial counts continue on the rest of the buffer. -/
theorem partial_counts_continue (outcome : Outcome Log (Except IoError Unit) WriteAllPanic Empty) :
    write_all_run (scriptedIndex [.ok 2, .ok 2]) [] [1, 2, 3, 4, 5] outcome ↔
      outcome = .returned (.ok ()) [[1, 2, 3, 4, 5], [3, 4, 5], [5]] :=
  only_run 3 rfl outcome

/-- `Ok(0)` stops with `WriteZero`, after the bytes already written. -/
theorem zero_count_is_write_zero
    (outcome : Outcome Log (Except IoError Unit) WriteAllPanic Empty) :
    write_all_run (scriptedIndex [.ok 1, .ok 0]) [] [1, 2, 3] outcome ↔
      outcome = .returned (.error ⟨⟨"WriteZero"⟩, "failed to write whole buffer"⟩)
        [[1, 2, 3], [2, 3]] :=
  only_run 2 rfl outcome

/-- An allocator that fails by terminating, as the one from `no_allocator!()` does under
`panic = "abort"`. -/
def failingAllocation : WriteAllAllocateFn Log WriteAllPanic String :=
  fun _ _ => .terminated "allocation failed"

/-- On `Ok(0)`, a failure of the allocation of the message of the `WriteZero` error
is the outcome: the error is not returned. -/
theorem zero_count_allocation_failure
    (outcome : Outcome Log (Except IoError Unit) WriteAllPanic String) :
    write_all_run ⟨Log, WriteAllPanic, String, Callback.ofFunction (scripted [.ok 1, .ok 0]),
        Callback.ofFunction unwinding, Callback.ofFunction failingAllocation⟩ [] [1, 2, 3]
      outcome ↔
      outcome = .terminated "allocation failed" :=
  (writeAllRuns_ofFunction_of_fuel (fuel := 2) rfl outcome).trans eq_comm

/-- `Interrupted` retries the same buffer; its error is dropped. -/
theorem interrupted_retries_same_buffer
    (outcome : Outcome Log (Except IoError Unit) WriteAllPanic Empty) :
    write_all_run (scriptedIndex [.error ⟨⟨"Interrupted"⟩, "again"⟩, .ok 1]) [] [1, 2] outcome ↔
      outcome = .returned (.ok ()) [[1, 2], [1, 2], [2]] :=
  only_run 3 rfl outcome

/-- Any other error is returned unchanged, after the partial write. -/
theorem other_error_unchanged (outcome : Outcome Log (Except IoError Unit) WriteAllPanic Empty) :
    write_all_run (scriptedIndex [.ok 1, .error ⟨⟨"BrokenPipe"⟩, "closed"⟩]) [] [1, 2, 3]
        outcome ↔
      outcome = .returned (.error ⟨⟨"BrokenPipe"⟩, "closed"⟩) [[1, 2, 3], [2, 3]] :=
  only_run 2 rfl outcome

/-- A count above the remaining length panics in `&buf[n..]`; the exit of the panic is the outcome.
-/
theorem overrun_panics (outcome : Outcome Log (Except IoError Unit) WriteAllPanic Empty) :
    write_all_run (scriptedIndex [.ok 1, .ok 5]) [] [1, 2, 3] outcome ↔
      outcome = .unwound (.sliceStartIndexLenFail 5 2) [[1, 2, 3], [2, 3]] :=
  only_run 2 rfl outcome

/-- A writer that unwinds on its second call. -/
def unwindsSecond : WriteFn Log String Empty := fun log buf =>
  if log.length = 0 then .returned (.ok 1) (log ++ [buf]) else .unwound "writer" (log ++ [buf])

/-- An unwind of `write` is forwarded with the state of the writer. -/
theorem write_unwind_forwarded :
    write_all_run ⟨Log, String, Empty, Callback.ofFunction unwindsSecond,
        Callback.ofFunction (fun log _ => .unwound "slice" log),
        Callback.ofFunction allocationReturns⟩ [] [1, 2]
      (.unwound "writer" [[1, 2], [2]]) :=
  (writeAllRuns_ofFunction_iff _ _ _ _ _ _).2 ⟨2, rfl⟩

/-- A writer that is always interrupted. -/
def alwaysInterrupted : WriteFn Log Empty Empty := fun log buf =>
  .returned (.error ⟨⟨"Interrupted"⟩, "again"⟩) (log ++ [buf])

/-- Retrying forever is no finite outcome: such a writer admits none. -/
theorem always_interrupted_has_no_outcome (before : Log) (byte : UInt8) (rest :
  Solanalib.Runtime.Bytes)
    (outcome : Outcome Log (Except IoError Unit) Empty Empty) :
    ¬ write_all_run ⟨Log, Empty, Empty, Callback.ofFunction alwaysInterrupted, fun _ _ _ => False,
        Callback.ofFunction allocationReturns⟩ before (byte :: rest) outcome := by
  intro runs
  generalize named : byte :: rest = buf at runs
  induction runs with
  | done => exact List.cons_ne_nil _ _ named
  | advance _ step => cases step
  | writeZero _ step => cases step
  | overrun _ step => cases step
  | interrupted _ _ _ _ ih => exact ih named
  | failed _ step kind =>
    cases step
    exact kind rfl
  | unwound _ step => cases step
  | terminated _ step => cases step

/-- the `u32` serializer of borsh over the modeled `write_all`: its one chunk is
written in two calls of `write`. -/
theorem u32_over_modelled_write_all :
    u32.serialize_run (WriterIndex.ofWrite (scriptedIndex [.ok 3])) ([] : Log) (0x04030201 : UInt32)
      (.returned (.ok ()) [[1, 2, 3, 4], [4]]) :=
  (Program.runs_call _ _ _ _ _).2
    ⟨.returned (.ok ()) [[1, 2, 3, 4], [4]], (only_run 2 rfl _).2 rfl, rfl⟩

end SolanalibTest.Specs.Borsh.NostdIo
