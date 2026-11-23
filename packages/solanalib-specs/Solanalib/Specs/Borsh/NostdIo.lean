/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshWriteAll

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! borsh 1.6.1 `nostd_io::Write::write_all` (`src/nostd_io.rs` 545-560), the
provided method of the `Write` trait that borsh uses without its `std`
feature. The index is the `write` of the writer, the panic of `&buf[n..]` and the
allocator of the message of the `WriteZero` error. A writer that overrides
`write_all` (`&mut W`, `&mut [u8]` and `Vec<u8>` in the same file) is another
implementation and is not this model. -/

namespace Solanalib.Specs.Borsh.nostd_io.Write

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- `while !buf.is_empty() { match self.write(buf) { .. } } Ok(())`. -/
def write_all_contract : Family := writeAllFamily
/-- The reference: the runs of the loop over the index callbacks. -/
def write_all_run : FamilyRun write_all_contract := writeAllRun
/-- The contract admits exactly the reference runs. -/
theorem write_all_reference : FamilyReference write_all_contract write_all_run :=
  writeAllFamily_reference

/-- The sample writer: takes at most two bytes per call and logs them. -/
def twoAtATime : WriteFn (List Solanalib.Runtime.Bytes) Empty Empty :=
  fun log buf => .returned (.ok (min 2 buf.length)) (log ++ [buf.take 2])

/-- The closed sample: the two-byte writer and an allocator that succeeds. Its
slice panic has no exit, since the sample has no unwind or terminal reasons;
neither the panic nor the allocation is reached. -/
def write_all_sample : write_all_contract.Index :=
  ⟨List Solanalib.Runtime.Bytes, Empty, Empty, Callback.ofFunction twoAtATime, fun _ _ _ => False,
    Callback.ofFunction allocationReturns⟩

/-- The contract has no precondition: the empty log and `[1, 2, 3]` are an
admissible input of the sample. -/
theorem write_all_satisfiable : FamilySatisfiable write_all_contract write_all_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), [1, 2, 3], trivial⟩

/-- `[1, 2, 3]` is written in two calls, `[1, 2]` and `[3]`, and returns `Ok(())`. -/
theorem write_all_has_execution :
    FamilyHasExecution write_all_contract write_all_run write_all_sample :=
  ⟨([] : List Solanalib.Runtime.Bytes), [1, 2, 3], .returned (.ok ()) [[1, 2], [3]], trivial,
    .advance (n := 2) (List.cons_ne_nil _ _) rfl (by decide) (by decide)
      (.advance (n := 1) (List.cons_ne_nil _ _) rfl (by decide) (by decide) (.done _))⟩

end Solanalib.Specs.Borsh.nostd_io.Write
