/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.RawSyscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Raw SDK contracts, organized by Rust function. The catalog records reviewed
releases and build conditions for each function. Each indexed provider supplies
its actual outcomes; the canonical provider interprets these contracts through
the Agave model. Rust implementation and pointer-translation obligations remain
separate from these mathematical contracts. -/

namespace Solanalib.Specs.SolanaDefineSyscall.definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawSyscall

/-- `fn abort() -> !`: the terminal exits of the environment for `.abort`. -/
def abort_contract : Family := abortFamily
/-- The reference: the terminal exits of the environment. -/
def abort_run : FamilyRun abort_contract := abortFamilyRun
/-- `abort_run` is the reference of `abort_contract` at every environment. -/
theorem abort_reference : FamilyReference abort_contract abort_run :=
  abortFamily_reference
/-- The sample environment. -/
def abort_sample : abort_contract.Index := sample
/-- The sample environment stops the call. -/
theorem abort_has_execution : FamilyHasExecution abort_contract abort_run abort_sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), (), .terminated (), trivial, rfl⟩
/-- The precondition holds at the sample environment, by the execution witness. -/
theorem abort_satisfiable : FamilySatisfiable abort_contract abort_sample :=
  abort_has_execution.satisfiable

/-- `sol_curve_multiscalar_mul(curve_id, scalars, points, points_len, result) -> u64`:
reject a count above 512, then return the result of the provider for the paired encodings. -/
def sol_curve_multiscalar_mul_contract : Family := msmFamily

/-- The request-level reference for multiscalar multiplication. -/
def sol_curve_multiscalar_mul_run : FamilyRun sol_curve_multiscalar_mul_contract := msmFamilyRun

/-- Reference correctness covers every provider index. -/
theorem sol_curve_multiscalar_mul_reference :
    FamilyReference sol_curve_multiscalar_mul_contract sol_curve_multiscalar_mul_run :=
  msmFamily_reference

/-- The explicit consistency sample; it is not a curve arithmetic implementation. -/
def sol_curve_multiscalar_mul_sample : sol_curve_multiscalar_mul_contract.Index := msmSample

/-- A nonempty paired input produces the 32-byte result of the sample and records the exact request.
-/
theorem sol_curve_multiscalar_mul_has_execution :
    FamilyHasExecution sol_curve_multiscalar_mul_contract sol_curve_multiscalar_mul_run
      sol_curve_multiscalar_mul_sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), ⟨0, [sampleInput]⟩,
    .returned ⟨0, [List.replicate 32 0]⟩
      [.curveMultiscalarMul 0 [List.replicate 32 1] [List.replicate 32 2]], trivial, rfl⟩

/-- The registered sample has a satisfiable precondition. -/
theorem sol_curve_multiscalar_mul_satisfiable :
    FamilySatisfiable sol_curve_multiscalar_mul_contract sol_curve_multiscalar_mul_sample :=
  sol_curve_multiscalar_mul_has_execution.satisfiable

/-- `fn sol_log_(message: *const u8, len: u64)`: `()` when the environment answers
`.log message`, and its terminal exits; every message is admissible. -/
def sol_log__contract : Family := logFamily
/-- The reference: `()` for each answer, and the terminal exits of the environment. -/
def sol_log__run : FamilyRun sol_log__contract := logFamilyRun
/-- `sol_log__run` is the reference of `sol_log__contract` at every environment. -/
theorem sol_log__reference : FamilyReference sol_log__contract sol_log__run :=
  logFamily_reference
/-- The sample environment. -/
def sol_log__sample : sol_log__contract.Index := sample
/-- `"hi"` is logged and the call returns. -/
theorem sol_log__has_execution :
    FamilyHasExecution sol_log__contract sol_log__run sol_log__sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), [104, 105], .returned () [.log [104, 105]],
    trivial, .returned .ok0 [.log [104, 105]], rfl, rfl⟩
/-- The precondition holds at the sample environment, by the execution witness. -/
theorem sol_log__satisfiable : FamilySatisfiable sol_log__contract sol_log__sample :=
  sol_log__has_execution.satisfiable

/-- `fn sol_panic_(filename: *const u8, filename_len: u64, line: u64, column: u64) -> !`: the
terminal exits of the environment for `.panic file line column`. -/
def sol_panic__contract : Family := panicFamily
/-- The reference: the terminal exits of the environment. -/
def sol_panic__run : FamilyRun sol_panic__contract := panicFamilyRun
/-- `sol_panic__run` is the reference of `sol_panic__contract` at every environment. -/
theorem sol_panic__reference : FamilyReference sol_panic__contract sol_panic__run :=
  panicFamily_reference
/-- The sample environment. -/
def sol_panic__sample : sol_panic__contract.Index := sample
/-- The sample environment stops the call. -/
theorem sol_panic__has_execution :
    FamilyHasExecution sol_panic__contract sol_panic__run sol_panic__sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), ⟨[109], 1, 2⟩, .terminated (), trivial, rfl⟩
/-- The precondition holds at the sample environment, by the execution witness. -/
theorem sol_panic__satisfiable : FamilySatisfiable sol_panic__contract sol_panic__sample :=
  sol_panic__has_execution.satisfiable

/-- `fn sol_sha256(vals: *const u8, val_len: u64, hash_result: *mut u8) -> u64`: the answer to
`.hash .sha256 slices`, of the hash shape by the law of the index; a call with more slices than
the limit of the index, or, where the index checks alignment, a call with a slice and an
unaligned `vals`, stops as `abort` does. -/
def sol_sha256_contract : Family := sha256Family
/-- The reference: the outcomes of the environment for the hash request, or for `.abort` on a call
with too many slices or an unaligned one. -/
def sol_sha256_run : FamilyRun sol_sha256_contract := sha256FamilyRun
/-- `sol_sha256_run` is the reference of `sol_sha256_contract` at every environment. -/
theorem sol_sha256_reference : FamilyReference sol_sha256_contract sol_sha256_run :=
  sha256Family_reference
/-- The sample environment. -/
def sol_sha256_sample : sol_sha256_contract.Index := sample
/-- Two slices at an aligned `vals` are hashed: status `0` and the 32 bytes of the sample, with the
request logged. -/
theorem sol_sha256_has_execution :
    FamilyHasExecution sol_sha256_contract sol_sha256_run sol_sha256_sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), ⟨[[1, 2], [3]], true⟩,
    .returned ⟨0, [List.replicate 32 0]⟩ [.hash .sha256 [[1, 2], [3]]], trivial, rfl⟩
/-- The precondition holds at the sample environment, by the execution witness. -/
theorem sol_sha256_satisfiable : FamilySatisfiable sol_sha256_contract sol_sha256_sample :=
  sol_sha256_has_execution.satisfiable

/-- `sol_sha512(vals, val_len, hash_result) -> u64`: check the slice count and alignment, then
return the answer of the provider, with one 64-byte output on success and no output on failure. -/
def sol_sha512_contract : Family := sha512Family

/-- The request-level reference for SHA-512. -/
def sol_sha512_run : FamilyRun sol_sha512_contract := sha512FamilyRun

/-- Reference correctness covers every provider index. -/
theorem sol_sha512_reference : FamilyReference sol_sha512_contract sol_sha512_run :=
  sha512Family_reference

/-- The explicit consistency sample; it is not a hash implementation. -/
def sol_sha512_sample : sol_sha512_contract.Index := sha512Sample

/-- Two nonempty slices produce the 64-byte result of the sample and record the actual request. -/
theorem sol_sha512_has_execution :
    FamilyHasExecution sol_sha512_contract sol_sha512_run sol_sha512_sample :=
  ⟨([] : List Solanalib.Runtime.SysReq), ⟨[[1, 2], [3]], true⟩,
    .returned ⟨0, [List.replicate 64 0]⟩ [.hash .sha512 [[1, 2], [3]]], trivial, rfl⟩

/-- The registered sample has a satisfiable precondition. -/
theorem sol_sha512_satisfiable : FamilySatisfiable sol_sha512_contract sol_sha512_sample :=
  sol_sha512_has_execution.satisfiable

end Solanalib.Specs.SolanaDefineSyscall.definitions
