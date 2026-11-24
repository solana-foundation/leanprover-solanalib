/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaDefineSyscall.Definitions

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Request-level controls: canonical results and terminal exits, count boundaries, empty inputs,
invalid curves and encodings, and malformed output interpretations. No crypto implementation
or Rust body is assumed proved by these mathematical tests. -/

namespace SolanalibTest.Specs.SolanaDefineSyscall.Definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawSyscall
open Solanalib.Specs.SolanaDefineSyscall.definitions

/-- A registered SHA-512 request returns the exact list-of-slices primitive result of the runtime.
-/
theorem canonical_sha512_two_slices (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
  (st : Solanalib.Runtime.InvState)
    (registered : (.hash .sha512 [[1, 2], [3]] : Solanalib.Runtime.SysReq).registered W.prof =
      true) :
    sol_sha512_run (canonicalSha512 W c) st ⟨[[1, 2], [3]], true⟩
      (.returned ⟨0, [W.prims.sha512 [[1, 2], [3]]]⟩ st) := by
  apply (canonical_sha512_returned_iff W c st st ⟨[[1, 2], [3]], true⟩ _).mpr
  exact ⟨rfl, registered, by change 2 ≤ Solanalib.Runtime.MAX_HASH_SLICES; decide, rfl, rfl⟩

/-- An empty descriptor list skips the alignment check while still producing a 64-byte digest. -/
theorem canonical_sha512_empty_unaligned (W : Solanalib.Runtime.World) (c :
  Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState)
    (registered : (.hash .sha512 [] : Solanalib.Runtime.SysReq).registered W.prof = true) :
    sol_sha512_run (canonicalSha512 W c) st ⟨[], false⟩
      (.returned ⟨0, [W.prims.sha512 []]⟩ st) ∧ (W.prims.sha512 []).length = 64 :=
  ⟨(canonical_sha512_returned_iff W c st st ⟨[], false⟩ _).mpr
    ⟨by simp [RawSyscall.Sha256Args.unaligned], registered, Nat.zero_le _, rfl, rfl⟩,
    W.prims.sha512_length _⟩

/-- Unregistered SHA-512 has a terminal execution and no ordinary return. -/
theorem canonical_sha512_unregistered (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (args : Sha512Args)
    (unregistered : (.hash .sha512 args.slices : Solanalib.Runtime.SysReq).registered W.prof =
      false) :
    sol_sha512_run (canonicalSha512 W c) st args (.terminated .ProgramFailedToComplete) ∧
      ∀ answer st', ¬ sol_sha512_run (canonicalSha512 W c) st args (.returned answer st') := by
  refine ⟨(canonical_sha512_terminated_iff W c st args _).mpr ⟨Or.inr unregistered, rfl⟩, ?_⟩
  intro answer st' returned
  have registered := ((canonical_sha512_returned_iff W c st st' args answer).mp returned).2.1
  rw [unregistered] at registered
  cases registered

/-- The release guard remains in effect even when the SHA-512 feature field is set. -/
theorem sha512_old_release_unregistered (p : Solanalib.Runtime.Profile)
    (old : p.release = .agave_3_1_12) (slices : List Solanalib.Runtime.Bytes) :
    (.hash .sha512 slices : Solanalib.Runtime.SysReq).registered p = false := by
  simp [Solanalib.Runtime.SysReq.registered, old]

/-- Nonempty descriptors at a rejected alignment cannot satisfy the returning contract. -/
theorem sha512_unaligned_no_return (index : Sha512Index) (st st' : index.State)
    (checked : index.checkAligned = true) (answer : Solanalib.Runtime.SysAns) :
    ¬ (sol_sha512_contract.contract index).post st ⟨[[1]], false⟩ (.returned answer st') := by
  apply sha512Post_rejected
  apply RawSyscall.Sha256Args.rejected_of_unaligned
  simp [RawSyscall.Sha256Args.unaligned, checked]

/-- Sixty-four bytes in two output buffers is not the single digest output of the syscall. -/
theorem split_sha512_output_rejected :
    ¬ OutputShape 64 ⟨0, [List.replicate 32 0, List.replicate 32 1]⟩ := by decide

/-- A SHA-256-sized result is not a SHA-512 result. -/
theorem short_sha512_output_rejected : ¬ OutputShape 64 ⟨0, [List.replicate 32 0]⟩ := by decide

/-- A nonzero status cannot be paired with output writes. -/
theorem failed_output_write_rejected : ¬ OutputShape 32 ⟨1, [List.replicate 32 0]⟩ := by decide

/-- A malformed encoded point cannot supply the successful-response law. -/
theorem short_msm_output_rejected : ¬ MsmShape ⟨0, []⟩ ⟨0, [List.replicate 31 0]⟩ := by
  intro shape
  exact (by decide : ¬ OutputShape 32 ⟨0, [List.replicate 31 0]⟩) shape.1

/-- A machine-sized nonzero status is insufficient: this syscall returns exactly `0` or `1`. -/
theorem unknown_msm_status_rejected : ¬ MsmShape ⟨0, []⟩ ⟨2, []⟩ := by
  intro shape
  exact (by decide : ¬ ((2 : Nat) = 0 ∨ 2 = 1)) shape.2.1

/-- The count 512 reaches the provider and can return, for the complete nonempty input array. -/
theorem msm_count_512_returns (inputs : List MsmInput) (count : inputs.length = 512) :
    sol_curve_multiscalar_mul_run msmSample [] ⟨0, inputs⟩
      (.returned ⟨0, [List.replicate 32 0]⟩ [(MsmArgs.mk 0 inputs).request]) := by
  change msmRun msmSample [] _ _
  unfold msmRun
  have accepted : (MsmArgs.mk 0 inputs).overLimit = false := by
    simp only [MsmArgs.overLimit, count, Nat.lt_irrefl, decide_false]
  rw [accepted, Bool.cond_false]
  rfl

/-- At 513 elements the call stops before invalid-curve dispatch; no provider return can bypass it.
-/
theorem msm_count_513_precedes_curve (inputs : List MsmInput) (count : inputs.length = 513) :
    sol_curve_multiscalar_mul_run msmSample [] ⟨99, inputs⟩ (.terminated ()) ∧
      ∀ answer after, ¬ (sol_curve_multiscalar_mul_contract.contract msmSample).post []
        ⟨99, inputs⟩ (.returned answer after) := by
  have over : (MsmArgs.mk 99 inputs).overLimit = true := by
    simp only [MsmArgs.overLimit, count, show (512 : Nat) < 513 by decide, decide_true]
  refine ⟨?_, fun answer after => msmPost_overLimit over answer after⟩
  change msmRun msmSample [] _ _
  unfold msmRun
  rw [over, Bool.cond_true]
  rfl

/-- The empty input is admitted; zero is not an invalid count. -/
theorem msm_zero_inputs_admitted :
    (sol_curve_multiscalar_mul_contract.contract msmSample).requires [] ⟨1, []⟩ ∧
      sol_curve_multiscalar_mul_run msmSample [] ⟨1, []⟩
        (.returned ⟨0, [List.replicate 32 0]⟩ [.curveMultiscalarMul 1 [] []]) :=
  ⟨trivial, rfl⟩

/-- At a supported count an invalid curve can return only failure and no output, at any index. -/
theorem msm_invalid_curve_no_output (index : MsmIndex) (st st' : index.State) (answer :
  Solanalib.Runtime.SysAns)
    (post : (sol_curve_multiscalar_mul_contract.contract index).post st ⟨99, []⟩
      (.returned answer st')) : answer.r0 = 1 ∧ answer.out = [] :=
  msmPost_invalid rfl post

/-- Disabling the invalid-curve abort feature returns status `1` and preserves invocation state. -/
theorem canonical_msm_invalid_returns (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st : Solanalib.Runtime.InvState)
    (registered : W.prof.features.curve25519Syscalls = true)
    (nonfatal : W.prof.features.abortOnInvalidCurve = false) :
    sol_curve_multiscalar_mul_run (canonicalMsm W c width) st ⟨99, []⟩ (.returned ⟨1, []⟩ st) := by
  apply (canonical_msm_returned_iff W c width st st ⟨99, []⟩ _).mpr
  exact ⟨registered, Nat.zero_le _, ⟨nonfatal, rfl⟩, rfl⟩

/-- Enabling the invalid-curve abort feature gives a terminal exit. -/
theorem canonical_msm_invalid_stops (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st : Solanalib.Runtime.InvState)
    (fatal : W.prof.features.abortOnInvalidCurve = true) :
    sol_curve_multiscalar_mul_run (canonicalMsm W c width) st ⟨99, []⟩
      (.terminated .ProgramFailedToComplete) :=
  (canonical_msm_terminated_iff W c width st ⟨99, []⟩ _).mpr
    ⟨Or.inr (Or.inr ⟨rfl, fatal⟩), rfl⟩

/-- Curve syscall registration is required independently of the supplied primitive. -/
theorem canonical_msm_unregistered (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st : Solanalib.Runtime.InvState) (args : MsmArgs)
    (unregistered : W.prof.features.curve25519Syscalls = false) :
    sol_curve_multiscalar_mul_run (canonicalMsm W c width) st args (.terminated
      .ProgramFailedToComplete) :=
  (canonical_msm_terminated_iff W c width st args _).mpr ⟨Or.inl unregistered, rfl⟩

/-- Any correctly sized scalar bit pattern is admitted, including the all-ones encoding. -/
def undecodableInput : MsmInput :=
  ⟨List.replicate 32 255, List.replicate 32 0, by simp, by simp⟩

/-- An encoding rejected by the primitive returns status `1`, without writes or invocation changes.
Successful scalar or point decoding is not a precondition. -/
theorem canonical_msm_decode_failure (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st : Solanalib.Runtime.InvState)
    (registered : W.prof.features.curve25519Syscalls = true)
    (rejected : W.prims.curveMultiscalarMul 0 [undecodableInput.scalar] [undecodableInput.point] =
      none) :
    (sol_curve_multiscalar_mul_contract.contract (canonicalMsm W c width)).requires st
      ⟨0, [undecodableInput]⟩ ∧
      sol_curve_multiscalar_mul_run (canonicalMsm W c width) st ⟨0, [undecodableInput]⟩
        (.returned ⟨1, []⟩ st) := by
  refine ⟨trivial, (canonical_msm_returned_iff W c width st st ⟨0, [undecodableInput]⟩ _).mpr ?_⟩
  refine ⟨registered, by decide, ?_, rfl⟩
  change (⟨1, []⟩ : Solanalib.Runtime.SysAns) = match
    W.prims.curveMultiscalarMul 0 [undecodableInput.scalar] [undecodableInput.point] with
    | some output => ⟨0, [output]⟩ | none => ⟨1, []⟩
  rw [rejected]

/-- A successful canonical primitive result yields exactly that output with the scoped width law. -/
theorem canonical_msm_success (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st : Solanalib.Runtime.InvState) (args : MsmArgs) (output :
      Solanalib.Runtime.Bytes)
    (registered : W.prof.features.curve25519Syscalls = true) (count : args.inputs.length ≤ 512)
    (valid : args.validCurve = true)
    (computed : W.prims.curveMultiscalarMul args.curve args.scalars args.points = some output) :
    sol_curve_multiscalar_mul_run (canonicalMsm W c width) st args (.returned ⟨0, [output]⟩ st) ∧
      output.length = 32 := by
  refine ⟨(canonical_msm_returned_iff W c width st st args _).mpr ?_,
    width args count valid output computed⟩
  exact ⟨registered, count, by simp only [MsmAnswer, valid, Bool.cond_true, computed], rfl⟩

/-- A successful provider reply for an invalid curve breaks the all-index law even with a valid
output width. -/
theorem invalid_curve_success_rejected :
    ¬ MsmShape ⟨99, []⟩ ⟨0, [List.replicate 32 0]⟩ := by
  intro shape
  cases shape.2.2 rfl

/-- Paired inputs preserve both complete arrays and every encoding width. -/
theorem paired_inputs_keep_widths (args : MsmArgs) :
    args.scalars.length = args.points.length ∧
      (∀ scalar ∈ args.scalars, scalar.length = 32) ∧
      (∀ point ∈ args.points, point.length = 32) :=
  ⟨args.equal_counts, args.scalars_width, args.points_width⟩

end SolanalibTest.Specs.SolanaDefineSyscall.Definitions

/-! Clients of the raw syscall models: the answers of the canonical runtime, the hash-shape law,
unaligned `sol_sha256` calls and calls with too many slices, and environments that stop, answer too
much or do not answer. -/

namespace SolanalibTest.Specs.SolanaDefineSyscall.Definitions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.RawSyscall
open Solanalib.Specs.SolanaDefineSyscall.definitions

/-! ## `sol_sha256` -/

/-- Two slices are within the canonical slice limit. -/
theorem two_within_limit (W : Solanalib.Runtime.World) : [[1, 2], [3]].length ≤
  W.prof.maxHashSlices := by
  change 2 ≤ Solanalib.Runtime.MAX_HASH_SLICES
  decide

/-- The canonical runtime answers two slices at an aligned `vals` with status `0` and the symbolic
hash of their concatenation, and leaves the state unchanged. -/
theorem canonical_hash_returned (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState) :
    sol_sha256_run (canonical W c) st ⟨[[1, 2], [3]], true⟩
      (.returned ⟨0, [W.prims.sha256 [1, 2, 3]]⟩ st) :=
  (canonical_sha256_returned_iff W c st st ⟨[[1, 2], [3]], true⟩ _).mpr
    ⟨rfl, two_within_limit W, rfl, rfl⟩

/-- Beyond the slice limit the canonical runtime stops the call and gives no answer. -/
theorem canonical_hash_over_limit (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st
  : Solanalib.Runtime.InvState)
    (args : Sha256Args) (over : W.prof.maxHashSlices < args.slices.length) :
    sol_sha256_run (canonical W c) st args (.terminated .ProgramFailedToComplete) ∧
      ∀ answer st', ¬ sol_sha256_run (canonical W c) st args (.returned answer st') := by
  refine ⟨(canonical_sha256_terminated_iff W c st args _).mpr ⟨Or.inr over, rfl⟩, ?_⟩
  intro answer st' returned
  have count := ((canonical_sha256_returned_iff W c st st' args answer).mp returned).2.1
  omega

/-- A canonical return that the contract admits is the symbolic digest, of 32 bytes. -/
theorem canonical_hash_post (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st st' :
  Solanalib.Runtime.InvState)
    (args : Sha256Args) (answer : Solanalib.Runtime.SysAns)
    (post : (sol_sha256_contract.contract (canonical W c)).post st args (.returned answer st')) :
    answer = ⟨0, [W.prims.sha256 args.slices.flatten]⟩ ∧
      (W.prims.sha256 args.slices.flatten).length = 32 ∧ st' = st := by
  obtain ⟨_, _, same, width, unchanged⟩ :=
    (canonical_sha256_post_iff W c st st' args answer).mp post
  exact ⟨same, width, unchanged⟩

/-- Every canonical call is admissible, and a canonical return is a 32-byte digest, with no premise
on the world: the width is a law of `Solanalib.Runtime.Prims`. -/
theorem canonical_hash_width (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState) :
    (sol_sha256_contract.contract (canonical W c)).requires st ⟨[[1, 2], [3]], true⟩ ∧
      ∃ digest, sol_sha256_run (canonical W c) st ⟨[[1, 2], [3]], true⟩
        (.returned ⟨0, [digest]⟩ st) ∧ digest.length = 32 :=
  ⟨trivial, _, canonical_hash_returned W c st, W.prims.sha256_length _⟩

/-- Under ABI `v1`, the canonical runtime admits a call with a slice at an unaligned `vals`, fails
it with `ProgramFailedToComplete` and gives it no answer, as Agave aborts it. -/
theorem canonical_hash_unaligned (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (v1 : c.abi = .v1) :
    (sol_sha256_contract.contract (canonical W c)).requires st ⟨[[1, 2], [3]], false⟩ ∧
      sol_sha256_run (canonical W c) st ⟨[[1, 2], [3]], false⟩
        (.terminated .ProgramFailedToComplete) ∧
      ∀ answer st', ¬ sol_sha256_run (canonical W c) st ⟨[[1, 2], [3]], false⟩
        (.returned answer st') := by
  have unaligned := (canonical_unaligned_iff W c ⟨[[1, 2], [3]], false⟩).mpr
    ⟨rfl, v1, List.cons_ne_nil _ _⟩
  refine ⟨trivial, (canonical_sha256_unaligned_iff W c st _ unaligned _).mpr rfl, ?_⟩
  intro answer st' returned
  cases (canonical_sha256_unaligned_iff W c st _ unaligned _).mp returned

/-- Agave translates `vals` only for a slice: a call without one at an unaligned `vals` is
hashed. -/
theorem canonical_hash_empty_unaligned (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) :
    sol_sha256_run (canonical W c) st ⟨[], false⟩ (.returned ⟨0, [W.prims.sha256 []]⟩ st) :=
  (canonical_sha256_returned_iff W c st st ⟨[], false⟩ _).mpr
    ⟨by simp [Sha256Args.unaligned], Nat.zero_le _, rfl, rfl⟩

/-- The canonical runtime does not check alignment for a program of the deprecated loader. -/
theorem canonical_v0_unaligned (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (v0 :
  c.abi = .v0) :
    (canonical W c).checkAligned = false := by
  change c.abi.checkAligned = false
  rw [v0]
  rfl

/-- So a call of such a program at an unaligned `vals` is hashed. -/
theorem canonical_hash_v0_unaligned (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
  (st : Solanalib.Runtime.InvState)
    (v0 : c.abi = .v0) :
    sol_sha256_run (canonical W c) st ⟨[[1, 2], [3]], false⟩
      (.returned ⟨0, [W.prims.sha256 [1, 2, 3]]⟩ st) :=
  (canonical_sha256_returned_iff W c st st ⟨[[1, 2], [3]], false⟩ _).mpr
    ⟨by simp [Sha256Args.unaligned, canonical_v0_unaligned W c v0], two_within_limit W, rfl, rfl⟩

/-- A provider that returns a 32-byte digest in two pieces. -/
def splitting : Callback.Run Unit Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty Empty :=
  Callback.ofFunction fun _ _ => .returned ⟨0, [List.replicate 16 0, List.replicate 16 1]⟩ ()

/-- An answer of two pieces does not fit one 32-byte result: the provider breaks the hash-shape law,
so it is no index. -/
theorem split_digest_breaks_law :
    ¬ ∀ slices answer, splitting () (.hash .sha256 slices) (.returned answer ()) →
      HashShape answer := by
  intro law
  have shape := law [[1]] _ rfl
  revert shape
  decide

/-- A provider that writes bytes with a nonzero status. -/
def nonzeroWritten : Callback.Run Unit Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty
  Empty :=
  Callback.ofFunction fun _ _ => .returned ⟨1, [List.replicate 32 7]⟩ ()

/-- Bytes with a nonzero status are not an answer of the hash shape: the provider is no index. -/
theorem nonzero_written_breaks_law :
    ¬ ∀ slices answer, nonzeroWritten () (.hash .sha256 slices) (.returned answer ()) →
      HashShape answer := by
  intro law
  have shape := law [[1]] _ rfl
  revert shape
  decide

/-- An environment that answers status `7` and writes nothing. It limits no slice count. -/
def nonzeroEmpty : Index where
  State := Unit
  Terminal := Empty
  provider := Callback.ofFunction fun _ _ => .returned ⟨7, []⟩ ()
  checkAligned := true
  maxHashSlices := none
  hashShape := by
    intro _ _ _ _ answered
    cases answered
    decide

/-- A nonzero status without bytes is returned. -/
theorem nonzero_status_returned :
    (sol_sha256_contract.contract nonzeroEmpty).requires () ⟨[[1]], true⟩ ∧
      (sol_sha256_contract.contract nonzeroEmpty).post () ⟨[[1]], true⟩
        (.returned ⟨7, []⟩ ()) :=
  ⟨trivial, rfl, rfl, by decide⟩

/-- An environment that stops every request, as when the compute budget runs out. -/
def exhausted : Index where
  State := Unit
  Terminal := String
  provider := Callback.ofFunction fun _ _ => .terminated "budget"
  checkAligned := true
  maxHashSlices := none
  hashShape := by
    intro _ _ _ _ answered
    cases answered

/-- A terminal exit of the environment is the terminal exit of the call. -/
theorem hash_terminal_passed :
    (sol_sha256_contract.contract exhausted).requires () ⟨[], true⟩ ∧
      sol_sha256_run exhausted () ⟨[], true⟩ (.terminated "budget") :=
  ⟨trivial, rfl⟩

/-! ## `sol_log_` -/

/-- The canonical runtime admits a UTF-8 message and appends it to the logs. -/
theorem canonical_log_utf8 (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (message : Solanalib.Runtime.Bytes) (utf8 : W.prims.isUtf8 message = true) :
    (sol_log__contract.contract (canonical W c)).requires st message ∧
      sol_log__run (canonical W c) st message (.returned () { st with logs := st.logs ++ [message]
        }) :=
  ⟨trivial, (canonical_log_returned_iff W c st _ message).mpr ⟨utf8, rfl⟩⟩

/-- The canonical runtime admits a message that is not UTF-8, does not answer it, and stops the
call: it does not return, as Agave aborts it. -/
theorem canonical_log_invalid (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (message : Solanalib.Runtime.Bytes) (invalid : W.prims.isUtf8 message = false) :
    (sol_log__contract.contract (canonical W c)).requires st message ∧
      ¬ Answered (canonical W c) st (.log message) ∧
      sol_log__run (canonical W c) st message (.terminated .ProgramFailedToComplete) ∧
      ∀ st', ¬ (sol_log__contract.contract (canonical W c)).post st message (.returned () st') := by
  have unanswered : ¬ Answered (canonical W c) st (.log message) := fun answered => by
    have utf8 := (canonical_log_answered_iff W c st message).mp answered
    rw [invalid] at utf8
    cases utf8
  exact ⟨trivial, unanswered, (canonical_log_terminated_iff W c st message _).mpr ⟨invalid, rfl⟩,
    logPost_unanswered unanswered⟩

/-- An environment that never answers admits a log call, which stops with its terminal exit and
does not return. -/
theorem exhausted_log_stops :
    (sol_log__contract.contract exhausted).requires () [104] ∧
      sol_log__run exhausted () [104] (.terminated "budget") ∧
      ∀ after, ¬ (sol_log__contract.contract exhausted).post () [104] (.returned () after) :=
  ⟨trivial, ⟨.terminated "budget", rfl, rfl⟩,
    logPost_unanswered (fun ⟨_, _, answered⟩ => by cases answered)⟩

/-! ## `sol_panic_` and `abort` -/

/-- The canonical runtime fails a `sol_panic_` call. -/
theorem canonical_panic_stops (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState) :
    sol_panic__run (canonical W c) st ⟨[109, 46, 114, 115], 7, 3⟩
      (.terminated .ProgramFailedToComplete) :=
  (canonical_panic_iff W c st _ _).mpr rfl

/-- The canonical runtime fails an `abort` call. -/
theorem canonical_abort_stops (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState) :
    abort_run (canonical W c) st () (.terminated .ProgramFailedToComplete) :=
  (canonical_abort_iff W c st _).mpr rfl

/-- An environment that answers every request and never stops: a 32-byte digest to a hash request,
and `0` to any other. It allows at most one slice. -/
def answering : Index where
  State := Unit
  Terminal := Empty
  provider := Callback.ofFunction fun _ request => match request with
    | .hash .sha256 _ => .returned ⟨0, [List.replicate 32 0]⟩ ()
    | _ => .returned .ok0 ()
  checkAligned := true
  maxHashSlices := some 1
  hashShape := by
    intro _ _ _ _ answered
    cases answered
    decide

/-- Within the limit, the call returns the answer of the environment. -/
theorem answering_hash_within_limit :
    (sol_sha256_contract.contract answering).requires () ⟨[[1, 2]], true⟩ ∧
      sol_sha256_run answering () ⟨[[1, 2]], true⟩ (.returned ⟨0, [List.replicate 32 0]⟩ ()) :=
  ⟨trivial, rfl⟩

/-- Beyond the limit, the call is admissible but stops as `abort` does, without asking, whatever
its alignment: the environment would answer the hash request, but the model forbids a return, and
since this environment never stops, the call has no outcome at all. -/
theorem answering_hash_over_limit (aligned : Bool)
    (outcome : Outcome Unit Solanalib.Runtime.SysAns Empty Empty) :
    (sol_sha256_contract.contract answering).requires () ⟨[[1], [2]], aligned⟩ ∧
      ¬ sol_sha256_run answering () ⟨[[1], [2]], aligned⟩ outcome := by
  have over : Sha256Args.overLimit ⟨[[1], [2]], aligned⟩ answering.maxHashSlices = true := rfl
  refine ⟨trivial, fun run => ?_⟩
  change (bif Sha256Args.rejected ⟨[[1], [2]], aligned⟩ answering.maxHashSlices
    answering.checkAligned then aborted answering ()
    else answering.provider () (.hash .sha256 [[1], [2]])) outcome at run
  rw [Sha256Args.rejected_of_overLimit over, Bool.cond_true] at run
  cases outcome with
  | returned _ _ => exact run
  | unwound reason _ => exact nomatch reason
  | terminated reason => exact nomatch reason

/-- `sol_panic_` returns `!`: an answer is not an outcome, so against an environment that only
answers, the call has no outcome at all. -/
theorem panic_answer_not_returned (args : PanicArgs) (outcome : Outcome Unit Empty Empty Empty) :
    ¬ sol_panic__run answering () args outcome := by
  cases outcome with
  | returned value _ => exact nomatch value
  | unwound reason _ => exact nomatch reason
  | terminated reason => exact nomatch reason

/-- The same holds for `abort`. -/
theorem abort_answer_not_returned (outcome : Outcome Unit Empty Empty Empty) :
    ¬ abort_run answering () () outcome := by
  cases outcome with
  | returned value _ => exact nomatch value
  | unwound reason _ => exact nomatch reason
  | terminated reason => exact nomatch reason

end SolanalibTest.Specs.SolanaDefineSyscall.Definitions
