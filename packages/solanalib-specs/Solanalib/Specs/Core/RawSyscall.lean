/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family
public import Solanalib.Runtime.Env

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-!
# Raw syscalls at the request level

A program can call a syscall directly, through the `extern "C"` declarations of
`solana-define-syscall`, such as `sol_sha256`. These models state such a call with the plain
values of the runtime model, its requests and answers (`Solanalib.Runtime.SysReq`,
`Solanalib.Runtime.SysAns`): the call asks a syscall environment, the `provider` of the index,
and returns its answer. How the program passes the request and receives the answer in memory is
not part of these models.

An `extern "C"` function cannot unwind, so the provider has no unwind exit. Each terminal exit
of the provider, such as the runtime failing the instruction, is a terminal exit of the call.

* `sol_sha256` asks `.hash .sha256 slices` and returns the answer, which has the shape that a
  `u64` status and a 32-byte result carry (`HashShape`): one 32-byte digest on status `0`, and
  no bytes otherwise. The shape is a law of the index (`Index.hashShape`), not a precondition of
  the call. Its arguments also say whether `vals`, where the descriptors of the slices are, is
  8-aligned (`Sha256Args`). A call with more slices than the limit of the index
  (`Sha256Args.overLimit`) does not return, and neither does, where the index checks alignment,
  a call with a slice and an unaligned `vals` (`Sha256Args.unaligned`): Agave aborts both, and
  the call stops as the environment stops `abort` (`Sha256Args.rejected`, `aborted`).
* `sol_sha512` uses the same slice arguments and count/alignment checks as SHA-256, but returns
  one 64-byte digest (`OutputShape 64`). The canonical primitive consumes the ordered slices
  without assuming that differently segmented inputs have the same hash.
* `sol_curve_multiscalar_mul` receives paired 32-byte scalar and point encodings. It checks the
  512-element limit before curve dispatch; an invalid curve cannot produce output. The canonical
  interpretation uses the scoped width law `MsmWidth` for successful supported operations.
* `sol_log_` asks `.log message` and returns `()` when the provider answers it (`Answered`).
  Every message is admissible. A message that the provider does not answer has only the terminal
  exits of the provider, as `sol_panic_` and `abort` have: under the canonical runtime, a
  message that is not UTF-8.
* `sol_panic_` and `abort` return `!`, which has no values, so no answer can be returned: their
  only outcomes are the terminal exits of the provider.

An index also records whether pointer arguments must be aligned for their types
(`Index.checkAligned`): under the canonical runtime, `check_aligned` in Agave. The `sol_sha256`
model reads it to stop an unaligned call, and it fixes what an adapter that reads the arguments
from memory may require. It records as well the most slices that a `sol_sha256` call may hash,
if it limits them (`Index.maxHashSlices`): under the canonical runtime, the `maxHashSlices` of
the profile, `sha256_max_slices` in Agave. The model reads it to stop a call with more, before
it asks anything, so an adapter need not read the arguments of such a call.

## Checks in Agave in `sol_sha256`

`SyscallHash` (Agave `a203300045b405f86c9c84308b2eae76af69ac3b`,
`syscalls/src/lib.rs:2717-2788`) checks, in order: the slice count against the limit, failing
with `TooManySlices` (`:2733-2742`); the base compute cost (`:2744`); the translation of
`hash_result` (`:2748-2756`); and, only when `val_len > 0`, the translation of `vals` as
`val_len` `VmSlice<u8>`s with `check_aligned` (`:2758-2764`), which fails with
`UnalignedPointer` when the translated pointer is not 8-aligned
(`program-runtime/src/memory.rs:113-115`). Every one of these failures aborts the program. So a
call with more slices than the limit does not return, and it aborts before Agave charges compute
or translates any address. A call within the limit with a slice and an unaligned `vals`, where
the runtime checks alignment, does not return either, whichever later check fails first. The
model stops a call that fails the first or the last of these checks (`Sha256Args.rejected`); it
does not state the two checks between them, whose aborts lie outside a partial-correctness
reading. The canonical runtime fails a stopped call with `ProgramFailedToComplete`, as it fails
`abort` (`canonical_sha256_terminated_iff`, `canonical_sha256_unaligned_iff`).

`canonical W c` is the canonical runtime as a provider: its answers are those of
`Solanalib.Runtime.Env W c`, and its terminal exits the failures of `Solanalib.Runtime.sysStep`,
as `Solanalib.Runtime.Exec` has them. Hashes stay symbolic: a canonical hash is `W.prims.sha256`
of the concatenated slices, a 32-byte digest by the width law of `Solanalib.Runtime.Prims`
(`canonical_sha256_post_iff`). It checks alignment as Agave does for the ABI of the invocation
(`Solanalib.Runtime.Abi.checkAligned`), and limits the slices to the `maxHashSlices` of the
profile. -/

namespace Solanalib.Specs.Core.RawSyscall

/-! ## The hash shape -/

/-- A `u64` status carries one output of the selected width on success, and no output on failure.
Hash and curve syscalls share this representation; their request-specific laws remain separate. -/
def OutputShape (width : Nat) (answer : Solanalib.Runtime.SysAns) : Prop :=
  answer.r0 < Solanalib.Runtime.U64_LIMIT ∧
    (answer.r0 = 0 → ∃ digest, answer.out = [digest] ∧ digest.length = width) ∧
    (answer.r0 ≠ 0 → answer.out = [])

/-- Decide the status bound and complete output shape, including the number of buffers. -/
def outputShapeB (width : Nat) (answer : Solanalib.Runtime.SysAns) : Bool :=
  decide (answer.r0 < Solanalib.Runtime.U64_LIMIT) &&
    (if answer.r0 = 0 then
      (match answer.out with
        | [digest] => decide (digest.length = width)
        | _ => false)
    else answer.out.isEmpty)

/-- The same decision procedure works for every syscall output width. -/
theorem outputShapeB_iff (width : Nat) (answer : Solanalib.Runtime.SysAns) :
    outputShapeB width answer = true ↔ OutputShape width answer := by
  obtain ⟨r0, out⟩ := answer
  unfold outputShapeB OutputShape
  by_cases zero : r0 = 0
  · subst zero
    rcases out with _ | ⟨digest, _ | ⟨next, rest⟩⟩ <;> simp
  · simp [zero]

instance (width : Nat) (answer : Solanalib.Runtime.SysAns) : Decidable (OutputShape width answer) :=
  decidable_of_iff _ (outputShapeB_iff width answer)

/-- the status of SHA-256 and 32-byte digest use the shared output shape. -/
def HashShape (answer : Solanalib.Runtime.SysAns) : Prop := OutputShape 32 answer

/-- `HashShape`, computed. -/
def hashShapeB (answer : Solanalib.Runtime.SysAns) : Bool := outputShapeB 32 answer

/-- `hashShapeB` decides `HashShape`. -/
theorem hashShapeB_iff (answer : Solanalib.Runtime.SysAns) : hashShapeB answer = true ↔ HashShape
  answer :=
  outputShapeB_iff 32 answer

instance (answer : Solanalib.Runtime.SysAns) : Decidable (HashShape answer) :=
  decidable_of_iff _ (hashShapeB_iff answer)

/-! ## Syscall environments -/

/-- A syscall environment: its state, and the answers and terminal exits it gives each request.
It has no unwind exit, since an `extern "C"` function cannot unwind. -/
structure Index where
  /-- The state of the environment, such as the invocation state of the runtime. -/
  State : Type
  /-- Reasons of terminal exits, such as the instruction error of a failed syscall. -/
  Terminal : Type
  /-- The answers and terminal exits for each request. -/
  provider : Callback.Run State Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty Terminal
  /-- Whether the pointer arguments must be aligned for their types: for `sol_sha256`, whether a
  call with a slice whose descriptors are not 8-aligned stops (`Sha256Args.unaligned`). A source
  binding that reads the arguments from memory must require alignment only where it is set.
  `canonical` takes it from `check_aligned` in Agave for the ABI of the invocation
  (`Solanalib.Runtime.Abi.checkAligned`); a source binding must justify the same ABI choice. -/
  checkAligned : Bool
  /-- The most slices that a `sol_sha256` call may hash, if the environment limits them: a call with
  more stops before it asks anything (`Sha256Args.overLimit`). `none` claims no limit. `canonical`
  takes it from the profile (`Solanalib.Runtime.Profile.maxHashSlices`), the `sha256_max_slices` of
  Agave; a source binding must supply and justify the selected limit. -/
  maxHashSlices : Option Nat
  /-- Every answer to a SHA-256 request has the hash shape: one 32-byte digest on status `0`, and
  no bytes otherwise, as `SyscallHash` in Agave 4.3.2 writes `size_of::<Hash>()` bytes on
  success. -/
  hashShape : ∀ before slices answer after,
    provider before (.hash .sha256 slices) (.returned answer after) → HashShape answer

/-! ## Calls that the runtime aborts -/

/-- A rejected request has only the terminal `abort` outcomes of the selected provider. -/
def abortedWith {State Terminal Value : Type}
    (provider : Callback.Run State Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty
      Terminal) (before : State) :
    Outcome State Value Empty Terminal → Prop
  | .returned _ _ => False
  | .unwound reason _ => nomatch reason
  | .terminated reason => provider before .abort (.terminated reason)

/-- The outcomes of a call that the runtime aborts before it asks anything: the terminal exits of
the environment for `.abort`, and no return. Agave fails the instruction on a failed argument check
as on `abort`. -/
def aborted (index : Index) (before : index.State) {Value : Type} :
    Outcome index.State Value Empty index.Terminal → Prop :=
  abortedWith index.provider before

/-- A checked call either stops before its request or retains the complete outcome of that request.
The response law of the provider is needed only on a return. -/
theorem checkedCall_reference {State Terminal : Type}
    (provider : Callback.Run State Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty Terminal)
    (before : State) (request : Solanalib.Runtime.SysReq) (rejected : Bool) (shape :
      Solanalib.Runtime.SysAns → Prop)
    (response : ∀ answer after, provider before request (.returned answer after) → shape answer)
    (outcome : Outcome State Solanalib.Runtime.SysAns Empty Terminal) :
    (bif rejected then abortedWith provider before else provider before request) outcome →
    (match outcome with
    | .returned answer after =>
        rejected = false ∧ provider before request (.returned answer after) ∧ shape answer
    | .unwound reason _ => nomatch reason
    | .terminated reason =>
        bif rejected then provider before .abort (.terminated reason)
        else provider before request (.terminated reason)) := by
  intro execution
  cases rejected with
  | false =>
    cases outcome with
    | returned answer after => exact ⟨rfl, execution, response answer after execution⟩
    | unwound reason _ => exact nomatch reason
    | terminated _ => exact execution
  | true =>
    cases outcome with
    | returned _ _ => exact execution.elim
    | unwound reason _ => exact nomatch reason
    | terminated _ => exact execution

/-! ## `sol_sha256` -/

/-- The arguments of `sol_sha256`: the slices that the descriptors at `vals` give, in order, and
whether `vals` is aligned for a descriptor, 8 bytes, as Agave checks it. -/
structure Sha256Args where
  /-- The hashed slices, in order. -/
  slices : List Solanalib.Runtime.Bytes
  /-- `vals` is 8-aligned. -/
  aligned : Bool

/-- The runtime aborts the call before it reads a descriptor: `vals` is not aligned, alignment is
checked (`checkAligned`) and there is a slice. Agave translates `vals` only when `val_len > 0`. -/
def Sha256Args.unaligned (args : Sha256Args) (checkAligned : Bool) : Bool :=
  !args.aligned && checkAligned && !args.slices.isEmpty

/-- The runtime aborts the call before it reads anything: there is a limit, `limit`, and the call
has more slices. Agave checks the count `val_len` first, before it charges compute or translates an
address. -/
def Sha256Args.overLimit (args : Sha256Args) (limit : Option Nat) : Bool :=
  match limit with
  | some most => decide (most < args.slices.length)
  | none => false

/-- The runtime aborts the call before it reads a descriptor: it has too many slices
(`overLimit`), which Agave checks first, or it is unaligned (`unaligned`), which Agave checks last.
Each check aborts the program, so the call does not return when either fails. -/
def Sha256Args.rejected (args : Sha256Args) (limit : Option Nat) (checkAligned : Bool) : Bool :=
  args.overLimit limit || args.unaligned checkAligned

/-- A call with too many slices is rejected, whatever its alignment. -/
theorem Sha256Args.rejected_of_overLimit {args : Sha256Args} {limit : Option Nat}
    {checkAligned : Bool} (over : args.overLimit limit = true) :
    args.rejected limit checkAligned = true := by
  simp [Sha256Args.rejected, over]

/-- An unaligned call is rejected. -/
theorem Sha256Args.rejected_of_unaligned {args : Sha256Args} {limit : Option Nat}
    {checkAligned : Bool} (unaligned : args.unaligned checkAligned = true) :
    args.rejected limit checkAligned = true := by
  simp [Sha256Args.rejected, unaligned]

/-- A call passes both checks when it is within the limit and not unaligned. -/
theorem Sha256Args.rejected_eq_false_iff {args : Sha256Args} {limit : Option Nat}
    {checkAligned : Bool} :
    args.rejected limit checkAligned = false ↔
      args.overLimit limit = false ∧ args.unaligned checkAligned = false := by
  simp [Sha256Args.rejected]

/-- Ask the hash request of the slices and return the answer; on a call with too many slices or an
unaligned one, stop as the environment stops `abort`, without asking. -/
def sha256Run (index : Index) :
    Callback.Run index.State Sha256Args Solanalib.Runtime.SysAns Empty index.Terminal :=
  fun before args => bif args.rejected index.maxHashSlices index.checkAligned then
      aborted index before
    else index.provider before (.hash .sha256 args.slices)

/-- The outcomes of `sol_sha256`: an answer, which has the hash shape, or a terminal exit, as the
environment gives them for the hash request of the slices. On status `0` the answer is one 32-byte
digest. A call with too many slices or an unaligned one does not return, and stops as the
environment stops `abort`. -/
def sha256Post (index : Index) (before : index.State) (args : Sha256Args) :
    Outcome index.State Solanalib.Runtime.SysAns Empty index.Terminal → Prop
  | .returned answer after =>
      args.rejected index.maxHashSlices index.checkAligned = false ∧
        index.provider before (.hash .sha256 args.slices) (.returned answer after) ∧
        HashShape answer
  | .unwound reason _ => nomatch reason
  | .terminated reason =>
      bif args.rejected index.maxHashSlices index.checkAligned then
        index.provider before .abort (.terminated reason)
      else index.provider before (.hash .sha256 args.slices) (.terminated reason)

/-- `sol_sha256(vals, val_len, hash_result) -> u64` at the request level. -/
def sha256Family : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Sha256Args
  Value := fun _ => Solanalib.Runtime.SysAns
  Unwind := fun _ => Empty
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := sha256Post index }

/-- A call with too many slices or an unaligned one does not return. -/
theorem sha256Post_rejected {index : Index} {before : index.State} {args : Sha256Args}
    (rejected : args.rejected index.maxHashSlices index.checkAligned = true)
    (answer : Solanalib.Runtime.SysAns) (after : index.State) :
    ¬ sha256Post index before args (.returned answer after) := by
  rintro ⟨accepted, _⟩
  rw [rejected] at accepted
  cases accepted

/-- An unaligned call does not return. -/
theorem sha256Post_unaligned {index : Index} {before : index.State} {args : Sha256Args}
    (unaligned : args.unaligned index.checkAligned = true) (answer : Solanalib.Runtime.SysAns)
    (after : index.State) : ¬ sha256Post index before args (.returned answer after) :=
  sha256Post_rejected (Sha256Args.rejected_of_unaligned unaligned) answer after

/-- A call with more slices than the limit of the index does not return. -/
theorem sha256Post_overLimit {index : Index} {before : index.State} {args : Sha256Args}
    (over : args.overLimit index.maxHashSlices = true) (answer : Solanalib.Runtime.SysAns)
    (after : index.State) : ¬ sha256Post index before args (.returned answer after) :=
  sha256Post_rejected (Sha256Args.rejected_of_overLimit over) answer after

/-- The reference at every index. -/
def sha256FamilyRun : FamilyRun sha256Family := sha256Run

/-- `sha256FamilyRun` is the reference of `sha256Family` at every index: the shape of its answers is
the law of the index. -/
theorem sha256Family_reference : FamilyReference sha256Family sha256FamilyRun := by
  intro index before args outcome _ execution
  have checked := checkedCall_reference index.provider before (.hash .sha256 args.slices)
    (args.rejected index.maxHashSlices index.checkAligned) HashShape
    (index.hashShape before args.slices) outcome execution
  cases outcome with
  | returned _ _ => exact checked
  | unwound reason _ => exact nomatch reason
  | terminated _ => exact checked

/-! ## `sol_log_` -/

/-- The environment answers `request`. -/
def Answered (index : Index) (before : index.State) (request : Solanalib.Runtime.SysReq) : Prop :=
  ∃ answer after, index.provider before request (.returned answer after)

/-- Ask the log request of the message and return `()`. -/
def logRun (index : Index) : Callback.Run index.State Solanalib.Runtime.Bytes Unit Empty
  index.Terminal :=
  fun before message => Callback.map (fun _ => ()) index.provider before (.log message)

/-- The outcomes of `sol_log_`: `()` when the environment answers the log request, or one of its
terminal exits. A message that the environment does not answer has only its terminal exits, as
`sol_panic_` and `abort` have (`stops`). -/
def logPost (index : Index) (before : index.State) (message : Solanalib.Runtime.Bytes) :
    Outcome index.State Unit Empty index.Terminal → Prop
  | .returned () after => ∃ answer, index.provider before (.log message) (.returned answer after)
  | .unwound reason _ => nomatch reason
  | .terminated reason => index.provider before (.log message) (.terminated reason)

/-- `sol_log_(message, len)` at the request level. Every message is admissible; one that the
environment does not answer does not return. -/
def logFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun _ => Unit
  Unwind := fun _ => Empty
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := logPost index }

/-- A message that the environment does not answer does not return. -/
theorem logPost_unanswered {index : Index} {before : index.State} {message :
  Solanalib.Runtime.Bytes}
    (unanswered : ¬ Answered index before (.log message)) (after : index.State) :
    ¬ logPost index before message (.returned () after) := by
  rintro ⟨answer, answered⟩
  exact unanswered ⟨answer, after, answered⟩

/-- The reference at every index. -/
def logFamilyRun : FamilyRun logFamily := logRun

/-- `logFamilyRun` is the reference of `logFamily` at every index. -/
theorem logFamily_reference : FamilyReference logFamily logFamilyRun := by
  intro index before message outcome _ execution
  obtain ⟨exit, source, mapped⟩ := execution
  cases exit with
  | returned answer after =>
    subst mapped
    exact ⟨answer, source⟩
  | unwound reason _ => exact nomatch reason
  | terminated reason =>
    subst mapped
    exact source

/-! ## `sol_panic_` and `abort` -/

/-- The outcomes of a call that returns `!`: the terminal exits of the environment for `request`. No
answer is an outcome, since `!` has no values. -/
def stops (index : Index) (before : index.State) (request : Solanalib.Runtime.SysReq) :
    Outcome index.State Empty Empty index.Terminal → Prop
  | .returned value _ => nomatch value
  | .unwound reason _ => nomatch reason
  | .terminated reason => index.provider before request (.terminated reason)

/-- The arguments of `sol_panic_`: the bytes of the file name, the line and the column. -/
structure PanicArgs where
  /-- The file name. -/
  file : Solanalib.Runtime.Bytes
  /-- The line. -/
  line : Nat
  /-- The column. -/
  column : Nat

/-- The request of a `sol_panic_` call. -/
def PanicArgs.request (args : PanicArgs) : Solanalib.Runtime.SysReq := .panic args.file args.line
  args.column

/-- `sol_panic_(file, len, line, column) -> !` at the request level. -/
def panicFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => PanicArgs
  Value := fun _ => Empty
  Unwind := fun _ => Empty
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args => stops index before args.request }

/-- The reference at every index. -/
def panicFamilyRun : FamilyRun panicFamily := fun index before args => stops index before
  args.request

/-- `panicFamilyRun` is the reference of `panicFamily` at every index. -/
theorem panicFamily_reference : FamilyReference panicFamily panicFamilyRun :=
  fun _ _ _ _ _ execution => execution

/-- `abort() -> !` at the request level. -/
def abortFamily : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Unit
  Value := fun _ => Empty
  Unwind := fun _ => Empty
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before _ => stops index before .abort }

/-- The reference at every index. -/
def abortFamilyRun : FamilyRun abortFamily := fun index before _ => stops index before .abort

/-- `abortFamilyRun` is the reference of `abortFamily` at every index. -/
theorem abortFamily_reference : FamilyReference abortFamily abortFamilyRun :=
  fun _ _ _ _ _ execution => execution

/-! ## The canonical runtime -/

/-- The canonical runtime fails `request` with `error`: a registered request other than CPI and
`sol_remaining_compute_units` that `Solanalib.Runtime.sysStep` fails, or an unregistered one, as in
the `sysFail` and `unregistered` rules of `Solanalib.Runtime.Exec`. -/
def Fails (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState) (request : Solanalib.Runtime.SysReq)
    (error : Solanalib.Runtime.InstrError) : Prop :=
  (request.registered W.prof = true ∧ (∀ q, request ≠ .invoke q) ∧
      request ≠ .remainingComputeUnits ∧
      Solanalib.Runtime.sysStep W.prof W.prims W.sysvars W.epochStake c st request = .error error) ∨
    (request.registered W.prof = false ∧ error = .ProgramFailedToComplete)

/-- The answers and terminal exits of the canonical runtime: the answers of
`Solanalib.Runtime.Env W c` and the failures `Fails W c`. -/
def canonicalProvider (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) :
    Callback.Run Solanalib.Runtime.InvState Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError :=
  fun st request outcome => match outcome with
    | .returned answer st' => Solanalib.Runtime.Env W c st request answer st'
    | .unwound reason _ => nomatch reason
    | .terminated error => Fails W c st request error

/-- Within the slice limit, the canonical runtime answers a SHA-256 request with status `0` and the
symbolic hash of the concatenated slices, and changes no state; beyond it, it answers nothing. -/
theorem canonicalProvider_sha256_answer_iff (W : Solanalib.Runtime.World) (c :
  Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (slices : List Solanalib.Runtime.Bytes) (answer :
      Solanalib.Runtime.SysAns) :
    canonicalProvider W c st (.hash .sha256 slices) (.returned answer st') ↔
      slices.length ≤ W.prof.maxHashSlices ∧ answer = ⟨0, [W.prims.sha256 slices.flatten]⟩ ∧
        st' = st := by
  change Solanalib.Runtime.Env W c st (.hash .sha256 slices) answer st' ↔ _
  constructor
  · rintro ⟨_, _, ⟨_, h⟩ | ⟨h, _⟩⟩
    · by_cases over : W.prof.maxHashSlices < slices.length
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_true,
        reduceCtorEq] at h
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_false,
        Except.ok.injEq,
          Prod.mk.injEq] at h
        exact ⟨Nat.le_of_not_lt over, h.1.symm, h.2.symm⟩
    · cases h
  · rintro ⟨count, rfl, rfl⟩
    refine ⟨rfl, (fun _ h => by cases h), Or.inl ⟨(fun h => by cases h), ?_⟩⟩
    simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply_ok _ _ _ count]

/-- The canonical runtime as a syscall environment: the invocation state, the answers of
`Solanalib.Runtime.Env W c` and the failures `Fails W c`. Its digests have 32 bytes by the width
law of `Solanalib.Runtime.Prims`, it checks alignment as Agave does for the ABI of the
invocation, and it limits the slices of a hash to the `maxHashSlices` of the profile, beyond
which its provider answers nothing either. -/
def canonical (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) : Index where
  State := Solanalib.Runtime.InvState
  Terminal := Solanalib.Runtime.InstrError
  provider := canonicalProvider W c
  checkAligned := c.abi.checkAligned
  maxHashSlices := some W.prof.maxHashSlices
  hashShape := by
    intro st slices answer st' answered
    obtain ⟨_, rfl, _⟩ := (canonicalProvider_sha256_answer_iff W c st st' slices answer).mp answered
    exact ⟨by simp [Solanalib.Runtime.U64_LIMIT], fun _ => ⟨_, rfl, W.prims.sha256_length _⟩,
      fun nonzero => (nonzero rfl).elim⟩

/-- `abort` gets no answer from the canonical runtime. -/
theorem canonical_abort_no_answer (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st
  st' : Solanalib.Runtime.InvState)
    (answer : Solanalib.Runtime.SysAns) : ¬ (canonical W c).provider st .abort (.returned answer
      st') := by
  rintro ⟨_, _, ⟨_, h⟩ | ⟨h, _⟩⟩
  · simp only [Solanalib.Runtime.sysStep, reduceCtorEq] at h
  · cases h

/-- `sol_panic_` gets no answer from the canonical runtime. -/
theorem canonical_panic_no_answer (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st
  st' : Solanalib.Runtime.InvState)
    (file : Solanalib.Runtime.Bytes) (line column : Nat) (answer : Solanalib.Runtime.SysAns) :
    ¬ (canonical W c).provider st (.panic file line column) (.returned answer st') := by
  rintro ⟨_, _, ⟨_, h⟩ | ⟨h, _⟩⟩
  · simp only [Solanalib.Runtime.sysStep, reduceCtorEq] at h
  · cases h

/-- The canonical runtime fails `abort` and `sol_panic_` with `ProgramFailedToComplete`. -/
theorem canonical_fails_stop (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (request : Solanalib.Runtime.SysReq) (stop : request = .abort ∨ ∃ file line column, request =
      .panic file line column)
    (error : Solanalib.Runtime.InstrError) :
    (canonical W c).provider st request (.terminated error) ↔ error = .ProgramFailedToComplete := by
  change Fails W c st request error ↔ _
  rcases stop with rfl | ⟨file, line, column, rfl⟩
  · constructor
    · rintro (⟨_, _, _, h⟩ | ⟨h, _⟩)
      · simp only [Solanalib.Runtime.sysStep, Except.error.injEq] at h
        exact h.symm
      · cases h
    · rintro rfl
      exact Or.inl ⟨rfl, (fun _ h => by cases h), (fun h => by cases h), rfl⟩
  · constructor
    · rintro (⟨_, _, _, h⟩ | ⟨h, _⟩)
      · simp only [Solanalib.Runtime.sysStep, Except.error.injEq] at h
        exact h.symm
      · cases h
    · rintro rfl
      exact Or.inl ⟨rfl, (fun _ h => by cases h), (fun h => by cases h), rfl⟩

/-- `sol_log_` answers `0` to a UTF-8 message and appends it to the logs; it answers nothing
else. -/
theorem canonical_log_answer_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st
  st' : Solanalib.Runtime.InvState)
    (message : Solanalib.Runtime.Bytes) (answer : Solanalib.Runtime.SysAns) :
    (canonical W c).provider st (.log message) (.returned answer st') ↔
      W.prims.isUtf8 message = true ∧ answer = .ok0 ∧
        st' = { st with logs := st.logs ++ [message] } := by
  change Solanalib.Runtime.Env W c st (.log message) answer st' ↔ _
  constructor
  · rintro ⟨_, _, ⟨_, h⟩ | ⟨h, _⟩⟩
    · simp only [Solanalib.Runtime.sysStep] at h
      split at h
      · cases h
        exact ⟨by assumption, rfl, rfl⟩
      · cases h
    · cases h
  · rintro ⟨utf8, rfl, rfl⟩
    refine ⟨rfl, (fun _ h => by cases h), Or.inl ⟨(fun h => by cases h), ?_⟩⟩
    simp only [Solanalib.Runtime.sysStep, utf8, ite_true]

/-- `sol_log_` fails a message that is not UTF-8, and only such a message. -/
theorem canonical_log_fails_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (message : Solanalib.Runtime.Bytes) (error : Solanalib.Runtime.InstrError) :
    (canonical W c).provider st (.log message) (.terminated error) ↔
      W.prims.isUtf8 message = false ∧ error = .ProgramFailedToComplete := by
  change Fails W c st (.log message) error ↔ _
  constructor
  · rintro (⟨_, _, _, h⟩ | ⟨h, _⟩)
    · simp only [Solanalib.Runtime.sysStep] at h
      split at h
      · cases h
      · cases h
        exact ⟨by simpa using ‹¬W.prims.isUtf8 message = true›, rfl⟩
    · cases h
  · rintro ⟨invalid, rfl⟩
    refine Or.inl ⟨rfl, (fun _ h => by cases h), (fun h => by cases h), ?_⟩
    simp only [Solanalib.Runtime.sysStep, invalid, Bool.false_eq_true, ite_false]

/-- Within the slice limit, `sol_sha256` answers `0` and the symbolic hash of the concatenated
slices, and changes no state; beyond it, it answers nothing. -/
theorem canonical_sha256_answer_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (slices : List Solanalib.Runtime.Bytes) (answer :
      Solanalib.Runtime.SysAns) :
    (canonical W c).provider st (.hash .sha256 slices) (.returned answer st') ↔
      slices.length ≤ W.prof.maxHashSlices ∧ answer = ⟨0, [W.prims.sha256 slices.flatten]⟩ ∧
        st' = st :=
  canonicalProvider_sha256_answer_iff W c st st' slices answer

/-- The canonical runtime checks alignment exactly for ABI `v1`. -/
theorem canonical_checkAligned (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) :
    (canonical W c).checkAligned = true ↔ c.abi = .v1 := by
  change c.abi.checkAligned = true ↔ _
  cases c.abi <;> decide

/-- Beyond the slice limit, and only there, `sol_sha256` fails with `ProgramFailedToComplete`. -/
theorem canonical_sha256_fails_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st
  : Solanalib.Runtime.InvState)
    (slices : List Solanalib.Runtime.Bytes) (error : Solanalib.Runtime.InstrError) :
    (canonical W c).provider st (.hash .sha256 slices) (.terminated error) ↔
      W.prof.maxHashSlices < slices.length ∧ error = .ProgramFailedToComplete := by
  change Fails W c st (.hash .sha256 slices) error ↔ _
  constructor
  · rintro (⟨_, _, _, h⟩ | ⟨h, _⟩)
    · by_cases over : W.prof.maxHashSlices < slices.length
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_true,
        Except.error.injEq] at h
        exact ⟨over, h.symm⟩
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_false,
        reduceCtorEq] at h
    · cases h
  · rintro ⟨over, rfl⟩
    refine Or.inl ⟨rfl, (fun _ h => by cases h), (fun h => by cases h), ?_⟩
    simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_true]

/-! ## The four models at the canonical runtime -/

/-- Under the canonical runtime, a call is unaligned exactly when its `vals` is not 8-aligned, the
ABI of the invocation is `v1` and it has a slice. -/
theorem canonical_unaligned_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (args
  : Sha256Args) :
    args.unaligned (canonical W c).checkAligned = true ↔
      args.aligned = false ∧ c.abi = .v1 ∧ args.slices ≠ [] := by
  rw [← canonical_checkAligned W c]
  obtain ⟨slices, aligned⟩ := args
  generalize (canonical W c).checkAligned = checked
  cases aligned <;> cases checked <;> cases slices <;> simp [Sha256Args.unaligned]

/-- Under the canonical runtime, a call has too many slices exactly when it has more than the
`maxHashSlices` of the
profile. -/
theorem canonical_overLimit_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (args
  : Sha256Args) :
    args.overLimit (canonical W c).maxHashSlices = true ↔
      W.prof.maxHashSlices < args.slices.length := by
  change args.overLimit (some W.prof.maxHashSlices) = true ↔ _
  simp [Sha256Args.overLimit]

/-- Under the canonical runtime, a call passes both checks exactly when it is not unaligned and is
within the `maxHashSlices` of the profile. -/
theorem canonical_rejected_eq_false_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (args : Sha256Args) :
    args.rejected (canonical W c).maxHashSlices (canonical W c).checkAligned = false ↔
      args.unaligned (canonical W c).checkAligned = false ∧
        args.slices.length ≤ W.prof.maxHashSlices := by
  rw [Sha256Args.rejected_eq_false_iff, ← Bool.not_eq_true, canonical_overLimit_iff, Nat.not_lt]
  exact And.comm

/-- A canonical `sol_sha256` call returns, when it passes the alignment check and is within the
slice limit, the symbolic SHA-256 of the concatenated slices with status `0`, and changes no
state. -/
theorem canonical_sha256_returned_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (args : Sha256Args) (answer : Solanalib.Runtime.SysAns) :
    sha256Run (canonical W c) st args (.returned answer st') ↔
      args.unaligned (canonical W c).checkAligned = false ∧
        args.slices.length ≤ W.prof.maxHashSlices ∧
        answer = ⟨0, [W.prims.sha256 args.slices.flatten]⟩ ∧ st' = st := by
  rw [← and_assoc, ← canonical_rejected_eq_false_iff]
  unfold sha256Run
  cases rejected : args.rejected (canonical W c).maxHashSlices (canonical W c).checkAligned with
  | true =>
    rw [Bool.cond_true]
    exact ⟨fun returned => returned.elim, fun ⟨accepted, _⟩ => nomatch accepted⟩
  | false =>
    rw [Bool.cond_false]
    refine (canonical_sha256_answer_iff W c st st' args.slices answer).trans
      ⟨fun ⟨_, returned⟩ => ⟨rfl, returned⟩, fun ⟨_, returned⟩ => ⟨?_, returned⟩⟩
    exact ((canonical_rejected_eq_false_iff W c args).mp rejected).2

/-- A canonical `sol_sha256` call stops exactly when it is unaligned or beyond the slice limit, with
`ProgramFailedToComplete`. -/
theorem canonical_sha256_terminated_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (args : Sha256Args) (error : Solanalib.Runtime.InstrError) :
    sha256Run (canonical W c) st args (.terminated error) ↔
      (args.unaligned (canonical W c).checkAligned = true ∨
        W.prof.maxHashSlices < args.slices.length) ∧ error = .ProgramFailedToComplete := by
  have stops : args.rejected (canonical W c).maxHashSlices (canonical W c).checkAligned = true ↔
      args.unaligned (canonical W c).checkAligned = true ∨
        W.prof.maxHashSlices < args.slices.length := by
    rw [Sha256Args.rejected, Bool.or_eq_true, canonical_overLimit_iff]
    exact Or.comm
  rw [← stops]
  unfold sha256Run
  cases rejected : args.rejected (canonical W c).maxHashSlices (canonical W c).checkAligned with
  | true =>
    rw [Bool.cond_true]
    exact (canonical_fails_stop W c st .abort (Or.inl rfl) error).trans
      ⟨fun failed => ⟨rfl, failed⟩, fun ⟨_, failed⟩ => failed⟩
  | false =>
    rw [Bool.cond_false]
    refine (canonical_sha256_fails_iff W c st args.slices error).trans
      ⟨fun ⟨over, _⟩ => ?_, fun ⟨accepted, _⟩ => nomatch accepted⟩
    have within := ((canonical_rejected_eq_false_iff W c args).mp rejected).2
    omega

/-- An unaligned canonical `sol_sha256` call fails the instruction, as `abort` does, and has no
other outcome. -/
theorem canonical_sha256_unaligned_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (args : Sha256Args)
    (unaligned : args.unaligned (canonical W c).checkAligned = true)
    (outcome : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError) :
    sha256Run (canonical W c) st args outcome ↔ outcome = .terminated .ProgramFailedToComplete := by
  cases outcome with
  | returned answer st' =>
    refine ⟨fun returned => ?_, fun same => by cases same⟩
    have aligned := ((canonical_sha256_returned_iff W c st st' args answer).mp returned).1
    rw [unaligned] at aligned
    cases aligned
  | unwound reason _ => exact nomatch reason
  | terminated error =>
    refine (canonical_sha256_terminated_iff W c st args error).trans ?_
    exact ⟨fun ⟨_, failed⟩ => by rw [failed],
      fun same => by cases same; exact ⟨Or.inl unaligned, rfl⟩⟩

/-- A canonical `sol_sha256` return that the postcondition of the model admits is, for a call that
passes the alignment check and is within the slice limit, status `0` and the symbolic SHA-256 of
the concatenated slices, a 32-byte digest, with the state unchanged. -/
theorem canonical_sha256_post_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (args : Sha256Args) (answer : Solanalib.Runtime.SysAns) :
    (sha256Family.contract (canonical W c)).post st args (.returned answer st') ↔
      args.unaligned (canonical W c).checkAligned = false ∧
        args.slices.length ≤ W.prof.maxHashSlices ∧
        answer = ⟨0, [W.prims.sha256 args.slices.flatten]⟩ ∧
        (W.prims.sha256 args.slices.flatten).length = 32 ∧ st' = st := by
  constructor
  · rintro ⟨accepted, answered, _⟩
    obtain ⟨count, rfl, rfl⟩ :=
      (canonical_sha256_answer_iff W c st st' args.slices answer).mp answered
    exact ⟨((canonical_rejected_eq_false_iff W c args).mp accepted).1, count, rfl,
      W.prims.sha256_length _, rfl⟩
  · rintro ⟨aligned, count, rfl, _, unchanged⟩
    have answered :=
      (canonical_sha256_answer_iff W c st st' args.slices _).mpr ⟨count, rfl, unchanged⟩
    exact ⟨(canonical_rejected_eq_false_iff W c args).mpr ⟨aligned, count⟩, answered,
      (canonical W c).hashShape st args.slices _ st' answered⟩

/-- A canonical `sol_log_` call returns exactly for a UTF-8 message, and appends it to the
logs. -/
theorem canonical_log_returned_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (message : Solanalib.Runtime.Bytes) :
    logRun (canonical W c) st message (.returned () st') ↔
      W.prims.isUtf8 message = true ∧ st' = { st with logs := st.logs ++ [message] } := by
  constructor
  · rintro ⟨exit, source, mapped⟩
    cases exit with
    | returned answer after =>
      cases mapped
      obtain ⟨utf8, _, rfl⟩ := (canonical_log_answer_iff W c st _ message answer).mp source
      exact ⟨utf8, rfl⟩
    | unwound reason _ => exact nomatch reason
    | terminated reason => cases mapped
  · rintro ⟨utf8, rfl⟩
    exact ⟨.returned .ok0 _, (canonical_log_answer_iff W c st _ message _).mpr ⟨utf8, rfl, rfl⟩,
      rfl⟩

/-- The canonical runtime answers a log request exactly for a UTF-8 message. -/
theorem canonical_log_answered_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st
  : Solanalib.Runtime.InvState)
    (message : Solanalib.Runtime.Bytes) :
    Answered (canonical W c) st (.log message) ↔ W.prims.isUtf8 message = true := by
  constructor
  · rintro ⟨answer, after, answered⟩
    exact ((canonical_log_answer_iff W c st after message answer).mp answered).1
  · intro utf8
    exact ⟨.ok0, _, (canonical_log_answer_iff W c st _ message _).mpr ⟨utf8, rfl, rfl⟩⟩

/-- A canonical `sol_log_` call stops exactly for a message that is not UTF-8, with
`ProgramFailedToComplete`. -/
theorem canonical_log_terminated_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (message : Solanalib.Runtime.Bytes) (error :
      Solanalib.Runtime.InstrError) :
    logRun (canonical W c) st message (.terminated error) ↔
      W.prims.isUtf8 message = false ∧ error = .ProgramFailedToComplete := by
  constructor
  · rintro ⟨exit, source, mapped⟩
    cases exit with
    | returned _ _ => cases mapped
    | unwound reason _ => exact nomatch reason
    | terminated reason =>
      cases mapped
      exact (canonical_log_fails_iff W c st message error).mp source
  · intro failed
    exact ⟨.terminated error, (canonical_log_fails_iff W c st message error).mpr failed, rfl⟩

/-- A canonical `sol_panic_` call fails the instruction, and has no other outcome. -/
theorem canonical_panic_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (args : PanicArgs) (outcome : Outcome Solanalib.Runtime.InvState Empty Empty
      Solanalib.Runtime.InstrError) :
    panicFamilyRun (canonical W c) st args outcome ↔ outcome = .terminated .ProgramFailedToComplete
      := by
  cases outcome with
  | returned value _ => exact nomatch value
  | unwound reason _ => exact nomatch reason
  | terminated error =>
    refine (canonical_fails_stop W c st args.request
      (Or.inr ⟨args.file, args.line, args.column, rfl⟩) error).trans ?_
    exact ⟨fun h => by rw [h], fun h => by cases h; rfl⟩

/-- A canonical `abort` call fails the instruction, and has no other outcome. -/
theorem canonical_abort_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (st :
  Solanalib.Runtime.InvState)
    (outcome : Outcome Solanalib.Runtime.InvState Empty Empty Solanalib.Runtime.InstrError) :
    abortFamilyRun (canonical W c) st () outcome ↔ outcome = .terminated .ProgramFailedToComplete
      := by
  cases outcome with
  | returned value _ => exact nomatch value
  | unwound reason _ => exact nomatch reason
  | terminated error =>
    refine (canonical_fails_stop W c st .abort (Or.inl rfl) error).trans ?_
    exact ⟨fun h => by rw [h], fun h => by cases h; rfl⟩

/-! ## A sample environment -/

/-- A closed environment for the consistency witnesses: it logs each request, answers a hash
request with status `0` and 32 zero bytes, answers a log request with `0`, and stops on every
other request. It is not a SHA-256 implementation. -/
def sampleProvider :
    Callback.Run (List Solanalib.Runtime.SysReq) Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns
      Empty Unit :=
  Callback.ofFunction fun log request => match request with
    | .hash .sha256 _ => .returned ⟨0, [List.replicate 32 0]⟩ (log ++ [request])
    | .log _ => .returned .ok0 (log ++ [request])
    | _ => .terminated ()

/-- The sample environment. It checks alignment and allows at most
`Solanalib.Runtime.MAX_HASH_SLICES` slices,
the limit of Agave. -/
def sample : Index where
  State := List Solanalib.Runtime.SysReq
  Terminal := Unit
  provider := sampleProvider
  checkAligned := true
  maxHashSlices := some Solanalib.Runtime.MAX_HASH_SLICES
  hashShape := by
    intro log slices answer after answered
    cases answered
    decide

/-! ## `sol_sha512` -/

/-- A SHA-512 provider, its argument checks and its 64-byte output interpretation. -/
structure Sha512Index where
  State : Type
  Terminal : Type
  provider : Callback.Run State Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty Terminal
  checkAligned : Bool
  maxHashSlices : Option Nat
  hashShape : ∀ before slices answer after,
    provider before (.hash .sha512 slices) (.returned answer after) → OutputShape 64 answer

/-- SHA-512 has the same slice-descriptor layout and alignment check as SHA-256. -/
abbrev Sha512Args := Sha256Args

/-- Stop a rejected call before asking its hash request; otherwise retain the exit of the provider.
-/
def sha512Run (index : Sha512Index) :
    Callback.Run index.State Sha512Args Solanalib.Runtime.SysAns Empty index.Terminal :=
  fun before args => bif args.rejected index.maxHashSlices index.checkAligned then
    abortedWith index.provider before
  else index.provider before (.hash .sha512 args.slices)

/-- A SHA-512 return passes the argument checks and carries the 64-byte result of the provider. -/
def sha512Post (index : Sha512Index) (before : index.State) (args : Sha512Args) :
    Outcome index.State Solanalib.Runtime.SysAns Empty index.Terminal → Prop
  | .returned answer after =>
      args.rejected index.maxHashSlices index.checkAligned = false ∧
        index.provider before (.hash .sha512 args.slices) (.returned answer after) ∧
        OutputShape 64 answer
  | .unwound reason _ => nomatch reason
  | .terminated reason =>
      bif args.rejected index.maxHashSlices index.checkAligned then
        index.provider before .abort (.terminated reason)
      else index.provider before (.hash .sha512 args.slices) (.terminated reason)

/-- The raw `sol_sha512` contract, for every explicit environment. -/
def sha512Family : Family where
  Index := Sha512Index
  State := Sha512Index.State
  Args := fun _ => Sha512Args
  Value := fun _ => Solanalib.Runtime.SysAns
  Unwind := fun _ => Empty
  Terminal := Sha512Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := sha512Post index }

/-- The reference family for SHA-512. -/
def sha512FamilyRun : FamilyRun sha512Family := sha512Run

/-- The reference satisfies the contract at every index; the output law supplies the width. -/
theorem sha512Family_reference : FamilyReference sha512Family sha512FamilyRun := by
  intro index before args outcome _ execution
  have checked := checkedCall_reference index.provider before (.hash .sha512 args.slices)
    (args.rejected index.maxHashSlices index.checkAligned) (OutputShape 64)
    (index.hashShape before args.slices) outcome execution
  cases outcome with
  | returned _ _ => exact checked
  | unwound reason _ => exact nomatch reason
  | terminated _ => exact checked

/-- No return satisfies the postcondition when the count or checked alignment rejects the call. -/
theorem sha512Post_rejected {index : Sha512Index} {before : index.State} {args : Sha512Args}
    (rejected : args.rejected index.maxHashSlices index.checkAligned = true)
    (answer : Solanalib.Runtime.SysAns) (after : index.State) :
    ¬ sha512Post index before args (.returned answer after) := by
  rintro ⟨accepted, _⟩
  rw [rejected] at accepted
  cases accepted

/-! ## `sol_curve_multiscalar_mul` -/

/-- One scalar encoding and point encoding. Width is representation, not successful decoding. -/
structure MsmInput where
  scalar : Solanalib.Runtime.Bytes
  point : Solanalib.Runtime.Bytes
  scalar_width : scalar.length = 32
  point_width : point.length = 32

/-- The curve identifier and paired scalar/point encodings. Every 32-byte encoding is allowed. -/
structure MsmArgs where
  curve : Nat
  inputs : List MsmInput

/-- Scalar encodings in source order. -/
def MsmArgs.scalars (args : MsmArgs) : List Solanalib.Runtime.Bytes := args.inputs.map
  MsmInput.scalar

/-- Point encodings in source order. -/
def MsmArgs.points (args : MsmArgs) : List Solanalib.Runtime.Bytes := args.inputs.map MsmInput.point

/-- Edwards and Ristretto are the two supported multiscalar curves. -/
def MsmArgs.validCurve (args : MsmArgs) : Bool := args.curve == 0 || args.curve == 1

/-- The 512-element limit is checked before curve dispatch or input translation. -/
def MsmArgs.overLimit (args : MsmArgs) : Bool := decide (512 < args.inputs.length)

/-- The runtime request obtained from the paired encodings. -/
def MsmArgs.request (args : MsmArgs) : Solanalib.Runtime.SysReq :=
  .curveMultiscalarMul args.curve args.scalars args.points

@[simp] theorem MsmArgs.scalars_length (args : MsmArgs) :
    args.scalars.length = args.inputs.length := List.length_map _

@[simp] theorem MsmArgs.points_length (args : MsmArgs) :
    args.points.length = args.inputs.length := List.length_map _

/-- Pairing retains equal counts, rather than dropping a surplus input through `zip`. -/
theorem MsmArgs.equal_counts (args : MsmArgs) : args.scalars.length = args.points.length := by simp

/-- Every scalar passed to the primitive has the fixed-width encoding of the source. -/
theorem MsmArgs.scalars_width (args : MsmArgs) (scalar : Solanalib.Runtime.Bytes)
    (member : scalar ∈ args.scalars) : scalar.length = 32 := by
  obtain ⟨input, _, rfl⟩ := List.mem_map.mp member
  exact input.scalar_width

/-- Every point passed to the primitive has the fixed-width encoding of the source. -/
theorem MsmArgs.points_width (args : MsmArgs) (point : Solanalib.Runtime.Bytes)
    (member : point ∈ args.points) : point.length = 32 := by
  obtain ⟨input, _, rfl⟩ := List.mem_map.mp member
  exact input.point_width

/-- Multiscalar multiplication returns only `0` or `1`; only a supported curve can write output. -/
def MsmShape (args : MsmArgs) (answer : Solanalib.Runtime.SysAns) : Prop :=
  OutputShape 32 answer ∧ (answer.r0 = 0 ∨ answer.r0 = 1) ∧
    (answer.r0 = 0 → args.validCurve = true)

/-- A multiscalar provider and its output interpretation. No successful-decoding assumption is
required of the inputs. -/
structure MsmIndex where
  State : Type
  Terminal : Type
  provider : Callback.Run State Solanalib.Runtime.SysReq Solanalib.Runtime.SysAns Empty Terminal
  responseShape : ∀ before args answer after,
    provider before args.request (.returned answer after) → MsmShape args answer

/-- Reject the count first; all remaining outcomes come from the selected provider. -/
def msmRun (index : MsmIndex) :
    Callback.Run index.State MsmArgs Solanalib.Runtime.SysAns Empty index.Terminal :=
  fun before args => bif args.overLimit then abortedWith index.provider before
    else index.provider before args.request

/-- A returning call is within the count limit, and an invalid curve writes no output. -/
def msmPost (index : MsmIndex) (before : index.State) (args : MsmArgs) :
    Outcome index.State Solanalib.Runtime.SysAns Empty index.Terminal → Prop
  | .returned answer after =>
      args.overLimit = false ∧ index.provider before args.request (.returned answer after) ∧
        MsmShape args answer
  | .unwound reason _ => nomatch reason
  | .terminated reason =>
      bif args.overLimit then index.provider before .abort (.terminated reason)
      else index.provider before args.request (.terminated reason)

/-- The raw `sol_curve_multiscalar_mul` contract. -/
def msmFamily : Family where
  Index := MsmIndex
  State := MsmIndex.State
  Args := fun _ => MsmArgs
  Value := fun _ => Solanalib.Runtime.SysAns
  Unwind := fun _ => Empty
  Terminal := MsmIndex.Terminal
  contract := fun index => { requires := fun _ _ => True, post := msmPost index }

/-- The reference family for multiscalar multiplication. -/
def msmFamilyRun : FamilyRun msmFamily := msmRun

/-- The reference satisfies the contract at every index, using its complete response law. -/
theorem msmFamily_reference : FamilyReference msmFamily msmFamilyRun := by
  intro index before args outcome _ execution
  have checked := checkedCall_reference index.provider before args.request args.overLimit
    (MsmShape args) (index.responseShape before args) outcome execution
  cases outcome with
  | returned _ _ => exact checked
  | unwound reason _ => exact nomatch reason
  | terminated _ => exact checked

/-- The count check rules out a return independently of the behavior of the provider. -/
theorem msmPost_overLimit {index : MsmIndex} {before : index.State} {args : MsmArgs}
    (over : args.overLimit = true) (answer : Solanalib.Runtime.SysAns) (after : index.State) :
    ¬ msmPost index before args (.returned answer after) := by
  rintro ⟨accepted, _⟩
  rw [over] at accepted
  cases accepted

/-- An invalid curve has no output on any permitted return, at every index. -/
theorem msmPost_invalid {index : MsmIndex} {before : index.State} {args : MsmArgs}
    (invalid : args.validCurve = false) {answer : Solanalib.Runtime.SysAns} {after : index.State}
    (post : msmPost index before args (.returned answer after)) :
    answer.r0 = 1 ∧ answer.out = [] := by
  obtain ⟨_, _, shape, status, valid⟩ := post
  have nonzero : answer.r0 ≠ 0 := by
    intro zero
    have accepted := valid zero
    rw [invalid] at accepted
    cases accepted
  exact ⟨status.resolve_left nonzero, shape.2.2 nonzero⟩

/-! ## Canonical SHA-512 -/

/-- A canonical hash return requires registration and the slice limit; it preserves state. -/
theorem canonicalProvider_sha512_answer_iff (W : Solanalib.Runtime.World) (c :
  Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (slices : List Solanalib.Runtime.Bytes) (answer :
      Solanalib.Runtime.SysAns) :
    canonicalProvider W c st (.hash .sha512 slices) (.returned answer st') ↔
      (.hash .sha512 slices : Solanalib.Runtime.SysReq).registered W.prof = true ∧
        slices.length ≤ W.prof.maxHashSlices ∧ answer = ⟨0, [W.prims.sha512 slices]⟩ ∧ st' = st :=
          by
  change Solanalib.Runtime.Env W c st (.hash .sha512 slices) answer st' ↔ _
  constructor
  · rintro ⟨registered, _, ⟨_, h⟩ | ⟨h, _⟩⟩
    · by_cases over : W.prof.maxHashSlices < slices.length
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_true,
        reduceCtorEq] at h
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_false,
        Except.ok.injEq,
          Prod.mk.injEq] at h
        exact ⟨registered, Nat.le_of_not_lt over, h.1.symm, h.2.symm⟩
    · cases h
  · rintro ⟨registered, count, rfl, rfl⟩
    refine ⟨registered, (fun _ h => by cases h), Or.inl ⟨(fun h => by cases h), ?_⟩⟩
    simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply_ok _ _ _ count]

/-- An unregistered SHA-512 request or an excessive slice count terminates the canonical call. -/
theorem canonicalProvider_sha512_fails_iff (W : Solanalib.Runtime.World) (c :
  Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (slices : List Solanalib.Runtime.Bytes) (error :
      Solanalib.Runtime.InstrError) :
    canonicalProvider W c st (.hash .sha512 slices) (.terminated error) ↔
      ((.hash .sha512 slices : Solanalib.Runtime.SysReq).registered W.prof = false ∨
        W.prof.maxHashSlices < slices.length) ∧ error = .ProgramFailedToComplete := by
  change Fails W c st (.hash .sha512 slices) error ↔ _
  constructor
  · rintro (⟨_, _, _, h⟩ | ⟨unregistered, failed⟩)
    · by_cases over : W.prof.maxHashSlices < slices.length
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_true,
        Except.error.injEq] at h
        exact ⟨Or.inr over, h.symm⟩
      · simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_false,
        reduceCtorEq] at h
    · exact ⟨Or.inl unregistered, failed⟩
  · rintro ⟨unregistered | over, rfl⟩
    · exact Or.inr ⟨unregistered, rfl⟩
    · cases registered : (.hash .sha512 slices : Solanalib.Runtime.SysReq).registered W.prof with
      | false => exact Or.inr ⟨registered, rfl⟩
      | true =>
        refine Or.inl ⟨registered, (fun _ h => by cases h), (fun h => by cases h), ?_⟩
        simp only [Solanalib.Runtime.sysStep, Solanalib.Runtime.hashReply, over, ite_true]

/-- The canonical SHA-512 interpretation. Its width is already a law of `Solanalib.Runtime.Prims`.
-/
def canonicalSha512 (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) : Sha512Index where
  State := Solanalib.Runtime.InvState
  Terminal := Solanalib.Runtime.InstrError
  provider := canonicalProvider W c
  checkAligned := c.abi.checkAligned
  maxHashSlices := some W.prof.maxHashSlices
  hashShape := by
    intro st slices answer st' answered
    obtain ⟨_, _, rfl, _⟩ :=
      (canonicalProvider_sha512_answer_iff W c st st' slices answer).mp answered
    exact ⟨by simp [Solanalib.Runtime.U64_LIMIT], fun _ => ⟨_, rfl, W.prims.sha512_length _⟩,
      fun nonzero => (nonzero rfl).elim⟩

/-- Passing the canonical count and alignment checks is exactly being within the limit and
passing the ABI-dependent alignment test. -/
theorem canonical_sha512_accepted_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
  (args : Sha512Args) :
    args.rejected (canonicalSha512 W c).maxHashSlices (canonicalSha512 W c).checkAligned = false ↔
      args.unaligned c.abi.checkAligned = false ∧ args.slices.length ≤ W.prof.maxHashSlices := by
  simpa only [canonicalSha512, canonical] using
    canonical_rejected_eq_false_iff W c args

/-- A canonical return has status zero and the exact symbolic SHA-512 result, with unchanged state.
-/
theorem canonical_sha512_returned_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (args : Sha512Args) (answer : Solanalib.Runtime.SysAns) :
    sha512Run (canonicalSha512 W c) st args (.returned answer st') ↔
      args.unaligned c.abi.checkAligned = false ∧
        (.hash .sha512 args.slices : Solanalib.Runtime.SysReq).registered W.prof = true ∧
        args.slices.length ≤ W.prof.maxHashSlices ∧
        answer = ⟨0, [W.prims.sha512 args.slices]⟩ ∧ st' = st := by
  unfold sha512Run
  cases rejected : args.rejected (canonicalSha512 W c).maxHashSlices
      (canonicalSha512 W c).checkAligned with
  | true =>
    rw [Bool.cond_true]
    constructor
    · exact False.elim
    · rintro ⟨aligned, _, count, _⟩
      have accepted := (canonical_sha512_accepted_iff W c args).mpr ⟨aligned, count⟩
      rw [rejected] at accepted
      cases accepted
  | false =>
    rw [Bool.cond_false]
    have aligned := ((canonical_sha512_accepted_iff W c args).mp rejected).1
    exact (canonicalProvider_sha512_answer_iff W c st st' args.slices answer).trans
      ⟨fun answered => ⟨aligned, answered⟩, fun ⟨_, answered⟩ => answered⟩

/-- Registration, count or checked alignment failure terminates the canonical hash call. -/
theorem canonical_sha512_terminated_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (args : Sha512Args) (error : Solanalib.Runtime.InstrError) :
    sha512Run (canonicalSha512 W c) st args (.terminated error) ↔
      (args.rejected (canonicalSha512 W c).maxHashSlices
        (canonicalSha512 W c).checkAligned = true ∨
        (.hash .sha512 args.slices : Solanalib.Runtime.SysReq).registered W.prof = false) ∧
      error = .ProgramFailedToComplete := by
  unfold sha512Run
  cases rejected : args.rejected (canonicalSha512 W c).maxHashSlices
      (canonicalSha512 W c).checkAligned with
  | true =>
    rw [Bool.cond_true]
    simpa only [true_or, true_and, abortedWith, canonicalSha512,
      canonical] using
      canonical_fails_stop W c st .abort (Or.inl rfl) error
  | false =>
    rw [Bool.cond_false]
    have within := ((canonical_sha512_accepted_iff W c args).mp rejected).2
    have notOver : ¬ W.prof.maxHashSlices < args.slices.length := Nat.not_lt_of_ge within
    simpa only [Bool.false_eq_true, false_or, notOver, or_false, canonicalSha512] using
      canonicalProvider_sha512_fails_iff W c st args.slices error

/-- The canonical postcondition exposes the symbolic digest and its 64-byte width. -/
theorem canonical_sha512_post_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (args : Sha512Args) (answer : Solanalib.Runtime.SysAns) :
    sha512Post (canonicalSha512 W c) st args (.returned answer st') ↔
      args.unaligned c.abi.checkAligned = false ∧
        (.hash .sha512 args.slices : Solanalib.Runtime.SysReq).registered W.prof = true ∧
        args.slices.length ≤ W.prof.maxHashSlices ∧
        answer = ⟨0, [W.prims.sha512 args.slices]⟩ ∧
        (W.prims.sha512 args.slices).length = 64 ∧ st' = st := by
  constructor
  · rintro ⟨accepted, answered, _⟩
    obtain ⟨registered, count, rfl, rfl⟩ :=
      (canonicalProvider_sha512_answer_iff W c st st' args.slices answer).mp answered
    exact ⟨((canonical_sha512_accepted_iff W c args).mp accepted).1, registered, count,
      rfl, W.prims.sha512_length _, rfl⟩
  · rintro ⟨aligned, registered, count, rfl, _, unchanged⟩
    have answered := (canonicalProvider_sha512_answer_iff W c st st' args.slices _).mpr
      ⟨registered, count, rfl, unchanged⟩
    exact ⟨(canonical_sha512_accepted_iff W c args).mpr ⟨aligned, count⟩, answered,
      (canonicalSha512 W c).hashShape st args.slices _ st' answered⟩

/-! ## Canonical multiscalar multiplication -/

/-- The only additional primitive law: a successful supported operation on paired fixed-width
inputs within the count limit of the source produces one encoded 32-byte point. -/
def MsmWidth (prims : Solanalib.Runtime.Prims) : Prop :=
  ∀ args : MsmArgs, args.inputs.length ≤ 512 → args.validCurve = true →
    ∀ output, prims.curveMultiscalarMul args.curve args.scalars args.points = some output →
      output.length = 32

/-- Canonical ordinary answers after the count check. Invalid curves never consult the primitive. -/
def MsmAnswer (W : Solanalib.Runtime.World) (args : MsmArgs) (answer : Solanalib.Runtime.SysAns) :
  Prop :=
  bif args.validCurve then
    answer = match W.prims.curveMultiscalarMul args.curve args.scalars args.points with
      | some output => ⟨0, [output]⟩
      | none => ⟨1, []⟩
  else W.prof.features.abortOnInvalidCurve = false ∧ answer = ⟨1, []⟩

/-- The complete ordinary result of the canonical provider: registration, count, curve/decoding
outcome and unchanged invocation state. -/
theorem canonicalProvider_msm_answer_iff (W : Solanalib.Runtime.World) (c :
  Solanalib.Runtime.InvCtx)
    (st st' : Solanalib.Runtime.InvState) (args : MsmArgs) (answer : Solanalib.Runtime.SysAns) :
    canonicalProvider W c st args.request (.returned answer st') ↔
      W.prof.features.curve25519Syscalls = true ∧ args.inputs.length ≤ 512 ∧
        MsmAnswer W args answer ∧ st' = st := by
  have step : Solanalib.Runtime.sysStep W.prof W.prims W.sysvars W.epochStake c st args.request =
      .ok (answer, st') ↔ args.inputs.length ≤ 512 ∧ MsmAnswer W args answer ∧ st' = st := by
    simp only [MsmArgs.request, Solanalib.Runtime.sysStep, MsmArgs.scalars_length]
    change ((if 512 < args.inputs.length then .error .ProgramFailedToComplete
      else if !args.validCurve then _ else _) : Except Solanalib.Runtime.InstrError
        (Solanalib.Runtime.SysAns × Solanalib.Runtime.InvState)) =
      .ok (answer, st') ↔ _
    unfold MsmAnswer
    by_cases over : 512 < args.inputs.length
    · simp only [over, ite_true, reduceCtorEq, Nat.not_le_of_gt over, false_and]
    · have count := Nat.le_of_not_lt over
      cases valid : args.validCurve with
      | false =>
        cases aborting : W.prof.features.abortOnInvalidCurve <;>
          simp only [over, ite_false, count, true_and, Bool.not_false,
            ite_true, Bool.false_eq_true, Bool.cond_false, reduceCtorEq,
            Except.ok.injEq, Prod.mk.injEq, false_and, eq_comm]
      | true =>
        cases result : W.prims.curveMultiscalarMul args.curve args.scalars args.points <;>
          simp only [over, ite_false, count, true_and, Bool.not_true, Bool.false_eq_true,
            Bool.cond_true, Except.ok.injEq, Prod.mk.injEq, eq_comm]
  change Solanalib.Runtime.Env W c st args.request answer st' ↔ _
  constructor
  · rintro ⟨registered, _, ⟨_, result⟩ | ⟨impossible, _⟩⟩
    · exact ⟨registered, step.mp result⟩
    · cases impossible
  · rintro ⟨registered, result⟩
    exact ⟨registered, (fun _ h => by cases h), Or.inl ⟨(fun h => by cases h), step.mpr result⟩⟩

/-- The provider fails on missing registration, excessive count or an invalid curve under the
abort feature. Decoding failure is an ordinary status `1`, not a terminal error. -/
theorem canonicalProvider_msm_fails_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (st : Solanalib.Runtime.InvState) (args : MsmArgs) (error : Solanalib.Runtime.InstrError) :
    canonicalProvider W c st args.request (.terminated error) ↔
      (W.prof.features.curve25519Syscalls = false ∨ 512 < args.inputs.length ∨
        (args.validCurve = false ∧ W.prof.features.abortOnInvalidCurve = true)) ∧
      error = .ProgramFailedToComplete := by
  have step : Solanalib.Runtime.sysStep W.prof W.prims W.sysvars W.epochStake c st args.request =
      .error error ↔ (512 < args.inputs.length ∨
        (args.validCurve = false ∧ W.prof.features.abortOnInvalidCurve = true)) ∧
      error = .ProgramFailedToComplete := by
    simp only [MsmArgs.request, Solanalib.Runtime.sysStep, MsmArgs.scalars_length]
    change ((if 512 < args.inputs.length then .error .ProgramFailedToComplete
      else if !args.validCurve then _ else _) : Except Solanalib.Runtime.InstrError
        (Solanalib.Runtime.SysAns × Solanalib.Runtime.InvState)) =
      .error error ↔ _
    by_cases over : 512 < args.inputs.length
    · simp only [over, ite_true, true_or, true_and, Except.error.injEq, eq_comm]
    · cases valid : args.validCurve with
      | false =>
        cases aborting : W.prof.features.abortOnInvalidCurve <;>
          simp only [over, ite_false, Bool.not_false, ite_true,
            Bool.false_eq_true, reduceCtorEq, false_or, true_and,
            false_and, Except.error.injEq, eq_comm]
      | true =>
        cases result : W.prims.curveMultiscalarMul args.curve args.scalars args.points <;>
          simp only [over, ite_false, Bool.not_true, Bool.false_eq_true,
            Bool.true_eq_false, false_or, false_and, reduceCtorEq]
  change Fails W c st args.request error ↔ _
  constructor
  · rintro (⟨_, _, _, failed⟩ | ⟨unregistered, failed⟩)
    · obtain ⟨reason, same⟩ := step.mp failed
      exact ⟨Or.inr reason, same⟩
    · exact ⟨Or.inl unregistered, failed⟩
  · rintro ⟨unregistered | reason, same⟩
    · exact Or.inr ⟨unregistered, same⟩
    · cases registered : W.prof.features.curve25519Syscalls with
      | false => exact Or.inr ⟨registered, same⟩
      | true => exact Or.inl ⟨registered, (fun _ h => by cases h), (fun h => by cases h),
          step.mpr ⟨reason, same⟩⟩

/-- Canonical multiscalar multiplication, with the scoped point-width interpretation. -/
def canonicalMsm (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx) (width : MsmWidth
  W.prims) : MsmIndex where
  State := Solanalib.Runtime.InvState
  Terminal := Solanalib.Runtime.InstrError
  provider := canonicalProvider W c
  responseShape := by
    intro st args answer st' answered
    obtain ⟨_, count, result, _⟩ :=
      (canonicalProvider_msm_answer_iff W c st st' args answer).mp answered
    cases valid : args.validCurve with
    | false =>
      obtain ⟨_, rfl⟩ : W.prof.features.abortOnInvalidCurve = false ∧ answer = ⟨1, []⟩ := by
        simpa only [MsmAnswer, valid, Bool.cond_false] using result
      exact ⟨by decide, Or.inr rfl, fun zero => by cases zero⟩
    | true =>
      have result' : answer = match W.prims.curveMultiscalarMul args.curve args.scalars args.points
        with
          | some output => ⟨0, [output]⟩ | none => ⟨1, []⟩ := by
        simpa only [MsmAnswer, valid, Bool.cond_true] using result
      cases computed : W.prims.curveMultiscalarMul args.curve args.scalars args.points with
      | none =>
        simp only [computed] at result'
        subst answer
        exact ⟨by decide, Or.inr rfl, fun zero => by cases zero⟩
      | some output =>
        simp only [computed] at result'
        subst answer
        exact ⟨⟨by simp [Solanalib.Runtime.U64_LIMIT], fun _ => ⟨output, rfl, width args count
          valid output computed⟩,
          fun nonzero => (nonzero rfl).elim⟩, Or.inl rfl, fun _ => valid⟩

/-- The count guard and provider of the call agree, so the complete canonical result is unchanged.
-/
theorem canonical_msm_returned_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st st' : Solanalib.Runtime.InvState) (args : MsmArgs) (answer :
      Solanalib.Runtime.SysAns) :
    msmRun (canonicalMsm W c width) st args (.returned answer st') ↔
      W.prof.features.curve25519Syscalls = true ∧ args.inputs.length ≤ 512 ∧
        MsmAnswer W args answer ∧ st' = st := by
  unfold msmRun
  cases rejected : args.overLimit with
  | true =>
    rw [Bool.cond_true]
    have over : 512 < args.inputs.length := by simpa [MsmArgs.overLimit] using rejected
    exact ⟨False.elim, fun ⟨_, count, _⟩ => (Nat.not_lt_of_ge count over).elim⟩
  | false =>
    rw [Bool.cond_false]
    exact canonicalProvider_msm_answer_iff W c st st' args answer

/-- The canonical postcondition retains exactly the ordinary result, with its proved output law. -/
theorem canonical_msm_post_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st st' : Solanalib.Runtime.InvState) (args : MsmArgs) (answer :
      Solanalib.Runtime.SysAns) :
    msmPost (canonicalMsm W c width) st args (.returned answer st') ↔
      W.prof.features.curve25519Syscalls = true ∧ args.inputs.length ≤ 512 ∧
        MsmAnswer W args answer ∧ st' = st := by
  constructor
  · rintro ⟨_, answered, _⟩
    exact (canonicalProvider_msm_answer_iff W c st st' args answer).mp answered
  · intro result
    have answered := (canonicalProvider_msm_answer_iff W c st st' args answer).mpr result
    exact ⟨by simp [MsmArgs.overLimit, Nat.not_lt_of_ge result.2.1], answered,
      (canonicalMsm W c width).responseShape st args answer st' answered⟩

/-- The count guard precedes curve dispatch, and all canonical terminal reasons are preserved. -/
theorem canonical_msm_terminated_iff (W : Solanalib.Runtime.World) (c : Solanalib.Runtime.InvCtx)
    (width : MsmWidth W.prims) (st : Solanalib.Runtime.InvState) (args : MsmArgs) (error :
      Solanalib.Runtime.InstrError) :
    msmRun (canonicalMsm W c width) st args (.terminated error) ↔
      (W.prof.features.curve25519Syscalls = false ∨ 512 < args.inputs.length ∨
        (args.validCurve = false ∧ W.prof.features.abortOnInvalidCurve = true)) ∧
      error = .ProgramFailedToComplete := by
  unfold msmRun
  cases rejected : args.overLimit with
  | true =>
    rw [Bool.cond_true]
    have over : 512 < args.inputs.length := by simpa [MsmArgs.overLimit] using rejected
    simpa only [over, true_or, or_true, true_and, abortedWith, canonicalMsm,
      canonical] using
      canonical_fails_stop W c st .abort (Or.inl rfl) error
  | false =>
    rw [Bool.cond_false]
    exact canonicalProvider_msm_fails_iff W c st args error

/-! ## Explicit consistency samples -/

/-- A closed sample logs each hash request and returns 64 zero bytes. It is not SHA-512. -/
def sha512Sample : Sha512Index where
  State := List Solanalib.Runtime.SysReq
  Terminal := Unit
  provider := Callback.ofFunction fun log request => match request with
    | .hash .sha512 _ => .returned ⟨0, [List.replicate 64 0]⟩ (log ++ [request])
    | _ => .terminated ()
  checkAligned := true
  maxHashSlices := some Solanalib.Runtime.MAX_HASH_SLICES
  hashShape := by
    intro _ _ _ _ answered
    cases answered
    decide

/-- A closed sample logs requests, answers supported curves with 32 zero bytes and rejects every
other curve with status `1`. It is a consistency interpretation, not curve arithmetic. -/
def msmSample : MsmIndex where
  State := List Solanalib.Runtime.SysReq
  Terminal := Unit
  provider := Callback.ofFunction fun log request => match request with
    | .curveMultiscalarMul curve _ _ =>
        if curve == 0 || curve == 1 then
          .returned ⟨0, [List.replicate 32 0]⟩ (log ++ [request])
        else .returned ⟨1, []⟩ (log ++ [request])
    | _ => .terminated ()
  responseShape := by
    intro _ args answer _ answered
    change (if args.validCurve then _ else _) = _ at answered
    split at answered
    · cases answered
      exact ⟨by decide, Or.inl rfl, fun _ => by assumption⟩
    · cases answered
      exact ⟨by decide, Or.inr rfl, fun zero => by cases zero⟩

/-- A fixed-width pair for the sample execution; no claim of successful decoding is made. -/
def sampleInput : MsmInput := ⟨List.replicate 32 1, List.replicate 32 2, by simp, by simp⟩

end Solanalib.Specs.Core.RawSyscall
