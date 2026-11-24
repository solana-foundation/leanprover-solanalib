/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Syscalls
import Solanalib.Specs.SolanaDefineSyscall.Definitions

/-!
# Raw syscall declarations over the shared test shim

The request-level models of `sol_sha256`, `sol_log_`, `sol_panic_` and `abort` from
solana-define-syscall 5.1.0 (`Solanalib.Specs.Core.RawSyscall`) ask the syscall environment of
their index, a provider over `Solanalib.Runtime.SysReq` and `Solanalib.Runtime.SysAns`, and
return its answer. The checker instantiates that provider with the behavior of the shim as a
function of the shim state (`Syscalls.ShimState`), so the decided relation is the registered
reference at that index (`rawIndex`):

* `.hash .sha256 slices`: the request is logged as the shim logs it, then the next reply, which
  must answer `sol_sha256`, gives the answer `⟨status, [data]⟩` on status `0` and `⟨status, []⟩`
  otherwise (`hashReplyAnswer`); a reply marked `terminate` ends the run with reason
  `sol_sha256`, and so does a reply outside the hash shape, a status of 2^64 or more or status
  `0` without exactly 32 bytes, with the detail `reply outside the hash shape` (`hashOutcome`);
* `.log message`: the request is logged, no reply is consumed, and the answer is `.ok0`;
* `.panic file line column` and `.abort`: the terminal exits of the shim, reasons `sol_panic_`
  and `abort`, with the detail the shim records (the bytes of the file, the line and the column
  for `sol_panic_`, `null` for `abort`) and no request logged;
* the 5.2.0 declarations `sol_sha512` and `sol_curve_multiscalar_mul` use the same provider and
  reply queue, with the 64-byte and curve-specific output checks described below;
* any other request ends the run with reason `shim` (no record has one).

A recorded `sol_sha256` return carries the status and the 32-byte result buffer after the call,
which started with a recorded pattern (`hash_result` in the arguments). It is read as the answer
`⟨status, [buffer]⟩` on status `0` and `⟨status, []⟩` otherwise; a buffer changed under a
nonzero status is no answer of the hash shape, and the record is rejected.

No recorded `sol_sha256` script has a reply outside the hash shape: `rust/shim` holds a status
as a `u64`, and those scripts give 32 bytes with status `0` and none with another status. The
reference ends the run on such a reply so that its answers satisfy the index law `hashShape`
(`rawIndex_hashShape`), not because a shim does:

* the shim of the driver, `rust/shim`, copies `min(len, 32)` of the bytes of the reply to
  `hash_result` and returns its status (`hasher!`), so after a status-`0` reply of 16 bytes the
  other 16 bytes of the buffer are those it held;
* a separate source execution binding must establish representable status words and the complete
  32-byte digest on status `0`, rejecting malformed provider replies under its selected
  protocol.

The reference reads a nonzero status with bytes as `⟨status, []⟩`, which has the hash shape, and
ignores the bytes. On such a reply `rust/shim` copies them to `hash_result`, where a buffer
changed under a nonzero status is rejected, and a source execution binding must reject that
case. No script has one either.

So `sol_sha256` has no precondition. `rawIndex` sets `checkAligned`, under which a call with a
slice at an unaligned `vals` stops without asking (`Sha256Args.unaligned`). The checker reads
every record as aligned, `⟨slices, true⟩`: the driver passes the descriptors as a `&[&[u8]]`,
which is 8-aligned by its type, and the records carry no `vals` address. So conformance does not
exercise the unaligned branch, on which Agave aborts and the descriptor reads of the native shim
are undefined behavior. `rawIndex` sets no slice limit (`maxHashSlices := none`), since neither
shim checks the count: every record is within the limit of Agave
(`Solanalib.Runtime.MAX_HASH_SLICES`) anyway, so conformance does not exercise the branch beyond
the limit (`Sha256Args.overLimit`), on which Agave aborts before it asks. `sol_log_` has no
precondition either: a message that the provider does not answer only stops, and the shim
answers every one.

The SHA-512 driver records aligned Rust slice descriptors and checks a 64-byte output. No native
unaligned descriptor is read. Multiscalar multiplication records paired 32-byte encodings;
zero-length inputs, invalid curves and counts above 512 pass null input pointers. Counts above
512 also pass a null output pointer and terminate before any request. Invalid curves log no
input bytes and either return 1 without a write or terminate, as scripted. These observations do
not establish memory translation or the cryptographic implementation of Agave.

For those two declarations, the result includes two eight-byte guards around the output buffer.
The checker compares both guards, the output, status, consumed replies, logged requests and
terminal details. A nonzero status must leave the output unchanged. Wrong reply widths, bytes on
failure and successful replies for an invalid curve are harness faults, not program executions. -/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.Runtime.RawSyscalls

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.RawSyscall (OutputShape MsmArgs MsmShape Sha512Index MsmIndex msmRun)
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Syscalls (ShimState ShimTerminal Logged
  answer logOnly shimState
  shimStateJson shimTerminalJson parseShimOutcome detailText fieldsOf unitOutcomeJson)
open Solanalib.Specs.SolanaDefineSyscall.definitions
open Solanalib.Specs.SolanaDefineSyscall.definitions

/-! ## The shim as a syscall environment -/

/-- The detail the shim records for `sol_panic_`: the bytes of the file, the line and the column. -/
def panicDetail (file : Solanalib.Runtime.Bytes) (line column : Nat) : String :=
  detailText (Json.mkObj [("file", bytesJson file), ("line", natJson line), ("column", natJson
    column)])

/-- The answer that a `sol_sha256` reply carries when it has the hash shape: status `0` with its 32
bytes, or another `u64` status with no bytes. -/
def hashReplyAnswer (r : Runtime.Reply) : Option Solanalib.Runtime.SysAns :=
  if r.ret < Solanalib.Runtime.U64_LIMIT ∧ (r.ret = 0 → r.data.length = 32) then
    some ⟨r.ret, if r.ret = 0 then [r.data] else []⟩
  else none

/-- An answer that `hashReplyAnswer` reads has the hash shape. -/
theorem hashReplyAnswer_shape {r : Runtime.Reply} {a : Solanalib.Runtime.SysAns}
    (read : hashReplyAnswer r = some a) : RawSyscall.HashShape a := by
  unfold hashReplyAnswer at read
  split at read
  · next shaped =>
    cases read
    obtain ⟨bound, width⟩ := shaped
    refine ⟨bound, fun zero => ?_, fun nonzero => ?_⟩
    · change r.ret = 0 at zero
      exact ⟨r.data, by simp [zero], width zero⟩
    · change r.ret ≠ 0 at nonzero
      simp [nonzero]
  · cases read

/-- A value that `answer` returns is the reading of a reply. -/
theorem answer_returned {R : Type} {s : ShimState} {request : Syscalls.Logged} {syscall : String}
    {reply : Runtime.Reply → R} {v : R} {after : ShimState}
    (returned : answer s request syscall reply = .returned v after) : ∃ r, reply r = v := by
  unfold answer at returned
  split at returned
  · split at returned
    · split at returned
      · cases returned
      · cases returned
        exact ⟨_, rfl⟩
    · cases returned
  · cases returned

/-- An outcome of a call that returns an answer, over the shim state. -/
abbrev AnswerOutcome := Outcome ShimState Solanalib.Runtime.SysAns Empty ShimTerminal

/-- The output bytes of a reply belong to the answer only on status zero. -/
def replyAnswer (reply : Runtime.Reply) : Solanalib.Runtime.SysAns :=
  ⟨reply.ret, if reply.ret = 0 then [reply.data] else []⟩

/-- The native harness faults on shape violations, including bytes on a failure reply. -/
def readReply (shape : Solanalib.Runtime.SysAns → Prop) [DecidablePred shape] (reply :
  Runtime.Reply) :
    Option Solanalib.Runtime.SysAns :=
  if shape (replyAnswer reply) ∧ (reply.ret ≠ 0 → reply.data = []) then
    some (replyAnswer reply)
  else none

theorem readReply_shape {shape : Solanalib.Runtime.SysAns → Prop} [DecidablePred shape]
    {reply : Runtime.Reply} {answer : Solanalib.Runtime.SysAns}
    (read : readReply shape reply = some answer) : shape answer := by
  unfold readReply at read
  split at read
  · next valid => cases read; exact valid.1
  · cases read

instance (curve : Nat) (answer : Solanalib.Runtime.SysAns) : Decidable (MsmShape ⟨curve, []⟩
  answer) := by
  unfold MsmShape
  infer_instance

/-- Read a raw output call through the shared reply queue, retaining its invalid-reply detail. -/
def checkedAnswer (before : ShimState) (request : Logged) (name : String)
    (decode : Runtime.Reply → Option Solanalib.Runtime.SysAns) (invalidReason invalidDetail :
      String) : AnswerOutcome :=
  match Syscalls.answer before request name decode with
  | .returned (some answer) after => .returned answer after
  | .returned none after => .terminated ⟨invalidReason, invalidDetail, after⟩
  | .unwound reason _ => nomatch reason
  | .terminated terminal => .terminated terminal

theorem checkedAnswer_returned {before : ShimState} {request : Logged} {name : String}
    {decode : Runtime.Reply → Option Solanalib.Runtime.SysAns} {invalidReason invalidDetail :
      String}
    {answer : Solanalib.Runtime.SysAns} {after : ShimState}
    (returned : checkedAnswer before request name decode invalidReason invalidDetail =
      .returned answer after) : ∃ reply, decode reply = some answer := by
  unfold checkedAnswer at returned
  split at returned
  · next read =>
    cases returned
    exact answer_returned read
  · cases returned
  · next reason _ _ => exact reason.elim
  · cases returned

/-- The outcome of the reference for a SHA-256 request. The invalid-reply detail is retained for
existing recordings and their controls; see the comparison of the module with the native shim. -/
def hashOutcome (s : ShimState) (slices : List Solanalib.Runtime.Bytes) : AnswerOutcome :=
  checkedAnswer s (.sha256 slices slices.length) "sol_sha256" hashReplyAnswer
    "sol_sha256" "reply outside the hash shape"

/-- The answers and terminal exits of the shared shim for the registered raw syscall requests. -/
def provider (s : ShimState) : Solanalib.Runtime.SysReq → AnswerOutcome
  | .hash .sha256 slices => hashOutcome s slices
  | .hash .sha512 slices =>
      checkedAnswer s (.sha512 slices) "sol_sha512" (readReply (OutputShape 64))
        "shim-fault" "reply outside the output shape"
  | .curveMultiscalarMul curve scalars points =>
      let valid := curve == 0 || curve == 1
      checkedAnswer s (.msm curve scalars.length (if valid then scalars else [])
        (if valid then points else [])) "sol_curve_multiscalar_mul"
        (readReply (MsmShape ⟨curve, []⟩)) "shim-fault" "reply outside the output shape"
  | .log message => Outcome.map (fun () => Solanalib.Runtime.SysAns.ok0) (logOnly s (.log message))
  | .panic file line column => .terminated ⟨"sol_panic_", panicDetail file line column, s⟩
  | .abort => .terminated ⟨"abort", detailText Json.null, s⟩
  | _ => .terminated ⟨"shim", "unexpected request", s⟩

/-- The answers of `provider` to a SHA-256 request have the hash shape. -/
theorem rawIndex_hashShape (before : ShimState) (slices : List Solanalib.Runtime.Bytes) (a :
  Solanalib.Runtime.SysAns)
    (after : ShimState) (returned : provider before (.hash .sha256 slices) = .returned a after) :
    RawSyscall.HashShape a := by
  obtain ⟨_, shaped⟩ := checkedAnswer_returned returned
  exact hashReplyAnswer_shape shaped

/-- The family index of the four models: the shim state, its terminal exits and the graph of
`provider`. It checks alignment (`checkAligned`); the driver passes 8-aligned descriptors. It sets
no slice limit, as the shims check none. -/
def rawIndex : RawSyscall.Index where
  State := ShimState
  Terminal := ShimTerminal
  provider := Callback.ofFunction provider
  checkAligned := true
  maxHashSlices := none
  hashShape := rawIndex_hashShape

/-! ## `sol_sha256` -/

/-- At `rawIndex`, the `sol_sha256` reference at an 8-aligned `vals`, `⟨slices, true⟩`, as the
checker reads every record, is the graph of `provider` at the hash request. The unaligned branch
is not exercised: no record carries a `vals` address. `rawIndex` sets no slice limit, so no call is
beyond it. -/
theorem sha256_graph (before : ShimState) (slices : List Solanalib.Runtime.Bytes) (o :
  AnswerOutcome) :
    sol_sha256_run rawIndex before ⟨slices, true⟩ o ↔ provider before (.hash .sha256 slices) = o :=
  Iff.rfl

/-- A recorded result: the status and the result buffer after the call. -/
def hashResult (j : Json) : Result (Nat × Solanalib.Runtime.Bytes) := do
  pure (← asUInt 64 (← field j "status"), (← bytesN 32 (← field j "hash_result")).val)

/-- The answer a recorded `sol_sha256` exit carries: the buffer after the call on status `0`, no
bytes on another status. A buffer changed under a nonzero status is no answer of the hash shape
(`none`: the record is rejected). -/
def hashAnswer (initial : Solanalib.Runtime.Bytes) :
    Outcome ShimState (Nat × Solanalib.Runtime.Bytes) Empty ShimTerminal → Option AnswerOutcome
  | .returned (status, buffer) after =>
    if status = 0 then some (.returned ⟨0, [buffer]⟩ after)
    else if buffer = initial then some (.returned ⟨status, []⟩ after)
    else none
  | .unwound reason _ => nomatch reason
  | .terminated t => some (.terminated t)

/-- An answer as JSON: its status and its output byte strings. -/
def answerJson (a : Solanalib.Runtime.SysAns) : Json :=
  Json.mkObj [("status", natJson a.r0), ("out", Json.arr (a.out.map bytesJson).toArray)]

/-- An answer outcome as JSON, for the report of the checker. -/
def answerOutcomeJson : AnswerOutcome → Json :=
  outcomeJson shimStateJson answerJson emptyJson shimTerminalJson

/-- The checker of `sol_sha256`: it decides the reference at `rawIndex` against the recorded status
and result buffer. It reads every record as aligned, `⟨slices, true⟩`, because the driver passes
a `&[&[u8]]`, 8-aligned by its type, and the records carry no `vals` address; so conformance does
not exercise the unaligned branch. -/
def solSha256 : Checker where
  function := "solana_define_syscall::definitions::sol_sha256"
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha256_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha256_run"]
  check := fun c => do
    let before ← shimState c.state
    let slices ← fieldsOf c.args "slices"
    let initial ← bytesN 32 (← field c.args "hash_result")
    let recorded := (← parseShimOutcome hashResult c.outcome).bind (hashAnswer initial.val)
    return decideGraph (S := ShimState) (V := Solanalib.Runtime.SysAns) (U := Empty) (T :=
      ShimTerminal)
      (sol_sha256_run rawIndex before ⟨slices, true⟩) (provider before (.hash .sha256 slices))
      (sha256_graph before slices) recorded answerOutcomeJson

/-! ## `sol_log_` -/

/-- At `rawIndex`, the `sol_log_` reference is the graph of `provider` at the log request, with the
answer replaced by `()`. -/
theorem log_graph (before : ShimState) (message : Solanalib.Runtime.Bytes) (o :
  Syscalls.UnitOutcome) :
    sol_log__run rawIndex before message o ↔
      Outcome.map (fun _ => ()) (provider before (.log message)) = o :=
  Callback.map_ofFunction _ provider before (.log message) o

/-- The checker of `sol_log_`: it decides the reference at `rawIndex` against the recorded
outcome. -/
def solLog : Checker where
  function := "solana_define_syscall::definitions::sol_log_"
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_log__run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_log__run"]
  check := fun c => do
    let before ← shimState c.state
    let message ← asBytes (← field c.args "message")
    let recorded ← parseShimOutcome asUnit c.outcome
    return decideGraph (S := ShimState) (V := Unit) (U := Empty) (T := ShimTerminal)
      (sol_log__run rawIndex before message)
      (Outcome.map (fun _ => ()) (provider before (.log message)))
      (log_graph before message) recorded unitOutcomeJson

/-! ## `sol_panic_` and `abort` -/

/-- An outcome of a call that returns `!`, over the shim state. -/
abbrev StopOutcome := Outcome ShimState Empty Empty ShimTerminal

/-- The outcome of a call that returns `!`: the terminal exit of the provider; an answer is none. -/
def stopComputed : AnswerOutcome → Option StopOutcome
  | .terminated reason => some (.terminated reason)
  | _ => none

/-- At `rawIndex`, `stops` is the graph of `stopComputed` after `provider`. -/
theorem stops_graph (before : ShimState) (request : Solanalib.Runtime.SysReq) (o : StopOutcome) :
    RawSyscall.stops rawIndex before request o ↔ stopComputed (provider before request) = some o :=
      by
  cases o with
  | returned value _ => exact value.elim
  | unwound reason _ => exact reason.elim
  | terminated reason =>
    show provider before request = .terminated reason ↔ _
    cases provider before request with
    | returned answer after => simp [stopComputed]
    | unwound u _ => exact u.elim
    | terminated t => simp [stopComputed]

/-- At `rawIndex`, the `sol_panic_` reference is `stops_graph` at the panic request. -/
theorem panic_graph (before : ShimState) (args : RawSyscall.PanicArgs) (o : StopOutcome) :
    sol_panic__run rawIndex before args o ↔ stopComputed (provider before args.request) = some o :=
  stops_graph before args.request o

/-- At `rawIndex`, the `abort` reference is `stops_graph` at the abort request. -/
theorem abort_graph (before : ShimState) (o : StopOutcome) :
    abort_run rawIndex before () o ↔ stopComputed (provider before .abort) = some o :=
  stops_graph before .abort o

/-- A recorded exit of a call that returns `!`: a terminated exit is read whole; a return or an
unwind is no outcome of the model. -/
def parseStopOutcome (j : Json) : Result (Option StopOutcome) := do
  match ← Runtime.terminated? j with
  | some _ => parseShimOutcome (fun _ => throw "a call that returns ! has no value") j
  | none => pure none

/-- The recorded arguments of `sol_panic_`: the bytes of the file, the line and the column. -/
def panicArgs (j : Json) : Result RawSyscall.PanicArgs := do
  pure ⟨← asBytes (← field j "file"), ← asUInt 64 (← field j "line"), ← asUInt 64 (← field j
    "column")⟩

/-- A stop outcome as JSON, for the report of the checker. -/
def stopOutcomeJson : StopOutcome → Json := outcomeJson shimStateJson emptyJson emptyJson
  shimTerminalJson

/-- The checker of `sol_panic_`: it decides the reference at `rawIndex` against the recorded exit.
-/
def solPanic : Checker where
  function := "solana_define_syscall::definitions::sol_panic_"
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_panic__run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_panic__run"]
  check := fun c => do
    let before ← shimState c.state
    let args ← panicArgs c.args
    let recorded ← parseStopOutcome c.outcome
    return decideOptGraph (S := ShimState) (V := Empty) (U := Empty) (T := ShimTerminal)
      (sol_panic__run rawIndex before args) (stopComputed (provider before args.request))
      (panic_graph before args) recorded stopOutcomeJson

/-- The checker of `abort`: it decides the reference at `rawIndex` against the recorded exit. -/
def abortChecker : Checker where
  function := "solana_define_syscall::definitions::abort"
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.abort_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.abort_run"]
  check := fun c => do
    let before ← shimState c.state
    asUnit c.args
    let recorded ← parseStopOutcome c.outcome
    return decideOptGraph (S := ShimState) (V := Empty) (U := Empty) (T := ShimTerminal)
      (abort_run rawIndex before ()) (stopComputed (provider before .abort))
      (abort_graph before) recorded stopOutcomeJson

/-! ## `sol_sha512` and `sol_curve_multiscalar_mul` -/

theorem provider_hash_shape (before : ShimState) (slices : List Solanalib.Runtime.Bytes)
    (answer : Solanalib.Runtime.SysAns) (after : ShimState)
    (returned : provider before (.hash .sha512 slices) = .returned answer after) :
    OutputShape 64 answer := by
  obtain ⟨_, read⟩ := checkedAnswer_returned returned
  exact readReply_shape read

theorem provider_msm_shape (before : ShimState) (args : MsmArgs) (answer : Solanalib.Runtime.SysAns)
    (after : ShimState) (returned : provider before args.request = .returned answer after) :
    MsmShape args answer := by
  obtain ⟨_, read⟩ := checkedAnswer_returned returned
  have shaped := readReply_shape read
  simpa [MsmShape, MsmArgs.validCurve] using shaped

/-- Native descriptors are aligned, and the shim does not implement a hash slice limit. -/
def sha512Index : Sha512Index where
  State := ShimState
  Terminal := ShimTerminal
  provider := Callback.ofFunction provider
  checkAligned := true
  maxHashSlices := none
  hashShape := provider_hash_shape

def msmIndex : MsmIndex where
  State := ShimState
  Terminal := ShimTerminal
  provider := Callback.ofFunction provider
  responseShape := provider_msm_shape

theorem sha512_graph (before : ShimState) (slices : List Solanalib.Runtime.Bytes) (outcome :
  AnswerOutcome) :
    sol_sha512_run sha512Index before ⟨slices, true⟩ outcome ↔
      provider before (.hash .sha512 slices) = outcome := Iff.rfl

def msmComputed (before : ShimState) (args : MsmArgs) : AnswerOutcome :=
  if args.overLimit then provider before .abort
  else provider before args.request

theorem msm_graph (before : ShimState) (args : MsmArgs) (outcome : AnswerOutcome) :
    sol_curve_multiscalar_mul_run msmIndex before args outcome ↔
      msmComputed before args = outcome := by
  change msmRun msmIndex before args outcome ↔ _
  cases limit : args.overLimit with
  | false => simp [msmRun, msmComputed, limit, msmIndex, Callback.ofFunction]
  | true =>
    cases outcome with
    | returned _ _ => simp [msmRun, msmComputed, limit, RawSyscall.abortedWith, provider]
    | unwound reason _ => exact nomatch reason
    | terminated _ => simp [msmRun, msmComputed, limit, RawSyscall.abortedWith, msmIndex,
        Callback.ofFunction, provider]

/-- Equal counts and widths are checked before creating paired model inputs. -/
def msmArgs (j : Json) : Result MsmArgs := do
  let curve ← asUInt 64 (← field j "curve_id")
  let count ← asUInt 64 (← field j "count")
  let scalars ← (← (← field j "scalars").getArr?).toList.mapM (bytesN 32)
  let points ← (← (← field j "points").getArr?).toList.mapM (bytesN 32)
  unless scalars.length = count ∧ points.length = count do
    throw "multiscalar input counts differ from the ABI count"
  return ⟨curve, (scalars.zip points).map fun (scalar, point) =>
    ⟨scalar.val, point.val, scalar.property, point.property⟩⟩

/-- Status, destination and guards from a native return. -/
def guardedResult (width : Nat) (j : Json) : Result (Nat × Solanalib.Runtime.Bytes ×
  Solanalib.Runtime.Bytes) := do
  return (← asUInt 64 (← field j "status"), (← bytesN width (← field j "output")).val,
    (← bytesN 16 (← field j "guards")).val)

/-- Nonzero status preserves the destination, and every return preserves the external guards. -/
def guardedAnswer (initial guards : Solanalib.Runtime.Bytes) :
    Outcome ShimState (Nat × Solanalib.Runtime.Bytes × Solanalib.Runtime.Bytes) Empty ShimTerminal
      → Option AnswerOutcome
  | .returned (status, buffer, observedGuards) after =>
      if observedGuards ≠ guards then none
      else hashAnswer initial (.returned (status, buffer) after)
  | .unwound reason _ => nomatch reason
  | .terminated terminal => some (.terminated terminal)

def solSha512 : Checker where
  function := "solana_define_syscall::definitions::sol_sha512"
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha512_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha512_run"]
  check := fun record => do
    let before ← shimState record.state
    let slices ← fieldsOf record.args "slices"
    let initial ← bytesN 64 (← field record.args "output")
    let guards ← bytesN 16 (← field record.args "guards")
    let recorded := (← parseShimOutcome (guardedResult 64) record.outcome).bind (guardedAnswer
      initial.val guards.val)
    return decideGraph (S := ShimState) (V := Solanalib.Runtime.SysAns) (U := Empty) (T :=
      ShimTerminal)
      (sol_sha512_run sha512Index before ⟨slices, true⟩)
      (provider before (.hash .sha512 slices)) (sha512_graph before slices) recorded
        answerOutcomeJson

def solCurveMultiscalarMul : Checker where
  function := "solana_define_syscall::definitions::sol_curve_multiscalar_mul"
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_curve_multiscalar_mul_r\
    un"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_curve_multiscalar_mul_ru\
    n"]
  check := fun record => do
    let before ← shimState record.state
    let args ← msmArgs record.args
    let initial ← bytesN 32 (← field record.args "output")
    let guards ← bytesN 16 (← field record.args "guards")
    let recorded := (← parseShimOutcome (guardedResult 32) record.outcome).bind (guardedAnswer
      initial.val guards.val)
    return decideGraph (S := ShimState) (V := Solanalib.Runtime.SysAns) (U := Empty) (T :=
      ShimTerminal)
      (sol_curve_multiscalar_mul_run msmIndex before args)
      (msmComputed before args) (msm_graph before args) recorded answerOutcomeJson

/-- The checkers for the four selected declarations of solana-define-syscall 5.1.0. -/
def checkers : List Checker := [solSha256, solLog, solPanic, abortChecker]

end SolanalibTest.Conformance.Library.Families.Runtime.RawSyscalls
