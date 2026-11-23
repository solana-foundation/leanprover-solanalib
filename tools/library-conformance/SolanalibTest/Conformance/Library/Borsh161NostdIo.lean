/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.BorshCommon
import Solanalib.Specs.Borsh.NostdIo

/-!
# borsh 1.6.1 no-std `Write::write_all` (`borsh.NostdIo`)

The family is indexed by the `write` of the writer, the panic of `&buf[n..]` and
the allocator of the message of the `WriteZero` error. The `ScriptedWriter` of the driver answers
call `k` with `script[k]` (a count, an error, or a
panic of the writer) and takes the whole buffer on every later call; its
state is the log of its calls. The recording build has `panic = "unwind"`, so
the slice panic is an unwind carrying the message of core. The driver links the
system allocator, so the allocation of the message returns. The checker
instantiates the index with those three functions and decides the registered
relation through the fuel lemma of the model: with one call per script entry and
one more, the executable form returns, and then its outcome is the only run.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Borsh.V161NostdIo

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- A scripted response of the `write` of the writer. -/
inductive Response where
  | count (n : Nat)
  | error (e : IoError)
  | panic (message : String)
  deriving DecidableEq

/-- One `write` call received by the writer: the bytes offered and its response. -/
structure WriteCall where
  bytes : Solanalib.Runtime.Bytes
  response : Response
  deriving DecidableEq

/-- `ScriptedWriter::write`: log the call, then answer its scripted response,
or take the whole buffer once the script is used up. -/
def scriptedWriteFn (script : List Response) : WriteFn (List WriteCall) String Empty :=
  fun calls buf =>
    let response := script.getD calls.length (.count buf.length)
    let after := calls ++ [⟨buf, response⟩]
    match response with
    | .count n => .returned (.ok n) after
    | .error e => .returned (.error e) after
    | .panic message => .unwound message after

/-- the `slice_start_index_len_fail` message of core. -/
def panicMessage : WriteAllPanic → String
  | .sliceStartIndexLenFail index length =>
    s!"range start index {index} out of range for slice of length {length}"

/-- The slice panic under `panic = "unwind"`: an unwind with the message of core,
in the state at the panic. -/
def unwindPanicFn : PanicFn (List WriteCall) String Empty :=
  fun calls reason => .unwound (panicMessage reason) calls

/-- The family index of a record: the scripted writer, the unwinding panic and
the native allocation, which returns in the same state. -/
def index (script : List Response) : WriteAllIndex :=
  ⟨List WriteCall, String, Empty, Callback.ofFunction (scriptedWriteFn script),
    Callback.ofFunction unwindPanicFn, Callback.ofFunction allocationReturns⟩

/-- Once the executable form returns, the registered relation at the index of the record admits
exactly its outcome. -/
theorem evaluated {script : List Response} {before : List WriteCall} {buf : Solanalib.Runtime.Bytes}
    {fuel : Nat} {computed : Outcome (List WriteCall) (Except IoError Unit) String Empty}
    (finished : writeAllFuel (scriptedWriteFn script) unwindPanicFn allocationReturns fuel before
      buf = some computed)
    (outcome : Outcome (List WriteCall) (Except IoError Unit) String Empty) :
    Solanalib.Specs.Borsh.nostd_io.Write.write_all_run (index script) before buf outcome ↔
      computed = outcome :=
  writeAllRuns_ofFunction_of_fuel finished outcome

/-! ## Records -/

/-- A recorded response: exactly one of `ok` (a count), `err` (an io error) or
`panic` (the panic message of the writer). -/
def response (j : Json) : Result Response :=
  match j.getObjVal? "ok", j.getObjVal? "err", j.getObjVal? "panic" with
  | .ok n, .error _, .error _ => do pure (.count (← n.getNat?))
  | .error _, .ok e, .error _ => do pure (.error (← ioError e))
  | .error _, .error _, .ok m => do pure (.panic (← m.getStr?))
  | _, _, _ => throw s!"expected one of ok, err or panic, got {j.compress}"

/-- A response in the recorded form of `response`. -/
def responseJson : Response → Json
  | .count n => okJson (toJson n)
  | .error e => errJson (ioErrorJson e)
  | .panic message => Json.mkObj [("panic", Json.str message)]

/-- A logged call of the writer. Only `write` is accepted: a logged `flush` or
any other call is rejected while the record is read. -/
def writeCall (j : Json) : Result WriteCall := do
  let op ← (← field j "op").getStr?
  unless op == "write" do throw s!"writer received {op}, which write_all does not call"
  pure ⟨← asBytes (← field j "bytes"), ← response (← field j "response")⟩

/-- A `write` call in the recorded form of `writeCall`. -/
def writeCallJson (c : WriteCall) : Json :=
  Json.mkObj [("op", "write"), ("bytes", bytesJson c.bytes), ("response", responseJson c.response)]

/-- The state of the writer: its log of calls, `{"calls": [...]}`. -/
def callsState (j : Json) : Result (List WriteCall) := do asList writeCall (← field j
  "calls")
/-- The state of the writer in the recorded form of `callsState`. -/
def callsJson (calls : List WriteCall) : Json :=
  Json.mkObj [("calls", listJson writeCallJson calls)]

/-- An outcome of `write_all` at the index of a record. -/
abbrev WriteAllOut := Outcome (List WriteCall) (Except IoError Unit) String Empty

/-- An outcome in the recorded form: a return with its result and state, or an
unwind with its message and state. The index has no terminal reasons. -/
def outcomeJson : WriteAllOut → Json
  | .returned result after =>
    returnedJson (exceptJson ioErrorJson (fun _ => Json.null) result) (callsJson after)
  | .unwound reason after =>
    Json.mkObj [("exit", "unwound"), ("reason", Json.str reason), ("state", callsJson after)]
  | .terminated reason => nomatch reason

/-- Decide `write_all_run` at the index of the record. Each scripted response is
used by at most one call and one more call takes the rest, so one call per
script entry and one more suffice for every record; were the fuel to run out,
the record would be rejected. -/
def decideWriteAll (c : Case) : Result Verdict := do
  let script ← asList response (← field (← field c.args "writer") "script")
  let buf ← asBytes (← field c.args "buf")
  let before ← callsState c.state
  let recorded ← parseOutcome (asExcept ioError asUnit) callsState some noReason c.outcome
  match finished : writeAllFuel (scriptedWriteFn script) unwindPanicFn allocationReturns
      (script.length + 1) before buf with
  | some computed =>
    pure (decideGraph (S := List WriteCall) (V := Except IoError Unit) (U := String) (T := Empty)
      (Solanalib.Specs.Borsh.nostd_io.Write.write_all_run (index script) before buf)
      computed (evaluated finished) recorded outcomeJson)
  | none => pure ⟨false, Json.str "the executable form ran out of fuel"⟩

/-- The one checker: `write_all` at the `ScriptedWriter` of the driver, deciding
the registered reference. -/
def checker : Checker where
  function := "borsh::nostd_io::Write::write_all"
  generics := [("Self", "conformance_borsh_1_6_1_nostd::ScriptedWriter")]
  reference := "Solanalib.Specs.Borsh.nostd_io.Write.write_all_run"
  decides := ["Solanalib.Specs.Borsh.nostd_io.Write.write_all_run"]
  check := decideWriteAll

/-- The checkers of corpus `borsh_1_6_1_nostd_io`. -/
def checkers : List Checker := [checker]

end SolanalibTest.Conformance.Library.Borsh.V161NostdIo
