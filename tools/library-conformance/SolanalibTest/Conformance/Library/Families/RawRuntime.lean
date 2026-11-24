/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Runtime
import Solanalib.Specs.AnchorLang.StackHeight
import Solanalib.Specs.SolanaCpi
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import Solanalib.Specs.SolanaDefineSyscall
import Solanalib.Specs.Pinocchio.Get
import Solanalib.Specs.PinocchioLog.Logger
import Solanalib.Specs.Core.RawRuntimeSample
import Solanalib.Specs.Core.InputWrites
import Solanalib.Specs.SolanaCpi.syscalls

/-!
Native calls of the exact published declarations use a fixed symbolic provider. This checker
compares the registered request references, destination prefixes/suffixes, guard bytes and the
shared invocation state of the
provider. Mapped cases observe the same live native buffer as serialized
input and check the actual output stores before projecting back to the fixed request snapshot.
The native trace checks call arguments and provider ordering. It is not
Agave execution, cryptographic validation or a proof of the pointer layout of the production target.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.RawRuntime
open _root_.SolanalibTest.Conformance.Library.Families.Runtime
open Solanalib.Specs.SolanaDefineSyscall.definitions

deriving instance DecidableEq for Solanalib.Runtime.TxState
deriving instance DecidableEq for Solanalib.Runtime.InvState

/-- The fixture gives every state field not exported by the native provider its closed value.
This reconstruction belongs only to this test interpretation, not to the source binding. -/
def state (j : Json) : Result Solanalib.Runtime.InvState := do
  let program ← pubkey (← field j "return_program")
  let bytes ← asBytes (← field j "return_data")
  let height ← asUInt 64 (← field j "height")
  let input ← asBytes (← field j "input")
  let heap ← asUInt 64 (← field j "heap_pos")
  let logs ← (← (← field j "logs").getArr?).toList.mapM asBytes
  return { Sample.state with
    ts := { Sample.state.ts with
      returnData := (program, bytes)
      stack := List.replicate height Sample.frame }
    buf := input
    heapPos := heap
    logs := logs }

def stateJson (s : Solanalib.Runtime.InvState) : Json := Json.mkObj [
  ("return_program", bytesJson s.ts.returnData.1.bytes), ("return_data", bytesJson
    s.ts.returnData.2),
  ("height", toJson s.ts.stack.length), ("input", bytesJson s.buf), ("heap_pos", toJson s.heapPos),
  ("logs", Json.arr (s.logs.map bytesJson).toArray)]

def index (onCurve : Bool) : Index :=
  { Sample.index with world := { Sample.world with
    prims := { Sample.primitives with onCurve := fun _ => onCurve } } }

def fields (j : Json) : Result (List Solanalib.Runtime.Bytes) :=
  do (← (← field j "seeds").getArr?).toList.mapM asBytes

def overlap (j : Json) : Result Bool := do (← field j "overlap").getBool?

/-- Mapped fixtures place the same guarded allocation at the VM input base. -/
def destination (j : Json) : Result Nat := do
  return if ← (← field j "input_region").getBool? then Solanalib.Runtime.MM_INPUT_START + 8 else
    4096

def copied (before : Solanalib.Runtime.InvState) (j : Json) : Result Nat := do
  return min (← asUInt 64 (← field j "capacity")) before.ts.returnData.2.length

/-- All output areas are observed, including areas that the raw call leaves untouched. -/
def answer (operation : String) (before : Solanalib.Runtime.InvState) (args j : Json) : Result
  Solanalib.Runtime.SysAns := do
  let status ← asUInt 64 (← field j "status")
  let output ← asBytes (← field j "output")
  let initial ← asBytes (← field args "output")
  let program ← (bytesN 32 (← field j "program_output"))
  let oldProgram ← bytesN 32 (← field args "program_output")
  let bump ← asUInt 8 (← field j "bump")
  let oldBump ← asUInt 8 (← field args "bump")
  unless output.length = initial.length do throw "output length changed"
  unless (← asBytes (← field j "guards")) = (← asBytes (← field args "guards")) ∧
      (← asBytes (← field j "program_guards")) = (← asBytes (← field args "program_guards")) do
    throw "output guard bytes changed"
  unless operation = "get-return" ∨ program.val = oldProgram.val do
    throw "unwritten program buffer changed"
  unless operation = "find" ∨ bump = oldBump do throw "unwritten bump changed"
  if operation = "create" ∨ operation = "find" ∨ operation = "sha256" then
    if status = 0 then
      if operation = "find" then return ⟨status, [output, [UInt8.ofNat bump]]⟩
      else return ⟨status, [output]⟩
    else
      unless output = initial ∧ bump = oldBump do throw "failed derivation wrote an output"
      return ⟨status, []⟩
  else if operation = "get-return" then
    let n ← copied before args
    unless output.drop n = initial.drop n do throw "return-data suffix changed"
    if n = 0 then
      unless program.val = oldProgram.val do throw "zero-copy get wrote program identity"
      return ⟨status, []⟩
    else return ⟨status, [output.take n, program.val]⟩
  else if operation = "stack" ∨ operation = "set-return" then
    unless output = initial do throw "non-output call wrote output bytes"
    return ⟨status, []⟩
  else return ⟨status, [output]⟩

def error : String → Option Solanalib.Runtime.InstrError
  | "ProgramFailedToComplete" => some .ProgramFailedToComplete
  | _ => none

def answerJson (answer : Solanalib.Runtime.SysAns) : Json := Json.mkObj [
  ("status", toJson answer.r0), ("out", Json.arr (answer.out.map bytesJson).toArray)]

def outcomeJson : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
  Solanalib.Runtime.InstrError → Json :=
  Runtime.outcomeJson stateJson answerJson emptyJson (fun reason => Json.str (reprStr reason))

/-- Seed-length rejection preserves the trace of earlier reads and skips later memory. -/
def seedTrace : List Solanalib.Runtime.Bytes → Bool × List Json
  | [] => (true, [])
  | bytes :: rest =>
    if 32 < bytes.length then (false, [])
    else let tail := seedTrace rest
         (tail.1, Json.mkObj [("seed", bytesJson bytes)] :: tail.2)

def trace (operation : String) (before : Solanalib.Runtime.InvState) (args : Json) : Result Json :=
  do
  let base := [Json.str operation]
  let overlapping ← overlap args
  let output ← match operation with
    | "copy" => do
      let input ← asBytes (← field args "input")
      if overlapping ∨ input = [] then pure base else
        pure (base ++ [Json.mkObj [("read", bytesJson input)], "write-data"])
    | "set" => do
      if (← asUInt 64 (← field args "count")) = 0 then pure base else pure (base ++ ([
        "write-data"]
        : List Json))
    | "create" | "find" => do
      let seeds ← fields args
      let base := base ++ (["descriptors"] : List Json)
      if 16 < seeds.length then pure base else
        let read := seedTrace seeds
        if !read.1 then pure (base ++ read.2) else do
          let program ← pubkey (← field args "program")
          let base := base ++ read.2 ++ [Json.mkObj [("program", pubkeyJson program)],
            "derive"]
          let onCurve ← (← field args "on_curve").getBool?
          if onCurve ∨ (operation = "find" ∧ seeds.length = 16) then pure base
          else if operation = "create" then pure (base ++ (["write-address"] : List Json))
          else if overlapping then pure base else pure (base ++ (["write-bump", "write-addr\
            ess"] :
            List Json))
    | "sha256" => do
      let slices ← fields args
      pure (base ++ (["descriptors"] : List Json) ++ slices.map (fun b => Json.mkObj [(
        "seed",
        bytesJson b)]) ++ (["write-data"] : List Json))
    | "clock" | "rent" | "epoch" => pure (base ++ (["write-data"] : List Json))
    | "set-return" => do
      let input ← asBytes (← field args "input")
      if 1024 < input.length then pure base else pure (base ++ [Json.mkObj [("read", bytesJson
        input)]])
    | "get-return" => do
      if (← copied before args) = 0 ∨ overlapping then pure base
      else pure (base ++ (["write-data", "write-program"] : List Json))
    | _ => pure base
  return Json.arr output.toArray

/-- The decision consumes the supplied registered run relation, with a proved graph equality. -/
def check (operation : String) (record : Case) (before : Solanalib.Runtime.InvState)
    (relation : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError → Prop)
    (computed : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError)
    (graph : ∀ result, relation result ↔ computed = result) : Result Verdict := do
  let mapped ← (← field record.args "input_region").getBool?
  if mapped then
    let initial ← asBytes (← field record.args "output")
    let guards ← asBytes (← field record.args "guards")
    unless before.buf = guards.take 8 ++ initial ++ guards.drop 8 do
      throw "input snapshot differs from mapped output storage"
  let actual ← parseOutcome (answer operation before record.args) state (fun _ => none) error
    record.outcome
  let observed ← match actual with
    | some (.returned result after) => do
      let writes := if mapped then
        (result.out[0]?.toList.map fun bytes =>
          (⟨Solanalib.Runtime.MM_INPUT_START + 8, bytes⟩ : InputWrites.Write)) else []
      let expected := (InputWrites.stores Solanalib.Runtime.MM_INPUT_START writes before).buf
      unless after.buf = expected do throw "actual input buffer differs from ordered \
        output stores"
      pure (some (.returned result (InputWrites.requestState before.buf after)))
    | other => pure other
  let verdict := decideGraph relation computed graph observed outcomeJson
  let expectedTrace ← trace operation before record.args
  unless (← field record.outcome "trace") == expectedTrace do
    return ⟨false, Json.mkObj [("trace", expectedTrace), ("model", verdict.expected)]⟩
  return verdict

def copy (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_memcpy__run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_memcpy__run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let bytes ← asBytes (← field record.args "input")
    unless bytes.length = (← asUInt 64 (← field record.args "count")) do
      throw "copy input count differs"
    let output ← destination record.args
    let overlapping ← overlap record.args
    let dst := if bytes = [] then 0 else output
    let src := if bytes = [] then 0 else if overlapping then dst else 8192
    let args : RawMemory.CopyArgs := ⟨dst, src, bytes⟩
    check "copy" record before (sol_memcpy__run index before args)
      (RawRuntime.outcome (RawMemory.copyStep index before args)) (fun _ => Iff.rfl)

def set (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_memset__run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_memset__run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let args : RawMemory.SetArgs := ⟨← u8 (← field record.args "byte"), ← asUInt 64 (← field
      record.args "count")⟩
    check "set" record before (sol_memset__run index before args)
      (RawRuntime.outcome (RawMemory.setStep index before args)) (fun _ => Iff.rfl)

def create (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_create_program_address_\
    run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_create_program_address_r\
    un"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let args : RawAddress.Args := ⟨← fields record.args, ← pubkey (← field record.args
      "program")⟩
    check "create" record before (sol_create_program_address_run index before args)
      (RawRuntime.outcome (RawAddress.createStep index before args)) (fun _ => Iff.rfl)

def find (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_try_find_program_addres\
    s_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_try_find_program_address\
    _run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let output ← destination record.args
    let dst := if onCurve then 0 else output
    let args : RawAddress.FindArgs := ⟨⟨← fields record.args, ← pubkey (← field record.args
      "program")⟩,
      dst, if ← overlap record.args then dst else if onCurve then 0 else 8192⟩
    check "find" record before (sol_try_find_program_address_run index before args)
      (RawRuntime.outcome (RawAddress.findStep index before args)) (fun _ => Iff.rfl)

def clock (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_clock_sysvar_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_clock_sysvar_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let dst ← destination record.args
    check "clock" record before (sol_get_clock_sysvar_run index before dst)
      (RawRuntime.outcome (RawState.typedStep .clock index before dst)) (fun _ => Iff.rfl)

def rent (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_rent_sysvar_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_rent_sysvar_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let dst ← destination record.args
    check "rent" record before (sol_get_rent_sysvar_run index before dst)
      (RawRuntime.outcome (RawState.typedStep .rent index before dst)) (fun _ => Iff.rfl)

def getReturn (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaCpi.syscalls.sol_get_return_data_run"
  decides := ["Solanalib.Specs.SolanaCpi.syscalls.sol_get_return_data_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let count ← copied before record.args
    let output ← destination record.args
    let overlapping ← overlap record.args
    let dst := if count = 0 then 0 else output
    let args : RawState.ReturnArgs := ⟨← asUInt 64 (← field record.args "capacity"),
      dst, if count = 0 then 0 else if overlapping then dst else 8192⟩
    check "get-return" record before (Solanalib.Specs.SolanaCpi.syscalls.sol_get_return_data_run
      index before args)
      (RawRuntime.outcome (RawState.getReturnStep index before args)) (fun _ => Iff.rfl)

/-- The exact SHA256 provider of the native fixture; it preserves shared state and supplies a fixed
32-byte output, without implementing a hash algorithm. -/
def hashProvider : Solanalib.Runtime.InvState → Solanalib.Runtime.SysReq →
    Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty Solanalib.Runtime.InstrError
      := fun before request =>
  match request with
  | .hash .sha256 _ => .returned ⟨0, [List.replicate 32 7]⟩ before
  | _ => .terminated .ProgramFailedToComplete

def hashIndex : RawSyscall.Index where
  State := Solanalib.Runtime.InvState
  Terminal := Solanalib.Runtime.InstrError
  provider := Callback.ofFunction hashProvider
  checkAligned := true
  maxHashSlices := some Solanalib.Runtime.MAX_HASH_SLICES
  hashShape := by
    intro before slices answer after returned
    cases returned
    decide

def hashComputed (before : Solanalib.Runtime.InvState) (args : RawSyscall.Sha256Args) :=
  if args.rejected hashIndex.maxHashSlices hashIndex.checkAligned then
    hashProvider before .abort else hashProvider before (.hash .sha256 args.slices)

theorem hash_graph (before : Solanalib.Runtime.InvState) (args : RawSyscall.Sha256Args)
    (result : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError) :
    sol_sha256_run hashIndex before args result ↔ hashComputed before args = result := by
  change RawSyscall.sha256Run hashIndex before args result ↔ _
  unfold RawSyscall.sha256Run hashComputed
  cases args.rejected hashIndex.maxHashSlices hashIndex.checkAligned with
  | false => rfl
  | true =>
    cases result with
    | unwound impossible _ => exact nomatch impossible
    | returned _ _ => simp [RawSyscall.aborted, RawSyscall.abortedWith, hashProvider]
    | terminated _ =>
      simp [RawSyscall.aborted, RawSyscall.abortedWith, hashIndex, Callback.ofFunction,
        hashProvider]

def hash (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha256_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha256_run"]
  check := fun record => do
    let before ← state record.state
    let args : RawSyscall.Sha256Args := ⟨← fields record.args, true⟩
    check "sha256" record before (sol_sha256_run hashIndex before args)
      (hashComputed before args) (hash_graph before args)

def define (version : String) : String := "raw_runtime_solana_define_syscall_" ++ version

def allDefine : List Checker := [
  copy "solana_define_syscall::definitions::sol_memcpy_",
  set "solana_define_syscall::definitions::sol_memset_",
  create "solana_define_syscall::definitions::sol_create_program_address",
  find "solana_define_syscall::definitions::sol_try_find_program_address",
  hash "solana_define_syscall::definitions::sol_sha256",
  clock "solana_define_syscall::definitions::sol_get_clock_sysvar",
  rent "solana_define_syscall::definitions::sol_get_rent_sysvar"]

def pinocchioLogCopy (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.PinocchioLog.logger.syscalls.sol_memcpy__run"
  decides := ["Solanalib.Specs.PinocchioLog.logger.syscalls.sol_memcpy__run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let bytes ← asBytes (← field record.args "input")
    unless bytes.length = (← asUInt 64 (← field record.args "count")) do
      throw "copy input count differs"
    let output ← destination record.args
    let overlapping ← overlap record.args
    let dst := if bytes = [] then 0 else output
    let src := if bytes = [] then 0 else if overlapping then dst else 8192
    let args : RawMemory.CopyArgs := ⟨dst, src, bytes⟩
    check "copy" record before (Solanalib.Specs.PinocchioLog.logger.syscalls.sol_memcpy__run index
      before args)
      (RawRuntime.outcome (RawMemory.copyStep index before args)) (fun _ => Iff.rfl)

def pinocchioLogSet (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.PinocchioLog.logger.syscalls.sol_memset__run"
  decides := ["Solanalib.Specs.PinocchioLog.logger.syscalls.sol_memset__run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let args : RawMemory.SetArgs := ⟨← u8 (← field record.args "byte"), ← asUInt 64 (← field
      record.args "count")⟩
    check "set" record before (Solanalib.Specs.PinocchioLog.logger.syscalls.sol_memset__run index
      before args)
      (RawRuntime.outcome (RawMemory.setStep index before args)) (fun _ => Iff.rfl)

def pinocchioClock (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.Pinocchio.syscalls.sol_get_clock_sysvar_run"
  decides := ["Solanalib.Specs.Pinocchio.syscalls.sol_get_clock_sysvar_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let dst ← destination record.args
    check "clock" record before (Solanalib.Specs.Pinocchio.syscalls.sol_get_clock_sysvar_run index
      before dst)
      (RawRuntime.outcome (RawState.typedStep .clock index before dst)) (fun _ => Iff.rfl)

end SolanalibTest.Conformance.Library.Families.RawRuntime

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.RawRuntime
open _root_.SolanalibTest.Conformance.Library.Families.Runtime
open Solanalib.Specs.SolanaDefineSyscall.definitions

deriving instance DecidableEq for Solanalib.Runtime.TxState
deriving instance DecidableEq for Solanalib.Runtime.InvState

def setReturn (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_set_return_data_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_set_return_data_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let bytes ← asBytes (← field record.args "input")
    check "set-return" record before (sol_set_return_data_run index before bytes)
      (RawRuntime.outcome (RawState.setReturnStep index before bytes)) (fun _ => Iff.rfl)

def sdkSetReturn : Checker where
  generics := []
  function := "solana_cpi::set_return_data"
  reference := "Solanalib.Specs.SolanaCpi.set_return_data_run"
  decides := ["Solanalib.Specs.SolanaCpi.set_return_data_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let bytes ← asBytes (← field record.args "input")
    check "set-return" record before (Solanalib.Specs.SolanaCpi.set_return_data_run index before
      bytes)
      (RawRuntime.outcome (RawState.setReturnStep index before bytes)) (fun _ => Iff.rfl)

end SolanalibTest.Conformance.Library.Families.RawRuntime

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

end SolanalibTest.Conformance.Library.Families.RawRuntime

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.RawRuntime
open _root_.SolanalibTest.Conformance.Library.Families.Runtime
open Solanalib.Specs.SolanaDefineSyscall.definitions

deriving instance DecidableEq for Solanalib.Runtime.TxState
deriving instance DecidableEq for Solanalib.Runtime.InvState

def epoch (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_epoch_schedule_sysv\
    ar_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_epoch_schedule_sysva\
    r_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let dst ← destination record.args
    check "epoch" record before (sol_get_epoch_schedule_sysvar_run index before dst)
      (RawRuntime.outcome (RawState.typedStep .epochSchedule index before dst)) (fun _ => Iff.rfl)

def stack (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_stack_height_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_get_stack_height_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    check "stack" record before (sol_get_stack_height_run index before ())
      (RawRuntime.outcome (RawState.stackStep index before ())) (fun _ => Iff.rfl)

def anchorStack : Checker where
  generics := []
  function := "anchor_lang::solana_program::instruction::get_stack_height"
  reference := "Solanalib.Specs.AnchorLang.solana_program.instruction.get_stack_height_run"
  decides := ["Solanalib.Specs.AnchorLang.solana_program.instruction.get_stack_height_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    check "stack" record before
      (Solanalib.Specs.AnchorLang.solana_program.instruction.get_stack_height_run index before ())
      (RawRuntime.outcome (RawState.stackStep index before ())) (fun _ => Iff.rfl)

end SolanalibTest.Conformance.Library.Families.RawRuntime

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

end SolanalibTest.Conformance.Library.Families.RawRuntime

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.RawRuntime
open _root_.SolanalibTest.Conformance.Library.Families.Runtime
open Solanalib.Specs.SolanaDefineSyscall.definitions

deriving instance DecidableEq for Solanalib.Runtime.TxState
deriving instance DecidableEq for Solanalib.Runtime.InvState

namespace Program

def copy (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_memcpy__run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_memcpy__run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let bytes ← asBytes (← field record.args "input")
    unless bytes.length = (← asUInt 64 (← field record.args "count")) do
      throw "copy input count differs"
    let output ← destination record.args
    let overlapping ← overlap record.args
    let dst := if bytes = [] then 0 else output
    let src := if bytes = [] then 0 else if overlapping then dst else 8192
    let args : RawMemory.CopyArgs := ⟨dst, src, bytes⟩
    check "copy" record before (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_memcpy__run
      index before args)
      (RawRuntime.outcome (RawMemory.copyStep index before args)) (fun _ => Iff.rfl)

def set (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_memset__run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_memset__run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let args : RawMemory.SetArgs := ⟨← u8 (← field record.args "byte"), ← asUInt 64 (← field
      record.args "count")⟩
    check "set" record before (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_memset__run
      index before args)
      (RawRuntime.outcome (RawMemory.setStep index before args)) (fun _ => Iff.rfl)

def create (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_create_program_addre\
    ss_run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_create_program_addres\
    s_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let args : RawAddress.Args := ⟨← fields record.args, ← pubkey (← field record.args
      "program")⟩
    check "create" record before
      (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_create_program_address_run index
      before args)
      (RawRuntime.outcome (RawAddress.createStep index before args)) (fun _ => Iff.rfl)

def find (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_try_find_program_add\
    ress_run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_try_find_program_addr\
    ess_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let output ← destination record.args
    let dst := if onCurve then 0 else output
    let args : RawAddress.FindArgs := ⟨⟨← fields record.args, ← pubkey (← field record.args
      "program")⟩,
      dst, if ← overlap record.args then dst else if onCurve then 0 else 8192⟩
    check "find" record before
      (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_try_find_program_address_run index
      before args)
      (RawRuntime.outcome (RawAddress.findStep index before args)) (fun _ => Iff.rfl)

def clock (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_get_clock_sysvar_run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_get_clock_sysvar_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let dst ← destination record.args
    check "clock" record before
      (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_get_clock_sysvar_run index before dst)
      (RawRuntime.outcome (RawState.typedStep .clock index before dst)) (fun _ => Iff.rfl)

def rent (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_get_rent_sysvar_run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_get_rent_sysvar_run"]
  check := fun record => do
    let before ← state record.state
    let onCurve ← (← field record.args "on_curve").getBool?
    let index := index onCurve
    let dst ← destination record.args
    check "rent" record before
      (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_get_rent_sysvar_run index before dst)
      (RawRuntime.outcome (RawState.typedStep .rent index before dst)) (fun _ => Iff.rfl)

theorem hash_graph (before : Solanalib.Runtime.InvState) (args : RawSyscall.Sha256Args)
    (result : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError) :
    Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_sha256_run hashIndex before args result
      ↔ hashComputed before args = result := by
  change RawSyscall.sha256Run hashIndex before args result ↔ _
  unfold RawSyscall.sha256Run hashComputed
  cases args.rejected hashIndex.maxHashSlices hashIndex.checkAligned with
  | false => rfl
  | true =>
    cases result with
    | unwound impossible _ => exact nomatch impossible
    | returned _ _ => simp [RawSyscall.aborted, RawSyscall.abortedWith, hashProvider]
    | terminated _ =>
      simp [RawSyscall.aborted, RawSyscall.abortedWith, hashIndex, Callback.ofFunction,
        hashProvider]

def hash (name : String) : Checker where
  generics := []
  function := name
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_sha256_run"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_sha256_run"]
  check := fun record => do
    let before ← state record.state
    let args : RawSyscall.Sha256Args := ⟨← fields record.args, true⟩
    check "sha256" record before (Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_sha256_run
      hashIndex before args)
      (hashComputed before args) (hash_graph before args)

end Program

def oldProgram : List Checker := [
  Program.copy "solana_program::syscalls::definitions::sol_memcpy_",
  Program.set "solana_program::syscalls::definitions::sol_memset_",
  Program.create "solana_program::syscalls::definitions::sol_create_program_address",
  Program.find "solana_program::syscalls::definitions::sol_try_find_program_address",
  Program.hash "solana_program::syscalls::definitions::sol_sha256",
  Program.rent "solana_program::syscalls::definitions::sol_get_rent_sysvar"]

end SolanalibTest.Conformance.Library.Families.RawRuntime

namespace SolanalibTest.Conformance.Library.Families.RawRuntime

def corpora : List (String × List Checker) := [
  ("raw_runtime_solana_define_syscall_2_3_0", allDefine),
  ("raw_runtime_solana_cpi_2_2_1", [getReturn "solana_cpi::syscalls::sol_get_return_data"]),
  ("raw_runtime_pinocchio_0_9_2", [pinocchioClock "pinocchio::syscalls::sol_get_clock_sysva\
    r"]),
  ("raw_runtime_pinocchio_log_0_5_1", [pinocchioLogCopy
    "pinocchio_log::logger::syscalls::sol_memcpy_",
    pinocchioLogSet "pinocchio_log::logger::syscalls::sol_memset_"]),
  (define "4_0_1", [copy "solana_define_syscall::definitions::sol_memcpy_", set
    "solana_define_syscall::definitions::sol_memset_", setReturn
    "solana_define_syscall::definitions::sol_set_return_data", epoch
    "solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar"]),
  (define "5_1_0", [create "solana_define_syscall::definitions::sol_create_program_address",
    setReturn "solana_define_syscall::definitions::sol_set_return_data", stack
    "solana_define_syscall::definitions::sol_get_stack_height"]),
  ("raw_runtime_solana_cpi_3_1_0", [sdkSetReturn]),
  ("raw_runtime_anchor_lang_1_0_2", [anchorStack]),
  ("raw_runtime_solana_program_1_18_26", oldProgram ++ [Program.clock
    "solana_program::syscalls::definitions::sol_get_clock_sysvar"]),
  ("raw_runtime_solana_program_1_15_2", oldProgram)]

end SolanalibTest.Conformance.Library.Families.RawRuntime
