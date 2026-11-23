/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.Core.ProgramPackExecutable
import SolanalibTest.Conformance.Library.Families.StakeCodecs.Values
import Solanalib.Specs.SolanaBorsh.Capabilities

set_option autoImplicit false
open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

def events (j : Json) : Result (List String) := asList Json.getStr? j
def eventsJson (state : List String) : Json := listJson Json.str state

def callbackJson {V : Type} (value : V → Json) : Outcome (List String) V String String → Json
  | .returned result state => returnedJson (value result) (eventsJson state)
  | .unwound reason state => Json.mkObj [("exit", "unwound"), ("reason", toJson reason), (
    "state",
    eventsJson state)]
  | .terminated reason => Json.mkObj [("exit", "terminated"), ("reason", toJson reason)]

namespace PackedLen

inductive Op where
  | write (bytes : Solanalib.Runtime.Bytes)
  | writeAll (bytes : Solanalib.Runtime.Bytes)
  | flush | fail | panic | abort

inductive Control where
  | start (ops : List Op)
  | remaining (ops : List Op)
  | log (event : String) (next : Control)
  | done (result : Except Borsh.IoError Unit)
  | unwind (reason : String)

def failure : Borsh.IoError := ⟨⟨"Other"⟩, "serializer-error"⟩

def afterWrite (all : Bool) (bytes : Solanalib.Runtime.Bytes) (rest : List Op) : Except String Nat
  → Control
  | .ok amount => .log (if all then s!"write_all:{bytes.length}" else s!"write:{amount}")
    (.remaining rest)
  | .error reason => .log "drop" (.unwind reason)

def command : Control → BorshPackedLen.Command Control (Option String) Unit Borsh.IoError String
  | .start ops => .effect (some "enter") (fun _ => .remaining ops)
  | .log event next => .effect (some event) (fun _ => next)
  | .done result => .done result
  | .unwind reason => .unwind reason
  | .remaining [] => .effect (some "drop") (fun _ => .done (.ok ()))
  | .remaining (.write bytes :: rest) => .write bytes (afterWrite false bytes rest)
  | .remaining (.writeAll bytes :: rest) =>
    if bytes.isEmpty then .advance (.log "write_all:0" (.remaining rest))
    else .write bytes (afterWrite true bytes rest)
  | .remaining (.flush :: rest) => .advance (.log "flush" (.remaining rest))
  | .remaining (.fail :: _) => .effect (some "fail") (fun _ => .log "drop" (.done (.error failure)))
  | .remaining (.panic :: _) => .effect (some "panic") (fun _ => .log "drop" (.unwind
    "serializer-panic"))
  | .remaining (.abort :: _) => .effect none (fun _ => .done (.ok ()))

def effects (before : List String) (event : Option String) : Outcome (List String) Unit String
  String :=
  match event with
  | some event => .returned () (before ++ [event])
  | none => .terminated "abort"

def index : BorshPackedLen.Index where
  State := List String
  Value := List Op
  Error := Borsh.IoError
  Unwind := String
  Terminal := String
  Control := Control
  EffectArg := Option String
  EffectValue := Unit
  wordBits := 64
  checkedOverflow := true
  start := .start
  command := command
  effects := Callback.ofFunction effects
  overflow := Callback.ofFunction fun state _ => .unwound "attempt to add with overflow" state

def executable : BorshPackedLen.Executable index where
  effects := effects
  overflow := fun state _ => .unwound "attempt to add with overflow" state
  effects_eq := rfl
  overflow_eq := rfl

def op (j : Json) : Result Op := do
  match j.getStr? with
  | .ok "flush" => pure .flush
  | .ok "fail" => pure .fail
  | .ok "panic" => pure .panic
  | .ok "abort" => pure .abort
  | .ok other => throw s!"unknown serializer operation {other}"
  | .error _ =>
    match j.getObjVal? "write" with
    | .ok bytes => pure (.write (← asBytes bytes))
    | .error _ => pure (.writeAll (← asBytes (← field j "write_all")))

def run := Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run index

theorem evaluated : run = BorshPackedLen.run index := rfl

def checker : Checker where
  function := "solana_borsh::v0_10::get_instance_packed_len"
  generics := [("T", "conformance_stake_codecs_interface::packed_len::Probe")]
  reference := "Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run"
  decides := ["Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run"]
  check := fun c => do
    let before ← events c.state
    let ops ← asList op c.args
    let observed ← parseOutcome (asExcept ioError (asUInt 64)) events some some c.outcome
    let fuel := 4 * ops.length + 4
    match computed : BorshPackedLen.runFuel index executable fuel (.start ops) 0 before with
    | none => throw "serializer replay did not finish; no source outcome is synthesized"
    | some expected =>
      have graph : ∀ outcome, run before ops outcome ↔ expected = outcome := by
        intro outcome
        rw [evaluated]
        exact BorshPackedLen.runFuel_graph index executable fuel (.start ops) 0 before expected
          computed outcome
      letI : DecidableEq (Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
        :=
        inferInstanceAs (DecidableEq (Outcome (List String) (Except Borsh.IoError Nat) String
          String))
      pure (decideGraph _ expected graph observed (callbackJson (exceptJson ioErrorJson toJson)))

end PackedLen

end SolanalibTest.Conformance.Library.Families.StakeCodecs

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

namespace PackedLen

def runForVersion (modern : Bool) := if modern then
  Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run index
  else Solanalib.Specs.SolanaProgram.borsh0_10.get_instance_packed_len_run index

theorem evaluatedForVersion (modern : Bool) : runForVersion modern = BorshPackedLen.run index := by
  cases modern <;> rfl

def checkerForVersion (modern : Bool) : Checker where
  function := if modern then "solana_borsh::v0_10::get_instance_packed_len"
    else "solana_program::borsh0_10::get_instance_packed_len"
  generics := [("T", if modern then "conformance_stake_codecs_interface::packed_len::Probe"
    else "conformance_stake_codecs_program::packed_len::Probe")]
  reference := if modern then "Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_ru\
    n"
    else "Solanalib.Specs.SolanaProgram.borsh0_10.get_instance_packed_len_run"
  decides := [if modern then "Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run"
    else "Solanalib.Specs.SolanaProgram.borsh0_10.get_instance_packed_len_run"]
  check := fun c => do
    let before ← events c.state
    let ops ← asList op c.args
    let observed ← parseOutcome (asExcept ioError (asUInt 64)) events some some c.outcome
    let fuel := 4 * ops.length + 4
    match computed : BorshPackedLen.runFuel index executable fuel (.start ops) 0 before with
    | none => throw "serializer replay did not finish; no source outcome is synthesized"
    | some expected =>
      have graph : ∀ outcome, runForVersion modern before ops outcome ↔ expected = outcome := by
        intro outcome
        rw [evaluatedForVersion]
        exact BorshPackedLen.runFuel_graph index executable fuel (.start ops) 0 before expected
          computed outcome
      letI : DecidableEq (Outcome index.State (Except index.Error Nat) index.Unwind index.Terminal)
        :=
        inferInstanceAs (DecidableEq (Outcome (List String) (Except Borsh.IoError Nat) String
          String))
      pure (decideGraph _ expected graph observed (callbackJson (exceptJson ioErrorJson toJson)))

end PackedLen

end SolanalibTest.Conformance.Library.Families.StakeCodecs

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

namespace Pack

def decode (overrideMethod : Bool) (before : List String) (bytes : Solanalib.Runtime.Bytes) :
    Outcome (List String) (Except String UInt8) String String :=
  if overrideMethod then .returned (.ok 1) (before ++ ["override"])
  else if bytes.length ≠ 1 then .returned (.error "InvalidAccountData") before
  else if bytes.headD 0 = 2 then .returned (.error "BorshIoError(\"codec-error\")") (before ++
    ["decode"])
  else .returned (.ok (bytes.headD 0)) (before ++ ["decode"])

def initialized (before : List String) (value : UInt8) : Outcome (List String) Bool String String :=
  if value = 3 ∨ value = 6 then .unwound "query" (before ++ ["query"])
  else if value = 5 then .terminated "abort"
  else .returned (value == 1) (before ++ ["query"])

def drop (before : List String) (value : UInt8) : Outcome (List String) Unit String String :=
  if value = 4 ∨ value = 6 then .unwound "drop" (before ++ ["drop"])
  else .returned () (before ++ ["drop"])

def index (overrideMethod : Bool) : ProgramPack.Index where
  State := List String
  Value := UInt8
  Error := String
  Unwind := String
  Terminal := String
  uninitializedAccount := "UninitializedAccount"
  unpackUnchecked := Callback.ofFunction (decode overrideMethod)
  initialized := Callback.ofFunction initialized
  dropValue := Callback.ofFunction drop
  doubleUnwind := fun _ _ _ terminal => terminal = "abort"

def executable (overrideMethod : Bool) : ProgramPack.Executable (index overrideMethod) where
  decode := decode overrideMethod
  initialized := initialized
  drop := drop
  double := fun _ _ _ => "abort"
  decode_eq := rfl
  initialized_eq := rfl
  drop_eq := rfl
  double_eq := rfl

theorem evaluated (overrideMethod : Bool) (before : List String) (bytes : Solanalib.Runtime.Bytes)
    (outcome : Outcome (List String) (Except String UInt8) String String) :
    Solanalib.Specs.SolanaProgram.program_pack.Pack.unpack_run (index overrideMethod) before bytes
      outcome ↔
      ProgramPack.unpackFn (index overrideMethod) (executable overrideMethod) before bytes =
        outcome :=
  ProgramPack.unpack_graph _ _ _ _ _

def checker (overrideMethod : Bool) : Checker where
  function := "solana_program::program_pack::Pack::unpack"
  generics := [("Self", if overrideMethod then "conformance_stake_codecs_legacy::OverridePr\
    obe"
    else "conformance_stake_codecs_legacy::Probe")]
  reference := "Solanalib.Specs.SolanaProgram.program_pack.Pack.unpack_run"
  decides := ["Solanalib.Specs.SolanaProgram.program_pack.Pack.unpack_run"]
  check := fun c => do
    let before ← events c.state
    let bytes ← asBytes c.args
    let observed ← parseOutcome (asExcept Json.getStr? u8Parse) events some some c.outcome
    pure (decideGraph _ _ (evaluated overrideMethod before bytes) observed
      (callbackJson (exceptJson Json.str u8Json)))

end Pack

end SolanalibTest.Conformance.Library.Families.StakeCodecs
