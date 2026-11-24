/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Borsh161De
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import Solanalib.Specs.SolanaBorsh.Capabilities

/-!
# Family `Instructions`: solana-borsh 3.0.2 `v1::try_from_slice_unchecked`

The model is a family over the deserializer callback `T::deserialize`. Two kinds of index are
checked:

- `T` one of the types defined in borsh 1.6.1: the callback is the registered borsh 1.6.1
  `BorshDeserialize::deserialize` relation at the registered `deserialize_reader` member of `T`,
  so the check composes registered models (`V161.deserialize_evaluated`);
- the scripted `T` of the driver: the callback is the graph of the script of the record, with a
  state that logs every slice the callback receives (what the Rust `deserialize` logs). -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Instructions.SolanaBorsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open SolanalibTest.Conformance.Library.Borsh

abbrev run := Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_run

/-! ## Borsh 1.6.1 types -/

/-- The index whose callback is the registered `deserialize` of borsh 1.6.1 at `T = t`. -/
def realIndex (t : Ty) : Solanalib.Specs.SolanaBorsh.v1.UncheckedIndex where
  State := Unit
  Error := IoError
  Value := t.Value
  Unwind := Empty
  Terminal := Empty
  deserialize := Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run
    ⟨Unit, Empty, Empty, t.Value, Callback.ofFunction t.decode⟩

theorem real_evaluated (t : Ty) (input : Solanalib.Runtime.Bytes)
    (o : Outcome Unit (Except IoError t.Value) Empty Empty) :
    run (realIndex t) () input o ↔ Outcome.map Prod.fst (deserializeFn t.decode () input) = o := by
  show Callback.map Prod.fst (realIndex t).deserialize () input o ↔ _
  constructor
  · rintro ⟨i, hi, hm⟩
    rw [← (V161.deserialize_evaluated t.decode () input i).mp hi] at hm
    exact hm
  · intro h
    exact ⟨_, (V161.deserialize_evaluated t.decode () input _).mpr rfl, h⟩

def realOut (t : Ty) : Outcome Unit (Except IoError t.Value) Empty Empty → Json
  | .returned r () => returnedJson (exceptJson ioErrorJson t.render r) Json.null
  | .unwound e _ => nomatch e
  | .terminated e => nomatch e

def realChecker (t : Ty) : Checker where
  function := "solana_borsh::v1::try_from_slice_unchecked"
  generics := [("T", t.rust)]
  reference := "Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_run"
  decides := ["Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_run"]
  check := fun c => do
    asUnit c.state
    let input ← asBytes (← field c.args "data")
    let recorded ← parseOutcome (asExcept ioError t.parse) asUnit noReason noReason c.outcome
    pure (decideGraph _ _ (real_evaluated t input) recorded (realOut t))

/-! ## The scripted deserializer -/

inductive ScriptResult where
  | ok (value : UInt64)
  | err (error : IoError)
  | panic (message : String)

structure Script where
  consume : Nat
  result : ScriptResult

abbrev Log := List Solanalib.Runtime.Bytes

/-- The scripted `deserialize`: log the received slice, consume a prefix, then return or panic. -/
def scriptFn (s : Script) (log : Log) (input : Solanalib.Runtime.Bytes) :
    Outcome Log (Except IoError UInt64 × Solanalib.Runtime.Bytes) String Empty :=
  match s.result with
  | .ok v => .returned (.ok v, input.drop s.consume) (log ++ [input])
  | .err e => .returned (.error e, input.drop s.consume) (log ++ [input])
  | .panic m => .unwound m (log ++ [input])

def scriptedIndex (s : Script) : Solanalib.Specs.SolanaBorsh.v1.UncheckedIndex where
  State := Log
  Error := IoError
  Value := UInt64
  Unwind := String
  Terminal := Empty
  deserialize := Callback.ofFunction (scriptFn s)

theorem scripted_evaluated (s : Script) (log : Log) (input : Solanalib.Runtime.Bytes)
    (o : Outcome Log (Except IoError UInt64) String Empty) :
    run (scriptedIndex s) log input o ↔ Outcome.map Prod.fst (scriptFn s log input) = o :=
  Callback.map_ofFunction Prod.fst (scriptFn s) log input o

def script (j : Json) : Result Script := do
  let consume ← (← field j "consume").getNat?
  let r ← field j "result"
  let result ← match r.getObjVal? "ok", r.getObjVal? "err", r.getObjVal? "panic" with
    | .ok v, _, _ => do pure (.ok (← u64Parse v))
    | _, .ok e, _ => do pure (.err (← ioError e))
    | _, _, .ok m => do pure (.panic (← m.getStr?))
    | _, _, _ => throw s!"unknown script result {r.compress}"
  pure ⟨consume, result⟩

def logState (j : Json) : Result Log := do asList asBytes (← field j "log")
def logJson (log : Log) : Json := Json.mkObj [("log", listJson bytesJson log)]

def scriptedOut : Outcome Log (Except IoError UInt64) String Empty → Json
  | .returned r log => returnedJson (exceptJson ioErrorJson u64Json r) (logJson log)
  | .unwound m log => Json.mkObj [("exit", "unwound"), ("reason", Json.str m), ("state", logJson
    log)]
  | .terminated e => nomatch e

def scriptedChecker : Checker where
  function := "solana_borsh::v1::try_from_slice_unchecked"
  generics := [("T", "conformance_instructions_3_4_0_bincode::borsh_unchecked::Scripted")]
  reference := "Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_run"
  decides := ["Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_run"]
  check := fun c => do
    let before ← logState c.state
    let input ← asBytes (← field c.args "data")
    let s ← script (← field c.args "script")
    let recorded ← parseOutcome (asExcept ioError u64Parse) logState (fun m => some m) noReason
      c.outcome
    pure (decideGraph _ _ (scripted_evaluated s before input) recorded scriptedOut)

def checkers : List Checker :=
  [V161.u8, V161.u32, V161.option V161.u8, V161.byteArray 32].map realChecker ++ [scriptedChecker]

end SolanalibTest.Conformance.Library.Families.Instructions.SolanaBorsh
