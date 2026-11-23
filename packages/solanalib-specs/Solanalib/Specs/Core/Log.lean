/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Log

/-- Events retain the arguments supplied to the selected backend. In particular,
binary field boundaries are not lost to the flattened log
observation of the canonical runtime, and host output is not called a validator log. -/
inductive Event where
  | text (utf8 : Solanalib.Runtime.Bytes)
  | data (fields : List Solanalib.Runtime.Bytes)
  | stdoutLine (message : String)
  | stubData (fields : List Solanalib.Runtime.Bytes)
  deriving DecidableEq, Repr

def utf8Bytes (message : String) : Solanalib.Runtime.Bytes := message.toUTF8.data.toList

/-- Projection to the raw log observation of the existing runtime model. Display
prefixes, base64 formatting, and host stdout are outside that abstraction. -/
def Event.runtimeBytes : Event → Option Solanalib.Runtime.Bytes
  | .text bytes => some bytes
  | .data fields => some fields.flatten
  | .stdoutLine _ | .stubData _ => none

inductive TextTarget where
  | solana
  | hostStd
  | hostNoStd
  deriving DecidableEq, Repr

inductive DataTarget where
  | solana
  | hostStub
  deriving DecidableEq, Repr

universe u v w

/-- `sol_log(&str)` selects a syscall, `println!`, or `black_box` according to
its actual cfg. Backend exceptions and their state effects are explicit. -/
def textCall {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (target : TextTarget) (sink : Callback.Run State Event Unit Unwind Terminal) :
    Callback.Run State String Unit Unwind Terminal :=
  fun before message outcome => match target with
  | .solana => sink before (.text (utf8Bytes message)) outcome
  | .hostStd => sink before (.stdoutLine message) outcome
  | .hostNoStd => outcome = .returned () before

/-- The source wrapper forwards nested fields unchanged to the syscall or
host stub. A concrete sink is responsible for logging, cost and failure. -/
def dataCall {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (target : DataTarget) (sink : Callback.Run State Event Unit Unwind Terminal) :
    Callback.Run State (List Solanalib.Runtime.Bytes) Unit Unwind Terminal :=
  fun before fields outcome => match target with
  | .solana => sink before (.data fields) outcome
  | .hostStub => sink before (.stubData fields) outcome

@[simp] theorem text_solana {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (sink : Callback.Run State Event Unit Unwind Terminal) (before : State)
    (message : String) (outcome : Outcome State Unit Unwind Terminal) :
    textCall .solana sink before message outcome ↔
      sink before (.text (utf8Bytes message)) outcome := Iff.rfl

@[simp] theorem text_host_no_std {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (sink : Callback.Run State Event Unit Unwind Terminal) (before : State)
    (message : String) (outcome : Outcome State Unit Unwind Terminal) :
    textCall .hostNoStd sink before message outcome ↔ outcome = .returned () before := Iff.rfl

@[simp] theorem data_solana {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (sink : Callback.Run State Event Unit Unwind Terminal) (before : State)
    (fields : List Solanalib.Runtime.Bytes) (outcome : Outcome State Unit Unwind Terminal) :
    dataCall .solana sink before fields outcome ↔
      sink before (.data fields) outcome := Iff.rfl

/-- An inhabited trace sink for closed mathematical witnesses. It does not
model compute exhaustion or prove anything about a runtime logging backend. -/
def appendEvent (before : List Event) (event : Event) :
    Outcome (List Event) Unit String String := .returned () (before ++ [event])

end Solanalib.Specs.Core.Log
