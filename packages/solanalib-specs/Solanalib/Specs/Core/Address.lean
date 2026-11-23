/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.Prims

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address

/-- A mathematical address has exactly the 32 bytes of the SDK. -/
abbrev Value := _root_.Solanalib.Runtime.Pubkey

/-- An array argument records its exact length; it is never padded or truncated. -/
abbrev Array32 := { bytes : _root_.Solanalib.Runtime.Bytes // bytes.length = 32 }

def newFromArray (array : Array32) : Value := ⟨array.val, array.property⟩

def asArray (address : Value) : Array32 := ⟨address.bytes, address.length_eq⟩

def equal (left right : Value) : Bool := decide (left.bytes = right.bytes)

@[simp] theorem newFromArray_bytes (array : Array32) :
    (newFromArray array).bytes = array.val := rfl

@[simp] theorem newFromArray_asArray (address : Value) :
    newFromArray (asArray address) = address := by cases address; rfl

@[simp] theorem asArray_newFromArray (array : Array32) :
    asArray (newFromArray array) = array := by cases array; rfl

/-- Explicit hash and curve functions; no concrete cryptography is proved here. -/
structure Crypto where
  primitives : _root_.Solanalib.Runtime.CryptoPrimitives

def isOnCurve (crypto : Crypto) (address : Value) : Bool :=
  crypto.primitives.onCurve address.bytes

/-- Inputs to the pure cryptographic PDA observation. The selected syscall
wrapper and its finite state effects are modeled in AddressSyscall. -/
structure SearchArgs where
  crypto : Crypto
  seeds : List _root_.Solanalib.Runtime.Bytes
  programId : Value

/-- Reuse the canonical search, which tries bump 255 through 1 and never 0.
The returned bytes pass through `Pubkey.ofBytes`; their source hash-width
correspondence remains a separate binding obligation. -/
def tryFind (args : SearchArgs) : Option (Value × UInt8) :=
  (_root_.Solanalib.Runtime.findProgramAddressBytes args.crypto.primitives args.seeds
    args.programId.bytes).map fun result =>
      (_root_.Solanalib.Runtime.Pubkey.ofBytes result.1, UInt8.ofNat result.2)

inductive SearchPanic where
  | noViableProgramAddress
  deriving DecidableEq, Repr

/-- Pure search/panic facet. This does not describe runtime syscall admission,
metering or finite failures when a mathematical PDA answer exists. The primary
selected-Solana family and its conditional projection are in AddressSyscall. -/
def findPost (args : SearchArgs)
    (outcome : Solanalib.Contracts.Model.Outcome Unit (Value × UInt8) SearchPanic SearchPanic) :
    Prop :=
  match outcome with
  | .returned result _ => tryFind args = some result
  | .unwound .noViableProgramAddress _ | .terminated .noViableProgramAddress =>
      tryFind args = none

/-- This pure mathematical reference uses the aborting panic strategy after
mathematical search failure. It is an observation, not the finite-outcome implementation model of
the selected syscall. -/
def findOutcome (args : SearchArgs) :
    Solanalib.Contracts.Model.Outcome Unit (Value × UInt8) SearchPanic SearchPanic :=
  match tryFind args with
  | some result => .returned result ()
  | none => .terminated .noViableProgramAddress

def findReference (_ : Unit) (args : SearchArgs)
    (outcome : Solanalib.Contracts.Model.Outcome Unit (Value × UInt8) SearchPanic SearchPanic) :
    Prop := outcome = findOutcome args

theorem findOutcome_satisfies (args : SearchArgs) : findPost args (findOutcome args) := by
  unfold findOutcome
  cases result : tryFind args <;> simp [findPost, result]

/-- An inhabited cryptographic interpretation used only for model witnesses.
It is explicitly not a SHA-256 or curve implementation. -/
def witnessCrypto : Crypto where
  primitives := { sha256 := fun _ => List.replicate 32 0, onCurve := fun _ => false }

def witnessSearch : SearchArgs := ⟨witnessCrypto, [], .zero⟩

end Solanalib.Specs.Core.Address
