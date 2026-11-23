/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsTypes

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedSeeds

universe u v w x y z a b

variable {State : Type u} {ByteResource : Type v} {SeedResource : Type w}
  {RefResource : Type x} {Unwind : Type y} {Terminal : Type z}

/-- A pure source Result still carries the exact current state. -/
def returnedResult {Value : Type a} (value : Except Error Value) :
    Callback.Run State Unit (Except Error Value) Unwind Terminal :=
  fun before _ outcome => outcome = .returned value before

/-- The question-mark continuation runs only on Ok. Ordinary source errors,
unwinds and terminal exits retain their actual states and reasons. -/
def bindResult {Value : Type a} {Next : Type b}
    (first : Callback.Run State Unit (Except Error Value) Unwind Terminal)
    (next : Value → Callback.Run State Unit (Except Error Next) Unwind Terminal) :
    Callback.Run State Unit (Except Error Next) Unwind Terminal :=
  Callback.bind first fun result after outcome =>
    match result with
    | .ok value => next value after () outcome
    | .error error => outcome = .returned (.error error) after

/-- `Seed::unpack` and its four ordinary helpers, at the pinned 0.11.1 source.
Literal conversion is one actual byte-vector construction before the seed is
returned to its caller. Constructor-internal cleanup belongs to that provider. -/
def unpackOne (bytes : Owned.VectorOps State UInt8 ByteResource Unwind Terminal)
    (input : Bytes) : Callback.Run State Unit (Except Error (Seed ByteResource)) Unwind Terminal :=
  match input with
  | [] => returnedResult (.error .InvalidAccountData)
  | tag :: rest =>
    if tag = 0 then returnedResult (.ok .uninitialized)
    else if tag = 1 then
      match rest with
      | [] => returnedResult (.error Hook.invalidSeedBytes)
      | length :: payload =>
        if payload.length < length.toNat then returnedResult (.error Hook.invalidSeedBytes)
        else Callback.map (fun resource => Except.ok (.literal resource))
          (fun state (_ : Unit) => bytes.fromList state (payload.take length.toNat))
    else if tag = 2 then
      match rest with
      | offset :: length :: _ => returnedResult (.ok (.instructionData offset length))
      | _ => returnedResult (.error Hook.invalidSeedBytes)
    else if tag = 3 then
      match rest with
      | index :: _ => returnedResult (.ok (.accountKey index))
      | _ => returnedResult (.error Hook.invalidSeedBytes)
    else if tag = 4 then
      match rest with
      | index :: offset :: length :: _ => returnedResult (.ok (.accountData index offset length))
      | _ => returnedResult (.error Hook.invalidSeedBytes)
    else returnedResult (.error .InvalidAccountData)

/-- Width read after unpacking a seed from a 32-byte address configuration.
The returned literal vector is observed after its construction callback.
Within this source domain its length is at most 30, so the u8 additions and
the usize loop counter cannot overflow. An absent or wider observation is a
failed provider/source representation, not an invented source error. -/
def widthAt (bytes : Owned.VectorOps State UInt8 ByteResource Unwind Terminal)
    (state : State) : Seed ByteResource → Option Nat
  | .uninitialized => some 0
  | .literal resource => do
    let current ← bytes.current state resource
    if current.length ≤ 30 then some (2 + current.length) else none
  | .instructionData _ _ => some 3
  | .accountKey _ => some 2
  | .accountData _ _ _ => some 4

/-- The unpacking loop reads the same configuration after every callback.
Its local offset advances using the width read before the seed push. A literal
is moved into that push; the caller does not retain a second cleanup owner. -/
def unpackFrom (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (configurationAt : State → Option Solanalib.Runtime.Pubkey) (resource : SeedResource)
    (offset : Nat) (before : State)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) : Prop :=
  if offset < 32 then
    ∃ configuration, configurationAt before = some configuration ∧
      ∃ decoded, unpackOne ops.bytes (configuration.bytes.drop offset) before () decoded ∧
        match decoded with
        | .returned (.error error) after => outcome = .returned (.error error) after
        | .returned (.ok seed) after =>
          ∃ width, widthAt ops.bytes after seed = some width ∧
            match seed with
            | .uninitialized => outcome = .returned (.ok ()) after
            | _ =>
              if _positive : 0 < width then
                Callback.bind (fun state (_ : Unit) => ops.seeds.push state (resource, seed))
                  (fun _ state result => unpackFrom ops configurationAt resource
                    (offset + width) state result) after () outcome
              else False
        | .unwound reason after => outcome = .unwound reason after
        | .terminated reason => outcome = .terminated reason
  else outcome = .returned (.ok ()) before
termination_by 32 - offset
decreasing_by omega

/-- `Seed::unpack_address_config` constructs its empty vector before decoding.
Only Ok transfers the resulting owner. Err and unwind drop the actual current
seed vector, including its owned literal elements through the provider; terminal
exits bypass cleanup. A second unwind follows the supplied terminal policy. -/
def unpack (ops : Ops State ByteResource SeedResource RefResource Unwind Terminal)
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (configurationAt : State → Option Solanalib.Runtime.Pubkey) :
    Callback.Run State Unit (Except Error SeedResource) Unwind Terminal :=
  fun before _ outcome =>
    ∃ configuration, configurationAt before = some configuration ∧
      let allocated := ops.seeds.empty before
      ∃ pending, unpackFrom ops configurationAt allocated.1 0 allocated.2 pending ∧
        let moved : Outcome State (Except Error SeedResource) Unwind Terminal :=
          Outcome.map (fun (result : Except Error Unit) => result.map (fun _ => allocated.1))
            pending
        match moved with
        | .returned (.ok resource) after => outcome = .returned (.ok resource) after
        | .returned (.error _) _ | .unwound _ _ | .terminated _ =>
          Owned.cleanup double [ops.seeds.dropAction allocated.1] moved outcome

end Solanalib.Specs.Core.Token.AllocatedSeeds
