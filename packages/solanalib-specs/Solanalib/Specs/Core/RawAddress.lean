/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.RawRuntime

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.RawAddress

open RawRuntime

/-- Seed order, duplicates, empty slices and the program identity are all retained. -/
structure Args where
  seeds : List Solanalib.Runtime.Bytes
  programId : Solanalib.Runtime.Pubkey
  deriving Repr

/-- Find-address additionally checks its two destination ranges on success. -/
structure FindArgs extends Args where
  addressDst : Nat
  bumpDst : Nat
  deriving Repr

/-- The create request of the runtime: excessive count/length terminates, on-curve derivation
returns one without a write, and success writes exactly the derived address. -/
def createStep : Step Args := fun index before args =>
  invoke index before (.createProgramAddress args.seeds args.programId)

/-- Runtime address search retains the 255-through-1 bump search and success-only output check. -/
def findStep : Step FindArgs := fun index before args =>
  invoke index before (.tryFindProgramAddress args.seeds args.programId args.addressDst
    args.bumpDst)

/-- The create request result, preserving request-phase state and checking seeds before derivation.
-/
theorem create_result (index : Index) (before : Solanalib.Runtime.InvState) (args : Args) :
    createStep index before args =
      if Solanalib.Runtime.MAX_SEEDS < args.seeds.length ||
          args.seeds.any (fun seed => decide (Solanalib.Runtime.MAX_SEED_LEN < seed.length)) then
        .error .ProgramFailedToComplete
      else match Solanalib.Runtime.createProgramAddress index.world.prims args.seeds args.programId
        with
        | .ok key => .ok (⟨0, [key.bytes]⟩, before)
        | .error _ => .ok (⟨1, []⟩, before) := rfl

/-- Search preserves request-phase state; the overlap check cannot turn failed search into error. -/
theorem find_result (index : Index) (before : Solanalib.Runtime.InvState) (args : FindArgs) :
    findStep index before args =
      match Solanalib.Runtime.findAddressReply index.world.prims.toCryptoPrimitives args.seeds
        args.programId.bytes with
      | .error error => .error error
      | .ok answer =>
        if answer.r0 = 0 && !Solanalib.Runtime.nonOverlapping args.addressDst 32 args.bumpDst 1 then
          .error .ProgramFailedToComplete
        else .ok (answer, before) := rfl

/-- Returned addresses have 32 bytes and a u64 status; failure writes nothing. -/
def CreateShape (answer : Solanalib.Runtime.SysAns) : Prop :=
  (∃ key : Solanalib.Runtime.Pubkey, answer = ⟨0, [key.bytes]⟩) ∨ answer = ⟨1, []⟩

/-- Search success returns a 32-byte address and a separate one-byte bump. -/
def FindShape (answer : Solanalib.Runtime.SysAns) : Prop :=
  (∃ (key : Solanalib.Runtime.Pubkey) (bump : UInt8), answer = ⟨0, [key.bytes, [bump]]⟩) ∨
    answer = ⟨1, []⟩

/-- The complete output shape and all invocation fields follow from a successful create call. -/
theorem create_shape (index : Index) (before after : Solanalib.Runtime.InvState) (args : Args)
    (answer : Solanalib.Runtime.SysAns) (result : createStep index before args = .ok (answer,
      after)) :
    CreateShape answer ∧ after = before := by
  rw [create_result] at result
  split at result
  · cases result
  · split at result
    · next key _ => cases result; exact ⟨Or.inl ⟨key, rfl⟩, rfl⟩
    · cases result; exact ⟨Or.inr rfl, rfl⟩

/-- A successful find call preserves every invocation field and has exactly one of its two
source-observable output shapes. -/
theorem find_shape (index : Index) (before after : Solanalib.Runtime.InvState) (args : FindArgs)
    (answer : Solanalib.Runtime.SysAns) (result : findStep index before args = .ok (answer, after))
      :
    FindShape answer ∧ after = before := by
  rw [find_result] at result
  cases valid : Solanalib.Runtime.seedsOk args.seeds with
  | false => simp [Solanalib.Runtime.findAddressReply, valid] at result
  | true =>
    cases found : Solanalib.Runtime.findProgramAddressBytes index.world.prims.toCryptoPrimitives
        args.seeds args.programId.bytes with
    | none =>
      simp only [Solanalib.Runtime.findAddressReply, valid, Bool.not_true, Bool.false_eq_true,
        ite_false,
        found, Nat.reduceEqDiff] at result
      cases result
      exact ⟨Or.inr rfl, rfl⟩
    | some pair =>
      rcases pair with ⟨key, bump⟩
      simp only [Solanalib.Runtime.findAddressReply, valid, Bool.not_true, Bool.false_eq_true,
        ite_false,
        found] at result
      split at result
      · cases result
      · cases result
        exact ⟨Or.inl ⟨Solanalib.Runtime.Pubkey.ofBytes key, UInt8.ofNat bump, rfl⟩, rfl⟩

/-- The seeded search never tries bump zero; this behavior comes from the reused primitive. -/
theorem search_zero (prims : Solanalib.Runtime.CryptoPrimitives) (seeds : List
  Solanalib.Runtime.Bytes)
    (program : Solanalib.Runtime.Bytes) : Solanalib.Runtime.findProgramAddressBytes.go prims seeds
      program 0 = none := rfl

end Solanalib.Specs.Core.RawAddress
