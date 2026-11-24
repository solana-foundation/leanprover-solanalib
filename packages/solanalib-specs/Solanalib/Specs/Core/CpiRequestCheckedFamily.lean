/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestChecked
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

/-- Shared state and its current AccountView pool. The source binding must
identify legal live handles and preserve their interpretation at each actual
access; the total mathematical pool projection is not a pointer-validity proof. -/
structure Types where
  /-- Complete state exposed by the supplied dependency interpretations. -/
  State : Type
  /-- Current shared account contents and borrow leases. -/
  pool : State → AccountView.State
  /-- Finite unwind reasons admitted by the dependency interpretation. -/
  Unwind : Type
  /-- Terminal reasons admitted by the dependency interpretation. -/
  Terminal : Type

/-- V2 additionally observes the actual raw header at each initialization.
The source binding relates these bytes and the Boolean observations of the pool at
legal current handles; neither an arbitrary 0/1 restriction nor padding
irrelevance is assumed by the checked wrapper. -/
structure HeaderTypes extends Types where
  /-- Current signer, writable, executable and padding bytes for each handle. -/
  rawHeader : State → AccountView.Handle → RawHeader

/-- The v2 monomorphized account type and its selected `AsRef` implementation.
No purity, identity stability or frame property is silently assumed. -/
structure ArrayTypes extends HeaderTypes where
  /-- The source array element type `A`. -/
  Account : Type
  /-- The same trait implementation used by every source `as_ref` call. -/
  asRef : AsRef State Account Unwind Terminal

/-- The array cardinality is a const generic in Rust. The exact extent is
structural; the upper bound of the source of 64 is an instantiation obligation,
not a restriction on the mathematical branch relation or a runtime error. -/
structure StaticAccounts (Account : Type) where
  /-- Const-generic array cardinality. -/
  size : Nat
  /-- Ordered elements, including repeated references and unused trailing entries. -/
  values : List Account
  /-- The exact array extent. -/
  length_eq : values.length = size

/-- Arguments of the checked v2 fixed-array entry. -/
structure ArrayCall (types : ArrayTypes) where
  /-- Immutable source instruction observation. -/
  instruction : Solanalib.Runtime.CpiInstruction
  /-- Complete input array before prefix validation. -/
  accounts : StaticAccounts types.Account
  /-- Ordered nested signer seeds. -/
  signers : List (List Solanalib.Runtime.Bytes)
  /-- Opaque unchecked invocation of the initialized prefix. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Checked v2 array family; all callback exits are represented. Binding a
Rust instance separately justifies its compile-time capacity restriction. -/
def arrayFamily : Family where
  Index := ArrayTypes
  State := fun types => types.State
  Args := ArrayCall
  Value := fun _ => Except Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => innerV2 types.pool types.rawHeader types.asRef args.invoke before
      ⟨args.instruction, args.accounts.values, args.signers⟩ }

/-- The actual mathematical checked array reference. -/
def arrayRun : FamilyRun arrayFamily := fun types before args =>
  innerV2 types.pool types.rawHeader types.asRef args.invoke before
    ⟨args.instruction, args.accounts.values, args.signers⟩

/-- Exact reference correctness, independent of provider success or termination. -/
theorem arrayReference : FamilyReference arrayFamily arrayRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- A finite concrete account pool with distinct addresses and no live leases. -/
def samplePool : AccountView.State :=
  ⟨(List.range 10).map (fun n =>
    ⟨{ AccountView.Account.empty with metadata := ⟨.ofNat n, false, true, false⟩ },
      Borrow.Policy.accountView⟩), []⟩

/-- A closed state interpretation whose natural number records dependency effects. -/
def sampleTypes : Types := ⟨Nat, fun _ => samplePool, Nat, Nat⟩

/-- Canonical raw bytes are an explicit choice of the closed sample only. -/
def sampleHeaderTypes : HeaderTypes where
  toTypes := sampleTypes
  rawHeader := fun _ => normalizedHeader samplePool

/-- The concrete borrowed-AccountView v2 trait instance. -/
def sampleArrayTypes : ArrayTypes where
  toHeaderTypes := sampleHeaderTypes
  Account := AccountView.Handle
  asRef := identityAsRef

/-- A two-account instruction with asymmetric source flags. -/
def sampleInstruction : Solanalib.Runtime.CpiInstruction :=
  Instruction.make .zero
    [Instruction.accountMeta (.ofNat 1) true false,
      Instruction.accountMeta (.ofNat 2) false true] [7, 9]

/-- Normal opaque completion changes state according to the actual prefix size. -/
def sampleProvider : Syscall Nat Nat Nat := fun before request outcome =>
  outcome = .returned () (before + request.accounts.length)

/-- A nonempty v2 input also includes an unused trailing reference. -/
def sampleArray : ArrayCall sampleArrayTypes where
  instruction := sampleInstruction
  accounts := ⟨3, [⟨1⟩, ⟨2⟩, ⟨7⟩], rfl⟩
  signers := [[], [[], [8, 9]]]
  invoke := sampleProvider

/-- The checked array family has a concrete admissible input. -/
theorem arraySatisfiable : FamilySatisfiable arrayFamily sampleArrayTypes :=
  ⟨(0 : Nat), sampleArray, trivial⟩


end Solanalib.Specs.Core.CpiRequest.Checked
