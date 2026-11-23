/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Instruction.Borrowed

/-- A borrowed metadata constructor retains the exact supplied address
reference and sets its flags. It does not acquire, copy or validate its key. -/
def metaFamily (writable signer : Bool) : Family where
  Index := Type
  State := fun _ => Unit
  Args := fun Ref => Ref
  Value := RefMeta
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True)
    (fun before ref value after => after = before ∧ value.address = ref ∧
      value.isWritable = writable ∧ value.isSigner = signer)

def metaRun (writable signer : Bool) : FamilyRun (metaFamily writable signer) :=
  fun _ => returnsOf (fun before ref => (⟨ref, signer, writable⟩, before))

theorem meta_reference (writable signer : Bool) :
    FamilyReference (metaFamily writable signer) (metaRun writable signer) := by
  intro Ref
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl, rfl, rfl⟩

def metaSample : Type := Nat

theorem meta_hasExecution (writable signer : Bool) :
    FamilyHasExecution (metaFamily writable signer) (metaRun writable signer) metaSample :=
  ⟨(), (17 : Nat), .returned ⟨(17 : Nat), signer, writable⟩ (), trivial, rfl⟩

/-- The array reference and its source const parameter remain explicit. -/
structure SeedIndex where
  Ref : Type
  size : Nat

structure SeedRef (Ref : Type) where
  source : Ref
  length : Nat
  deriving DecidableEq, Repr

/-- A Seed is only a retained pointer and length; this constructor has no PDA
seed-size check and no allocation, including at size zero. -/
def seedArrayFamily : Family where
  Index := SeedIndex
  State := fun _ => Unit
  Args := SeedIndex.Ref
  Value := fun index => SeedRef index.Ref
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun index => .returning (fun _ _ => True)
    (fun before ref value after => after = before ∧ value.source = ref ∧ value.length = index.size)

def seedArrayRun : FamilyRun seedArrayFamily :=
  fun index => returnsOf (fun before ref => (⟨ref, index.size⟩, before))

theorem seedArray_reference : FamilyReference seedArrayFamily seedArrayRun := by
  intro index
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl, rfl⟩

def seedArraySample : SeedIndex := ⟨Nat, 0⟩
theorem seedArray_hasExecution : FamilyHasExecution seedArrayFamily seedArrayRun seedArraySample :=
  ⟨(), (23 : Nat), .returned ⟨(23 : Nat), 0⟩ (), trivial, rfl⟩

end Solanalib.Specs.Core.Instruction.Borrowed
