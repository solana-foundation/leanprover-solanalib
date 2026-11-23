/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorViewsFacts
public import Solanalib.Specs.Core.AnchorViewsLamports

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViews

structure ProjectionTypes where
  Payload : Type
  Aux : Type

/-- Shared payload access returns a live field reference, with no snapshot,
new owner, callback or independent lifetime. -/
def sharedFamily : Family where
  Index := ProjectionTypes
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => PayloadRef
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => {
    requires := fun before guard => Readable before.1 guard
    post := returnsOf (payloadReference false) }

def sharedReference : FamilyRun sharedFamily := fun _ => returnsOf (payloadReference false)

theorem shared_reference : FamilyReference sharedFamily sharedReference := by
  intro _ _ _ _ _ called
  exact called

/-- the mutable projection of Sysvar has no anchor-debug check. Its exclusive
parent loan authorizes field mutation without changing the serialized bytes. -/
def sysvarMutableFamily : Family where
  Index := ProjectionTypes
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => PayloadRef
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => {
    requires := fun before guard => Writable before.1 guard
    post := returnsOf (payloadReference true) }

def sysvarMutableReference : FamilyRun sysvarMutableFamily :=
  fun _ => returnsOf (payloadReference true)

theorem sysvarMutable_reference : FamilyReference sysvarMutableFamily sysvarMutableReference := by
  intro _ _ _ _ _ called
  exact called

def infoFamily (storage : InfoStorage) : Family where
  Index := ProjectionTypes
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => InfoRef
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => {
    requires := fun before guard => Readable before.1 guard
    post := returnsOf (infoReference storage) }

def infoRun (storage : InfoStorage) : FamilyRun (infoFamily storage) :=
  fun _ => returnsOf (infoReference storage)

theorem info_reference (storage : InfoStorage) : FamilyReference (infoFamily storage) (infoRun
  storage) := by
  intro _ _ _ _ _ called
  exact called

/-- the source receiver of Key remains borrowed, but its returned Pubkey/Address
is an ordinary copied value. It establishes no signer or owner authorization. -/
def keyFamily : Family where
  Index := ProjectionTypes
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => Solanalib.Runtime.Pubkey
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => {
    requires := fun before guard => Readable before.1 guard
    post := returnsOf keyReference }

def keyRun : FamilyRun keyFamily := fun _ => returnsOf keyReference

theorem key_reference : FamilyReference keyFamily keyRun := by
  intro _ _ _ _ _ called
  exact called

/-- Key for Pubkey/Address copies the complete address and preserves any
ambient state. Its defining crate identity is supplied per reviewed release. -/
def pubkeyFamily : Family where
  Index := Type
  State := id
  Args := fun _ => Solanalib.Runtime.Pubkey
  Value := fun _ => Solanalib.Runtime.Pubkey
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => {
    requires := fun _ _ => True
    post := returnsOf (fun before key => (key, before)) }

def pubkeyRun : FamilyRun pubkeyFamily := fun _ => returnsOf (fun before key => (key, before))

theorem pubkey_reference : FamilyReference pubkeyFamily pubkeyRun := by
  intro _ _ _ _ _ called
  exact called

def mutableFamily : Family where
  Index := MutableTypes
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => PayloadRef
  Unwind := MutableTypes.Unwind
  Terminal := MutableTypes.Terminal
  contract := fun i => {
    requires := fun before guard => Writable before.1 guard
    post := mutableRun i }

def mutableReference : FamilyRun mutableFamily := mutableRun

theorem mutable_reference : FamilyReference mutableFamily mutableReference := by
  intro _ _ _ _ _ called
  exact called

def cloneFamily (storage : InfoStorage) : Family where
  Index := CloneTypes storage
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => Borrow.Handle
  Unwind := CloneTypes.Unwind
  Terminal := CloneTypes.Terminal
  contract := fun i => {
    requires := fun before guard => Readable before.1 guard
    post := cloneRun storage i }

def cloneReference (storage : InfoStorage) : FamilyRun (cloneFamily storage) := cloneRun storage

theorem clone_reference (storage : InfoStorage) :
    FamilyReference (cloneFamily storage) (cloneReference storage) := by
  intro _ _ _ _ _ called
  exact called

def infoCloneFamily (storage : InfoStorage) : Family where
  Index := InfoCloneTypes storage
  State := fun i => World Unit i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => Borrow.Handle
  Unwind := fun _ => Empty
  Terminal := InfoCloneTypes.Terminal
  contract := fun i => {
    requires := fun before guard => Readable before.1 guard
    post := infoCloneRun storage i }

def infoCloneReference (storage : InfoStorage) : FamilyRun (infoCloneFamily storage) :=
  infoCloneRun storage

theorem infoClone_reference (storage : InfoStorage) :
    FamilyReference (infoCloneFamily storage) (infoCloneReference storage) := by
  intro _ _ _ _ _ called
  exact called

def intoInnerFamily (storage : InfoStorage) : Family where
  Index := MoveTypes storage
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Handle
  Value := MoveTypes.Payload
  Unwind := fun _ => Empty
  Terminal := MoveTypes.Terminal
  contract := fun i => {
    requires := fun before handle => Movable before.1 handle
    post := intoInnerRun storage i }

def intoInnerReference (storage : InfoStorage) : FamilyRun (intoInnerFamily storage) :=
  intoInnerRun storage

theorem intoInner_reference (storage : InfoStorage) :
    FamilyReference (intoInnerFamily storage) (intoInnerReference storage) := by
  intro _ _ _ _ _ called
  exact called

def setInnerFamily : Family where
  Index := SetTypes
  State := fun i => World i.Payload i.Aux
  Args := fun i => Borrow.Guard × i.Payload
  Value := fun _ => Unit
  Unwind := SetTypes.Unwind
  Terminal := SetTypes.Terminal
  contract := fun i => {
    requires := fun before args => Writable before.1 args.1
    post := setInnerRun i }

def setInnerReference : FamilyRun setInnerFamily := setInnerRun

theorem setInner_reference : FamilyReference setInnerFamily setInnerReference := by
  intro _ _ _ _ _ called
  exact called

def sysvarCloneFamily (storage : InfoStorage) : Family where
  Index := SysvarCloneTypes storage
  State := fun i => World i.Payload i.Aux
  Args := fun _ => Borrow.Guard
  Value := fun _ => Borrow.Handle
  Unwind := SysvarCloneTypes.Unwind
  Terminal := SysvarCloneTypes.Terminal
  contract := fun i => {
    requires := fun before guard => Readable before.1 guard
    post := sysvarCloneRun storage i }

def sysvarCloneReference (storage : InfoStorage) : FamilyRun (sysvarCloneFamily storage) :=
  sysvarCloneRun storage

theorem sysvarClone_reference (storage : InfoStorage) :
    FamilyReference (sysvarCloneFamily storage) (sysvarCloneReference storage) := by
  intro _ _ _ _ _ called
  exact called

end Solanalib.Specs.Core.AnchorViews
