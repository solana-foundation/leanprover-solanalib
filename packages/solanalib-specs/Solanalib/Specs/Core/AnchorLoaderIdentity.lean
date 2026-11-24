/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoader

/-- Identity of the borrowed AccountInfo record, separate from the two Rc
cell handles it contains. Distinct records can contain aliases of both cells. -/
structure Reference where
  /-- Stable identity of the referenced record; a source binding must establish its actual
  address/lifetime correspondence. -/
  id : Nat
  /-- The scalar metadata and actual cell/owner-reference aliases of the record. -/
  info : AccountInfo.Value
  deriving DecidableEq, Repr

/-- AccountLoader owns no payload or data lease. Its PhantomData carries only
the source type; the one stored reference retains the original record identity. -/
structure Value (Payload : Type) where
  /-- The exact borrowed AccountInfo record. -/
  account : Reference
  deriving DecidableEq, Repr

/-- The common loading model receives the same underlying AccountInfo alias. -/
def Value.loader {Payload : Type} (value : Value Payload) : AnchorAccount.Loader Payload :=
  ⟨value.account.info⟩

/-- Derived Clone copies the reference and PhantomData. It does not clone
the Rc fields of AccountInfo, call `T::clone`, or acquire a data lease. -/
def clone {Payload : Type} (value : Value Payload) : Value Payload := value

/-- AsRef returns the stored record reference itself, retaining its identity. -/
def asRef {Payload : Type} (value : Value Payload) : Reference := value.account

/-- Both projection families are independent of the surrounding state type. -/
abbrev IdentityIndex := AnchorAccount.ProjectionIndex

def cloneFamily : Family := AnchorAccount.projectionFamily Value Value (fun _ => clone)
def cloneReference : FamilyRun cloneFamily :=
  AnchorAccount.projectionRun Value Value (fun _ => clone)
theorem clone_reference : FamilyReference cloneFamily cloneReference :=
  AnchorAccount.projection_reference Value Value (fun _ => clone)

def asRefFamily : Family :=
  AnchorAccount.projectionFamily Value (fun _ => Reference) (fun _ => asRef)
def asRefReference : FamilyRun asRefFamily :=
  AnchorAccount.projectionRun Value (fun _ => Reference) (fun _ => asRef)
theorem asRef_reference : FamilyReference asRefFamily asRefReference :=
  AnchorAccount.projection_reference Value (fun _ => Reference) (fun _ => asRef)

def identitySample : IdentityIndex := ⟨AccountInfo.State, Nat⟩
def sampleReference : Reference := ⟨7, AccountInfo.sampleInfo⟩
def sampleValue : Value Nat := ⟨sampleReference⟩

theorem clone_execution : FamilyHasExecution cloneFamily cloneReference identitySample :=
  ⟨AccountInfo.sampleState, sampleValue, .returned sampleValue AccountInfo.sampleState, trivial,
    rfl⟩

theorem asRef_execution : FamilyHasExecution asRefFamily asRefReference identitySample :=
  ⟨AccountInfo.sampleState, sampleValue, .returned sampleReference AccountInfo.sampleState,
    trivial, rfl⟩

end Solanalib.Specs.Core.AnchorLoader
