/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Witness

open Solanalib.Runtime

/-- Closed deterministic primitive fixtures. These functions establish model
consistency only; they assert no cryptographic implementation correspondence. -/
def primitives : Prims where
  sha256 := fun _ => List.replicate 32 0
  onCurve := fun _ => false
  keccak256 := fun _ => List.replicate 32 0
  blake3 := fun _ => List.replicate 32 0
  sha512 := fun _ => List.replicate 64 0
  sha256_length := fun _ => List.length_replicate
  keccak256_length := fun _ => List.length_replicate
  blake3_length := fun _ => List.length_replicate
  sha512_length := fun _ => List.length_replicate
  isUtf8 := fun _ => true
  secp256k1Recover := fun _ _ _ => .error 2
  poseidon := fun _ _ _ => none
  curveValidate := fun _ _ => false
  curveGroupOp := fun _ _ _ _ => none
  curveMultiscalarMul := fun _ _ _ => none
  curveDecompress := fun _ _ => none
  curvePairingMap := fun _ _ _ => none
  altBn128GroupOp := fun _ _ => none
  altBn128Compression := fun _ _ => none
  bigModExp := fun _ _ modulus => List.replicate modulus.length 0
  bigModExpLe := fun _ _ _ => none
  precompileVerify := fun _ _ _ => none

def programId : Pubkey := .ofNat 17
def callerId : Pubkey := .ofNat 99

def caller : Frame := ⟨1, [⟨0, false, false⟩], []⟩

def context : InvCtx where
  abi := .v1
  cfg := .L
  frame := caller
  layout := []
  heapSize := DEFAULT_HEAP_SIZE

/-- The complete mock callee contract is an identity transition. It supplies
neither an invocation wrapper implementation nor a deployed callee proof. -/
def index : Index :=
  ⟨mainnet, primitives, context, fun state _ result => result = .ok state⟩

def tx : TxState where
  keys := [programId, callerId]
  accts := [⟨1, [], Ids.nativeLoader, true, 0⟩, ⟨1, [], Ids.nativeLoader, true, 0⟩]
  lamportsDelta := 0
  resizeDelta := 0
  stack := [caller]
  trace := []
  returnData := (callerId, [])
  topIndex := 0

def before : InvState := ⟨tx, [], 0, []⟩

def request : CpiReq := ⟨⟨programId, [], [7, 9]⟩, [], true, []⟩

/-- Closed normal execution traverses the canonical preparation and copyback
relations and uses only the declared mock callee result. -/
def success : Success index before request where
  prepared := ⟨⟨0, [], [7, 9]⟩, []⟩
  prepare := rfl
  synchronized := before
  synchronize := rfl
  returned := tx
  execute := rfl
  after := before
  lengths := []
  restore := rfl

theorem unitHasExecution : FamilyHasExecution unitFamily unitRun index :=
  ⟨before, request, .returned () before, trivial, success, rfl⟩

theorem unitSatisfiable : FamilySatisfiable unitFamily index := unitHasExecution.satisfiable

theorem rawHasExecution : FamilyHasExecution rawFamily rawFamilyRun index :=
  ⟨before, request, .returned (0 : UInt64) before, trivial, rfl, success, rfl⟩

theorem rawSatisfiable : FamilySatisfiable rawFamily index := rawHasExecution.satisfiable

def sdkBefore : Sdk.State := ⟨before, ⟨[], []⟩⟩

def unsignedArgs : Sdk.UnsignedArgs := ⟨request.ix, [], true⟩

def signedArgs : Sdk.Args := unsignedArgs.signed

theorem signedHasExecution :
    FamilyHasExecution Sdk.signedFamily Sdk.signedRun index :=
  ⟨sdkBefore, signedArgs, .returned (.ok ()) sdkBefore, trivial,
    Or.inr ⟨rfl, rfl, success, rfl⟩⟩

theorem signedSatisfiable : FamilySatisfiable Sdk.signedFamily index :=
  signedHasExecution.satisfiable

theorem unsignedHasExecution :
    FamilyHasExecution Sdk.unsignedFamily Sdk.unsignedRun index :=
  ⟨sdkBefore, unsignedArgs, .returned (.ok ()) sdkBefore, trivial,
    Or.inr ⟨rfl, rfl, success, rfl⟩⟩

theorem unsignedSatisfiable : FamilySatisfiable Sdk.unsignedFamily index :=
  unsignedHasExecution.satisfiable

end Solanalib.Specs.Core.OpaqueCpi.Witness
