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

namespace Solanalib.Specs.Core.RawRuntime.Sample

/-- A closed consistency interpretation with correctly sized outputs. It does not implement
hashing, curve arithmetic or any deployed cryptography. -/
def primitives : Solanalib.Runtime.Prims where
  sha256 := fun _ => List.replicate 32 7
  onCurve := fun _ => false
  keccak256 := fun _ => List.replicate 32 0
  blake3 := fun _ => List.replicate 32 0
  sha512 := fun _ => List.replicate 64 0
  sha256_length := fun _ => by simp
  keccak256_length := fun _ => by simp
  blake3_length := fun _ => by simp
  sha512_length := fun _ => by simp
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
  bigModExp := fun _ _ _ => []
  bigModExpLe := fun _ _ _ => none
  precompileVerify := fun _ _ _ => none

/-- Nontrivial fixed sysvar values for reference executions and tests. -/
def sysvars : Solanalib.Runtime.Sysvars where
  clock := ⟨17, -3, 2, 3, 41⟩
  epochSchedule := ⟨432000, 432000, true, 14, 524256⟩
  rent := Solanalib.Runtime.mainnetRent.toSysvar
  epochRewards := none
  lastRestartSlot := none
  feesLamportsPerSignature := 0
  data := fun _ => none

/-- The existing mainnet runtime profile, with the closed symbolic primitives above. -/
def world : Solanalib.Runtime.World where
  prof := Solanalib.Runtime.mainnet
  prims := primitives
  sysvars := sysvars
  epochStake := fun _ => 0
  heapSize := Solanalib.Runtime.DEFAULT_HEAP_SIZE
  builtins := fun _ => none
  programs := fun _ => .notDeployed

/-- One currently active instruction. -/
def frame : Solanalib.Runtime.Frame := ⟨0, [], [1, 2]⟩

/-- ABI v1, in the existing copying-memory configuration. -/
def context : Solanalib.Runtime.InvCtx := ⟨.v1, .L, frame, [], Solanalib.Runtime.DEFAULT_HEAP_SIZE,
  .agave_4_3_2⟩

/-- A closed index used by every raw-runtime reference witness. -/
def index : Index := ⟨world, context⟩

/-- The state has nonempty input, return data, a log and a live frame so preservation claims
are not witnessed only by an empty state. -/
def state : Solanalib.Runtime.InvState where
  ts := {
    keys := [Solanalib.Runtime.Pubkey.ofNat 7]
    accts := []
    lamportsDelta := 0
    resizeDelta := 0
    stack := [frame]
    trace := []
    returnData := (Solanalib.Runtime.Pubkey.ofNat 9, [2, 3])
    topIndex := 0 }
  buf := [5, 6]
  heapPos := 17
  logs := [[99]]

end Solanalib.Specs.Core.RawRuntime.Sample
