/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtension
public import Solanalib.Specs.Core.TokenFee

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The packed transfer-fee record occupies 18 bytes with alignment one. -/
def transferFeeLength : Nat := 18

/-- Interpret one fee record at its layout offset. This projection alone does
not admit a byte buffer: callers establish the full 18-byte range. -/
def observeTransferFeeAt (bytes : Bytes) (offset : Nat) : TransferFee where
  epoch := UInt64.ofNat (Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes offset 8))
  maximumFee := UInt64.ofNat (Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes (offset + 8)
    8))
  basisPoints := UInt16.ofNat (Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes (offset + 16)
    2))

/-- The concrete Pod type used by get_extension for a fee configuration. -/
def transferFeeConfigPod : ExtensionPod := ⟨.transferFeeConfig, 108, 1⟩

/-- Observe the fixed configuration layout: two nullable addresses, withheld
amount, then the older and newer packed fee records. This projection does not
add configuration-policy checks that bytemuck does not perform. -/
def observeTransferFeeConfig (bytes : Bytes) : TransferFeeConfig where
  configAuthority := .ofBytes (Solanalib.Runtime.slice bytes 0 32)
  withdrawWithheldAuthority := .ofBytes (Solanalib.Runtime.slice bytes 32 32)
  withheldAmount := UInt64.ofNat (Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes 64 8))
  older := observeTransferFeeAt bytes 72
  newer := observeTransferFeeAt bytes 90

/-- The logical representation of the fee configuration is reusable by the generic
typed extension contract, while retaining its actual selected byte range. -/
def transferFeeConfigRepresentation : ExtensionRepresentation where
  Value := TransferFeeConfig
  pod := transferFeeConfigPod
  observe := observeTransferFeeConfig

/-- Checked decoding of an isolated complete fee record. All u16 rates remain
accepted; validity of a configured rate is a different source operation. -/
def decodeTransferFee (bytes : Bytes) : Except Error TransferFee :=
  if bytes.length = transferFeeLength then .ok (observeTransferFeeAt bytes 0)
  else .error .InvalidArgument

/-- Checked decoding of an isolated complete configuration value. -/
def decodeTransferFeeConfig (bytes : Bytes) : Except Error TransferFeeConfig :=
  if bytes.length = transferFeeConfigPod.byteLength then .ok (observeTransferFeeConfig bytes)
  else .error .InvalidArgument

/-- Complete typed retrieval from the TLV slice of the mint, preserving both
lookup failures and bytemuck layout failures before field observation. -/
def getTransferFeeConfig (tlvAddress : Nat) (bytes : Bytes) :
    Except Error (ExtensionReference TransferFeeConfig) :=
  getRepresentedExtension transferFeeConfigRepresentation .mint tlvAddress bytes

/-- Every complete fee record preserves the entire source epoch word. -/
theorem observeTransferFeeAt_epoch (bytes : Bytes) (offset : Nat)
    (fullRange : offset + transferFeeLength ≤ bytes.length) :
    (observeTransferFeeAt bytes offset).epoch.toNat =
      Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes offset 8) := by
  apply UInt64.toNat_ofNat_of_lt'
  have range : offset + 8 ≤ bytes.length := by
    simp only [transferFeeLength] at fullRange
    omega
  have bound := Solanalib.Runtime.leNat_lt (Solanalib.Runtime.slice bytes offset 8)
  simpa only [Solanalib.Runtime.length_slice_of_le range] using bound

/-- The rate projection preserves all two-byte encodings, rather than clamping
the word to the 10,000-basis-point configuration policy. -/
theorem observeTransferFeeAt_rate (bytes : Bytes) (offset : Nat)
    (fullRange : offset + transferFeeLength ≤ bytes.length) :
    (observeTransferFeeAt bytes offset).basisPoints.toNat =
      Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes (offset + 16) 2) := by
  apply UInt16.toNat_ofNat_of_lt'
  have range : offset + 16 + 2 ≤ bytes.length := by
    simpa only [transferFeeLength, Nat.add_assoc] using fullRange
  have bound := Solanalib.Runtime.leNat_lt (Solanalib.Runtime.slice bytes (offset + 16) 2)
  simpa only [Solanalib.Runtime.length_slice_of_le range] using bound

/-- Successful typed retrieval guarantees the full, exact configuration size. -/
theorem getTransferFeeConfig_length (tlvAddress : Nat) (bytes : Bytes)
    (reference : ExtensionReference TransferFeeConfig)
    (success : getTransferFeeConfig tlvAddress bytes = .ok reference) :
    reference.view.bytes.length = 108 := by
  have raw := getRepresentedExtension_raw transferFeeConfigRepresentation .mint tlvAddress bytes
  change (getTransferFeeConfig tlvAddress bytes).map ExtensionReference.view =
    getExtension .mint transferFeeConfigPod tlvAddress bytes at raw
  rw [success] at raw
  have selected : getExtension .mint transferFeeConfigPod tlvAddress bytes = .ok reference.view :=
    raw.symm
  exact (getExtension_ok_iff .mint transferFeeConfigPod tlvAddress bytes reference.view).mp
    selected |>.2.2.1

end Solanalib.Specs.Core.Token
