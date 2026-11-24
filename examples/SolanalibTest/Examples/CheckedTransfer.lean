/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.System
public import Solanalib.Specs.SolanaSystemInterface.Instruction

@[expose] public section

/-!
# From an SDK transfer contract to checked runtime execution

A constructor result satisfying the System transfer value contract moves seven
lamports between these two accounts through the checked setters of the runtime.
The example proves the resulting balances and conservation, and checks rejection
when the signature flag of the sender is missing. The primitive functions are arbitrary.

This is one modeled System instruction, without transaction admission, fees or
commit. The SDK premise concerns a returned value; allocation, serialization
failure and Rust implementation correctness remain outside that premise.
-/

namespace SolanalibTest.Examples.CheckedTransfer

open Solanalib.Runtime
open Solanalib.Specs.SolanaSystemInterface.instruction

/-- Distinct addresses in the fixed transaction account list. -/
def senderKey : Pubkey := .ofNat 1

/-- The recipient occupies transaction account index one. -/
def recipientKey : Pubkey := .ofNat 2

/-- The SDK constructor arguments use the public-key representation of the runtime. -/
def args : TransferArgs := ⟨senderKey, recipientKey, 7⟩

/-- The System-owned sender can spend its initial balance. -/
def sender : Account := ⟨100, [], Ids.systemProgram, false, 0⟩

/-- A destination with enough room for the incoming lamports. -/
def recipient : Account := ⟨20, [], Ids.systemProgram, false, 0⟩

/-- The program account gives the frame its executing program identity. -/
def program : Account := ⟨1, [], Ids.nativeLoader, true, 0⟩

/-- The context before this instruction; all counters start at zero. -/
def before : TxState where
  keys := [senderKey, recipientKey, Ids.systemProgram]
  accts := [sender, recipient, program]
  lamportsDelta := 0
  resizeDelta := 0
  stack := []
  trace := []
  returnData := (Ids.systemProgram, [])
  topIndex := 0

/-- Resolve the keys and flags of the constructor in this fixed account list.
This small example does not implement general transaction or CPI preparation. -/
def frameOf (instruction : CpiInstruction) : Frame where
  programIdx := before.keys.idxOf instruction.programId
  accounts := instruction.metas.map fun account =>
    ⟨before.keys.idxOf account.key, account.signerByte != 0, account.writableByte != 0⟩
  data := instruction.data

/-- The expected checked state, including both runtime mutation markers. -/
def after : TxState :=
  { before with
    accts := [{ sender with lamports := 93 }, { recipient with lamports := 27 }, program]
    touched := [1, 0] }

/-- The mathematical SDK reference really supplies the premise used below. -/
theorem constructor_satisfies_contract :
    transfer_contract.ensures () args (transfer_model () args).1 () :=
  transfer_reference () args trivial

set_option maxRecDepth 16384 in
/-- Every value admitted by the selected constructor contract runs successfully
in this context. Both balances are checked and the total is conserved. -/
theorem checked_transfer (prims : Prims) (instruction : CpiInstruction)
    (constructed : transfer_contract.ensures () args instruction ()) :
    systemProcess mainnet prims before (frameOf instruction) = some (.ok after) ∧
    (after.acct 0).lamports = 93 ∧ (after.acct 1).lamports = 27 ∧
    after.lamportSum = before.lamportSum := by
  have value : instruction =
      Solanalib.Specs.Core.Instruction.systemTransfer senderKey recipientKey 7 := constructed.2
  subst instruction
  constructor
  · cbv
  · decide

set_option maxRecDepth 16384 in
/-- Removing the signer flag of the sender reaches the actual runtime rejection. -/
theorem missing_signature_rejected (prims : Prims) :
    systemProcess mainnet prims before
      { frameOf (transfer_model () args).1 with
        accounts := [⟨0, false, true⟩, ⟨1, false, true⟩] } =
      some (.error .MissingRequiredSignature) := by
  cbv

end SolanalibTest.Examples.CheckedTransfer
