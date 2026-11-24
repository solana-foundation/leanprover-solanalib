/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionsSysvarChecked
public import Solanalib.Specs.Core.InstructionBuilderSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionsSysvar.Checked.Witness

def info : AccountInfo.Value :=
  { AccountInfo.sampleInfo with key := Solanalib.Runtime.Ids.sysvarInstructions }

def borrows (bytes : Solanalib.Runtime.Bytes) : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data bytes, AccountInfo.sampleProfile.policy⟩], []⟩

theorem ready (bytes : Solanalib.Runtime.Bytes) : Ready (borrows bytes) info :=
  fun _ => ⟨bytes, AccountInfo.sampleProfile.policy, rfl⟩

def currentSample : currentFamily.Index := ⟨⟨true, .unwind⟩⟩
def currentBefore : State Unit := ⟨borrows [0, 1], ()⟩
def currentAfter : State Unit :=
  ⟨{ borrows [0, 1] with slots := [none] }, ()⟩

theorem current_execution :
    currentReference currentSample currentBefore info (.returned (.ok 256) currentAfter) := by
  apply acquired_exit_retained _ _ _ rfl ⟨0, 0⟩
    { borrows [0, 1] with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] } [0, 1]
    (by rfl) (by rfl) (.returned (.ok 256) ()) (by rfl)

theorem current_hasExecution :
    FamilyHasExecution currentFamily currentReference currentSample :=
  ⟨currentBefore, info, .returned (.ok 256) currentAfter, ready [0, 1], current_execution⟩

/-- One real entry, preserving both account flags and nonempty instruction
data. The provider ledgers allocate two distinct typed vector resources. -/
def instructionData : Solanalib.Runtime.Bytes :=
  [1, 0, 4, 0, 1, 0, 3] ++ Solanalib.Runtime.Pubkey.zero.bytes ++
    Solanalib.Runtime.Pubkey.zero.bytes ++
    [3, 0, 7, 8, 9, 0, 0]

def instructionSample : Index where
  Aux := InstructionBuilder.Sample.State
  MetaResource := Nat
  ByteResource := Nat
  Unwind := Nat
  Terminal := Nat
  metas := InstructionBuilder.Sample.metaVec
  bytes := InstructionBuilder.Sample.byteVec
  doubleUnwind := fun _ first later terminal => terminal = first + later + 1000

def instructionBefore : State instructionSample.Aux := ⟨borrows instructionData, {}⟩

def instructionAuxAfter : instructionSample.Aux where
  metas := [some [Instruction.accountMeta .zero true true]]
  bytes := [some [7, 8, 9]]
  events := [10, 11]

def instructionAfter : State instructionSample.Aux :=
  ⟨{ borrows instructionData with slots := [none] }, instructionAuxAfter⟩

def instructionValue : Value instructionSample := ⟨.zero, (0 : Nat), (0 : Nat)⟩

theorem decode_execution :
    decode instructionSample 0 {} instructionData
      (.returned (.ok instructionValue) instructionAuxAfter) := by
  simp [decode, readMetas, readTail, protectMetas, word, key, readMeta, takeBytes,
    instructionData, instructionSample, instructionValue, instructionAuxAfter,
    InstructionBuilder.Sample.metaVec, InstructionBuilder.Sample.byteVec,
    InstructionBuilder.Sample.allocateMetas, InstructionBuilder.Sample.allocateBytes,
    InstructionBuilder.Sample.metasAt, Callback.bind, Callback.map, Callback.ofFunction,
    Outcome.map, Solanalib.Runtime.slice, Solanalib.Runtime.leNat, Solanalib.Runtime.Pubkey.zero,
      Solanalib.Runtime.Pubkey.ofBytes,
    Instruction.accountMeta, List.set]

theorem instruction_execution :
    instructionReference instructionSample instructionBefore (0, info)
      (.returned (.ok instructionValue) instructionAfter) := by
  apply acquired_exit_retained _ _ _ rfl ⟨0, 0⟩
    { borrows instructionData with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] } instructionData
    (by rfl) (by rfl) (.returned (.ok instructionValue) instructionAuxAfter) decode_execution

theorem instruction_hasExecution :
    FamilyHasExecution instructionFamily instructionReference instructionSample :=
  ⟨instructionBefore, (0, info), .returned (.ok instructionValue) instructionAfter,
    ready instructionData, instruction_execution⟩

end Solanalib.Specs.Core.InstructionsSysvar.Checked.Witness
