/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EpochSchedule

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.epoch_schedule.EpochSchedule

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev Value := Solanalib.Specs.Core.EpochSchedule.Value

def get_last_slot_in_epoch_contract : Solanalib.Contracts.Model Unit (Value × UInt64) UInt64 :=
  .returning (fun _ _ => True)
    (fun before args value after => value = EpochSchedule.lastSlot args.1 args.2 ∧ after = before)

def get_last_slot_in_epoch_run (before : Unit) (args : Value × UInt64) : UInt64 × Unit :=
  (EpochSchedule.lastSlot args.1 args.2, before)

theorem get_last_slot_in_epoch_reference : get_last_slot_in_epoch_contract.RealizedBy
  get_last_slot_in_epoch_run := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem get_last_slot_in_epoch_satisfiable : get_last_slot_in_epoch_contract.Satisfiable :=
  ⟨(), (EpochSchedule.defaultValue, 0), True.intro⟩

end Solanalib.Specs.SolanaProgram.epoch_schedule.EpochSchedule
