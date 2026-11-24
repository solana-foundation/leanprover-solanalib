/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.LegacyStake

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.stake.state.Lockup

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.StakeState
open Solanalib.Specs.Core.LegacyStake

def default_run (before : Unit) (args : Unit) : Lockup × Unit :=
  ((fun _ => defaultLockup) args, before)

def default_contract : Solanalib.Contracts.Model Unit (Unit) (Lockup) :=
  .returning (fun _ _ => True)
    (fun before args result after => result = (fun _ => defaultLockup) args ∧ after = before)

theorem default_reference : default_contract.RealizedBy default_run :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem default_satisfiable : default_contract.Satisfiable :=
  ⟨(), (), trivial⟩

def is_in_force_run (before : Unit) (args : Lockup × Clock × Option Solanalib.Runtime.Pubkey) :
  Bool × Unit :=
  ((fun args => isInForce args.1 args.2.1 args.2.2) args, before)

def is_in_force_contract : Solanalib.Contracts.Model Unit (Lockup × Clock × Option
  Solanalib.Runtime.Pubkey) (Bool) :=
  .returning (fun _ _ => True)
    (fun before args result after => result = (fun args => isInForce args.1 args.2.1 args.2.2) args
      ∧ after = before)

theorem is_in_force_reference : is_in_force_contract.RealizedBy is_in_force_run :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem is_in_force_satisfiable : is_in_force_contract.Satisfiable :=
  ⟨(), ⟨defaultLockup, ⟨0, 0⟩, none⟩, trivial⟩

end Solanalib.Specs.SolanaProgram.stake.state.Lockup

namespace Solanalib.Specs.SolanaProgram.stake.state.StakeState

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.StakeState
open Solanalib.Specs.Core.LegacyStake

def delegation_run (before : Unit) (args : State) : Option Delegation × Unit :=
  ((delegation) args, before)

def delegation_contract : Solanalib.Contracts.Model Unit (State) (Option Delegation) :=
  .returning (fun _ _ => True)
    (fun before args result after => result = (delegation) args ∧ after = before)

theorem delegation_reference : delegation_contract.RealizedBy delegation_run :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem delegation_satisfiable : delegation_contract.Satisfiable :=
  ⟨(), .uninitialized, trivial⟩

def lockup_run (before : Unit) (args : State) : Option Lockup × Unit :=
  ((lockup) args, before)

def lockup_contract : Solanalib.Contracts.Model Unit (State) (Option Lockup) :=
  .returning (fun _ _ => True)
    (fun before args result after => result = (lockup) args ∧ after = before)

theorem lockup_reference : lockup_contract.RealizedBy lockup_run :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem lockup_satisfiable : lockup_contract.Satisfiable :=
  ⟨(), .uninitialized, trivial⟩

def meta_run (before : Unit) (args : State) : Option Meta × Unit :=
  ((metadata) args, before)

def meta_contract : Solanalib.Contracts.Model Unit (State) (Option Meta) :=
  .returning (fun _ _ => True)
    (fun before args result after => result = (metadata) args ∧ after = before)

theorem meta_reference : meta_contract.RealizedBy meta_run :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem meta_satisfiable : meta_contract.Satisfiable :=
  ⟨(), .uninitialized, trivial⟩

end Solanalib.Specs.SolanaProgram.stake.state.StakeState
