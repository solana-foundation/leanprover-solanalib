/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.StakeState
public import Solanalib.Specs.Core

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.LegacyStake

open StakeState

/-- The original four-variant stake state. Unlike `StakeStateV2`, its Stake
variant contains no flags byte. The stored float retains every bit pattern. -/
inductive State where
  | uninitialized
  | initialized (metadata : Meta)
  | stake (metadata : Meta) (active : Stake)
  | rewardsPool
  deriving DecidableEq, Repr

/-- The two clock fields read by `Lockup::is_in_force`. The remaining Clock
fields are deliberately absent because the function never inspects them. -/
structure Clock where
  unixTimestamp : Int64
  epoch : UInt64
  deriving DecidableEq, Repr

/-- Derived Default initializes every field, including the all-zero custodian. -/
def defaultLockup : Lockup := ⟨0, 0, .zero⟩

/-- Equality with the supplied custodian bypasses both strict comparisons.
This comparison does not authenticate a signature. -/
def isInForce (lockup : Lockup) (clock : Clock) (custodian : Option Solanalib.Runtime.Pubkey) :
  Bool :=
  if custodian = some lockup.custodian then false
  else lockup.unixTimestamp > clock.unixTimestamp || lockup.epoch > clock.epoch

def delegation : State → Option Delegation
  | .stake _ active => some active.delegation
  | _ => none

def metadata : State → Option Meta
  | .initialized metadata | .stake metadata _ => some metadata
  | _ => none

def lockup (state : State) : Option Lockup := (metadata state).map Meta.lockup

/-- An authorized custodian is exempt even before both time thresholds. -/
theorem custodian_exempt (lockup : Lockup) (clock : Clock) :
    isInForce lockup clock (some lockup.custodian) = false := by
  simp [isInForce]

/-- At both exact thresholds the lockup has expired. -/
theorem expires_at_thresholds (lockup : Lockup) (custodian : Option Solanalib.Runtime.Pubkey) :
    isInForce lockup ⟨lockup.unixTimestamp, lockup.epoch⟩ custodian = false := by
  simp [isInForce]

/-- Delegation is available exactly in the delegated variant, without imposing
activation, lamport, rate or authority conditions that this getter never checks. -/
theorem delegation_some_iff (state : State) (value : Delegation) :
    delegation state = some value ↔
      ∃ metadata active, state = .stake metadata active ∧ active.delegation = value := by
  cases state <;> simp [delegation, and_assoc]

/-- Lockup and metadata observe the same copied source metadata. -/
theorem lockup_of_meta (state : State) (value : Meta) (found : metadata state = some value) :
    lockup state = some value.lockup := by
  simp [lockup, found]

end Solanalib.Specs.Core.LegacyStake
