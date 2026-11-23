/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.LegacyStake
public import Solanalib.Specs.Core.Instruction
public import Solanalib.Runtime.Ids

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.LegacyStakeInstruction

open StakeState
open Instruction

inductive Authorize where
  | staker
  | withdrawer
  deriving DecidableEq, Repr

structure LockupArgs where
  unixTimestamp : Option Int64
  epoch : Option UInt64
  custodian : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure InitializeArgs where
  stake : Solanalib.Runtime.Pubkey
  authorized : Authorized
  lockup : Lockup
  deriving DecidableEq, Repr

structure AuthorizeArgs where
  stake : Solanalib.Runtime.Pubkey
  authorized : Solanalib.Runtime.Pubkey
  newAuthorized : Solanalib.Runtime.Pubkey
  role : Authorize
  custodian : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure DelegateArgs where
  stake : Solanalib.Runtime.Pubkey
  authorized : Solanalib.Runtime.Pubkey
  vote : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure SetLockupArgs where
  stake : Solanalib.Runtime.Pubkey
  lockup : LockupArgs
  custodian : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure MergeArgs where
  destination : Solanalib.Runtime.Pubkey
  source : Solanalib.Runtime.Pubkey
  authorized : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

structure SplitArgs where
  stake : Solanalib.Runtime.Pubkey
  authorized : Solanalib.Runtime.Pubkey
  lamports : UInt64
  destination : Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- A fixed concrete instruction codec and its allocation sequence: the
literal metadata prefix is allocated first, then every optional push in order.
Data bytes use the fixed integers of bincode 1.x, u32 enum tags and u8 option tags. -/
structure Plan where
  programId : Solanalib.Runtime.Pubkey
  data : Solanalib.Runtime.Bytes
  initial : List Instruction.Meta
  extra : List Instruction.Meta := []

def Plan.value (plan : Plan) : Value :=
  make plan.programId (plan.initial ++ plan.extra) plan.data

def encodeOption {α : Type} (encode : α → Solanalib.Runtime.Bytes) : Option α →
  Solanalib.Runtime.Bytes
  | none => [0]
  | some value => [1] ++ encode value

def encodeLockupArgs (args : LockupArgs) : Solanalib.Runtime.Bytes :=
  encodeOption i64Bytes args.unixTimestamp ++ encodeOption u64Bytes args.epoch ++
    encodeOption Solanalib.Runtime.Pubkey.bytes args.custodian

def initializePlan (args : InitializeArgs) : Plan :=
  ⟨Solanalib.Runtime.Ids.stakeProgram, u32Bytes 0 ++ args.authorized.encode ++ args.lockup.encode,
    [accountMeta args.stake false true, accountMeta Solanalib.Runtime.Ids.sysvarRent false false],
      []⟩

def authorizePlan (args : AuthorizeArgs) : Plan :=
  ⟨Solanalib.Runtime.Ids.stakeProgram, u32Bytes 1 ++ args.newAuthorized.bytes ++
    u32Bytes (match args.role with | .staker => 0 | .withdrawer => 1),
    [accountMeta args.stake false true, accountMeta Solanalib.Runtime.Ids.sysvarClock false false,
      accountMeta args.authorized true false],
    args.custodian.toList.map (fun key => accountMeta key true false)⟩

def delegatePlan (args : DelegateArgs) : Plan :=
  ⟨Solanalib.Runtime.Ids.stakeProgram, u32Bytes 2,
    [accountMeta args.stake false true, accountMeta args.vote false false,
      accountMeta Solanalib.Runtime.Ids.sysvarClock false false,
      accountMeta Solanalib.Runtime.Ids.sysvarStakeHistory false false,
      accountMeta Solanalib.Runtime.Ids.stakeConfig false false,
      accountMeta args.authorized true false], []⟩

def setLockupPlan (args : SetLockupArgs) : Plan :=
  ⟨Solanalib.Runtime.Ids.stakeProgram, u32Bytes 6 ++ encodeLockupArgs args.lockup,
    [accountMeta args.stake false true, accountMeta args.custodian true false], []⟩

def mergePlan (args : MergeArgs) : Plan :=
  ⟨Solanalib.Runtime.Ids.stakeProgram, u32Bytes 7,
    [accountMeta args.destination false true, accountMeta args.source false true,
      accountMeta Solanalib.Runtime.Ids.sysvarClock false false,
      accountMeta Solanalib.Runtime.Ids.sysvarStakeHistory false false,
      accountMeta args.authorized true false], []⟩

def splitPlan (args : SplitArgs) : Plan :=
  ⟨Solanalib.Runtime.Ids.stakeProgram, u32Bytes 3 ++ u64Bytes args.lamports,
    [accountMeta args.stake false true, accountMeta args.destination false true,
      accountMeta args.authorized true false], []⟩

/-- The public split helper first prepares System Allocate(200), then System
Assign(stake program), then Stake Split(lamports). No program is invoked. -/
def splitPlans (args : SplitArgs) : List Plan := [
  ⟨.zero, u32Bytes 8 ++ u64Bytes 200, [accountMeta args.destination true true], []⟩,
  ⟨.zero, u32Bytes 1 ++ Solanalib.Runtime.Ids.stakeProgram.bytes,
    [accountMeta args.destination true true], []⟩,
  splitPlan args]

theorem initialize_data_length (args : InitializeArgs) :
    (initializePlan args).data.length = 116 := by
  simp [initializePlan]

theorem authorize_data_length (args : AuthorizeArgs) :
    (authorizePlan args).data.length = 40 := by
  simp [authorizePlan, args.newAuthorized.length_eq]

theorem split_instruction_count (args : SplitArgs) : (splitPlans args).length = 3 := rfl

/-- The allocating helper reserves the 200-byte size of the original stake account,
independently of its shorter current serialized variant. -/
theorem split_allocate (args : SplitArgs) :
    ((splitPlans args)[0]'(by simp [splitPlans])).value =
      systemAllocate args.destination 200 := by
  rfl

end Solanalib.Specs.Core.LegacyStakeInstruction
