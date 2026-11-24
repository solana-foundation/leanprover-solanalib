/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorContext
public import Solanalib.Specs.Core.AccountInfo
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorContextOwned

/-- The arbitrary account payload moves into the context. Its independent
remaining-account vector has a stable logical resource identity; the program
ID and nested signer seeds are stored without validation or invocation. -/
structure Value (Accounts Resource : Type) where
  accounts : Accounts
  remaining : Resource
  programId : _root_.Solanalib.Runtime.Pubkey
  signerSeeds : AnchorContext.SignerSeeds

/-- The only dependency called by this constructor is infallible empty-vector
construction. Other vector operations belong to later clients and are never
called here. The state update of the provider records the new logical owner without
claiming a Rust allocation, pointer or layout. -/
structure Types where
  State : Type
  Accounts : Type
  Resource : Type
  Unwind : Type
  Terminal : Type
  remaining : Owned.VectorOps State AccountInfo.Value Resource Unwind Terminal

/-- The reached empty-vector primitive returns an empty observation and a
fresh identity. No law for an uncalled vector operation is required here. -/
structure EmptyReady (types : Types) (before : types.State) : Prop where
  current : types.remaining.current (types.remaining.empty before).2
    (types.remaining.empty before).1 = some []
  fresh : types.remaining.current before (types.remaining.empty before).1 = none

def newWithSigner (types : Types) (before : types.State)
    (args : AnchorContext.NewWithSignerArgs types.Accounts) :
    Value types.Accounts types.Resource × types.State :=
  let (resource, after) := types.remaining.empty before
  (⟨args.accounts, resource, args.programId, args.signerSeeds⟩, after)

/-- Observe the current remaining sequence of the context. Later clients cannot
replace this state-dependent observation with the empty value of the constructor. -/
def observe (types : Types) (state : types.State)
    (context : Value types.Accounts types.Resource) :
    Option (AnchorContext.Value types.Accounts AccountInfo.Value) :=
  (types.remaining.current state context.remaining).map fun values =>
    ⟨context.accounts, values, context.programId, context.signerSeeds⟩

def family : Family where
  Index := Types
  State := Types.State
  Args := fun types => AnchorContext.NewWithSignerArgs types.Accounts
  Value := fun types => Value types.Accounts types.Resource
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun types => .returning (fun before _ => EmptyReady types before)
    (fun before args context after =>
      (context, after) = newWithSigner types before args ∧
      types.remaining.current after context.remaining = some [] ∧
      types.remaining.current before context.remaining = none)

def reference : FamilyRun family := fun types => returnsOf (newWithSigner types)

/-- The two reached empty-provider guarantees give a fresh empty owner while
the constructor preserves all fields. No later vector-operation law is used. -/
theorem realizes (types : Types) :
    (family.contract types).RealizedBy (newWithSigner types) := by
  intro before args ready
  exact ⟨rfl, ready.current, ready.fresh⟩

theorem reference_holds : FamilyReference family reference := by
  intro types
  exact (realized_iff_holds _ _).mp (realizes types)

/-- The reference sample uses a finite ledger, with an arbitrary two-key
payload distinct from the independently created remaining-account vector. -/
def sample : Types where
  State := Owned.VectorState AccountInfo.Value
  Accounts := _root_.Solanalib.Runtime.Pubkey × _root_.Solanalib.Runtime.Pubkey
  Resource := Nat
  Unwind := Empty
  Terminal := Empty
  remaining := Owned.vectorReference

def sampleArgs : AnchorContext.NewWithSignerArgs sample.Accounts :=
  ⟨.ofNat 9, (.ofNat 1, .ofNat 2), [[[1, 2], [255]], [[3]]]⟩

theorem sample_satisfiable : FamilySatisfiable family sample :=
  ⟨[], sampleArgs,
    ⟨Owned.vectorReference_laws.empty_current [], Owned.vectorReference_laws.empty_fresh []⟩⟩

theorem sample_execution : FamilyHasExecution family reference sample :=
  ⟨[], sampleArgs, .returned ⟨sampleArgs.accounts, (0 : Nat), .ofNat 9,
    sampleArgs.signerSeeds⟩ [some []],
    ⟨Owned.vectorReference_laws.empty_current [], Owned.vectorReference_laws.empty_fresh []⟩, rfl⟩

end Solanalib.Specs.Core.AnchorContextOwned
