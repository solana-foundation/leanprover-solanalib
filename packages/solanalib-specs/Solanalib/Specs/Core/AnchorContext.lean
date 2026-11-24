/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core
public import Solanalib.Runtime.Basic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorContext

universe u v w

/-- Outer list: signing PDAs; middle list: the seeds of that PDA; inner list: bytes.
The constructor preserves these lists without checking PDA derivation or limits. -/
abbrev SignerSeeds := List (List _root_.Solanalib.Runtime.Bytes)

/-- `T` remains an arbitrary account payload. Remaining account handles are a
separate type, as they are in the `CpiContext` of Anchor. -/
structure Value (Accounts : Type u) (AccountInfo : Type v) where
  accounts : Accounts
  remainingAccounts : List AccountInfo
  programId : _root_.Solanalib.Runtime.Pubkey
  signerSeeds : SignerSeeds
  deriving DecidableEq, Repr

structure NewWithSignerArgs (Accounts : Type u) where
  programId : _root_.Solanalib.Runtime.Pubkey
  accounts : Accounts
  signerSeeds : SignerSeeds
  deriving DecidableEq, Repr

def newWithSigner {Accounts : Type u} {AccountInfo : Type v}
    (args : NewWithSignerArgs Accounts) : Value Accounts AccountInfo where
  accounts := args.accounts
  remainingAccounts := []
  programId := args.programId
  signerSeeds := args.signerSeeds

/-- Value construction for Anchor 1.0.2. Its first argument is a program ID.
No `ToAccountInfos`, `ToAccountMetas`, seed validation or invocation occurs. -/
def newWithSignerContract (State : Type w) (Accounts : Type u) (AccountInfo : Type v) :
    Solanalib.Contracts.Model State (NewWithSignerArgs Accounts) (Value Accounts AccountInfo) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = newWithSigner args)

def newWithSignerReference {State : Type w} {Accounts : Type u} {AccountInfo : Type v}
    (before : State) (args : NewWithSignerArgs Accounts) : Value Accounts AccountInfo × State :=
  (newWithSigner args, before)

theorem newWithSignerReference_realizes
    (State : Type w) (Accounts : Type u) (AccountInfo : Type v) :
    (newWithSignerContract State Accounts AccountInfo).RealizedBy newWithSignerReference := by
  intro before args _
  exact ⟨rfl, rfl⟩

end Solanalib.Specs.Core.AnchorContext
