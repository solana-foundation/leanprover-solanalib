/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.InstructionSystemCreateAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSystemInterface.instruction

open Solanalib.Specs.Core.Instruction

structure CreateAccountArgs where
  fromAddress : _root_.Solanalib.Runtime.Pubkey
  toAddress : _root_.Solanalib.Runtime.Pubkey
  lamports : Nat
  space : Nat
  owner : _root_.Solanalib.Runtime.Pubkey

structure TransferArgs where
  fromAddress : _root_.Solanalib.Runtime.Pubkey
  toAddress : _root_.Solanalib.Runtime.Pubkey
  lamports : Nat

/-- These contracts describe instruction values. They neither execute the
System program nor establish allocation or serialization termination in Rust. -/

def create_account_model (before : Unit) (args : CreateAccountArgs) : Value × Unit :=
  (systemCreateAccount args.fromAddress args.toAddress args.lamports args.space args.owner, before)

def create_account_contract : Solanalib.Contracts.Model Unit (CreateAccountArgs) (Value) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = systemCreateAccount args.fromAddress
      args.toAddress args.lamports args.space args.owner)

theorem create_account_reference : create_account_contract.RealizedBy create_account_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem create_account_satisfiable : create_account_contract.Satisfiable :=
  ⟨(), ⟨.zero, .zero, 0, 0, .zero⟩, trivial⟩

def transfer_model (before : Unit) (args : TransferArgs) : Value × Unit :=
  (systemTransfer args.fromAddress args.toAddress args.lamports, before)

def transfer_contract : Solanalib.Contracts.Model Unit (TransferArgs) (Value) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = systemTransfer args.fromAddress
      args.toAddress args.lamports)

theorem transfer_reference : transfer_contract.RealizedBy transfer_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem transfer_satisfiable : transfer_contract.Satisfiable :=
  ⟨(), ⟨.zero, .zero, 0⟩, trivial⟩

end Solanalib.Specs.SolanaSystemInterface.instruction
