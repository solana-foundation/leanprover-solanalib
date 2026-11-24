/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Instruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest

universe u v w x y

/-- The SDK value-level request. Account payloads remain caller supplied.
Lists retain order, duplicate identities, empty signers and empty seeds.
There are no fabricated runtime pointers or account-info storage locations. -/
structure Request (Account : Type u) where
  instruction : _root_.Solanalib.Runtime.CpiInstruction
  accounts : List Account
  signers : List (List _root_.Solanalib.Runtime.Bytes)

/-- An account argument and its observed address. Relating that observation to
Rust storage belongs to a separate implementation binding. -/
structure AccountRef (Account : Type u) where
  value : Account
  address : _root_.Solanalib.Runtime.Pubkey

abbrev Invocation (State : Type u) (Account : Type v) (Error : Type w)
    (Unwind : Type x) (Terminal : Type y) :=
  State → Request Account →
    Solanalib.Contracts.Model.Outcome State (Except Error Unit) Unwind Terminal → Prop

/-- An opaque invocation provider is explicit data supplied by the caller of
the mathematical model. No success, preservation or rollback premise is added. -/
structure Call (State : Type u) (Account : Type v) (Error : Type w)
    (Unwind : Type x) (Terminal : Type y) where
  request : Request Account
  invoke : Invocation State Account Error Unwind Terminal

def forward {State : Type u} {Account : Type v} {Error : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (before : State) (call : Call State Account Error Unwind Terminal) :
    Solanalib.Contracts.Model.Outcome State (Except Error Unit) Unwind Terminal → Prop :=
  call.invoke before call.request

/-- The generic forwarding contract restricts only how the supplied provider
is called. Its outcome and actual returned/unwound state are preserved. -/
def forwardingContract {State : Type u} {Account : Type v} {Error : Type w}
    {Unwind Terminal : Type} :
    Solanalib.Contracts.Model State (Call State Account Error Unwind Terminal)
      (Except Error Unit) Unwind Terminal where
  requires := fun _ _ => True
  post := forward

theorem forwarding_holds {State : Type u} {Account : Type v} {Error : Type w}
    {Unwind Terminal : Type} :
    (@forwardingContract State Account Error Unwind Terminal).Holds forward := by
  intro _ _ _ _ result
  exact result

def unsigned {Account : Type u} (instruction : _root_.Solanalib.Runtime.CpiInstruction)
    (accounts : List Account) : Request Account := ⟨instruction, accounts, []⟩

def signed {Account : Type u} (instruction : _root_.Solanalib.Runtime.CpiInstruction)
    (accounts : List Account) (signers : List (List _root_.Solanalib.Runtime.Bytes)) :
    Request Account := ⟨instruction, accounts, signers⟩

@[simp] theorem signed_accounts {Account : Type u} (instruction :
  _root_.Solanalib.Runtime.CpiInstruction)
    (accounts : List Account) (signers : List (List _root_.Solanalib.Runtime.Bytes)) :
    (signed instruction accounts signers).accounts = accounts := rfl

@[simp] theorem signed_signers {Account : Type u} (instruction :
  _root_.Solanalib.Runtime.CpiInstruction)
    (accounts : List Account) (signers : List (List _root_.Solanalib.Runtime.Bytes)) :
    (signed instruction accounts signers).signers = signers := rfl

end Solanalib.Specs.Core.CpiRequest
