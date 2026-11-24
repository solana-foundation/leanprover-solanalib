/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAddress.Address

open Solanalib.Specs.Core.Address

/-! Value observations for the reviewed SDK builds. Borrowed returns project
their bytes; no pointer, allocation, lifetime or Rust-body statement is made. -/

def new_from_array_model (before : Unit) (args : Array32) : Value × Unit :=
  (newFromArray args, before)

def new_from_array_contract : Solanalib.Contracts.Model Unit (Array32) (Value) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = newFromArray args)

theorem new_from_array_reference : new_from_array_contract.RealizedBy new_from_array_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem new_from_array_satisfiable : new_from_array_contract.Satisfiable :=
  ⟨(), ⟨List.replicate 32 0, by simp⟩, trivial⟩

def as_array_model (before : Unit) (args : Value) : Array32 × Unit :=
  (asArray args, before)

def as_array_contract : Solanalib.Contracts.Model Unit (Value) (Array32) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = asArray args)

theorem as_array_reference : as_array_contract.RealizedBy as_array_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem as_array_satisfiable : as_array_contract.Satisfiable :=
  ⟨(), .zero, trivial⟩

def as_ref_model (before : Unit) (args : Value) : _root_.Solanalib.Runtime.Bytes × Unit :=
  (args.bytes, before)

def as_ref_contract : Solanalib.Contracts.Model Unit (Value) (_root_.Solanalib.Runtime.Bytes) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = args.bytes)

theorem as_ref_reference : as_ref_contract.RealizedBy as_ref_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem as_ref_satisfiable : as_ref_contract.Satisfiable :=
  ⟨(), .zero, trivial⟩

def to_bytes_model (before : Unit) (args : Value) : Array32 × Unit :=
  (asArray args, before)

def to_bytes_contract : Solanalib.Contracts.Model Unit (Value) (Array32) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = asArray args)

theorem to_bytes_reference : to_bytes_contract.RealizedBy to_bytes_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem to_bytes_satisfiable : to_bytes_contract.Satisfiable :=
  ⟨(), .zero, trivial⟩

def default_model (before : Unit) (_ : Unit) : Value × Unit :=
  (_root_.Solanalib.Runtime.Pubkey.zero, before)

def default_contract : Solanalib.Contracts.Model Unit (Unit) (Value) :=
  .returning (fun _ _ => True)
    (fun before _ result after => after = before ∧ result = _root_.Solanalib.Runtime.Pubkey.zero)

theorem default_reference : default_contract.RealizedBy default_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem default_satisfiable : default_contract.Satisfiable :=
  ⟨(), (), trivial⟩

def eq_model (before : Unit) (args : Value × Value) : Bool × Unit :=
  (equal args.1 args.2, before)

def eq_contract : Solanalib.Contracts.Model Unit (Value × Value) (Bool) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = equal args.1 args.2)

theorem eq_reference : eq_contract.RealizedBy eq_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem eq_satisfiable : eq_contract.Satisfiable :=
  ⟨(), (.zero, .zero), trivial⟩

/-- Pure curve facet, conditional on normal syscall-register correspondence.
The primary selected-Solana contract is is_on_curve_solana_contract. -/
def is_on_curve_model (before : Unit) (args : Crypto × Value) : Bool × Unit :=
  (isOnCurve args.1 args.2, before)

def is_on_curve_contract : Solanalib.Contracts.Model Unit (Crypto × Value) (Bool) :=
  .returning (fun _ _ => True)
    (fun before args result after => after = before ∧ result = isOnCurve args.1 args.2)

theorem is_on_curve_reference : is_on_curve_contract.RealizedBy is_on_curve_model := by
  intro _ _ _
  exact ⟨rfl, rfl⟩

theorem is_on_curve_satisfiable : is_on_curve_contract.Satisfiable :=
  ⟨(), (witnessCrypto, .zero), trivial⟩

/-- Pure search/panic observation under explicit crypto and hash width. It
does not model syscall failures when a pure answer exists; those exits belong
to the primary find_program_address_solana_contract and its provider model. -/
def find_program_address_contract :
    Solanalib.Contracts.Model Unit SearchArgs (Value × UInt8)
      SearchPanic SearchPanic where
  requires := fun _ _ => True
  post := fun _ args outcome => findPost args outcome

def find_program_address_run := findReference

theorem find_program_address_reference :
    find_program_address_contract.Holds find_program_address_run := by
  intro before args outcome _ execution
  change outcome = findOutcome args at execution
  subst outcome
  exact findOutcome_satisfies args

theorem find_program_address_satisfiable : find_program_address_contract.Satisfiable :=
  ⟨(), witnessSearch, trivial⟩

theorem find_program_address_has_execution :
    find_program_address_contract.HasExecution find_program_address_run :=
  ⟨(), witnessSearch, findOutcome witnessSearch, trivial, rfl⟩

end Solanalib.Specs.SolanaAddress.Address
