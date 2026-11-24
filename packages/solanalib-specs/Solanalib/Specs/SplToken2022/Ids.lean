/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface.Instructions
public import Solanalib.Specs.Core.TokenInstruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplToken2022

/-- The program identity defined by this crate. Its source and exact build
profiles are distinct from the equal constant of the interface crate. -/
def id_contract := Solanalib.Specs.SplToken2022Interface.id_contract

/-- Returning the declared key preserves the unit state without allocation. -/
def id_reference := Solanalib.Specs.SplToken2022Interface.id_reference

theorem id_reference_realizes : id_contract.RealizedBy id_reference :=
  Solanalib.Specs.SplToken2022Interface.id_reference_realizes

theorem id_satisfiable : id_contract.Satisfiable :=
  Solanalib.Specs.SplToken2022Interface.id_satisfiable

end Solanalib.Specs.SplToken2022

namespace Solanalib.Specs.SplToken2022.native_mint

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token.Instruction

/-- The exact declared Base58 key `9pan9bMn5HatX4EJdBwg9VgCa7Uz5HL8N1m5D3NdXejP`. No
address-derivation syscall is performed. -/
def declaredId : Solanalib.Runtime.Pubkey := ⟨[131, 13, 252, 159, 222, 95, 230, 184, 170, 124, 4,
  164, 118, 233, 30, 138, 198, 187, 38, 74, 173, 144, 250, 25, 201, 223, 73, 216, 92, 62, 91, 94],
  by decide⟩

/-- Declaration-generated identity equality; it checks no account owner or data. -/
def check_id_contract := valueContract (fun (_ : Solanalib.Runtime.Pubkey) => True) (fun key => key
  == declaredId)

/-- Compare the complete 32-byte key. -/
def check_id_reference := valueReference (fun key : Solanalib.Runtime.Pubkey => key == declaredId)

/-- The pure equality reference realizes the declared identity check. -/
theorem check_id_reference_realizes : check_id_contract.RealizedBy check_id_reference :=
  valueReference_realizes _ _

/-- The declared key itself is an admitted input. -/
theorem check_id_satisfiable : check_id_contract.Satisfiable := ⟨(), declaredId, trivial⟩

end Solanalib.Specs.SplToken2022.native_mint
