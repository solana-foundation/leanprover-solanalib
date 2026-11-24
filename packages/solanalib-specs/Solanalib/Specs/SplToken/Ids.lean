/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstruction

@[expose] public section

open Solanalib.Contracts.Model

namespace Solanalib.Specs.SplToken.native_mint

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token.Instruction

/-- The exact declared Base58 key `So11111111111111111111111111111111111111112`. No
address-derivation syscall is performed. -/
def declaredId : Solanalib.Runtime.Pubkey := ⟨[6, 155, 136, 87, 254, 171, 129, 132, 251, 104, 127,
  99, 70, 24, 192, 53, 218, 196, 57, 220, 26, 235, 59, 85, 152, 160, 240, 0, 0, 0, 0, 1], by decide⟩

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

end Solanalib.Specs.SplToken.native_mint
