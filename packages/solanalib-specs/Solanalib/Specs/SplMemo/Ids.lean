/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstruction

@[expose] public section

open Solanalib.Contracts.Model

namespace Solanalib.Specs.SplMemo

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token.Instruction

/-- The exact declared Base58 key `MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr`. No
address-derivation syscall is performed. -/
def declaredId : Solanalib.Runtime.Pubkey := ⟨[5, 74, 83, 90, 153, 41, 33, 6, 77, 36, 232, 113, 96,
  218, 56, 124, 124, 53, 181, 221, 188, 146, 187, 129, 228, 31, 168, 64, 65, 5, 68, 141], by decide⟩

/-- Return the source-declared constant key. -/
def id_contract := valueContract (fun (_ : Unit) => True) (fun _ => declaredId)

/-- Pure constant reference. -/
def id_reference := valueReference (fun (_ : Unit) => declaredId)

/-- Every reference return is the declared key in the unchanged state. -/
theorem id_reference_realizes : id_contract.RealizedBy id_reference := valueReference_realizes _ _

/-- Unit input is admitted. -/
theorem id_satisfiable : id_contract.Satisfiable := ⟨(), (), trivial⟩

end Solanalib.Specs.SplMemo
