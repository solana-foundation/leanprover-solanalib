/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressValueOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaAddress.Address

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-- Comparison of all 32 unsigned bytes, from first to last. The 2.6.1
profile retains this exact value behavior and its defining source version. -/
def cmp_contract : Solanalib.Contracts.Model Unit (Value × Value) (Ordering) :=
  valueContract (Operations.compare)

def cmp_model : Unit → (Value × Value) → (Ordering) × Unit := valueModel (Operations.compare)

theorem cmp_reference : cmp_contract.RealizedBy cmp_model :=
  valueReference (Operations.compare)

theorem cmp_satisfiable : cmp_contract.Satisfiable :=
  valueSatisfiable (Operations.compare) ((_root_.Solanalib.Runtime.Pubkey.zero,
    _root_.Solanalib.Runtime.Pubkey.zero))

end Solanalib.Specs.SolanaAddress.Address
