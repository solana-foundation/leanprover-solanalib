/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaHash.Hash

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaHash.Hash

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- A nonuniform hash makes byte order observable. -/
def ascending : Hash.Value :=
  ⟨(List.range 32).map UInt8.ofNat, by simp⟩

theorem copies_exact_array :
    (Solanalib.Specs.SolanaHash.Hash.to_bytes_model () ascending).1.val =
      (List.range 32).map UInt8.ofNat ∧
    (Solanalib.Specs.SolanaHash.Hash.to_bytes_model () ascending).1.val.length = 32 :=
  ⟨rfl, ascending.length_eq⟩

theorem versioned_contract_holds :
    Solanalib.Specs.SolanaHash.Hash.to_bytes_contract.ensures () ascending
      (Solanalib.Specs.SolanaHash.Hash.to_bytes_model () ascending).1 () :=
  Solanalib.Specs.SolanaHash.Hash.to_bytes_reference () ascending trivial

theorem copied_array_is_not_reversed :
    (Solanalib.Specs.SolanaHash.Hash.to_bytes_model () ascending).1.val ≠ ascending.bytes.reverse
      := by
  decide

theorem zero_and_ascending_are_distinct :
    Hash.toArray Hash.zero ≠ Hash.toArray ascending := by decide

end SolanalibTest.Specs.SolanaHash.Hash
