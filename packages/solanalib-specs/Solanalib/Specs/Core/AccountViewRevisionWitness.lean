/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewWitness
public import Solanalib.Specs.Core.AccountViewRevision

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

theorem close_satisfiable (revision : Revision) : (close_contract revision).Satisfiable :=
  ⟨witnessState, witnessHandle, witness_ready.2, fun _ _ => by decide⟩

theorem resize_satisfiable : resize_contract.Satisfiable :=
  ⟨witnessState, (witnessHandle, 0), witness_ready.2, by decide⟩

end Solanalib.Specs.Core.AccountView
