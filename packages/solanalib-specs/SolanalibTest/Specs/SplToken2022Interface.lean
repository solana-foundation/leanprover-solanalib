/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.SplToken2022Interface.Instructions
public import SolanalibTest.Specs.SplToken2022Interface.Extensions
public import SolanalibTest.Specs.SplToken2022Interface.Fees
public import SolanalibTest.Specs.SplToken2022Interface.FeeReference
public import SolanalibTest.Specs.SplToken2022Interface.state.Mint
public import SolanalibTest.Specs.SplToken2022Interface.Models

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Finite mathematical token-interface, extension and fee controls at version 3.1.1. -/
