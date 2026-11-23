/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022Interface.Instructions
public import Solanalib.Specs.SplToken2022Interface.Extensions
public import Solanalib.Specs.SplToken2022Interface.Fees
public import Solanalib.Specs.SplToken2022Interface.FeeReference
public import Solanalib.Specs.SplToken2022Interface.Capabilities
public import Solanalib.Specs.SplToken2022Interface.state.Mint

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Pure mathematical token interfaces, extensions and fees at version 3.1.1. -/
