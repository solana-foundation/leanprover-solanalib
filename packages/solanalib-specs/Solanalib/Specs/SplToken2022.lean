/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022.Instructions
public import Solanalib.Specs.SplToken2022.Ids
public import Solanalib.Specs.SplToken2022.Capabilities
public import Solanalib.Specs.SplToken2022.Extensions
public import Solanalib.Specs.SplToken2022.Fees
public import Solanalib.Specs.SplToken2022.MetadataPointer
public import Solanalib.Specs.SplToken2022.StateExtra

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! Pure mathematical Token-2022 operations: local CPI preparation, selected
extension access and sizing, instruction construction and epoch fees.
Each operation retains its exact reviewed source and build profile. -/
