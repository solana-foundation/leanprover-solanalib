/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaPubkey.Borsh
public import Solanalib.Specs.SolanaPubkey.Pubkey
public import Solanalib.Specs.SolanaPubkey.Capabilities

/-!
Pubkey models shared by the explicitly reviewed source profiles.
The thirteen registered keys retain exact release and build applicability.
`to_bytes` admits the reviewed 2.2.1 and 2.4.0 profiles; `clone` remains 2.4.0.
Borsh selection keeps the concrete trait generation and resolved dependencies.
-/

@[expose] public section

open Solanalib.Contracts.Model
