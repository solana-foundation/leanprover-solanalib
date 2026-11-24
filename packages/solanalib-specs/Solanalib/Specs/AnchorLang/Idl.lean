/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorCodecDecoders
public import Solanalib.Specs.AnchorLang.bpf_writer

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.idl.IdlInstruction

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorCodec

/-- Decode the seven Borsh 0.9.3 enum arms with exact cursor/error behavior and an owned vector only
for the Write arm. -/
def deserialize_contract : Family := idlFamily
def deserialize_run : FamilyRun deserialize_contract := idlRun
def deserialize_sample : deserialize_contract.Index := idlSample
theorem deserialize_reference : FamilyReference deserialize_contract deserialize_run :=
  idl_reference
theorem deserialize_has_execution :
    FamilyHasExecution deserialize_contract deserialize_run deserialize_sample :=
  idl_execution
theorem deserialize_satisfiable : FamilySatisfiable deserialize_contract deserialize_sample :=
  deserialize_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.idl.IdlInstruction
