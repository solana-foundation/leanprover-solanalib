/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorCodecDecoders

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang

open Solanalib.Contracts.Model Solanalib.Specs.Core

open AnchorCodec

namespace bpf_writer.BpfWriter

/-- Perform the one partial write implemented by BpfWriter, retaining its cursor and copied prefix
before a short-write diagnostic. No retry or rollback occurs. -/
def write_all_contract : Family := writeAllFamily
def write_all_run : FamilyRun write_all_contract := writeAllRun
def write_all_sample : write_all_contract.Index := writeSample
theorem write_all_reference : FamilyReference write_all_contract write_all_run :=
  writeAll_reference
theorem write_all_has_execution :
    FamilyHasExecution write_all_contract write_all_run write_all_sample :=
  writeAll_execution
theorem write_all_satisfiable : FamilySatisfiable write_all_contract write_all_sample :=
  write_all_has_execution.satisfiable

end bpf_writer.BpfWriter

end Solanalib.Specs.AnchorLang
