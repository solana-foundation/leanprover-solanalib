/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLog

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.solana_program.log

open Solanalib.Contracts.Model Solanalib.Specs.Core

def sol_log_data_contract := AnchorLog.family
def sol_log_data_run := AnchorLog.run
def sol_log_data_sample := AnchorLog.sample
theorem sol_log_data_reference : FamilyReference sol_log_data_contract sol_log_data_run :=
  AnchorLog.reference
theorem sol_log_data_has_execution :
    FamilyHasExecution sol_log_data_contract sol_log_data_run sol_log_data_sample :=
      AnchorLog.execution
theorem sol_log_data_satisfiable : FamilySatisfiable sol_log_data_contract sol_log_data_sample :=
  sol_log_data_has_execution.satisfiable

end Solanalib.Specs.AnchorLang.solana_program.log
