/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacyFamilies
public import Solanalib.Specs.SplToken2022Interface.Extensions

@[expose] public section

open Solanalib.Specs

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solanalib.Specs.SplToken2022.extension

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

namespace StateWithExtensions

/-- Version 8.0.1 retains its zero-vector allocation and rejects an extended buffer with no TLV
byte. -/
def unpack_contract : Family := Legacy.unpackFamily true

/-- The full operational reference for the selected source version. -/
def unpack_run : FamilyRun unpack_contract := Legacy.unpackRun true

/-- Closed correctness retains every dependency interpretation. -/
theorem unpack_reference : FamilyReference unpack_contract unpack_run := Legacy.unpack_reference
  true

/-- A concrete interpretation with an actual successful execution. -/
def unpack_sample : unpack_contract.Index := Legacy.mintUnpacker

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem unpack_has_execution :
    FamilyHasExecution unpack_contract unpack_run unpack_sample := Legacy.unpack_execution true

/-- The same actual execution supplies an admitted caller. -/
theorem unpack_satisfiable : FamilySatisfiable unpack_contract unpack_sample := by
  rcases unpack_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end StateWithExtensions

namespace BaseStateWithExtensions

/-- The resolved byte getter is followed by the exact Pod cast; the closed sample binds the stricter
old lookup. -/
def get_extension_contract : Family :=
  SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_operational_contract

/-- The full operational reference for the selected source version. -/
def get_extension_run : FamilyRun get_extension_contract :=
  SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_operational_run

/-- Closed correctness retains every dependency interpretation. -/
theorem get_extension_reference : FamilyReference get_extension_contract get_extension_run :=
  SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_operational_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_extension_sample : get_extension_contract.Index := ⟨transferFeeConfigRepresentation,
  Legacy.defaultByteProvider⟩

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_extension_has_execution :
    FamilyHasExecution get_extension_contract get_extension_run get_extension_sample := by
  let receiver : ExtensionReceiver := ⟨.mint, 4096, [1, 0, 108, 0] ++ List.replicate 108 0⟩
  refine ⟨receiver, (), .returned (Legacy.getDefaultExtension transferFeeConfigRepresentation
    receiver)
    receiver, trivial, ?_⟩
  exact (Legacy.getDefaultExtension_iff transferFeeConfigRepresentation receiver _).2 rfl

/-- The same actual execution supplies an admitted caller. -/
theorem get_extension_satisfiable : FamilySatisfiable get_extension_contract get_extension_sample
  := by
  rcases get_extension_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

/-- The legacy scanner pushes each decoded tag before validating its payload length. -/
def get_extension_types_contract : Family := Legacy.typesFamily

/-- The full operational reference for the selected source version. -/
def get_extension_types_run : FamilyRun get_extension_types_contract := Legacy.typesRun

/-- Closed correctness retains every dependency interpretation. -/
theorem get_extension_types_reference : FamilyReference get_extension_types_contract
  get_extension_types_run := Legacy.types_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_extension_types_sample : get_extension_types_contract.Index := Legacy.typesSample

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_extension_types_has_execution :
    FamilyHasExecution get_extension_types_contract get_extension_types_run
      get_extension_types_sample := Legacy.types_execution

/-- The same actual execution supplies an admitted caller. -/
theorem get_extension_types_satisfiable : FamilySatisfiable get_extension_types_contract
  get_extension_types_sample := by
  rcases get_extension_types_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

/-- The actual accessor, packed-length method, old TLV scan and temporary-vector cleanup remain
explicit. -/
def try_get_new_account_len_for_variable_len_extension_contract : Family := Legacy.newLengthFamily

/-- The full operational reference for the selected source version. -/
def try_get_new_account_len_for_variable_len_extension_run : FamilyRun
  try_get_new_account_len_for_variable_len_extension_contract := Legacy.newLengthRun

/-- Closed correctness retains every dependency interpretation. -/
theorem try_get_new_account_len_for_variable_len_extension_reference : FamilyReference
  try_get_new_account_len_for_variable_len_extension_contract
  try_get_new_account_len_for_variable_len_extension_run := Legacy.newLength_reference

/-- A concrete interpretation with an actual successful execution. -/
def try_get_new_account_len_for_variable_len_extension_sample :
  try_get_new_account_len_for_variable_len_extension_contract.Index := Legacy.newLengthSample

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem try_get_new_account_len_for_variable_len_extension_has_execution :
    FamilyHasExecution try_get_new_account_len_for_variable_len_extension_contract
      try_get_new_account_len_for_variable_len_extension_run
      try_get_new_account_len_for_variable_len_extension_sample := Legacy.newLength_execution

/-- The same actual execution supplies an admitted caller. -/
theorem try_get_new_account_len_for_variable_len_extension_satisfiable : FamilySatisfiable
  try_get_new_account_len_for_variable_len_extension_contract
  try_get_new_account_len_for_variable_len_extension_sample := by
  rcases try_get_new_account_len_for_variable_len_extension_has_execution with ⟨before, args,
    outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end BaseStateWithExtensions

namespace ExtensionType

/-- All source-order deduplication allocations precede width validation and scoped cleanup. -/
def try_calculate_account_len_contract : Family := Legacy.sizeFamily

/-- The full operational reference for the selected source version. -/
def try_calculate_account_len_run : FamilyRun try_calculate_account_len_contract := Legacy.sizeRun

/-- Closed correctness retains every dependency interpretation. -/
theorem try_calculate_account_len_reference : FamilyReference try_calculate_account_len_contract
  try_calculate_account_len_run := Legacy.size_reference

/-- A concrete interpretation with an actual successful execution. -/
def try_calculate_account_len_sample : try_calculate_account_len_contract.Index := Legacy.sizeSample

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem try_calculate_account_len_has_execution :
    FamilyHasExecution try_calculate_account_len_contract try_calculate_account_len_run
      try_calculate_account_len_sample := Legacy.size_execution

/-- The same actual execution supplies an admitted caller. -/
theorem try_calculate_account_len_satisfiable : FamilySatisfiable
  try_calculate_account_len_contract try_calculate_account_len_sample := by
  rcases try_calculate_account_len_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end ExtensionType

namespace permanent_delegate

/-- The resolved delegate extension getter returns its optional key, masking ordinary lookup errors.
-/
def get_permanent_delegate_contract : Family := Legacy.keyFamily

/-- The full operational reference for the selected source version. -/
def get_permanent_delegate_run : FamilyRun get_permanent_delegate_contract := Legacy.keyRun

/-- Closed correctness retains every dependency interpretation. -/
theorem get_permanent_delegate_reference : FamilyReference get_permanent_delegate_contract
  get_permanent_delegate_run := Legacy.key_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_permanent_delegate_sample : get_permanent_delegate_contract.Index := Legacy.keySample false

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_permanent_delegate_has_execution :
    FamilyHasExecution get_permanent_delegate_contract get_permanent_delegate_run
      get_permanent_delegate_sample := Legacy.key_execution false

/-- The same actual execution supplies an admitted caller. -/
theorem get_permanent_delegate_satisfiable : FamilySatisfiable get_permanent_delegate_contract
  get_permanent_delegate_sample := by
  rcases get_permanent_delegate_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end permanent_delegate

end Solanalib.Specs.SplToken2022.extension

namespace Solanalib.Specs.SplToken2022.extension

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

namespace StateWithExtensions

/-- The concrete implementation returns its existing borrowed TLV field unchanged. -/
def get_tlv_data_contract : Family := Legacy.tlvFamily

/-- The full operational reference for the selected source version. -/
def get_tlv_data_run : FamilyRun get_tlv_data_contract := Legacy.tlvRun

/-- Closed correctness retains every dependency interpretation. -/
theorem get_tlv_data_reference : FamilyReference get_tlv_data_contract get_tlv_data_run :=
  Legacy.tlv_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_tlv_data_sample : get_tlv_data_contract.Index := Legacy.tlvSample

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_tlv_data_has_execution :
    FamilyHasExecution get_tlv_data_contract get_tlv_data_run get_tlv_data_sample :=
      Legacy.tlv_execution

/-- The same actual execution supplies an admitted caller. -/
theorem get_tlv_data_satisfiable : FamilySatisfiable get_tlv_data_contract get_tlv_data_sample := by
  rcases get_tlv_data_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end StateWithExtensions

namespace transfer_hook

/-- The resolved hook extension getter selects its second nullable key and preserves abnormal exits.
-/
def get_program_id_contract : Family := Legacy.keyFamily

/-- The full operational reference for the selected source version. -/
def get_program_id_run : FamilyRun get_program_id_contract := Legacy.keyRun

/-- Closed correctness retains every dependency interpretation. -/
theorem get_program_id_reference : FamilyReference get_program_id_contract get_program_id_run :=
  Legacy.key_reference

/-- A concrete interpretation with an actual successful execution. -/
def get_program_id_sample : get_program_id_contract.Index := Legacy.keySample true

/-- Closed execution covers allocation, borrowing and cleanup where reached. -/
theorem get_program_id_has_execution :
    FamilyHasExecution get_program_id_contract get_program_id_run get_program_id_sample :=
      Legacy.key_execution true

/-- The same actual execution supplies an admitted caller. -/
theorem get_program_id_satisfiable : FamilySatisfiable get_program_id_contract
  get_program_id_sample := by
  rcases get_program_id_has_execution with ⟨before, args, outcome, admitted, execution⟩
  exact ⟨before, args, admitted⟩

end transfer_hook

end Solanalib.Specs.SplToken2022.extension
