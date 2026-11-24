/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorSpl.Token
import Solanalib.Specs.AnchorSpl.token_2022
import SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.Observation

set_option autoImplicit false
set_option maxRecDepth 8192

open Solanalib.Specs.AnchorSpl

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

abbrev Contracts (binding : Binding) := (index : Types binding) →
  Solanalib.Contracts.Model index.builder.instruction.State (Input index)
    (Except (Error index) Return) index.builder.instruction.Unwind
      index.builder.instruction.Terminal

/-- Decide the actual contract precondition using a proved finite check. -/
def decideRequirement (binding : Binding) (contracts : Contracts binding)
    (index : Types binding) (state : index.builder.instruction.State) (args : Input index)
    (checked : Bool) (exact : checked = true ↔ (contracts index).requires state args) : Bool :=
  @decide ((contracts index).requires state args) (decidable_of_iff _ exact)

theorem decideRequirement_correct (binding : Binding) (contracts : Contracts binding)
    (index : Types binding) (state : index.builder.instruction.State) (args : Input index)
    (checked : Bool) (exact : checked = true ↔ (contracts index).requires state args) :
    decideRequirement binding contracts index state args checked exact = true ↔
      (contracts index).requires state args := by
  simp only [decideRequirement, decide_eq_true_eq]

namespace MissingMetas

/-- Only the current observation is missing. All allocation, push, clone and
cleanup primitives remain the actual reference primitives. In particular the
constructor and array preparation really return before admission fails. -/
def types (binding : Binding) : Types binding :=
  let original := Sample.types binding
  { original with builder := { original.builder with
      instruction := { original.builder.instruction with
        metas := { original.builder.instruction.metas with current := fun _ _ => none } } } }

def functions (binding : Binding) : Execution.Functions (types binding) where
  instruction := {
    bytes := (Reference.functions binding (Sample.script binding)).instruction.bytes
    metas := (Reference.functions binding (Sample.script binding)).instruction.metas
    double := (Reference.functions binding (Sample.script binding)).instruction.double }
  copyExtensions := (Reference.functions binding (Sample.script binding)).copyExtensions
  dropExtensions := (Reference.functions binding (Sample.script binding)).dropExtensions
  cloneRc := (Reference.functions binding (Sample.script binding)).cloneRc
  dropRc := (Reference.functions binding (Sample.script binding)).dropRc
  dropRemaining := (Reference.functions binding (Sample.script binding)).dropRemaining
  newBox := (Reference.functions binding (Sample.script binding)).newBox
  invoke := (Reference.functions binding (Sample.script binding)).invoke
  getReturnData := (Reference.functions binding (Sample.script binding)).getReturnData

theorem graphs (binding : Binding) : Execution.Graph (functions binding) where
  instruction := {
    bytes := (Reference.graphs binding (Sample.script binding)).instruction.bytes
    metas := {
      withCapacity := (Reference.graphs binding (Sample.script
        binding)).instruction.metas.withCapacity
      fromList := (Reference.graphs binding (Sample.script binding)).instruction.metas.fromList
      push := (Reference.graphs binding (Sample.script binding)).instruction.metas.push
      extend := (Reference.graphs binding (Sample.script binding)).instruction.metas.extend
      drop := (Reference.graphs binding (Sample.script binding)).instruction.metas.drop }
    double := (Reference.graphs binding (Sample.script binding)).instruction.double }
  copyExtensions := (Reference.graphs binding (Sample.script binding)).copyExtensions
  dropExtensions := (Reference.graphs binding (Sample.script binding)).dropExtensions
  cloneRc := (Reference.graphs binding (Sample.script binding)).cloneRc
  dropRc := (Reference.graphs binding (Sample.script binding)).dropRc
  dropRemaining := (Reference.graphs binding (Sample.script binding)).dropRemaining
  newBox := (Reference.graphs binding (Sample.script binding)).newBox
  invoke := (Reference.graphs binding (Sample.script binding)).invoke
  getReturnData := (Reference.graphs binding (Sample.script binding)).getReturnData

def built (binding : Binding) : InstructionOwner (types binding) × Reference.State binding.release
  :=
  match Execution.buildFn (functions binding) (Sample.initial binding)
      (argsConstruction (Sample.args binding)) with
  | some (.returned (.ok instruction) state) => (instruction, state)
  | _ => (⟨Token.token2022ProgramId, (0 : Nat), (0 : Nat)⟩, Sample.initial binding)

theorem actual_build (binding : Binding) :
    build (types binding).builder (Sample.initial binding) (argsConstruction (Sample.args binding))
      (.returned (.ok (built binding).1) (built binding).2) := by
  apply (Execution.build_graph (functions binding) (graphs binding) _ _ _).mpr
  cases binding <;> rfl

def prepared (binding : Binding) : Reference.State binding.release :=
  match Execution.prepareFn (functions binding) (Sample.args binding) (built binding).2 with
  | some (.returned _ state) => state
  | _ => (built binding).2

theorem actual_prepare (binding : Binding) :
    prepareAccounts (types binding) (Sample.args binding) (built binding).2 ()
      (.returned (invocationAccounts (Sample.args binding)) (prepared binding)) := by
  apply (Execution.prepare_graph (functions binding) (graphs binding) _ _ _).mpr
  cases binding <;> rfl

theorem rejected (binding : Binding) :
    ¬ ((family binding).contract (types binding)).requires
      (Sample.initial binding) (Sample.args binding) := by
  intro ready
  obtain ⟨metas, _, _⟩ := ready.requestInput (built binding).1 (built binding).2
    (actual_build binding) (invocationAccounts (Sample.args binding)) (prepared binding)
    (actual_prepare binding)
  obtain ⟨values, current⟩ := metas
  change none = some values at current
  cases current

theorem checked_false (binding : Binding) (contracts : Contracts binding)
    (same : contracts = (family binding).contract) :
    false = true ↔ (contracts (types binding)).requires
      (Sample.initial binding) (Sample.args binding) := by
  rw [same]
  exact iff_of_false Bool.false_ne_true (rejected binding)

/-- The same decision bridge used on every native record rejects this real
reached request. No completed wrapper outcome is assumed in the control. -/
theorem decider_rejects (binding : Binding) (contracts : Contracts binding)
    (same : contracts = (family binding).contract) :
    ¬ (contracts (types binding)).requires (Sample.initial binding) (Sample.args binding) := by
  intro admitted
  have accepted := (decideRequirement_correct binding contracts (types binding)
    (Sample.initial binding) (Sample.args binding) false (checked_false binding contracts
      same)).mpr admitted
  have rejected : decideRequirement binding contracts (types binding)
      (Sample.initial binding) (Sample.args binding) false (checked_false binding contracts same) =
        false := rfl
  rw [rejected] at accepted
  cases accepted

end MissingMetas

theorem tokenTransfer0321_rejects_missing_metas :
    ¬ (token.transfer_with_program_owner_contract.contract
      (MissingMetas.types .tokenTransfer0321)).requires
      (Sample.initial .tokenTransfer0321) (Sample.args .tokenTransfer0321) :=
  MissingMetas.decider_rejects .tokenTransfer0321
    token.transfer_with_program_owner_contract.contract rfl

theorem token2022Burn0321_rejects_missing_metas :
    ¬ (token_2022.burn_contract.contract (MissingMetas.types
      .token2022Burn0321)).requires
      (Sample.initial .token2022Burn0321) (Sample.args .token2022Burn0321) :=
  MissingMetas.decider_rejects .token2022Burn0321
    token_2022.burn_contract.contract rfl

theorem token2022CloseAccount0321_rejects_missing_metas :
    ¬ (token_2022.close_account_contract.contract (MissingMetas.types
      .token2022CloseAccount0321)).requires
      (Sample.initial .token2022CloseAccount0321) (Sample.args .token2022CloseAccount0321) :=
  MissingMetas.decider_rejects .token2022CloseAccount0321
    token_2022.close_account_contract.contract rfl

theorem token2022GetAccountDataSize0321_rejects_missing_metas :
    ¬ (token_2022.get_account_data_size_contract.contract
      (MissingMetas.types .token2022GetAccountDataSize0321)).requires
      (Sample.initial .token2022GetAccountDataSize0321) (Sample.args
        .token2022GetAccountDataSize0321) :=
  MissingMetas.decider_rejects .token2022GetAccountDataSize0321
    token_2022.get_account_data_size_contract.contract rfl

theorem token2022InitializeAccount30321_rejects_missing_metas :
    ¬ (token_2022.initialize_account3_contract.contract
      (MissingMetas.types .token2022InitializeAccount30321)).requires
      (Sample.initial .token2022InitializeAccount30321) (Sample.args
        .token2022InitializeAccount30321) :=
  MissingMetas.decider_rejects .token2022InitializeAccount30321
    token_2022.initialize_account3_contract.contract rfl

theorem token2022InitializeImmutableOwner0321_rejects_missing_metas :
    ¬ (token_2022.initialize_immutable_owner_contract.contract
      (MissingMetas.types .token2022InitializeImmutableOwner0321)).requires
      (Sample.initial .token2022InitializeImmutableOwner0321) (Sample.args
        .token2022InitializeImmutableOwner0321) :=
  MissingMetas.decider_rejects .token2022InitializeImmutableOwner0321
    token_2022.initialize_immutable_owner_contract.contract rfl

theorem token2022InitializeMint20321_rejects_missing_metas :
    ¬ (token_2022.initialize_mint2_contract.contract (MissingMetas.types
      .token2022InitializeMint20321)).requires
      (Sample.initial .token2022InitializeMint20321) (Sample.args .token2022InitializeMint20321) :=
  MissingMetas.decider_rejects .token2022InitializeMint20321
    token_2022.initialize_mint2_contract.contract rfl

theorem token2022MintTo0321_rejects_missing_metas :
    ¬ (token_2022.mint_to_contract.contract (MissingMetas.types
      .token2022MintTo0321)).requires
      (Sample.initial .token2022MintTo0321) (Sample.args .token2022MintTo0321) :=
  MissingMetas.decider_rejects .token2022MintTo0321
    token_2022.mint_to_contract.contract rfl

theorem token2022SetAuthority0321_rejects_missing_metas :
    ¬ (token_2022.set_authority_contract.contract (MissingMetas.types
      .token2022SetAuthority0321)).requires
      (Sample.initial .token2022SetAuthority0321) (Sample.args .token2022SetAuthority0321) :=
  MissingMetas.decider_rejects .token2022SetAuthority0321
    token_2022.set_authority_contract.contract rfl

theorem token2022TransferChecked0321_rejects_missing_metas :
    ¬ (token_2022.transfer_checked_contract.contract (MissingMetas.types
      .token2022TransferChecked0321)).requires
      (Sample.initial .token2022TransferChecked0321) (Sample.args .token2022TransferChecked0321) :=
  MissingMetas.decider_rejects .token2022TransferChecked0321
    token_2022.transfer_checked_contract.contract rfl

theorem groupMemberPointer0321_rejects_missing_metas :
    ¬ (token_2022_extensions.group_member_pointer.group_member_pointer_initialize_contract.contract
      (MissingMetas.types .groupMemberPointer0321)).requires
      (Sample.initial .groupMemberPointer0321) (Sample.args .groupMemberPointer0321) :=
  MissingMetas.decider_rejects .groupMemberPointer0321
    token_2022_extensions.group_member_pointer.group_member_pointer_initialize_contract.contract
    rfl

theorem groupPointer0321_rejects_missing_metas :
    ¬ (token_2022_extensions.group_pointer.group_pointer_initialize_contract.contract
      (MissingMetas.types .groupPointer0321)).requires
      (Sample.initial .groupPointer0321) (Sample.args .groupPointer0321) :=
  MissingMetas.decider_rejects .groupPointer0321
    token_2022_extensions.group_pointer.group_pointer_initialize_contract.contract
    rfl

theorem metadataPointer0321_rejects_missing_metas :
    ¬ (token_2022_extensions.metadata_pointer.metadata_pointer_initialize_contract.contract
      (MissingMetas.types .metadataPointer0321)).requires
      (Sample.initial .metadataPointer0321) (Sample.args .metadataPointer0321) :=
  MissingMetas.decider_rejects .metadataPointer0321
    token_2022_extensions.metadata_pointer.metadata_pointer_initialize_contract.contract
    rfl

theorem mintCloseAuthority0321_rejects_missing_metas :
    ¬ (token_2022_extensions.mint_close_authority.mint_close_authority_initialize_contract.contract
      (MissingMetas.types .mintCloseAuthority0321)).requires
      (Sample.initial .mintCloseAuthority0321) (Sample.args .mintCloseAuthority0321) :=
  MissingMetas.decider_rejects .mintCloseAuthority0321
    token_2022_extensions.mint_close_authority.mint_close_authority_initialize_contract.contract
    rfl

theorem nonTransferableMint0321_rejects_missing_metas :
    ¬ (token_2022_extensions.non_transferable.non_transferable_mint_initialize_contract.contract
      (MissingMetas.types .nonTransferableMint0321)).requires
      (Sample.initial .nonTransferableMint0321) (Sample.args .nonTransferableMint0321) :=
  MissingMetas.decider_rejects .nonTransferableMint0321
    token_2022_extensions.non_transferable.non_transferable_mint_initialize_contract.contract
    rfl

theorem permanentDelegate0321_rejects_missing_metas :
    ¬ (token_2022_extensions.permanent_delegate.permanent_delegate_initialize_contract.contract
      (MissingMetas.types .permanentDelegate0321)).requires
      (Sample.initial .permanentDelegate0321) (Sample.args .permanentDelegate0321) :=
  MissingMetas.decider_rejects .permanentDelegate0321
    token_2022_extensions.permanent_delegate.permanent_delegate_initialize_contract.contract
    rfl

theorem transferHook0321_rejects_missing_metas :
    ¬ (token_2022_extensions.transfer_hook.transfer_hook_initialize_contract.contract
      (MissingMetas.types .transferHook0321)).requires
      (Sample.initial .transferHook0321) (Sample.args .transferHook0321) :=
  MissingMetas.decider_rejects .transferHook0321
    token_2022_extensions.transfer_hook.transfer_hook_initialize_contract.contract
    rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

theorem token2022BurnChecked112_rejects_missing_metas :
    ¬ (token_2022.burn_checked_contract.contract (MissingMetas.types
      .token2022BurnChecked112)).requires
      (Sample.initial .token2022BurnChecked112) (Sample.args .token2022BurnChecked112) :=
  MissingMetas.decider_rejects .token2022BurnChecked112
    token_2022.burn_checked_contract.contract rfl

theorem token2022MintToChecked112_rejects_missing_metas :
    ¬ (token_2022.mint_to_checked_contract.contract (MissingMetas.types
      .token2022MintToChecked112)).requires
      (Sample.initial .token2022MintToChecked112) (Sample.args .token2022MintToChecked112) :=
  MissingMetas.decider_rejects .token2022MintToChecked112
    token_2022.mint_to_checked_contract.contract rfl

theorem token2022SetAuthority112_rejects_missing_metas :
    ¬ (token_2022.set_authority_program_id_contract.contract
      (MissingMetas.types .token2022SetAuthority112)).requires
      (Sample.initial .token2022SetAuthority112) (Sample.args .token2022SetAuthority112) :=
  MissingMetas.decider_rejects .token2022SetAuthority112
    token_2022.set_authority_program_id_contract.contract rfl

theorem token2022TransferChecked112_rejects_missing_metas :
    ¬ (token_2022.transfer_checked_program_id_contract.contract
      (MissingMetas.types .token2022TransferChecked112)).requires
      (Sample.initial .token2022TransferChecked112) (Sample.args .token2022TransferChecked112) :=
  MissingMetas.decider_rejects .token2022TransferChecked112
    token_2022.transfer_checked_program_id_contract.contract rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

theorem token2022InitializeAccount3102_rejects_missing_metas :
    ¬ (token_2022.initialize_account3_program_id_contract.contract
      (MissingMetas.types .token2022InitializeAccount3102)).requires
      (Sample.initial .token2022InitializeAccount3102) (Sample.args
        .token2022InitializeAccount3102) :=
  MissingMetas.decider_rejects .token2022InitializeAccount3102
    token_2022.initialize_account3_program_id_contract.contract rfl

theorem token2022TransferChecked102_rejects_missing_metas :
    ¬ (token_2022.transfer_checked_program_id_interface_contract.contract
      (MissingMetas.types .token2022TransferChecked102)).requires
      (Sample.initial .token2022TransferChecked102) (Sample.args .token2022TransferChecked102) :=
  MissingMetas.decider_rejects .token2022TransferChecked102
    token_2022.transfer_checked_program_id_interface_contract.contract rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

theorem token2022TransferChecked029_rejects_missing_metas :
    ¬ (token_2022.transfer_checked_legacy_interface_contract.contract
      (MissingMetas.types .token2022TransferChecked029)).requires
      (Sample.initial .token2022TransferChecked029) (Sample.args .token2022TransferChecked029) :=
  MissingMetas.decider_rejects .token2022TransferChecked029
    token_2022.transfer_checked_legacy_interface_contract.contract rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

theorem tokenBurn027_rejects_missing_metas :
    ¬ (token.burn_contract.contract (MissingMetas.types
      .tokenBurn027)).requires
      (Sample.initial .tokenBurn027) (Sample.args .tokenBurn027) :=
  MissingMetas.decider_rejects .tokenBurn027 token.burn_contract.contract
    rfl

theorem tokenMintTo027_rejects_missing_metas :
    ¬ (token.mint_to_contract.contract (MissingMetas.types
      .tokenMintTo027)).requires
      (Sample.initial .tokenMintTo027) (Sample.args .tokenMintTo027) :=
  MissingMetas.decider_rejects .tokenMintTo027
    token.mint_to_contract.contract rfl

theorem tokenTransfer027_rejects_missing_metas :
    ¬ (token.transfer_inline_error_contract.contract (MissingMetas.types
      .tokenTransfer027)).requires
      (Sample.initial .tokenTransfer027) (Sample.args .tokenTransfer027) :=
  MissingMetas.decider_rejects .tokenTransfer027
    token.transfer_inline_error_contract.contract rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations
