# Recorded model and test boundaries

Generated from the existing source registries, recorded release census and conformance policies by `python3.12 tools/model-audit/generate_gap_index.py`. Edit the underlying record, review changed inputs in [gap-review.json](gap-review.json), then regenerate. This index adds no model, source proof or native-test credit.

Last index review: **2026-11-24**. Review of model limitations, the release census, test records, links and classifications, including runtime types and transfer conservation; the pinned source reviews provide the per-model arguments.

The [authoring standard](model-standard.md) distinguishes intentional model scope, implementation bindings and missing test evidence. Assumptions are not classified as defects merely because a theorem uses them. The machine-readable `--json` output retains exact declarations, immutable source records, build-profile references, tests, status and resolution criteria; this page is their readable index.

## Runtime correspondence

Runtime theorems concern the modeled functions under their stated premises. The source arguments retain the listed projections, differences and interpretation conditions.

**Status:** recorded model scope. **Resolution criterion:** Establish the missing correspondence for the exact source/build and observables, or retain the explicit boundary. A mathematical theorem alone does not discharge a source interpretation.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `runtime:basic-representation` | `Solanalib.Runtime.Pubkey`, `Solanalib.Runtime.u64le`, `Solanalib.Runtime.leNat` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:profile-and-identities` | `Solanalib.Runtime.Ids.reservedKeys`, `Solanalib.Runtime.mainnet`, `Solanalib.Runtime.Profile.memConfig`, `Solanalib.Runtime.RentParams.WF` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:account-and-rent` | `Solanalib.Runtime.Account`, `Solanalib.Runtime.Account.WF`, `Solanalib.Runtime.RentParams.minBalance`, `Solanalib.Runtime.relaxedMinBalanceOk`, `Solanalib.Runtime.rentCheck`, `Solanalib.Runtime.feePayerRentCheck` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:program-errors` | `Solanalib.Runtime.InstrError.fromU64`, `Solanalib.Runtime.IsComputeError` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:context-and-setters` | `Solanalib.Runtime.TxState`, `Solanalib.Runtime.Frame.FlagsConsistent`, `Solanalib.Runtime.push`, `Solanalib.Runtime.pop`, `Solanalib.Runtime.setLamports`, `Solanalib.Runtime.setOwner`, `Solanalib.Runtime.canDataBeResized`, `Solanalib.Runtime.setDataFromSlice`, `Solanalib.Runtime.setExecutable`, `Solanalib.Runtime.setNativeReturnData` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:input-layout-and-readback` | `Solanalib.Runtime.serializeChecked`, `Solanalib.Runtime.layout`, `Solanalib.Runtime.readBack`, `Solanalib.Runtime.readBackAcct` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:input-memory` | `Solanalib.Runtime.loadRegion`, `Solanalib.Runtime.storeRegion`, `Solanalib.Runtime.handlerGrow`, `Solanalib.Runtime.dataFault` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:library-state` | `Solanalib.Runtime.Cell`, `Solanalib.Runtime.Store`, `Solanalib.Runtime.stepInPlace`, `Solanalib.Runtime.Lease.addShared`, `Solanalib.Runtime.PartialCell`, `Solanalib.Runtime.Completes`, `Solanalib.Runtime.initialStore`, `Solanalib.Runtime.copyBack_run`, `Solanalib.Runtime.WellBracketedRun` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:primitive-contracts` | `Solanalib.Runtime.Prims`, `Solanalib.Runtime.createProgramAddress`, `Solanalib.Runtime.findProgramAddress`, `Solanalib.Runtime.createWithSeed` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:sysvar-values` | `Solanalib.Runtime.Sysvars`, `Solanalib.Runtime.Sysvars.WF`, `Solanalib.Runtime.TypedSysvar.value` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:syscall-values` | `Solanalib.Runtime.SysReq.registered`, `Solanalib.Runtime.sysStep`, `Solanalib.Runtime.findSibling`, `Solanalib.Runtime.getSysvarReply`, `Solanalib.Runtime.siblingOutputsDisjoint`, `Solanalib.Runtime.HashAlg.width`, `Solanalib.Runtime.sysStep_hash`, `Solanalib.Runtime.Abi.checkAligned` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:cpi-boundary` | `Solanalib.Runtime.mergeMeta`, `Solanalib.Runtime.checkPrivileges`, `Solanalib.Runtime.prepareCallee`, `Solanalib.Runtime.cpiPrepare`, `Solanalib.Runtime.updateCallee`, `Solanalib.Runtime.updateCaller`, `Solanalib.Runtime.cpiAnswer` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:system-instructions` | `Solanalib.Runtime.decodeSystemIx`, `Solanalib.Runtime.systemProcess`, `Solanalib.Runtime.sysAllocate`, `Solanalib.Runtime.sysAssign`, `Solanalib.Runtime.sysTransfer`, `Solanalib.Runtime.sysCreateAccount` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:transaction-local-program-cache` | `Solanalib.Runtime.ModifiedProgram`, `Solanalib.Runtime.ModifiedProgram.effectiveSlot`, `Solanalib.Runtime.ModifiedProgram.delayedAt`, `Solanalib.Runtime.ProgramCacheChanges.lookup`, `Solanalib.Runtime.ProgramCacheChanges.store`, `Solanalib.Runtime.LoaderV3CacheAction`, `Solanalib.Runtime.loaderV3CacheAction`, `Solanalib.Runtime.loaderV3CacheEffect`, `Solanalib.Runtime.LoaderV3ResultContract`, `Solanalib.Runtime.applyLoaderV3Effect`, `Solanalib.Runtime.finishLoaderV3`, `Solanalib.Runtime.applyLoaderV3Effect_lookup` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:execution-and-message` | `Solanalib.Runtime.Program`, `Solanalib.Runtime.Exec`, `Solanalib.Runtime.ProcInstr`, `Solanalib.Runtime.dispatch`, `Solanalib.Runtime.Message.WF`, `Solanalib.Runtime.Message.isWritable`, `Solanalib.Runtime.ixSysvarOffsetsFit`, `Solanalib.Runtime.ProcMessage`, `Solanalib.Runtime.RunProgram.loaderV3_cache`, `Solanalib.Runtime.dispatch_modified` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:nonce-and-transactions` | `Solanalib.Runtime.NonceData.encode`, `Solanalib.Runtime.decodeCurrentNonce`, `Solanalib.Runtime.Message.durableNonceIndex`, `Solanalib.Runtime.Message.nonceAuthoritySigned`, `Solanalib.Runtime.checkNonceSelection`, `Solanalib.Runtime.advanceNonceAccount`, `Solanalib.Runtime.validateNonce`, `Solanalib.Runtime.validateNonce_advanced`, `Solanalib.Runtime.validateNonce_preserves_fields`, `Solanalib.Runtime.validateNonce_preserves_length`, `Solanalib.Runtime.ProcTx`, `Solanalib.Runtime.ProcTx.nonce_error`, `Solanalib.Runtime.validateFeePayer`, `Solanalib.Runtime.checkLoad`, `Solanalib.Runtime.Execute`, `Solanalib.Runtime.commitSuccess`, `Solanalib.Runtime.commitRollback`, `Solanalib.Runtime.ProcTxWithCache`, `Solanalib.Runtime.ProcTxWithCache.toProcTx`, `Solanalib.Runtime.ProcTx.withCache`, `Solanalib.Runtime.procTx_iff_withCache`, `Solanalib.Runtime.ProcTxWithCache.failure_changes`, `Solanalib.Runtime.committedPrograms`, `Solanalib.Runtime.BankEnv.withCommittedPrograms`, `Solanalib.Runtime.ProcTxWithCache.failure_programs` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:derived-runtime-proofs` | `Solanalib.Runtime.ProcInstr.frame`, `Solanalib.Runtime.ProcMessage.lamports`, `Solanalib.Runtime.ExecutableEq`, `Solanalib.Runtime.ExecutableEq.of_readBack`, `Solanalib.Runtime.ProcInstr.readonly_lamports`, `Solanalib.Runtime.ProcInstr.stack`, `Solanalib.Runtime.IndexCoherent.of_push`, `Solanalib.Runtime.ProcInstr.readonly_account`, `Solanalib.Runtime.readBackL_of_legal`, `Solanalib.Runtime.noCpi_result`, `Solanalib.Runtime.message_frame_flagsConsistent`, `Solanalib.Runtime.calleeAccounts_flagsConsistent`, `Solanalib.Runtime.prepareCallee_flagsConsistent`, `Solanalib.Runtime.flagsConsistent_queries`, `Solanalib.Runtime.checkPrivileges_first`, `Solanalib.Runtime.sysTransferVerified_preserves_total`, `Solanalib.Runtime.transfer_preserves_total` | [source record](../packages/solanalib-runtime/source-map/sources.json) |
| `runtime:state-threading` | `Solanalib.Runtime.Env`, `Solanalib.Runtime.ValidTrace.clock_constant`, `Solanalib.Runtime.Protocol.forgetState`, `Solanalib.Runtime.Protocol.uniform_post` | [source record](../packages/solanalib-runtime/source-map/sources.json) |

## SDK model scope and remaining work

The canonical model role, omitted behavior and remaining requirements limit the mathematical contract. An observation or supporting facet does not replace its primary operational model.

**Status:** recorded scope or remaining requirement. **Resolution criterion:** Address the canonical model_gaps and remaining_requirements with substantive scoped results and tests before changing the registered role or claim. Preserve existing behavior and keep separate source bindings open until proved.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `sdk-model:anchor-lang::ToAccountInfo::to_account_info_observation` | `Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::accounts::account::Account::try_from_observation` | `Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::accounts::account_loader::AccountLoader::load_mut_observation` | `Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_mut_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::accounts::account_loader::AccountLoader::load_observation` | `Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::accounts::account_loader::AccountLoader::try_from_observation` | `Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::accounts::interface_account::InterfaceAccount::try_from_observation` | `Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_from_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::context::CpiContext::new_with_signer_observation` | `Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::error::Error::from_anchor_error_observation` | `Solanalib.Specs.AnchorLang.error.Error.from_anchor_error_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::error::Error::with_pubkeys_observation` | `Solanalib.Specs.AnchorLang.error.Error.with_pubkeys_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::error::Error::with_values_observation` | `Solanalib.Specs.AnchorLang.error.Error.with_values_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-spl::token::accessor::amount_observation` | `Solanalib.Specs.AnchorSpl.token.accessor.amount_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-spl::token::transfer_observation` | `Solanalib.Specs.AnchorSpl.token.transfer_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:pinocchio::sysvars::instructions::Instructions::load_current_index` | `Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.load_current_index_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:pinocchio::sysvars::instructions::Instructions::load_instruction_at` | `Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.load_instruction_at_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:pinocchio::sysvars::instructions::IntrospectedInstruction::get_instruction_data` | `Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.get_instruction_data_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:pinocchio::sysvars::instructions::IntrospectedInstruction::get_program_id` | `Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.get_program_id_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:shared-owned-array::construction` | `Solanalib.Specs.Core.Owned.Array.construction_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-info::AccountInfo::clone_observation` | `Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-view::AccountView::Observation::data_len` | `Solanalib.Specs.SolanaAccountView.AccountView.Observation.data_len_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-view::AccountView::Observation::is_signer` | `Solanalib.Specs.SolanaAccountView.AccountView.Observation.is_signer_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-view::AccountView::Observation::lamports` | `Solanalib.Specs.SolanaAccountView.AccountView.Observation.lamports_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-view::AccountView::Observation::set_lamports` | `Solanalib.Specs.SolanaAccountView.AccountView.Observation.set_lamports_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-view::AccountView::Observation::try_borrow` | `Solanalib.Specs.SolanaAccountView.AccountView.Observation.try_borrow_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-account-view::AccountView::Observation::try_borrow_mut` | `Solanalib.Specs.SolanaAccountView.AccountView.Observation.try_borrow_mut_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-address::Address::find_program_address` | `Solanalib.Specs.SolanaAddress.Address.find_program_address_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-address::Address::is_on_curve` | `Solanalib.Specs.SolanaAddress.Address.is_on_curve_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-system-interface::instruction::create_account` | `Solanalib.Specs.SolanaSystemInterface.instruction.create_account_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-system-interface::instruction::transfer` | `Solanalib.Specs.SolanaSystemInterface.instruction.transfer_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::extension::BaseStateWithExtensions::get_extension` | `Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::extension::BaseStateWithExtensions::get_extension_types` | `Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_types_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::extension::StateWithExtensions::unpack` | `Solanalib.Specs.SplToken2022Interface.extension.StateWithExtensions.unpack_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee` | `Solanalib.Specs.SplToken2022Interface.extension.transfer_fee.TransferFeeConfig.get_epoch_fee_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::instruction::close_account_value` | `Solanalib.Specs.SplToken2022Interface.instruction.close_account_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::instruction::initialize_account3_value` | `Solanalib.Specs.SplToken2022Interface.instruction.initialize_account3_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::instruction::transfer_checked_value` | `Solanalib.Specs.SplToken2022Interface.instruction.transfer_checked_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022-interface::instruction::withdraw_excess_lamports_value` | `Solanalib.Specs.SplToken2022Interface.instruction.withdraw_excess_lamports_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-2022::onchain::invoke_transfer_checked_value` | `Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-interface::instruction::initialize_account3_value` | `Solanalib.Specs.SplTokenInterface.instruction.initialize_account3_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:spl-token-interface::instruction::transfer_value` | `Solanalib.Specs.SplTokenInterface.instruction.transfer_value_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:anchor-lang::accounts::account_loader::AccountLoader::load_init_observation` | `Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.load_init_observation_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-program::program::invoke_forwarded_inputs` | `Solanalib.Specs.SolanaProgram.program.invoke_forwarded_inputs_contract` | [source record](../packages/solanalib-specs/source-map.json) |
| `sdk-model:solana-program::program::invoke_signed_forwarded_inputs` | `Solanalib.Specs.SolanaProgram.program.invoke_signed_forwarded_inputs_contract` | [source record](../packages/solanalib-specs/source-map.json) |

## Rust implementation bindings

Closed reference-correctness, satisfiability and execution witnesses establish mathematical model facts. They do not establish correctness of the registered Rust bodies or their bindings.

**Status:** open. **Resolution criterion:** Prove the source implementation and representation/dependency bindings for the exact selected functions and builds, retaining the explicit boundary of any external call.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `sdk:rust-implementation-bindings` | 560 source-facing models; 791 API records | [source record](../packages/solanalib-specs/source-map.json) |

## Pending release applicability reviews

The 22 November 2026 census found these stable releases outside the recorded source histories. Their release-specific applicability remains unreviewed; this finding neither changes exact reviewed releases or assumed compatible ranges nor supplies source-proof or native-test credit.

**Status:** applicability review pending. **Resolution criterion:** Authenticate each release archive, review the reached functions, representations, dependencies and build conditions, and record its applicability or exclusion in the authoritative source registry with matching generated artifacts and relevant tests. Retain the original census evidence and explicitly review the gap presentation before closing the pending record.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `release-review:pinocchio-system@0.7.1` | `pinocchio-system 0.7.1`; detected 2026-11-22 | [source record](../docs/release-census.json) |
| `release-review:pinocchio-token-2022@0.5.1` | `pinocchio-token-2022 0.5.1`; detected 2026-11-22 | [source record](../docs/release-census.json) |

## Native test exceptions

The named helper has mathematical scenarios and no standalone native entry point. Its exception does not give native conformance credit.

**Status:** documented mathematical-only exception. **Resolution criterion:** Retain the justified exception and its scenarios. If a real source-facing entry is introduced, add its exact deciding checker and controls before removing the exception.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `native-test:shared-owned-array::construction` | `Solanalib.Specs.Core.Owned.Array.construction_contract` | [source record](../tools/library-conformance/not-tested.toml) |

## Open checker preconditions

The checker decides the registered reference on recorded inputs; the separate operational precondition at each actual record index remains unproved as recorded.

**Status:** open. **Resolution criterion:** Prove or decide the precondition at the actual recorded index, then remove the exception only when the complete replay verifies that the entry is no longer needed.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `precondition-test:spl-token-2022::onchain::invoke_transfer_checked` | `Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_contract` | [source record](../tools/library-conformance/requires-open.toml) |

## Checker selection

Authenticated native observations without a selected checker, and controls targeting them, earn no conformance credit. The replay records exact selected and omitted identities.

**Status:** explicit finite coverage omission. **Resolution criterion:** Add the exact versioned function/instantiation checker and relevant controls; remove its exception when complete replay succeeds without that omission. Keep the original authenticated observation.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `library-tests:registered-checker-omissions` | 273 allowed observation identities | [source record](../tools/library-conformance/checker_selection.py) |

## Execution connections

Runtime and SDK models share Solana value types. The System transfer theorem proves conservation for successful runtime transfers; no sBPF-to-runtime execution interpretation is established.

**Status:** open. **Resolution criterion:** Supply a scoped simulation relating machine memory, syscalls, outcomes and compute effects to the runtime program relation, with matching premises and boundary tests.

| Stable ID | Affected declarations or selection | Canonical record |
| --- | --- | --- |
| `execution:sbpf-runtime` | `Solanalib.SBPF.bpfInterp`, `Solanalib.Runtime.Program`, `Solanalib.Runtime.Exec` | [review record](../docs/gap-review.json) |

The SDK registry is the authority for per-model assumptions, selected observables and exact source/build applicability. Follow its [registry guide](../packages/solanalib-specs/source-map/README.md) and [binding obligations](../packages/solanalib-specs/BINDINGS.md). Runtime rows refer to the matching `correspondence` IDs in its [source registry](../packages/solanalib-runtime/source-map/sources.json) and [trust boundary](../packages/solanalib-runtime/TRUST.md).

Allowed omission identities are policy, not a claim about a newly executed replay. Each replay must authenticate its complete corpora and record the actual selected, omitted and rejected-control identities. Use the [conformance guide](../tools/library-conformance/REFERENCE.md) for the mathematical-only exception and the precise open Token-2022 precondition.
