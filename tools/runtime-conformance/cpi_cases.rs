//! A native test callee behind the Agave CPI translation and synchronization.
//! No callee or CPI body is extracted. The callee is an explicit finite fixture.

use super::{Account, AccountSharedData, InstructionAccount, InstructionError, bytes, hex, key};
use solana_instruction::Instruction;
use solana_program_runtime::{
    __private::Hash,
    cpi::{self, SyscallInvokeSigned, TranslatedAccount},
    declare_process_instruction,
    execution_budget::{SVMTransactionExecutionBudget, SVMTransactionExecutionCost},
    invoke_context::{BpfAllocator, EnvironmentConfig, InvokeContext},
    loaded_programs::{ProgramCacheForTxBatch, ProgramRuntimeEnvironments},
    memory_context::MemoryContext,
    program_cache_entry::ProgramCacheEntry,
    serialization::serialize_parameters,
    solana_sbpf::{
        aligned_memory::AlignedMemory,
        ebpf::{HOST_ALIGN, MM_HEAP_START, MM_INPUT_START},
        memory_region::{MemoryMapping, MemoryRegion},
        program::{BuiltinFunctionDefinition, SBPFVersion},
        vm::Config,
    },
    sysvar_cache::SysvarCache,
};
use solana_rent::Rent;
use solana_sdk_ids::{bpf_loader_upgradeable, native_loader};
use solana_svm_callback::InvokeContextCallback;
use solana_svm_feature_set::SVMFeatureSet;
use solana_transaction_context::transaction::TransactionContext;
use std::{error::Error, sync::Arc};

// The local language dispatch calls the Agave instruction and account-info translators.
struct CTranslator;

struct FixtureCallback;
impl InvokeContextCallback for FixtureCallback {}

impl SyscallInvokeSigned for CTranslator {
    fn translate_instruction(
        address: u64,
        context: &InvokeContext,
    ) -> Result<Instruction, Box<dyn Error>> {
        cpi::translate_instruction_c(address, context)
    }

    fn translate_accounts<'a>(
        address: u64,
        count: u64,
        context: &InvokeContext,
    ) -> Result<Vec<TranslatedAccount<'a>>, Box<dyn Error>> {
        cpi::translate_accounts_c(address, count, context)
    }
}

declare_process_instruction!(FixtureCallee, 1, |context| {
    let observation = {
        let instruction = context.transaction_context.get_current_instruction_context()?;
        let message = instruction.get_instruction_data();
        let expected_len = usize::from(message[0]);
        let expected = &message[1..1 + expected_len];
        let replacement = &message[2 + expected_len..];
        if usize::from(message[1 + expected_len]) != replacement.len() {
            return Err(InstructionError::InvalidInstructionData);
        }
        let mut account = instruction.try_borrow_instruction_account(0)?;
        if account.get_data() != expected || *account.get_owner() != key(30) {
            return Err(InstructionError::InvalidAccountData);
        }
        let mut observation = vec![instruction.get_number_of_instruction_accounts() as u8];
        for index in 0..instruction.get_number_of_instruction_accounts() {
            observation.push(u8::from(instruction.is_instruction_account_signer(index)?));
            observation.push(u8::from(instruction.is_instruction_account_writable(index)?));
        }
        observation.extend_from_slice(account.get_data());
        account.set_data_from_slice(replacement)?;
        observation
    };
    context.transaction_context.set_return_data(key(30), observation)
});

fn write_u64(buffer: &mut [u8], offset: usize, value: u64) {
    buffer[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

fn read_u64(buffer: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(buffer[offset..offset + 8].try_into().unwrap())
}

pub fn run_case(fields: &[&str]) {
    assert_eq!(fields.len(), 8);
    let entry_data = bytes(fields[1]);
    let caller_data = bytes(fields[2]);
    let callee_expected = bytes(fields[3]);
    let callee_data = bytes(fields[4]);
    let duplicate = fields[5] == "1";
    let bad_pointer = fields[6] == "1";
    let writable = fields[7] == "1";
    assert!(caller_data.len() <= entry_data.len() + 10240);
    assert!(callee_expected.len() < 256 && callee_data.len() < 256);

    let transaction_accounts = vec![
        (key(10), AccountSharedData::from(Account {
            lamports: 1_000_000, data: entry_data, owner: key(20), executable: false, rent_epoch: 7,
        })),
        (key(20), AccountSharedData::from(Account {
            lamports: 1, data: vec![], owner: bpf_loader_upgradeable::id(), executable: true, rent_epoch: 0,
        })),
        (key(30), AccountSharedData::from(Account {
            lamports: 1, data: vec![], owner: native_loader::id(), executable: true, rent_epoch: 0,
        })),
    ];
    let features = SVMFeatureSet {
        syscall_parameter_address_restrictions: true,
        virtual_address_space_adjustments: false,
        account_data_direct_mapping: false,
        raise_cpi_nesting_limit_to_8: false,
        ..SVMFeatureSet::default()
    };
    let budget = SVMTransactionExecutionBudget::new_with_defaults(false);
    let mut transaction_context = TransactionContext::new(
        transaction_accounts, Rent::with_lamports_per_byte(5080),
        budget.max_instruction_stack_depth, budget.max_instruction_trace_length, 1,
    );
    let environments = ProgramRuntimeEnvironments::mock();
    let sysvars = SysvarCache::default();
    let environment = EnvironmentConfig::new(
        Hash::default(), 0, false, &FixtureCallback, &features, &environments, &sysvars,
    );
    let mut cache = ProgramCacheForTxBatch::default();
    let mut invoke_context = InvokeContext::new(
        &mut transaction_context, &mut cache, environment, None, budget,
        SVMTransactionExecutionCost::default(),
    );
    invoke_context.program_cache_for_tx_batch.replenish(
        key(30), Arc::new(ProgramCacheEntry::new_builtin(0, FixtureCallee::register)),
    );
    invoke_context.transaction_context.configure_top_level_instruction_for_tests(
        1,
        vec![
            InstructionAccount::new(0, true, writable),
            InstructionAccount::new(0, true, writable),
            InstructionAccount::new(2, false, false),
        ],
        vec![7, 8, 9],
    ).unwrap();
    invoke_context.push().unwrap();
    let (mut buffer, regions, metadata, _) = serialize_parameters(
        &invoke_context.transaction_context.get_current_instruction_context().unwrap(),
        false, false, false,
    ).unwrap();
    let original = hex(buffer.as_slice());
    let account = &metadata[0];
    let data_offset = (account.vm_data_addr - MM_INPUT_START) as usize;
    let owner_offset = (account.vm_owner_addr - MM_INPUT_START) as usize;
    buffer.as_slice_mut()[owner_offset..owner_offset + 32].copy_from_slice(key(30).as_ref());
    write_u64(buffer.as_slice_mut(), data_offset - 8, caller_data.len() as u64);
    buffer.as_slice_mut()[data_offset..data_offset + caller_data.len()].copy_from_slice(&caller_data);

    // C wire records use the pinned #[repr(C)] layouts in program-runtime/src/cpi.rs.
    // Descriptor memory is separate from the input account region and 8-byte aligned.
    let mut heap = AlignedMemory::<HOST_ALIGN>::zero_filled(1024);
    let ix_offset = 0;
    let metas_offset = 64;
    let info_offset = 128;
    let program_offset = 192;
    let message_offset = 256;
    let mut message = vec![callee_expected.len() as u8];
    message.extend_from_slice(&callee_expected);
    message.push(callee_data.len() as u8);
    message.extend_from_slice(&callee_data);
    let h = heap.as_slice_mut();
    write_u64(h, ix_offset, MM_HEAP_START + program_offset as u64);
    write_u64(h, ix_offset + 8, MM_HEAP_START + metas_offset as u64);
    write_u64(h, ix_offset + 16, if duplicate { 2 } else { 1 });
    write_u64(h, ix_offset + 24, MM_HEAP_START + message_offset as u64);
    write_u64(h, ix_offset + 32, message.len() as u64);
    write_u64(h, metas_offset, account.vm_key_addr);
    h[metas_offset + 8] = 1; // writable
    h[metas_offset + 9] = 1; // signer
    write_u64(h, metas_offset + 16, account.vm_key_addr);
    // The zero privilege bytes in the duplicate must merge with the first meta.
    write_u64(h, info_offset, account.vm_key_addr);
    write_u64(h, info_offset + 8, account.vm_lamports_addr);
    write_u64(h, info_offset + 16, caller_data.len() as u64);
    write_u64(h, info_offset + 24, account.vm_data_addr + u64::from(bad_pointer));
    write_u64(h, info_offset + 32, account.vm_owner_addr);
    write_u64(h, info_offset + 40, 7);
    // Account-info flags are deliberately zero. The runtime ignores these flags.
    h[program_offset..program_offset + 32].copy_from_slice(key(30).as_ref());
    h[message_offset..message_offset + message.len()].copy_from_slice(&message);

    let config = Config { aligned_memory_mapping: false, ..Config::default() };
    let heap_region = MemoryRegion::new(&raw mut heap.as_slice_mut()[..], MM_HEAP_START);
    let all_regions = std::iter::once(heap_region).chain(regions).collect();
    // SAFETY: heap and buffer remain live and are not reallocated until the mapping
    // is dropped. No host reference into either backing allocation is retained
    // during cpi_common, and all writable regions have disjoint backing storage.
    let mapping = unsafe { MemoryMapping::new(all_regions, &config, SBPFVersion::V3).unwrap() };
    invoke_context.memory_contexts.set_memory_context_abi_v1(MemoryContext::new(
        BpfAllocator::new(1024), metadata, mapping,
    )).unwrap();

    let raw_result = cpi::cpi_common::<CTranslator>(
        &mut invoke_context,
        MM_HEAP_START + ix_offset as u64,
        MM_HEAP_START + info_offset as u64,
        1,
        0,
        0,
    );
    let result = match raw_result {
        Ok(value) => {
            assert!(!bad_pointer, "the invalid-pointer fixture unexpectedly returned");
            assert_eq!(value, 0);
            Ok(())
        }
        Err(error) => {
            eprintln!("native_cpi_raw\t{}\t{error:?}", fields[0]);
            if bad_pointer {
                assert!(matches!(error.downcast_ref::<cpi::CpiError>(),
                    Some(cpi::CpiError::InvalidPointer)), "unexpected raw CPI error: {error:?}");
                Err(InstructionError::ProgramFailedToComplete)
            } else {
                Err(error.downcast_ref::<InstructionError>()
                    .expect("unexpected non-instruction CPI error").clone())
            }
        }
    };
    let (return_program, return_data) = invoke_context.transaction_context.get_return_data();
    let auxiliary = format!(
        "info_len={};return_program={};return={};cpi_count={};stack={}",
        read_u64(heap.as_slice(), info_offset + 16),
        hex(return_program.as_ref()),
        hex(return_data),
        invoke_context.transaction_context.number_of_cpis_in_trace(),
        invoke_context.transaction_context.get_instruction_stack_height(),
    );
    let after = hex(buffer.as_slice());
    // Destroy the mapping before its backing allocations and release the context borrow.
    drop(invoke_context);
    super::emit_with_aux(fields[0], "cpi", &result, transaction_context, &original, &after, &auxiliary);
}
