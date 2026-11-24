//! Finite native observations from the unmodified, pinned Agave libraries.
//! The build runner links the exact rlibs emitted by Cargo under the Agave lockfile.

use solana_account::{Account, AccountSharedData, ReadableAccount};
use solana_instruction::error::InstructionError;
use solana_program_runtime::serialization::{deserialize_parameters, serialize_parameters};
use solana_pubkey::Pubkey;
use solana_rent::Rent;
use solana_sdk_ids::{bpf_loader_deprecated, bpf_loader_upgradeable};
use solana_transaction_context::{
    instruction_accounts::InstructionAccount, transaction::TransactionContext,
};
use std::{env, fs, path::Path};

mod cpi_cases;

fn key(value: u64) -> Pubkey {
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&value.to_be_bytes());
    Pubkey::new_from_array(bytes)
}

fn bytes(value: &str) -> Vec<u8> {
    if value == "-" {
        Vec::new()
    } else {
        value.split(',').map(|n| n.parse().unwrap()).collect()
    }
}

fn hex(data: &[u8]) -> String {
    data.iter().map(|b| format!("{b:02x}")).collect()
}

fn status<T>(result: &Result<T, InstructionError>) -> String {
    match result {
        Ok(_) => "ok".to_owned(),
        Err(error) => format!("{error:?}"),
    }
}

fn context(
    owner: u64,
    writable: bool,
    signer: bool,
    lamports: u64,
    data: Vec<u8>,
    executable: bool,
    rent_epoch: u64,
    references: usize,
    deprecated: bool,
) -> TransactionContext<'static> {
    let account = AccountSharedData::from(Account {
        lamports,
        data,
        owner: key(owner),
        executable,
        rent_epoch,
    });
    let program = AccountSharedData::from(Account {
        lamports: 1,
        data: vec![],
        owner: if deprecated {
            bpf_loader_deprecated::id()
        } else {
            bpf_loader_upgradeable::id()
        },
        executable: true,
        rent_epoch: 0,
    });
    let mut transaction = TransactionContext::new(
        vec![(key(10), account), (key(20), program)],
        Rent::with_lamports_per_byte(5080),
        5,
        64,
        1,
    );
    transaction
        .configure_top_level_instruction_for_tests(
            1,
            vec![InstructionAccount::new(0, signer, writable); references],
            vec![7, 8, 9],
        )
        .unwrap();
    transaction.push().unwrap();
    transaction
}

fn accounts(transaction: &TransactionContext) -> String {
    (0..transaction.get_number_of_accounts())
        .map(|index| {
            let account = transaction.accounts().try_borrow(index).unwrap();
            format!(
                "{},{},{},{},{}",
                account.lamports(),
                hex(account.owner().as_ref()),
                hex(account.data()),
                u8::from(account.executable()),
                account.rent_epoch(),
            )
        })
        .collect::<Vec<_>>()
        .join("|")
}

fn emit(
    id: &str,
    kind: &str,
    result: &Result<(), InstructionError>,
    transaction: TransactionContext,
    serialized: &str,
    edited: &str,
) {
    emit_with_aux(id, kind, result, transaction, serialized, edited, "-");
}

fn emit_with_aux(
    id: &str,
    kind: &str,
    result: &Result<(), InstructionError>,
    mut transaction: TransactionContext,
    serialized: &str,
    edited: &str,
    auxiliary: &str,
) {
    let snapshot = accounts(&transaction);
    let resize = transaction.accounts().resize_delta();
    let pop = status(&transaction.pop());
    println!(
        "{id}\t{kind}\t{}\t{snapshot}\t{resize}\t{pop}\t{serialized}\t{edited}\t{auxiliary}",
        status(result),
    );
}

fn account_case(fields: &[&str]) {
    assert_eq!(fields.len(), 11);
    let transaction = context(
        fields[2].parse().unwrap(),
        fields[3] == "1",
        fields[4] == "1",
        fields[5].parse().unwrap(),
        bytes(fields[6]),
        fields[7] == "1",
        fields[8].parse().unwrap(),
        1,
        false,
    );
    let value: u64 = fields[9].parse().unwrap();
    let result = {
        let instruction = transaction.get_current_instruction_context().unwrap();
        let index = if fields[1] == "missing_account" { 2 } else { 0 };
        match instruction.try_borrow_instruction_account(index) {
            Err(error) => Err(error),
            Ok(mut account) => match fields[1] {
                "read_fields" => {
                    assert_eq!(*account.get_key(), key(10));
                    assert_eq!(account.is_signer(), fields[4] == "1");
                    assert_eq!(account.is_writable(), fields[3] == "1");
                    Ok(())
                }
                "set_lamports" => account.set_lamports(value),
                "checked_add" => account.checked_add_lamports(value),
                "checked_sub" => account.checked_sub_lamports(value),
                "set_data" => account.set_data_from_slice(&bytes(fields[10])),
                "set_length" => account.set_data_length(value as usize),
                "set_owner" => account.set_owner(key(value).as_ref()),
                "set_executable" => account.set_executable(value != 0),
                "can_data" => account.can_data_be_changed(),
                "can_resize" => account.can_data_be_resized(value as usize),
                operation => panic!("unknown account operation: {operation}"),
            },
        }
    };
    emit(fields[0], "account", &result, transaction, "-", "-");
}

fn serialization_case(fields: &[&str]) {
    assert_eq!(fields.len(), 11);
    let transaction = context(
        fields[3].parse().unwrap(),
        fields[4] == "1",
        fields[5] == "1",
        fields[6].parse().unwrap(),
        bytes(fields[7]),
        fields[8] == "1",
        fields[9].parse().unwrap(),
        fields[2].parse().unwrap(),
        fields[1] == "v0",
    );
    let (result, before, after) = {
        let instruction = transaction.get_current_instruction_context().unwrap();
        match serialize_parameters(&instruction, false, false, false) {
            Err(error) => (Err(error), "-".to_owned(), "-".to_owned()),
            Ok((mut buffer, _regions, metadata, _instruction_data_offset)) => {
                let before = hex(buffer.as_slice());
                if fields[10] != "-" {
                    for edit in fields[10].split(';') {
                        let (offset, replacement) = edit.split_once(':').unwrap();
                        let offset: usize = offset.parse().unwrap();
                        let replacement = bytes(replacement);
                        buffer.as_slice_mut()[offset..offset + replacement.len()]
                            .copy_from_slice(&replacement);
                    }
                }
                let after = hex(buffer.as_slice());
                let result = deserialize_parameters(
                    &instruction,
                    false,
                    false,
                    buffer.as_slice(),
                    &metadata,
                );
                (result, before, after)
            }
        }
    };
    emit(fields[0], "serialization", &result, transaction, &before, &after);
}

fn native_borrow_observations() {
    let transaction = context(20, true, true, 1_000_000, vec![9], false, 7, 1, false);
    let instruction = transaction.get_current_instruction_context().unwrap();
    let held = instruction.try_borrow_instruction_account(0).unwrap();
    let mutable_conflict = status(&instruction.try_borrow_instruction_account(0));
    let shared_conflict = status(&transaction.accounts().try_borrow(0));
    assert_eq!(mutable_conflict, "AccountBorrowFailed");
    assert_eq!(shared_conflict, "AccountBorrowFailed");
    drop(held);
    let released = status(&instruction.try_borrow_instruction_account(0));
    assert_eq!(released, "ok");
    eprintln!("native_only\tborrow_mut_mut\t{mutable_conflict}");
    eprintln!("native_only\tborrow_mut_shared\t{shared_conflict}");
    eprintln!("native_only\tborrow_after_drop\t{released}");

    let address = key(10);
    let owner = key(20);
    let mut lamports = 1_000_000;
    let mut data = [9];
    let info = solana_account_info::AccountInfo::new(
        &address, true, true, &mut lamports, &mut data, &owner, false,
    );
    let alias = info.clone();
    let held = info.try_borrow_mut_data().unwrap();
    let conflict = alias.try_borrow_data().unwrap_err();
    assert_eq!(format!("{conflict:?}"), "AccountBorrowFailed");
    drop(held);
    assert_eq!(&**alias.try_borrow_data().unwrap(), &[9]);
    eprintln!("native_only\tsdk_account_info_alias_borrow\t{conflict:?}");
}

fn for_rows(path: &Path, apply: fn(&[&str])) {
    let text = fs::read_to_string(path).unwrap();
    for line in text.lines() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        apply(&line.split('\t').collect::<Vec<_>>());
    }
}

fn main() {
    let root = env::args().nth(1).expect("fixture directory argument");
    let root = Path::new(&root);
    for_rows(&root.join("accounts.tsv"), account_case);
    for_rows(&root.join("serialization.tsv"), serialization_case);
    for_rows(&root.join("cpi.tsv"), cpi_cases::run_case);
    native_borrow_observations();
}
