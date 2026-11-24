//! Real MaybeNull<Address> calls through the pinned Pinocchio reexport.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use pinocchio::Address;
use solana_nullable::MaybeNull;

fn values() -> Vec<[u8; 32]> {
    let mut values = vec![[0; 32], [255; 32]];
    for offset in 0..32 {
        let mut value = [0; 32];
        value[offset] = 1;
        values.push(value);
    }
    values
}

fn nullable() {
    let mut corpus = Corpus::new(
        "nullable_address_2_6_1",
        &[
            ("solana-nullable", "1.3.0"),
            ("solana-address", "2.6.1"),
            ("pinocchio", "0.10.2"),
        ],
    );
    for (index, bytes) in values().into_iter().enumerate() {
        let address = Address::new_from_array(bytes);
        let value = MaybeNull::from(address).get();
        corpus.push(Record {
            id: format!("get/{index}"),
            function: "solana_nullable::maybe_null::MaybeNull::<T>::get",
            generics: vec![("T", "solana-address-2.6.1::Address".into())],
            layout: None,
            state: Json::Null,
            args: Json::obj([("key", rec::bytes(&bytes))]),
            outcome: rec::returned(
                rec::option(&value, |key| rec::bytes(&key.to_bytes())),
                Json::Null,
            ),
            observed: None,
        });
    }
    corpus
        .write(&rec::out_dir())
        .expect("write nullable Address corpus");
}

use solana_program_error::ProgramError as E;

fn push(c: &mut Corpus, id: String, function: &'static str, args: Json, result: Json) {
    c.push(Record {
        id,
        function,
        generics: vec![],
        layout: None,
        state: Json::Null,
        args,
        outcome: rec::returned(result, Json::Null),
        observed: None,
    });
}
fn error_json(e: &E) -> Json {
    format!("{e:?}").into()
}
fn errors() {
    let mut c = Corpus::new(
        "error_nullable_program_error_3_0_1",
        &[("solana-program-error", "3.0.1")],
    );
    let mut values = vec![0, 1, u32::MAX as u64, u64::MAX, 1u64 << 63, 27u64 << 32];
    for tag in 1u64..=26 {
        values.push(tag << 32);
        values.push((tag << 32) | 7);
    }
    for (i, status) in values.into_iter().enumerate() {
        let value = E::from(status);
        push(
            &mut c,
            format!("from_u64/{i}"),
            "<solana_program_error::ProgramError as core::convert::From<u64>>::from",
            Json::obj([("status", status.into())]),
            error_json(&value),
        );
    }
    let mut errors = vec![
        E::Custom(0),
        E::Custom(1),
        E::Custom(u32::MAX),
        E::InvalidArgument,
        E::InvalidInstructionData,
        E::InvalidAccountData,
        E::AccountDataTooSmall,
        E::InsufficientFunds,
        E::IncorrectProgramId,
        E::MissingRequiredSignature,
        E::AccountAlreadyInitialized,
        E::UninitializedAccount,
        E::NotEnoughAccountKeys,
        E::AccountBorrowFailed,
        E::MaxSeedLengthExceeded,
        E::InvalidSeeds,
        E::BorshIoError,
        E::AccountNotRentExempt,
        E::UnsupportedSysvar,
        E::IllegalOwner,
        E::MaxAccountsDataAllocationsExceeded,
        E::InvalidRealloc,
        E::MaxInstructionTraceLengthExceeded,
        E::BuiltinProgramsMustConsumeComputeUnits,
        E::InvalidAccountOwner,
        E::ArithmeticOverflow,
        E::Immutable,
        E::IncorrectAuthority,
    ];
    for (i, error) in errors.drain(..).enumerate() {
        let args = Json::obj([("error", error_json(&error))]);
        let status = u64::from(error);
        push(&mut c,format!("into_u64/{i}"),"solana_program_error::<impl core::convert::From<solana_program_error::ProgramError> for u64>::from",args,status.into());
    }
    c.write(&rec::out_dir()).expect("write error corpus");
}

fn main() {
    rec::init();
    nullable();
    errors();
}
