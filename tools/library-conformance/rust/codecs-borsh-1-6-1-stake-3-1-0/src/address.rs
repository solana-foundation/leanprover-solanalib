//! solana-address 2.6.0: `Address` Borsh encoding and decoding (derived over
//! borsh 1.6.1).

use crate::borsh_de::{self, decode_cases, Ty, NO_TRY_FROM_SLICE};
use crate::ser::{ser_cases, SerTy};
use conformance_recorder::{self as rec, Corpus};
use solana_address::Address;

pub const TYPE: &str = "solana_address::Address";

fn enc(a: &Address) -> conformance_recorder::Json {
    rec::bytes(a.as_ref())
}

pub fn record(corpus: &mut Corpus, prefix: &str) {
    let ser = SerTy::<Address> {
        name: TYPE.to_string(),
        function: "<solana_address::Address as borsh::ser::BorshSerialize>::serialize",
        generics: vec![],
        enc,
    };
    let pattern: [u8; 32] = borsh_de::pattern(32, 3).try_into().unwrap();
    ser_cases(corpus, prefix, &ser, &[
        ("zero".to_string(), Address::new_from_array([0; 32])),
        ("ones".to_string(), Address::new_from_array([0xff; 32])),
        ("pattern".to_string(), Address::new_from_array(pattern)),
    ]);

    let ty = Ty::<Address> {
        name: TYPE.to_string(),
        reader_fn: "<solana_address::Address as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![],
        enc,
    };
    let full = pattern.to_vec();
    let mut inputs: Vec<(String, Vec<u8>)> = vec![
        ("zero".into(), vec![0; 32]),
        ("ones".into(), vec![0xff; 32]),
        ("pattern".into(), full.clone()),
        ("pattern+trailing".into(), rec::with_trailing(&full)),
    ];
    for n in [0usize, 1, 16, 31] {
        inputs.push((format!("pattern/truncated{n}"), full[..n].to_vec()));
    }
    decode_cases(corpus, prefix, &ty, NO_TRY_FROM_SLICE, &inputs);
}
