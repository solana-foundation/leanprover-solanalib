//! Records the pinned library versions: borsh 1.6.1 serializers and
//! decoders, bytemuck 1.25.0 `try_from_bytes` and `Zeroable::zeroed`,
//! solana-stake-interface 3.1.0 `StakeStateV2` decoding and solana-address
//! 2.6.0 `Address` Borsh encoding and decoding.

#[allow(dead_code)]
#[path = "../../common/borsh_de.rs"]
mod borsh_de;
#[allow(dead_code)]
#[path = "../../common/bytemuck_cases.rs"]
mod bytemuck_cases;
mod address;
mod ser;
mod stake;

use borsh_de::*;
use conformance_recorder::{self as rec, Corpus, Json};

fn borsh_corpus() -> Corpus {
    let mut c = Corpus::new("borsh_1_6_1", &[("borsh", "1.6.1")]);
    let p = "borsh_1_6_1";
    ser::record(&mut c, p);

    const E: Entries = NO_TRY_FROM_SLICE;
    decode_cases(&mut c, p, &u8_ty(), E, &u8_inputs());
    decode_cases(&mut c, p, &bool_ty(), E, &bool_inputs());
    decode_cases(&mut c, p, &u32_ty(), E, &u32_inputs());
    decode_cases(&mut c, p, &i32_ty(), E, &i32_inputs());
    decode_cases(&mut c, p, &u64_ty(), E, &u64_inputs());
    decode_cases(&mut c, p, &i64_ty(), E, &i64_inputs());
    decode_cases(&mut c, p, &f64_ty(), E, &f64_inputs());

    let opt_u8 = option_ty(&u8_ty(), |v| rec::option(v, |x| Json::from(*x)));
    decode_cases(&mut c, p, &opt_u8, E, &option_inputs(&[0x7f]));
    let opt_u64 = option_ty(&u64_ty(), |v| rec::option(v, |x| Json::from(*x)));
    decode_cases(&mut c, p, &opt_u64, E, &option_inputs(&u64::MAX.to_le_bytes()));

    let arr_u8_32 = array_ty::<u8, 32>(&u8_ty(), |v| rec::bytes(v));
    let full = pattern(32, 9);
    let mut a = vec![
        ("zero".to_string(), vec![0; 32]),
        ("pattern".to_string(), full.clone()),
        ("pattern+trailing".to_string(), rec::with_trailing(&full)),
    ];
    for n in [0usize, 1, 16, 31] {
        a.push((format!("pattern/truncated{n}"), full[..n].to_vec()));
    }
    decode_cases(&mut c, p, &arr_u8_32, E, &a);
    array_from_reader_cases::<32>(&mut c, p, &a);
    array_from_reader_cases::<16>(&mut c, p, &a[1..]);
    array_from_reader_cases::<0>(&mut c, p, &[("empty".to_string(), vec![]), ("one".to_string(), vec![1])]);
    let arr_u64_2 = array_ty::<u64, 2>(&u64_ty(), |v| Json::arr(v.iter(), |x| Json::from(*x)));
    let two = [1u64.to_le_bytes(), u64::MAX.to_le_bytes()].concat();
    let mut b = vec![("pair".to_string(), two.clone()), ("pair+trailing".to_string(), rec::with_trailing(&two))];
    for n in [0usize, 3, 8, 12] {
        b.push((format!("pair/truncated{n}"), two[..n].to_vec()));
    }
    decode_cases(&mut c, p, &arr_u64_2, E, &b);
    c
}

fn bytemuck_corpus() -> Corpus {
    let mut c = Corpus::new("bytemuck_1_25_0", &[("bytemuck", "1.25.0")]);
    bytemuck_cases::try_from_bytes_cases(&mut c, "bytemuck_1_25_0");
    bytemuck_cases::zeroed_cases(&mut c, "bytemuck_1_25_0");
    c
}

fn stake_corpus() -> Corpus {
    let mut c = Corpus::new(
        "solana_stake_interface_3_1_0",
        &[("solana-stake-interface", "3.1.0"), ("borsh", "1.6.1")],
    );
    stake::record(&mut c, "solana_stake_interface_3_1_0");
    c
}

fn address_corpus() -> Corpus {
    let mut c = Corpus::new("solana_address_2_6_0", &[("solana-address", "2.6.0"), ("borsh", "1.6.1")]);
    address::record(&mut c, "solana_address_2_6_0");
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    for corpus in [borsh_corpus(), bytemuck_corpus(), stake_corpus(), address_corpus()] {
        corpus.write(&out).expect("write corpus");
    }
}
