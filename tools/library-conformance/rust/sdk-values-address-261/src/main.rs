//! Actual SDK calls with the exact reviewed key provider.
use conformance_recorder::{self as rec, Corpus, Json, Record};
#[path = "../../sdk-values-common/support.rs"]
mod support;
use option_v3::COption as V3;
use solana_address::Address;
fn some(value: Json) -> Json { Json::obj([("some", value)]) }

fn push(c: &mut Corpus, id: String, function: &'static str,
        generics: Vec<(&'static str, String)>, args: Json, outcome: Json) {
    c.push(Record { id, function, generics, layout: None, state: Json::Null,
                   args, outcome, observed: None });
}

fn keys() -> [[u8; 32]; 3] {
    let mut last = [0; 32];
    last[31] = 1;
    [[0; 32], [255; 32], last]
}

fn addresses() {
    let mut c = Corpus::new("sdk_values_address_2_6_1",
        &[("solana-program-option", "3.1.0"), ("solana-address", "2.6.1"),
          ("solana-sdk-ids", "3.1.0")]);
    let values = [V3::None, V3::Some(Address::new_from_array([0; 32])),
                  V3::Some(Address::new_from_array([255; 32])),
                  V3::Some(Address::new_from_array(keys()[2]))];
    let encode = |value: &V3<Address>| match value {
        V3::None => Json::Null,
        V3::Some(key) => some(rec::bytes(&key.to_bytes())),
    };
    for (i, left) in values.iter().enumerate() {
        for (j, right) in values.iter().enumerate() {
            push(&mut c, format!("eq/{i}_{j}"),
                "<solana_program_option::COption<T> as core::cmp::PartialEq>::eq",
                vec![("T", "solana-address@2.6.1::Address".into())],
                Json::obj([("left", encode(left)), ("right", encode(right))]),
                rec::returned((left == right).into(), Json::Null));
        }
        let owned = match left {
            V3::None => V3::None,
            V3::Some(key) => V3::Some(Address::new_from_array(key.to_bytes())),
        };
        let outcome = support::case(|| rec::returned(rec::bytes(&owned.unwrap().to_bytes()), Json::Null));
        push(&mut c, format!("unwrap/{i}"), "solana_program_option::COption::<T>::unwrap",
            vec![("T", "solana-address@2.6.1::Address".into())],
            Json::obj([("option", encode(left))]), outcome);
    }
    for (name, call) in [
        ("solana_sdk_ids::bpf_loader_upgradeable::id", solana_sdk_ids::bpf_loader_upgradeable::id as fn() -> Address),
        ("solana_sdk_ids::ed25519_program::id", solana_sdk_ids::ed25519_program::id),
    ] {
        push(&mut c, name.into(), name, vec![], Json::Null,
            rec::returned(rec::bytes(&call().to_bytes()), Json::Null));
    }
    c.write(&rec::out_dir()).expect("write Address provider corpus");
}

// This driver has no signature-check feature; still observe any injected cfg.
#[allow(unexpected_cfgs)]
fn print_build_config() {
    println!("{}", Json::obj([
        ("scope", "linked-source".into()),
        ("panic", if cfg!(panic = "abort") { "abort" } else { "unwind" }.into()),
        ("debug_assertions", cfg!(debug_assertions).into()),
        ("solana_cfg", cfg!(target_os = "solana").into()),
        ("pointer_width", (std::mem::size_of::<usize>() * 8).into()),
        ("little_endian", cfg!(target_endian = "little").into()),
        ("signature_check_enabled", cfg!(feature = "signature-check").into()),
    ]).to_text());
}

fn main() {
    rec::init();
    if std::env::args().nth(1).as_deref() == Some("--build-config") {
        print_build_config();
        return;
    }
    addresses();
}
