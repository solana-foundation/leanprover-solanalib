//! Actual SDK calls with the exact reviewed key provider.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use option_v2::COption as V2;
use solana_pubkey::Pubkey;
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

fn pubkeys() {
    let mut c = Corpus::new("sdk_values_pubkey_2_4_0",
        &[("solana-program-option", "2.2.1"), ("solana-pubkey", "2.4.0")]);
    let query = Pubkey::new_from_array([0; 32]);
    for (i, bytes) in keys().into_iter().enumerate() {
        let key = Pubkey::new_from_array(bytes);
        for present in [false, true] {
            let value = if present { V2::Some(key) } else { V2::None };
            let borrowed = value.as_ref();
            let result = match borrowed {
                V2::None => Json::Null,
                V2::Some(actual) => {
                    let expected = match &value { V2::Some(key) => key, V2::None => unreachable!() };
                    some(Json::obj([
                        ("parent", if std::ptr::eq(actual, expected) { 0_u64 } else { 1_u64 }.into()),
                        ("key", rec::bytes(&actual.to_bytes())),
                    ]))
                }
            };
            push(&mut c, format!("as_ref/{i}_{present}"),
                "solana_program_option::COption::<T>::as_ref",
                vec![("T", "solana-pubkey@2.4.0::Pubkey".into())],
                Json::obj([("parent", 0_u64.into()), ("key", rec::bytes(&bytes)),
                           ("present", present.into())]), rec::returned(result, Json::Null));
            push(&mut c, format!("is_none/{i}_{present}"),
                "solana_program_option::COption::<T>::is_none",
                vec![("T", "solana-pubkey@2.4.0::Pubkey".into())],
                Json::obj([("option", if present { some(rec::bytes(&bytes)) } else { Json::Null })]),
                rec::returned(value.is_none().into(), Json::Null));

            // Both payload and captured query are actual shared references.
            let reference = if present { V2::Some(&key) } else { V2::None };
            let right = &query;
            let mapped = reference.map(move |left| left == right);
            let result = match mapped { V2::None => Json::Null, V2::Some(value) => some(value.into()) };
            push(&mut c, format!("map/{i}_{present}"),
                "solana_program_option::COption::<T>::map",
                vec![("T", "&solana-pubkey@2.4.0::Pubkey".into()), ("U", "bool".into()),
                     ("F", "closure(&Pubkey)".into())],
                Json::obj([("option", if present { some(rec::bytes(&bytes)) } else { Json::Null }),
                           ("query", rec::bytes(&query.to_bytes()))]),
                rec::returned(result, Json::Null));
        }
    }
    c.write(&rec::out_dir()).expect("write Pubkey provider corpus");
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
    pubkeys();
}
