use conformance_recorder::{self as rec, Corpus, Json, Record};

fn main() {
    rec::init();
    let mut corpus = Corpus::new(CORPUS, &[("solana-hash", VERSION)]);
    let cases = [
        [0; 32],
        [255; 32],
        core::array::from_fn(|i| i as u8),
        core::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(200)),
        core::array::from_fn(|i| if i == 0 { 1 } else { 0 }),
        core::array::from_fn(|i| if i == 31 { 128 } else { 0 }),
    ];
    for (i, bytes) in cases.into_iter().enumerate() {
        let hash = solana_hash::Hash::new_from_array(bytes);
        let outcome = match rec::catch(|| hash.to_bytes()) {
            Ok(value) => rec::returned(rec::bytes(&value), Json::Null),
            Err(reason) => rec::unwound(reason, Json::Null),
        };
        corpus.push(Record {
            id: format!("to_bytes/{i}"),
            function: "solana_hash::Hash::to_bytes",
            generics: vec![], layout: None, state: Json::Null,
            args: Json::obj([("hash", rec::bytes(&bytes))]),
            outcome, observed: None,
        });
    }
    corpus.write(&rec::out_dir()).expect("write corpus");
}
