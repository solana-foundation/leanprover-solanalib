use conformance_recorder::{self as rec, Corpus, Json, Record};

fn main() {
    rec::init();
    let mut corpus = Corpus::new(CORPUS, &[("solana-zero-copy", VERSION)]);
    let mut cases = vec![
        [0; 8], [255; 8], 1u64.to_le_bytes(), 256u64.to_le_bytes(),
        (1u64 << 63).to_le_bytes(), (i64::MAX as u64).to_le_bytes(),
        [1, 2, 3, 4, 5, 6, 7, 8],
    ];
    for i in 0..8 {
        let mut bytes = [0; 8];
        bytes[i] = 128 | i as u8;
        cases.push(bytes);
    }
    for (i, bytes) in cases.into_iter().enumerate() {
        let value = solana_zero_copy::unaligned::U64(bytes);
        let outcome = match rec::catch(|| u64::from(value)) {
            Ok(value) => rec::returned(Json::from(value), Json::Null),
            Err(reason) => rec::unwound(reason, Json::Null),
        };
        corpus.push(Record {
            id: format!("into_u64/{i}"),
            function: "solana_zero_copy::unaligned::<impl core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from",
            generics: vec![], layout: None, state: Json::Null,
            args: Json::obj([("value", rec::bytes(&bytes))]),
            outcome, observed: None,
        });
    }
    corpus.write(&rec::out_dir()).expect("write corpus");
}
