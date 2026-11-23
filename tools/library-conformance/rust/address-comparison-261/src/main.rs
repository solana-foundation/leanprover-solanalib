use conformance_recorder::{self as rec, Corpus, Json, Record};
use solana_address::Address;

fn main() {
    rec::init();
    let mut corpus = Corpus::new("address_comparison_261", &[("solana-address", "2.6.1")]);
    let pattern: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(53).wrapping_add(17));
    for (i, left) in [[0u8; 32], [255u8; 32], pattern].iter().enumerate() {
        let mut different = *left;
        let offset = if i == 0 { 0 } else { 31 };
        different[offset] = different[offset].wrapping_add(1);
        for (j, right) in [*left, different].iter().enumerate() {
            let left_key = Address::new_from_array(*left);
            let right_key = Address::new_from_array(*right);
            let result = left_key.cmp(&right_key);
            corpus.push(Record {
                id: format!("cmp/{i}/{j}"),
                function: "<solana_address::Address as core::cmp::Ord>::cmp",
                generics: vec![],
                layout: None,
                state: Json::Null,
                args: Json::obj([("self", rec::bytes(left)), ("other", rec::bytes(right))]),
                outcome: rec::returned(format!("{result:?}").into(), Json::Null),
                observed: None,
            });
        }
    }
    corpus.write(&rec::out_dir()).expect("write comparison corpus");
}
