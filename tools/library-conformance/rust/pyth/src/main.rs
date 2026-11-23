//! Records pyth-solana-receiver-sdk 2.0.0 `PriceUpdateV2` Borsh decoding and
//! the pythnet-sdk 3.0.0 `PriceFeedMessage` decoder it calls, from crates.io
//! with dependencies pinned in Cargo.lock (borsh 1.6.1 through anchor-lang 1.0.2).
//!
//! The caller checks the 8-byte Anchor discriminator before calling
//! `BorshDeserialize::deserialize::<PriceUpdateV2>(&mut &data[8..])`; the
//! inputs here are such `data[8..]` slices. The discriminator check is client
//! code and is not recorded.

#[allow(dead_code)]
#[path = "../../common/borsh_de.rs"]
mod borsh_de;

use borsh_de::{decode_cases, dedup, pattern, Entries, Ty, NO_TRY_FROM_SLICE};
use conformance_recorder::{self as rec, Corpus, Json};
use pyth_solana_receiver_sdk::price_update::{PriceFeedMessage, PriceUpdateV2, VerificationLevel};

const PRICE_UPDATE: &str = "pyth_solana_receiver_sdk::price_update::PriceUpdateV2";
const PRICE_FEED: &str = "pythnet_sdk::messages::PriceFeedMessage";

fn message(m: &PriceFeedMessage) -> Json {
    Json::obj([
        ("feed_id", rec::bytes(&m.feed_id)),
        ("price", m.price.into()),
        ("conf", m.conf.into()),
        ("exponent", m.exponent.into()),
        ("publish_time", m.publish_time.into()),
        ("prev_publish_time", m.prev_publish_time.into()),
        ("ema_price", m.ema_price.into()),
        ("ema_conf", m.ema_conf.into()),
    ])
}

fn level(v: &VerificationLevel) -> Json {
    match v {
        VerificationLevel::Partial { num_signatures } => Json::obj([
            ("variant", "Partial".into()),
            ("fields", Json::obj([("num_signatures", (*num_signatures).into())])),
        ]),
        VerificationLevel::Full => rec::variant("Full", vec![]),
    }
}

fn update(u: &PriceUpdateV2) -> Json {
    Json::obj([
        ("write_authority", rec::bytes(u.write_authority.as_ref())),
        ("verification_level", level(&u.verification_level)),
        ("price_message", message(&u.price_message)),
        ("posted_slot", u.posted_slot.into()),
    ])
}

/// Field chunks of a `PriceFeedMessage` encoding.
fn message_chunks(price: i64, exponent: i32) -> Vec<Vec<u8>> {
    vec![
        pattern(32, 0x40),
        price.to_le_bytes().to_vec(),
        0x0102_0304_0506_0708u64.to_le_bytes().to_vec(),
        exponent.to_le_bytes().to_vec(),
        1_730_000_000i64.to_le_bytes().to_vec(),
        1_729_999_999i64.to_le_bytes().to_vec(),
        (-price).to_le_bytes().to_vec(),
        u64::MAX.to_le_bytes().to_vec(),
    ]
}

/// Field chunks of a `PriceUpdateV2` encoding; `level` is the encoded
/// verification level (tag and fields).
fn update_chunks(level: Vec<u8>, price: i64, exponent: i32) -> Vec<Vec<u8>> {
    let mut chunks = vec![pattern(32, 0x20), level];
    chunks.extend(message_chunks(price, exponent));
    chunks.push(300_000_000u64.to_le_bytes().to_vec());
    chunks
}

fn boundaries(chunks: &[Vec<u8>]) -> Vec<usize> {
    let mut out = vec![];
    let mut at = 0;
    for c in &chunks[..chunks.len() - 1] {
        at += c.len();
        out.push(at);
    }
    out
}

fn truncations(label: &str, chunks: &[Vec<u8>], every: bool) -> Vec<(String, Vec<u8>)> {
    let bytes = chunks.concat();
    let cuts: Vec<usize> = if every { (0..bytes.len()).collect() } else {
        // Each field boundary (the field is missing) and one byte into each
        // field (the field is short).
        let mut cuts: Vec<usize> = std::iter::once(0)
            .chain(boundaries(chunks))
            .flat_map(|b| [b, b + 1])
            .chain([bytes.len() - 1])
            .filter(|n| *n < bytes.len())
            .collect();
        cuts.sort();
        cuts.dedup();
        cuts
    };
    cuts.into_iter().map(|n| (format!("{label}/truncated{n}"), bytes[..n].to_vec())).collect()
}

fn price_update_corpus() -> Corpus {
    let mut c = Corpus::new(
        "pyth_solana_receiver_sdk_2_0_0",
        &[("pyth-solana-receiver-sdk", "2.0.0"), ("pythnet-sdk", "3.0.0"), ("borsh", "1.6.1")],
    );
    let p = "pyth_solana_receiver_sdk_2_0_0";
    let ty = Ty::<PriceUpdateV2> {
        name: PRICE_UPDATE.to_string(),
        reader_fn: "<pyth_solana_receiver_sdk::price_update::PriceUpdateV2 as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![],
        enc: update,
    };
    let full = update_chunks(vec![1], -12_345_678, -8);
    let partial = update_chunks(vec![0, 13], 98_765_432_100, -5);
    let mut inputs: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("full".into(), full.concat()),
        ("partial13".into(), partial.concat()),
        ("partial0".into(), update_chunks(vec![0, 0], 0, 0).concat()),
        ("partial255".into(), update_chunks(vec![0, 255], i64::MAX, i32::MAX).concat()),
        ("full/min_values".into(), update_chunks(vec![1], i64::MIN + 1, i32::MIN).concat()),
        // A 134-byte account minus the discriminator: `Full` leaves one byte.
        ("full+account_padding".into(), [full.concat(), vec![0]].concat()),
        ("partial13+trailing".into(), rec::with_trailing(&partial.concat())),
    ];
    for tag in [2u8, 3, 0x7f, 0xff] {
        inputs.push((format!("level_tag{tag:02x}"), update_chunks(vec![tag, 0], 1, 1).concat()));
    }
    inputs.extend(truncations("partial13", &partial, false));
    inputs.extend(truncations("full", &full, false));
    decode_cases(&mut c, p, &ty, NO_TRY_FROM_SLICE, &dedup(inputs));

    // The derived `VerificationLevel` decoder: every tag, each followed by one
    // payload byte; the empty input; a `Partial` tag without its count.
    let level_ty = Ty::<VerificationLevel> {
        name: "pyth_solana_receiver_sdk::price_update::VerificationLevel".to_string(),
        reader_fn: "<pyth_solana_receiver_sdk::price_update::VerificationLevel as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![],
        enc: level,
    };
    let mut levels: Vec<(String, Vec<u8>)> = (0..=255u8).map(|t| (format!("tag{t:02x}+05"), vec![t, 5])).collect();
    levels.push(("empty".into(), vec![]));
    levels.push(("partial/truncated1".into(), vec![0]));
    levels.push(("full+trailing".into(), rec::with_trailing(&[1])));
    let only_reader = Entries { deserialize: false, deserialize_reader: true, try_from_slice: false };
    decode_cases(&mut c, p, &level_ty, only_reader, &levels);
    c
}

fn price_feed_corpus() -> Corpus {
    let mut c = Corpus::new("pythnet_sdk_3_0_0", &[("pythnet-sdk", "3.0.0"), ("borsh", "1.6.1")]);
    let p = "pythnet_sdk_3_0_0";
    let ty = Ty::<PriceFeedMessage> {
        name: PRICE_FEED.to_string(),
        reader_fn: "<pythnet_sdk::messages::PriceFeedMessage as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![],
        enc: message,
    };
    let m = message_chunks(-12_345_678, -8);
    let mut inputs: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("message".into(), m.concat()),
        ("message/extremes".into(), message_chunks(i64::MAX, i32::MIN).concat()),
        ("message+trailing".into(), rec::with_trailing(&m.concat())),
    ];
    inputs.extend(truncations("message", &m, false));
    decode_cases(&mut c, p, &ty, NO_TRY_FROM_SLICE, &dedup(inputs));
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    for corpus in [price_update_corpus(), price_feed_corpus()] {
        corpus.write(&out).expect("write corpus");
    }
}
