//! pyth-solana-receiver-sdk 2.0.0 from crates.io
//! `PriceUpdateV2::get_price_no_older_than_with_custom_verification_level`.
//!
//! The getter only reads its arguments; the state is `()`. Cases cover each check in source
//! order (verification level, feed id, the unwrapped `u64 -> i64` age conversion, the saturating
//! inclusive freshness comparison) and the orders in which their failures win.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use pyth_solana_receiver_sdk::error::GetPriceError;
use pyth_solana_receiver_sdk::price_update::{Price, PriceFeedMessage, PriceUpdateV2, VerificationLevel};
use solana_clock::Clock;

const FUNCTION: &str =
    "pyth_solana_receiver_sdk::price_update::PriceUpdateV2::get_price_no_older_than_with_custom_verification_level";

fn level(v: &VerificationLevel) -> Json {
    match v {
        VerificationLevel::Partial { num_signatures } => Json::obj([
            ("variant", "Partial".into()),
            ("fields", Json::obj([("num_signatures", (*num_signatures).into())])),
        ]),
        VerificationLevel::Full => rec::variant("Full", vec![]),
    }
}

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

fn update(u: &PriceUpdateV2) -> Json {
    Json::obj([
        ("write_authority", rec::bytes(u.write_authority.as_ref())),
        ("verification_level", level(&u.verification_level)),
        ("price_message", message(&u.price_message)),
        ("posted_slot", u.posted_slot.into()),
    ])
}

fn clock(c: &Clock) -> Json {
    Json::obj([
        ("slot", c.slot.into()),
        ("epoch_start_timestamp", c.epoch_start_timestamp.into()),
        ("epoch", c.epoch.into()),
        ("leader_schedule_epoch", c.leader_schedule_epoch.into()),
        ("unix_timestamp", c.unix_timestamp.into()),
    ])
}

fn price(p: &Price) -> Json {
    Json::obj([
        ("price", p.price.into()),
        ("conf", p.conf.into()),
        ("exponent", p.exponent.into()),
        ("publish_time", p.publish_time.into()),
    ])
}

fn error(e: &GetPriceError) -> Json {
    Json::from(match e {
        GetPriceError::PriceTooOld => "PriceTooOld",
        GetPriceError::InvalidWindowSize => "InvalidWindowSize",
        GetPriceError::MismatchedFeedId => "MismatchedFeedId",
        GetPriceError::InsufficientVerificationLevel => "InsufficientVerificationLevel",
        GetPriceError::FeedIdMustBe32Bytes => "FeedIdMustBe32Bytes",
        GetPriceError::FeedIdNonHexCharacter => "FeedIdNonHexCharacter",
    })
}

const FEED: [u8; 32] = [0x40; 32];
const OTHER_FEED: [u8; 32] = [0x41; 32];

fn make_update(level: VerificationLevel, publish_time: i64) -> PriceUpdateV2 {
    PriceUpdateV2 {
        write_authority: [0x20; 32].into(),
        verification_level: level,
        price_message: PriceFeedMessage {
            feed_id: FEED,
            price: -12_345_678,
            conf: 0x0102_0304_0506_0708,
            exponent: -8,
            publish_time,
            prev_publish_time: publish_time.wrapping_sub(1),
            ema_price: 12_345_678,
            ema_conf: u64::MAX,
        },
        posted_slot: 300_000_000,
    }
}

fn make_clock(unix_timestamp: i64) -> Clock {
    Clock {
        slot: 400_000_000,
        epoch_start_timestamp: -5,
        epoch: 900,
        leader_schedule_epoch: 901,
        unix_timestamp,
    }
}

pub fn record(c: &mut Corpus) {
    use VerificationLevel::{Full, Partial};
    let p = |n: u8| Partial { num_signatures: n };
    let t0: i64 = 1_730_000_000;
    let huge = 1u64 << 63;
    // (label, update level, required level, feed, maximum_age, publish_time, clock time)
    let cases: Vec<(&str, VerificationLevel, VerificationLevel, [u8; 32], u64, i64, i64)> = vec![
        ("full_vs_full", Full, Full, FEED, 60, t0, t0 + 30),
        ("full_vs_partial255", Full, p(255), FEED, 60, t0, t0 + 30),
        ("partial5_vs_partial5", p(5), p(5), FEED, 60, t0, t0 + 30),
        ("partial5_vs_partial0", p(5), p(0), FEED, 60, t0, t0 + 30),
        ("partial5_vs_partial6", p(5), p(6), FEED, 60, t0, t0 + 30),
        ("partial255_vs_full", p(255), Full, FEED, 60, t0, t0 + 30),
        ("partial0_vs_partial0", p(0), p(0), FEED, 60, t0, t0 + 30),
        ("feed_mismatch", Full, Full, OTHER_FEED, 60, t0, t0 + 30),
        ("level_before_feed", p(1), p(2), OTHER_FEED, 60, t0, t0 + 30),
        ("age_2pow63_panics", Full, Full, FEED, huge, t0, t0 + 30),
        ("age_max_panics", p(3), p(3), FEED, u64::MAX, t0, t0),
        ("age_i64max_saturates", Full, Full, FEED, huge - 1, t0, i64::MAX),
        ("level_before_age", p(1), p(2), FEED, u64::MAX, t0, t0),
        ("feed_before_age", Full, Full, OTHER_FEED, u64::MAX, t0, t0),
        ("boundary_equal", Full, Full, FEED, 60, t0, t0 + 60),
        ("one_second_too_old", Full, Full, FEED, 60, t0, t0 + 61),
        ("age0_same_second", Full, Full, FEED, 0, t0, t0),
        ("age0_one_later", Full, Full, FEED, 0, t0, t0 + 1),
        ("future_price", Full, Full, FEED, 0, t0, t0 - 100),
        ("publish_near_max_saturates", Full, Full, FEED, 10, i64::MAX - 1, i64::MAX),
        ("negative_times", Full, Full, FEED, 5, -100, -95),
        ("negative_times_too_old", Full, Full, FEED, 5, -100, -94),
        ("min_publish", Full, Full, FEED, 7, i64::MIN, i64::MIN + 7),
    ];
    for (label, have, need, feed, age, publish, now) in cases {
        let u = make_update(have, publish);
        let clk = make_clock(now);
        let args = Json::obj([
            ("update", update(&u)),
            ("clock", clock(&clk)),
            ("maximum_age", age.into()),
            ("feed_id", rec::bytes(&feed)),
            ("verification_level", level(&need)),
        ]);
        let outcome = match rec::catch(|| u.get_price_no_older_than_with_custom_verification_level(&clk, age, &feed, need)) {
            Ok(Ok(v)) => rec::returned(rec::ok(price(&v)), Json::Null),
            Ok(Err(e)) => rec::returned(rec::err(error(&e)), Json::Null),
            Err(reason) => rec::unwound(reason, Json::Null),
        };
        c.push(Record {
            id: label.to_string(),
            function: FUNCTION,
            generics: vec![],
            layout: None,
            state: Json::Null,
            args,
            outcome,
            observed: None,
        });
    }
}
