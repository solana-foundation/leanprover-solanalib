//! solana-stake-interface 3.1.0: `StakeStateV2` Borsh decoding (its manual
//! `BorshDeserialize` impl over borsh 1.6.1).

use crate::borsh_de::{self, decode_cases, Ty, NO_TRY_FROM_SLICE};
use conformance_recorder::{self as rec, Corpus, Json};
use solana_stake_interface::stake_flags::StakeFlags;
use solana_stake_interface::state::{Authorized, Delegation, Lockup, Meta, Stake, StakeStateV2};

pub const TYPE: &str = "solana_stake_interface::state::StakeStateV2";

fn address(a: &solana_address::Address) -> Json {
    rec::bytes(a.as_ref())
}

fn flags(f: &StakeFlags) -> Json {
    // `StakeFlags.bits` is private; its derived Borsh encoding is that byte.
    let bits = borsh::to_vec(f).expect("StakeFlags encodes");
    Json::obj([("bits", Json::from(bits[0]))])
}

#[allow(deprecated)]
fn meta(m: &Meta) -> Json {
    Json::obj([
        ("rent_exempt_reserve", m.rent_exempt_reserve.into()),
        ("authorized", authorized(&m.authorized)),
        ("lockup", lockup(&m.lockup)),
    ])
}

fn authorized(a: &Authorized) -> Json {
    Json::obj([("staker", address(&a.staker)), ("withdrawer", address(&a.withdrawer))])
}

fn lockup(l: &Lockup) -> Json {
    Json::obj([
        ("unix_timestamp", l.unix_timestamp.into()),
        ("epoch", l.epoch.into()),
        ("custodian", address(&l.custodian)),
    ])
}

#[allow(deprecated)]
fn delegation(d: &Delegation) -> Json {
    Json::obj([
        ("voter_pubkey", address(&d.voter_pubkey)),
        ("stake", d.stake.into()),
        ("activation_epoch", d.activation_epoch.into()),
        ("deactivation_epoch", d.deactivation_epoch.into()),
        ("warmup_cooldown_rate", rec::f64_bits(d.warmup_cooldown_rate)),
    ])
}

fn stake(s: &Stake) -> Json {
    Json::obj([("delegation", delegation(&s.delegation)), ("credits_observed", s.credits_observed.into())])
}

pub fn encode(v: &StakeStateV2) -> Json {
    match v {
        StakeStateV2::Uninitialized => rec::variant("Uninitialized", vec![]),
        StakeStateV2::Initialized(m) => rec::variant("Initialized", vec![meta(m)]),
        StakeStateV2::Stake(m, s, f) => rec::variant("Stake", vec![meta(m), stake(s), flags(f)]),
        StakeStateV2::RewardsPool => rec::variant("RewardsPool", vec![]),
    }
}

/// Hand-built wire encodings, as field chunks so that field boundaries are
/// known. Independent of the serializer under test.
struct Wire(Vec<Vec<u8>>);

impl Wire {
    fn bytes(&self) -> Vec<u8> {
        self.0.concat()
    }

    /// Offsets of every field boundary, including 0 and excluding the end.
    fn boundaries(&self) -> Vec<usize> {
        let mut out = vec![0];
        let mut at = 0;
        for chunk in &self.0[..self.0.len() - 1] {
            at += chunk.len();
            out.push(at);
        }
        out
    }
}

fn meta_chunks(seed: u8) -> Vec<Vec<u8>> {
    vec![
        (1_000_000_000u64 + seed as u64).to_le_bytes().to_vec(), // rent_exempt_reserve
        borsh_de::pattern(32, seed),                             // staker
        borsh_de::pattern(32, seed.wrapping_add(1)),             // withdrawer
        (-1_700_000_000i64).to_le_bytes().to_vec(),              // unix_timestamp
        u64::MAX.to_le_bytes().to_vec(),                         // epoch
        borsh_de::pattern(32, seed.wrapping_add(2)),             // custodian
    ]
}

fn stake_chunks(rate_bits: u64) -> Vec<Vec<u8>> {
    vec![
        borsh_de::pattern(32, 0x90),                       // voter_pubkey
        123_456_789u64.to_le_bytes().to_vec(),             // stake
        7u64.to_le_bytes().to_vec(),                       // activation_epoch
        u64::MAX.to_le_bytes().to_vec(),                   // deactivation_epoch
        rate_bits.to_le_bytes().to_vec(),                  // warmup_cooldown_rate
        42u64.to_le_bytes().to_vec(),                      // credits_observed
    ]
}

fn wire_stake(rate_bits: u64, flag_bits: u8) -> Wire {
    let mut chunks = vec![2u32.to_le_bytes().to_vec()];
    chunks.extend(meta_chunks(0x10));
    chunks.extend(stake_chunks(rate_bits));
    chunks.push(vec![flag_bits]);
    Wire(chunks)
}

fn wire_initialized() -> Wire {
    let mut chunks = vec![1u32.to_le_bytes().to_vec()];
    chunks.extend(meta_chunks(0x20));
    Wire(chunks)
}

pub fn record(corpus: &mut Corpus, prefix: &str) {
    let ty = Ty::<StakeStateV2> {
        name: TYPE.to_string(),
        reader_fn: "<solana_stake_interface::state::StakeStateV2 as borsh::de::BorshDeserialize>::deserialize_reader",
        reader_generics: vec![],
        enc: encode,
    };
    let rate = 0x3fd0_0000_0000_0000u64; // 0.25
    let stake = wire_stake(rate, 1);
    let init = wire_initialized();

    let mut whole: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("uninitialized".into(), 0u32.to_le_bytes().to_vec()),
        ("uninitialized+account_padding".into(), [0u32.to_le_bytes().to_vec(), vec![0; 196]].concat()),
        ("rewards_pool".into(), 3u32.to_le_bytes().to_vec()),
        ("initialized".into(), init.bytes()),
        ("stake".into(), stake.bytes()),
        ("stake+account_padding".into(), [stake.bytes(), vec![0; 3]].concat()),
        ("stake/flags_ff".into(), wire_stake(rate, 0xff).bytes()),
        ("tag4".into(), 4u32.to_le_bytes().to_vec()),
        ("tag5".into(), 5u32.to_le_bytes().to_vec()),
        ("tag_big_endian_1+meta".into(), [1u32.to_be_bytes().to_vec(), init.bytes()[4..].to_vec()].concat()),
        ("tag_big_endian_2+stake".into(), [2u32.to_be_bytes().to_vec(), stake.bytes()[4..].to_vec()].concat()),
        ("tag256".into(), 0x100u32.to_le_bytes().to_vec()),
        ("tag_u32max+meta".into(), [u32::MAX.to_le_bytes().to_vec(), init.bytes()[4..].to_vec()].concat()),
        ("uninitialized+trailing".into(), rec::with_trailing(&0u32.to_le_bytes())),
        ("stake+trailing".into(), rec::with_trailing(&stake.bytes())),
    ];
    for (label, bits) in rec::F64_PATTERNS {
        whole.push((format!("stake/rate_{label}"), wire_stake(*bits, 0).bytes()));
    }
    for n in 1..4 {
        whole.push((format!("tag/truncated{n}"), 2u32.to_le_bytes()[..n].to_vec()));
    }
    // Truncation classes: a cut at each field boundary (the field is missing)
    // and one byte into each field (the field is short).
    for (label, wire) in [("stake", &stake), ("initialized", &init)] {
        let bytes = wire.bytes();
        for b in wire.boundaries() {
            for cut in [b, b + 1] {
                if cut > 0 && cut < bytes.len() {
                    whole.push((format!("{label}/truncated{cut}"), bytes[..cut].to_vec()));
                }
            }
        }
    }
    decode_cases(corpus, prefix, &ty, NO_TRY_FROM_SLICE, &borsh_de::dedup(whole));
}
