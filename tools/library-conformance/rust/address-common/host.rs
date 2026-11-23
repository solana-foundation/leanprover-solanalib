//! solana-address 2.6.x on the plain host branch (no `target_os = "solana"`,
//! feature `curve25519`): `find_program_address` and `is_on_curve` compute
//! with SHA-256 (`sha2`) and Ed25519 decompression (`curve25519-dalek`)
//! instead of syscalls. These runs test the pure observation models
//! `find_program_address_contract` and `is_on_curve_contract`, whose
//! arguments include an explicit `Crypto` (hash and curve functions).
//!
//! The `args.crypto` field of each record is that `Crypto` restricted to the points the
//! models query: `sha256` pairs (input, digest) and `on_curve` pairs (32 bytes,
//! decompresses). The table is computed here with `sha2` and
//! `curve25519-dalek` directly, not through solana-address, along the
//! search order of the canonical PDA derivation (bump 255 down to the first
//! off-curve digest). The Lean side answers a query outside the table with an
//! empty digest that is on the curve, so a table that misses a point the
//! model queries makes the model fail to find an address and the record is
//! rejected, unless the native call failed for the same reason.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use curve25519_dalek::edwards::CompressedEdwardsY;
use sha2::{Digest, Sha256};
use solana_address::Address;

pub const FIND: &str = "solana_address::syscalls::<impl solana_address::Address>::find_program_address";
pub const IS_ON_CURVE: &str = "solana_address::Address::is_on_curve";

const PDA_MARKER: &[u8] = b"ProgramDerivedAddress";
const MAX_SEEDS: usize = 16;
const MAX_SEED_LEN: usize = 32;

fn address(bytes: [u8; 32]) -> Address {
    // SAFETY: `Address` is `#[repr(transparent)]` over `[u8; 32]`.
    unsafe { core::mem::transmute::<[u8; 32], Address>(bytes) }
}

fn bytes_of(a: &Address) -> [u8; 32] {
    // SAFETY: as above.
    unsafe { *(a as *const Address as *const [u8; 32]) }
}

fn on_curve(point: &[u8; 32]) -> bool {
    CompressedEdwardsY(*point).decompress().is_some()
}

#[derive(Default)]
struct Table {
    sha256: Vec<(Vec<u8>, [u8; 32])>,
    on_curve: Vec<([u8; 32], bool)>,
}

impl Table {
    fn json(&self) -> Json {
        Json::obj([
            ("sha256", Json::arr(self.sha256.iter(), |(i, o)| Json::Arr(vec![rec::bytes(i), rec::bytes(o)]))),
            ("on_curve", Json::arr(self.on_curve.iter(), |(p, b)| Json::Arr(vec![rec::bytes(p), (*b).into()]))),
        ])
    }
}

/// The digests and curve answers along the canonical search, and the bump at
/// which it stops (`None` when seed limits make every attempt fail).
fn search_table(seeds: &[Vec<u8>], program_id: &[u8; 32]) -> (Table, Option<u8>) {
    let mut table = Table::default();
    if seeds.len() + 1 > MAX_SEEDS || seeds.iter().any(|s| s.len() > MAX_SEED_LEN) {
        return (table, None);
    }
    for bump in (1..=255u8).rev() {
        let mut input = seeds.concat();
        input.push(bump);
        input.extend_from_slice(program_id);
        input.extend_from_slice(PDA_MARKER);
        let digest: [u8; 32] = Sha256::digest(&input).into();
        let curve = on_curve(&digest);
        table.sha256.push((input, digest));
        table.on_curve.push((digest, curve));
        if !curve {
            return (table, Some(bump));
        }
    }
    (table, None)
}

fn find_record(c: &mut Corpus, id: String, seeds: &[Vec<u8>], program_id: [u8; 32]) {
    let (table, _) = search_table(seeds, &program_id);
    let slices: Vec<&[u8]> = seeds.iter().map(|s| s.as_slice()).collect();
    let pid = address(program_id);
    let outcome = match rec::catch(|| Address::find_program_address(&slices, &pid)) {
        Ok((a, bump)) => rec::returned(
            Json::obj([("address", rec::bytes(&bytes_of(&a))), ("bump", bump.into())]),
            Json::Null,
        ),
        Err(reason) => rec::unwound(reason, Json::Null),
    };
    let args = Json::obj([
        ("seeds", Json::arr(seeds.iter(), |s| rec::bytes(s))),
        ("program_id", rec::bytes(&program_id)),
        ("crypto", table.json()),
    ]);
    c.push(Record { id, function: FIND, generics: vec![], layout: None, state: Json::Null, args, outcome, observed: None });
}

fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(29).wrapping_add(seed)).collect()
}

fn pattern32(seed: u8) -> [u8; 32] {
    pattern(32, seed).try_into().unwrap()
}

/// The first `probe<i>` seed whose search starts with `on_curve_first`
/// on-curve digests (bump 255 down) before an off-curve one.
fn probe_with_retries(program_id: &[u8; 32], on_curve_first: usize) -> Vec<Vec<u8>> {
    for i in 0u32.. {
        let seeds = vec![format!("probe{i}").into_bytes()];
        if let (_, Some(bump)) = search_table(&seeds, program_id) {
            if 255 - bump as usize == on_curve_first {
                return seeds;
            }
        }
    }
    unreachable!()
}

pub fn record_find(c: &mut Corpus) {
    let zero = [0u8; 32];
    let pid = pattern32(5);
    let key = pattern32(77);
    let s = |x: &str| x.as_bytes().to_vec();
    let mut cases: Vec<(String, Vec<Vec<u8>>, [u8; 32])> = vec![
        ("no_seeds/zero_program".into(), vec![], zero),
        ("no_seeds".into(), vec![], pid),
        ("vault".into(), vec![s("vault")], pid),
        ("vault_key".into(), vec![s("vault"), key.to_vec()], pid),
        ("empty_seeds".into(), vec![vec![], vec![], vec![]], pid),
        ("split_abc_def".into(), vec![s("abc"), s("def")], pid),
        ("joined_abcdef".into(), vec![s("abcdef")], pid),
        ("duplicate_seeds".into(), vec![s("x"), s("x")], pid),
        ("seed_len_32".into(), vec![pattern(32, 1)], pid),
        ("seed_len_33".into(), vec![pattern(33, 1)], pid),
        ("seed_len_32_and_33".into(), vec![pattern(32, 1), pattern(33, 2)], pid),
        ("seeds_15".into(), (0..15).map(|i| vec![i as u8]).collect(), pid),
        ("seeds_16".into(), (0..16).map(|i| vec![i as u8]).collect(), pid),
        ("seeds_17".into(), (0..17).map(|i| vec![i as u8]).collect(), pid),
    ];
    for retries in [1usize, 2, 3] {
        cases.push((format!("bump_{}", 255 - retries), probe_with_retries(&pid, retries), pid));
    }
    for (name, seeds, program_id) in cases {
        find_record(c, format!("find_program_address/{name}"), &seeds, program_id);
    }
}

/// `Address::is_on_curve` (2.6.0 models it). Points: the value samples,
/// encodings with y = p and y = 2^255 - 1 (non-canonical), and digests from
/// the PDA search, on and off the curve.
pub fn record_is_on_curve(c: &mut Corpus) {
    let mut points: Vec<(String, [u8; 32])> = Vec::new();
    let mut first = [0u8; 32];
    first[0] = 1;
    let mut last = [0u8; 32];
    last[31] = 0x80;
    let mut p = [0xffu8; 32];
    p[0] = 0xed;
    p[31] = 0x7f;
    let mut max_y = [0xffu8; 32];
    max_y[31] = 0x7f;
    points.extend([
        ("zero".to_string(), [0u8; 32]),
        ("ones".to_string(), [0xff; 32]),
        ("pattern11".to_string(), pattern32(11)),
        ("pattern12".to_string(), pattern32(12)),
        ("pattern13".to_string(), pattern32(13)),
        ("pattern14".to_string(), pattern32(14)),
        ("identity".to_string(), first),
        ("y0_sign".to_string(), last),
        ("y_eq_p".to_string(), p),
        ("y_max".to_string(), max_y),
    ]);
    let pid = pattern32(5);
    let (table, _) = search_table(&probe_with_retries(&pid, 3), &pid);
    for (i, (digest, curve)) in table.on_curve.iter().enumerate() {
        points.push((format!("pda_digest{i}_{}", if *curve { "on" } else { "off" }), *digest));
    }
    for (name, bytes) in points {
        let a = address(bytes);
        let crypto = Table { sha256: vec![], on_curve: vec![(bytes, on_curve(&bytes))] };
        let outcome = match rec::catch(|| a.is_on_curve()) {
            Ok(b) => rec::returned(b.into(), Json::Null),
            Err(reason) => rec::unwound(reason, Json::Null),
        };
        let args = Json::obj([("self", rec::bytes(&bytes)), ("crypto", crypto.json())]);
        c.push(Record {
            id: format!("is_on_curve/{name}"),
            function: IS_ON_CURVE,
            generics: vec![],
            layout: None,
            state: Json::Null,
            args,
            outcome,
            observed: None,
        });
    }
}
