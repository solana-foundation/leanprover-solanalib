//! Case material shared by the Rent drivers (pinocchio 0.10.2 and 0.11.1, solana-rent 3.0.0).
//!
//! Case selection (the suite rule: every distinct behavior once, at its boundary): each case
//! below is one behavior of the source: an accepted input at the edge of a guard and the first
//! rejected one; the largest product that fits in `u64` and the first that overflows, for
//! `128 + len` and for `(128 + len) * rate`; the binary64 roundings of the floating calculation
//! (exact, ties to even in both directions, below and above half, rounding up to `2^64`); one
//! integer under every class of threshold (fractions, neighbours of the integer thresholds,
//! zeros, negatives, subnormals, values that saturate the cast, infinities, NaNs). Cases marked
//! `wrapping` are those whose outcome depends on overflow checking; the drivers built without
//! overflow checks record only those.

use conformance_recorder::{self as rec, Json};

pub const MAX_DATA: u64 = 10 * 1024 * 1024;
/// `u64::MAX / (2 * (128 + MAX_DATA))`, the pinocchio 0.10.2 bound for threshold 2.0.
pub const CURRENT_MAX_RATE: u64 = 879_598_564_933;
/// `u64::MAX / (128 + MAX_DATA)`, the bound for threshold 1.0 (and the only pinocchio 0.11.1 bound).
pub const SIMD_MAX_RATE: u64 = 1_759_197_129_867;
pub const TWO_53: u64 = 1 << 53;

pub const ONE: u64 = 0x3ff0_0000_0000_0000;
pub const TWO: u64 = 0x4000_0000_0000_0000;
pub const ONE_PLUS_ULP: u64 = 0x3ff0_0000_0000_0001;

/// Thresholds as binary64 bit patterns, one per class.
pub const THRESHOLDS: &[(&str, u64)] = &[
    ("one", ONE),
    ("two", TWO),
    ("one_plus_ulp", ONE_PLUS_ULP),
    ("two_minus_ulp", 0x3fff_ffff_ffff_ffff),
    ("half", 0x3fe0_0000_0000_0000),
    ("one_and_half", 0x3ff8_0000_0000_0000),
    ("three", 0x4008_0000_0000_0000),
    ("tenth", 0x3fb9_9999_9999_999a),
    ("pos_zero", 0x0000_0000_0000_0000),
    ("neg_zero", 0x8000_0000_0000_0000),
    ("neg_one", 0xbff0_0000_0000_0000),
    ("min_subnormal", 0x0000_0000_0000_0001),
    ("min_normal", 0x0010_0000_0000_0000),
    ("two_pow_64", 0x43f0_0000_0000_0000),
    ("max", 0x7fef_ffff_ffff_ffff),
    ("pos_inf", 0x7ff0_0000_0000_0000),
    ("neg_inf", 0xfff0_0000_0000_0000),
    ("qnan", 0x7ff8_0000_0000_0000),
    ("neg_qnan", 0xfff8_0000_0000_0000),
    ("snan_payload", 0x7ff0_0000_0000_0001),
];

/// One case: (name, rate, threshold bits, data length, outcome depends on overflow checking).
pub type Case = (&'static str, u64, u64, u64, bool);

/// solana-rent 3.0.0 `minimum_balance` (no guard): integer edges at the default threshold,
/// conversion roundings at threshold 1.0, then every threshold class over one integer.
pub fn sdk_cases() -> Vec<Case> {
    let mut v: Vec<Case> = vec![
        ("default", 3480, TWO, 0, false),
        ("default_165", 3480, TWO, 165, false),
        ("zero_rate_long", 0, TWO, u64::MAX - 128, true),
        ("add_edge", 1, TWO, u64::MAX - 128, true),
        ("add_overflow", 1, TWO, u64::MAX - 127, true),
        ("add_overflow_zero_rate", 0, TWO, u64::MAX, true),
        ("mul_edge", 3, TWO, u64::MAX / 3 - 128, true),
        ("mul_overflow", 3, TWO, u64::MAX / 3 - 127, true),
        ("mul_overflow_max_rate", u64::MAX, TWO, 0, true),
        ("round_exact", 1, ONE, TWO_53 - 128, false),
        ("round_tie_down", 1, ONE, TWO_53 + 1 - 128, false),
        ("round_tie_up", 1, ONE, TWO_53 + 3 - 128, false),
        ("round_above_half", TWO_53 + 1, ONE, 1, false),
        ("round_below_half", TWO_53 - 1, ONE, 127, false),
        ("round_up_to_2_64", 1, ONE, u64::MAX - 128, true),
        ("second_rounding", 1, ONE_PLUS_ULP, u64::MAX - 128, true),
        ("zero_times_inf", 0, 0x7ff0_0000_0000_0000, 0, false),
    ];
    for &(name, bits) in THRESHOLDS {
        if bits != ONE && bits != TWO {
            v.push((name, 3480, bits, 0, false));
        }
    }
    v
}

/// pinocchio 0.10.2 `try_minimum_balance`: the data guard, the rate guard of threshold 2.0
/// (and the unreachable one of threshold 1.0), both integer branches and the floating branch.
pub fn pinocchio_0_10_2_cases() -> Vec<Case> {
    let half = 0x3fe0_0000_0000_0000;
    let mut v: Vec<Case> = vec![
        ("two_default", 3480, TWO, 165, false),
        ("one_default", 6960, ONE, 165, false),
        ("zero", 0, TWO, 0, false),
        ("data_limit", 1, TWO, MAX_DATA, false),
        ("data_over_limit", 1, TWO, MAX_DATA + 1, false),
        ("data_max_before_overflow", u64::MAX, ONE, u64::MAX, false),
        ("data_over_limit_float", 1, half, MAX_DATA + 1, false),
        ("two_rate_limit", CURRENT_MAX_RATE, TWO, MAX_DATA, false),
        ("two_rate_over_limit", CURRENT_MAX_RATE + 1, TWO, 0, false),
        ("two_rate_max", u64::MAX, TWO, 0, false),
        ("one_rate_limit", SIMD_MAX_RATE, ONE, MAX_DATA, false),
        ("one_rate_between_limits", CURRENT_MAX_RATE + 1, ONE, MAX_DATA, false),
        ("one_rate_over_limit_small", SIMD_MAX_RATE + 1, ONE, 0, false),
        ("one_rate_over_limit_overflow", SIMD_MAX_RATE + 1, ONE, MAX_DATA, true),
        ("one_rate_max", u64::MAX, ONE, 0, true),
        ("float_rate_unguarded", CURRENT_MAX_RATE + 1, half, MAX_DATA, false),
        ("float_overflow", SIMD_MAX_RATE + 1, half, MAX_DATA, true),
        ("float_overflow_max_rate", u64::MAX, half, 0, true),
        ("float_tie", TWO_53 + 1, ONE_PLUS_ULP, 0, false),
        ("float_tie_up", TWO_53 + 3, ONE_PLUS_ULP, 0, false),
        ("float_above_half", TWO_53 + 1, ONE_PLUS_ULP, 1, false),
        ("float_below_half", TWO_53 - 1, ONE_PLUS_ULP, 127, false),
        ("float_up_to_2_64", u64::MAX / 128, ONE_PLUS_ULP, 0, false),
    ];
    for &(name, bits) in THRESHOLDS {
        if bits != ONE && bits != TWO {
            v.push((name, 3480, bits, 0, false));
        }
    }
    v
}

/// pinocchio 0.11.1 `try_minimum_balance`: the data guard, then the rate guard, then a product
/// that always fits.
pub fn pinocchio_0_11_1_cases() -> Vec<(&'static str, u64, u64)> {
    vec![
        ("zero", 0, 0),
        ("default", 6960, 165),
        ("largest_product", SIMD_MAX_RATE, MAX_DATA),
        ("rate_over_limit", SIMD_MAX_RATE + 1, 0),
        ("rate_max", u64::MAX, MAX_DATA),
        ("data_over_limit", 1, MAX_DATA + 1),
        ("data_over_limit_rate_over_limit", SIMD_MAX_RATE + 1, MAX_DATA + 1),
        ("data_max", 1, u64::MAX),
        ("data_word", 1, 1 << 32),
    ]
}

/// Whether this build checks integer overflow: a local `u64::MAX + 1` expression panics or wraps.
/// Every crate of a driver is compiled with its `[profile.dev]`, so this is the libraries'
/// setting too.
pub fn overflow_checks() -> bool {
    rec::catch(|| core::hint::black_box(u64::MAX) + core::hint::black_box(1)).is_err()
}

/// The driver arithmetic profile: its overflow checking, and unwinding panics.
pub fn arithmetic_profile() -> Vec<(&'static str, Json)> {
    vec![("overflow_checks", Json::from(overflow_checks())), ("panic", "unwind".into())]
}

pub fn profile_json(extra: &[(&'static str, Json)]) -> Json {
    let mut fields: Vec<(String, Json)> =
        arithmetic_profile().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    fields.extend(extra.iter().map(|(k, v)| (k.to_string(), v.clone())));
    Json::Obj(fields)
}

/// A call whose state is a constant profile: `Ok`/`Err` returns and panics keep the profile.
pub fn profile_call<T>(state: &Json, f: impl FnOnce() -> T, enc: impl Fn(&T) -> Json) -> Json {
    match rec::catch(f) {
        Ok(v) => rec::returned(enc(&v), state.clone()),
        Err(reason) => rec::unwound(reason, state.clone()),
    }
}
