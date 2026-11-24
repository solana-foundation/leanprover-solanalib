//! Transfer-fee arithmetic and epoch selection of spl-token-2022-interface
//! 3.1.1, over exhaustive boundary products.
//!
//! The receiver (`&TransferFee`, `&TransferFeeConfig`) is the model state; it
//! is read back after the call. `get_epoch_fee` returns a reference: the
//! record keeps which field it points to (compared by address with the two
//! fields of the receiver) and the value read through it.

use crate::common::{k, key, opt, Selection};
use conformance_recorder::{catch, returned, unwound, Corpus, Json, Record};
use spl_token_2022_interface::extension::transfer_fee::{TransferFee, TransferFeeConfig};

fn fee(epoch: u64, maximum_fee: u64, basis_points: u16) -> TransferFee {
    TransferFee {
        epoch: epoch.into(),
        maximum_fee: maximum_fee.into(),
        transfer_fee_basis_points: basis_points.into(),
    }
}

fn fee_json(f: &TransferFee) -> Json {
    Json::obj([
        ("epoch", u64::from(f.epoch).into()),
        ("maximum_fee", u64::from(f.maximum_fee).into()),
        ("transfer_fee_basis_points", u16::from(f.transfer_fee_basis_points).into()),
    ])
}

pub fn config_json(c: &TransferFeeConfig) -> Json {
    let raw = bytemuck::bytes_of(c);
    Json::obj([
        ("transfer_fee_config_authority", key(&raw[0..32])),
        ("withdraw_withheld_authority", key(&raw[32..64])),
        ("withheld_amount", u64::from(c.withheld_amount).into()),
        ("older_transfer_fee", fee_json(&c.older_transfer_fee)),
        ("newer_transfer_fee", fee_json(&c.newer_transfer_fee)),
    ])
}

/// Basis points: zero, one, the rounding neighbourhood, below/at/above
/// 100 percent, and the u16 maximum.
const BASIS_POINTS: [u16; 8] = [0, 1, 3, 5000, 9999, 10000, 10001, u16::MAX];
/// Maximum fees: zero, one, mid-range, and the top of u64.
const MAXIMUM_FEES: [u64; 4] = [0, 1, 5000, u64::MAX];
/// Amounts: zero, one, the basis-point scale and its neighbours, rounding
/// neighbourhoods, and the top of u64 (overflow of `amount * 10000` in u64
/// is not an overflow in the u128 the source uses).
const AMOUNTS: [u64; 10] = [
    0,
    1,
    2,
    9999,
    10000,
    10001,
    u64::MAX / 10000,
    u64::MAX / 10000 + 1,
    u64::MAX - 1,
    u64::MAX,
];

type Method = fn(&TransferFee, u64) -> Option<u64>;

/// The source branch a case exercises (selection only; computed here from the
/// inputs with u128 arithmetic, mirroring the source branch order).
fn fee_class(bps: u16, max: u64, amount: u64) -> String {
    let (b, a) = (bps as u128, amount as u128);
    if b == 0 {
        return "zero_rate".into();
    }
    if a == 0 {
        return "zero_amount".into();
    }
    let n = a * b;
    let raw = (n + 9999) / 10000;
    let exact = n % 10000 == 0;
    let rate = if b > 10000 { "over" } else { "within" };
    if raw > u64::MAX as u128 {
        format!("overflow/{rate}")
    } else if raw <= max as u128 {
        format!("raw/{rate}/exact={exact}")
    } else {
        format!("capped/{rate}/exact={exact}")
    }
}

fn pre_fee_class(bps: u16, max: u64, post: u64) -> String {
    let (b, p) = (bps as u128, post as u128);
    if b == 0 {
        return "zero_rate".into();
    }
    if p == 0 {
        return "zero_amount".into();
    }
    if b == 10000 {
        return format!("full/overflow={}", max.checked_add(post).is_none());
    }
    if b > 10000 {
        return "excess_rate".into();
    }
    let n = p * 10000;
    let d = 10000 - b;
    let raw = (n + d - 1) / d;
    let exact = n % d == 0;
    if raw - p >= max as u128 {
        format!("capped/overflow={}", post.checked_add(max).is_none())
    } else {
        format!("raw/exact={exact}/overflow={}", raw > u64::MAX as u128)
    }
}

pub fn record(c: &mut Corpus) {
    let methods: [(&str, &'static str, Method); 3] = [
        (
            "calculate_fee",
            "spl_token_2022_interface::extension::transfer_fee::TransferFee::calculate_fee",
            TransferFee::calculate_fee,
        ),
        (
            "calculate_post_fee_amount",
            "spl_token_2022_interface::extension::transfer_fee::TransferFee::calculate_post_fee_amount",
            TransferFee::calculate_post_fee_amount,
        ),
        (
            "calculate_pre_fee_amount",
            "spl_token_2022_interface::extension::transfer_fee::TransferFee::calculate_pre_fee_amount",
            TransferFee::calculate_pre_fee_amount,
        ),
    ];
    for (name, function, method) in methods {
        let mut sel = Selection::new();
        for bps in BASIS_POINTS {
            for max in MAXIMUM_FEES {
                for amount in AMOUNTS {
                    // The epoch is not read by the arithmetic; two values suffice.
                    let receiver = fee(if amount % 2 == 0 { 0 } else { u64::MAX }, max, bps);
                    let before = fee_json(&receiver);
                    let r = catch(|| method(&receiver, amount));
                    let after = fee_json(&receiver);
                    let class = match name {
                        "calculate_pre_fee_amount" => pre_fee_class(bps, max, amount),
                        "calculate_post_fee_amount" => format!(
                            "{}/{}",
                            fee_class(bps, max, amount),
                            matches!(r, Ok(Some(_)))
                        ),
                        _ => fee_class(bps, max, amount),
                    };
                    let outcome = match r {
                        Ok(v) => returned(opt(v, Json::from), after),
                        Err(reason) => unwound(reason, after),
                    };
                    sel.offer(class, Record {
                        id: format!("{name}/{bps}/{max}/{amount}"),
                        function,
                        generics: vec![],
                        layout: None,
                        state: before,
                        args: Json::obj([("amount", amount.into())]),
                        outcome,
                        observed: None,
                    });
                }
            }
        }
        sel.into_corpus(c);
    }

    // Epoch selection: newer activation epochs at the u64 boundaries; requested
    // epochs below, at and above them. The epoch in the older record is set
    // above the newer one in half of the cases, which must not matter.
    let newer_epochs = [0u64, 1, 100, u64::MAX - 1, u64::MAX];
    let mut sel = Selection::new();
    for (i, newer_epoch) in newer_epochs.into_iter().enumerate() {
        for older_epoch in [0u64, u64::MAX] {
            // Authorities are raw nullable 32-byte values (all zero is None).
            let mut raw = [0u8; 108];
            raw[0..32].copy_from_slice(&if i % 2 == 0 { [0; 32] } else { k(7) });
            raw[32..64].copy_from_slice(&k(8));
            let mut config: TransferFeeConfig = *bytemuck::from_bytes(&raw);
            config.withheld_amount = (i as u64 * 1000).into();
            config.older_transfer_fee = fee(older_epoch, 200, 9);
            config.newer_transfer_fee = fee(newer_epoch, 100, 3);
            let mut epochs = vec![0, 1, u64::MAX];
            for d in [newer_epoch.wrapping_sub(1), newer_epoch, newer_epoch.wrapping_add(1)] {
                if !epochs.contains(&d) {
                    epochs.push(d);
                }
            }
            epochs.sort();
            for epoch in epochs {
                let before = config_json(&config);
                let r = catch(|| {
                    let selected: &TransferFee = config.get_epoch_fee(epoch);
                    let field = if std::ptr::eq(selected, &config.newer_transfer_fee) {
                        "newer"
                    } else if std::ptr::eq(selected, &config.older_transfer_fee) {
                        "older"
                    } else {
                        "other"
                    };
                    Json::obj([("field", field.into()), ("value", fee_json(selected))])
                });
                let after = config_json(&config);
                let relation = match epoch.cmp(&newer_epoch) {
                    std::cmp::Ordering::Less => "before",
                    std::cmp::Ordering::Equal => "at",
                    std::cmp::Ordering::Greater => "after",
                };
                let class = format!("{relation}/older_above={}", older_epoch > newer_epoch);
                let outcome = match r {
                    Ok(v) => returned(v, after),
                    Err(reason) => unwound(reason, after),
                };
                sel.offer(class, Record {
                    id: format!("get_epoch_fee/{newer_epoch}/{older_epoch}/{epoch}"),
                    function: "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee",
                    generics: vec![],
                    layout: None,
                    state: before,
                    args: Json::obj([("epoch", epoch.into())]),
                    outcome,
                    observed: None,
                });
            }
        }
    }
    sel.into_corpus(c);
}
