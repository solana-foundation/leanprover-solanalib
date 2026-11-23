//! Extension unpacking, lookup, listing and account sizing of
//! spl-token-2022-interface 3.1.1.
//!
//! TLV boundary cases (`tlv_cases`) cover empty and one-byte tails, the zero
//! sentinel, short headers, unknown tags, every production tag at its fixed
//! size, wrong sizes, values past the end, duplicates and trailing bytes.
//! Receivers for `get_extension` and `get_extension_types` are
//! `StateWithExtensions::<S>::unpack` of a valid base, zero padding, the
//! account marker and the TLV bytes (unpack does not validate TLV entries).
//! Addresses are recorded as `0x1000 + offset` within that input buffer.

use crate::common::{k, key, opt, result, Selection};
use bytemuck::Pod;
use conformance_recorder::{bytes, catch, returned, unwound, Corpus, Json, Record};
use spl_token_2022_interface::extension::{
    account_len::try_calculate_account_len_from_mint_data, immutable_owner::ImmutableOwner,
    memo_transfer::MemoTransfer, mint_close_authority::MintCloseAuthority,
    non_transferable::NonTransferable,
    transfer_fee::{TransferFeeAmount, TransferFeeConfig},
    transfer_hook::TransferHook, BaseState, BaseStateWithExtensions, Extension, ExtensionType,
    StateWithExtensions,
};
use spl_token_2022_interface::state::{Account, AccountState, Mint};

const BASE_ADDRESS: usize = 0x1000;
const MINT: &str = "spl_token_2022_interface::state::Mint";
const ACCOUNT: &str = "spl_token_2022_interface::state::Account";

/// Production fixed value sizes by tag; `None` for variable-length metadata.
fn fixed_size(tag: u16) -> Option<usize> {
    const SIZES: [usize; 29] = [
        0, 108, 8, 32, 65, 295, 1, 0, 1, 0, 52, 1, 32, 0, 64, 1, 129, 64, 64, 0, 64, 80, 64, 72,
        196, 56, 33, 0, 32,
    ];
    if tag == 19 {
        None
    } else {
        Some(SIZES[tag as usize])
    }
}

/// Value bytes: zero except at a few positions (the first and last byte, and
/// the field boundaries of a fee configuration), so that offsets and field
/// decoding are visible while zero runs keep the corpus compact.
fn pattern(len: usize, seed: u8) -> Vec<u8> {
    let marks = [0usize, 31, 32, 63, 64, 71, 72, 80, 88, 89, 90, 98, 106, 107];
    let mut v = vec![0u8; len];
    for (j, &i) in marks.iter().enumerate() {
        if i < len {
            v[i] = seed.wrapping_add(j as u8).max(1);
        }
    }
    if len > 0 {
        v[len - 1] = seed ^ 0xa5;
    }
    v
}

/// The selection class of a TLV case: the branch family it exercises.
fn tlv_kind(name: &str) -> &'static str {
    match name {
        "empty" | "byte00" | "byte01" | "byteff" => "short",
        n if n.starts_with("sentinel") => "sentinel",
        "tag1_only" | "tag1_one_len_byte" => "header_incomplete",
        "tag29_only" | "tag29_len0" | "tagffff" | "tag29_then_fee" | "tag29_then_own" => "unknown_tag",
        n if n.starts_with("entry") || n == "own" => "entry",
        "fee_short" | "fee_long" | "close_long" | "immutable_len1" | "fee_amount_short" | "own_long"
        | "own_short" => "wrong_size",
        "past_end" | "len_ffff_short" | "fee_then_past_end" => "past_end",
        "fee_sentinel_garbage" | "fee_then_byte" | "fee_then_partial_header" | "fee_then_tag29"
        | "hook_then_tag29" => "trailing",
        _ => "multi",
    }
}

fn outcome_class(r: &Result<Json, String>) -> String {
    match r {
        Ok(j) => j.to_text(),
        Err(reason) => format!("unwound:{reason}"),
    }
}

fn entry(tag: u16, len: usize, seed: u8) -> Vec<u8> {
    let mut v = tag.to_le_bytes().to_vec();
    v.extend_from_slice(&(len as u16).to_le_bytes());
    v.extend(pattern(len, seed));
    v
}

fn cat(parts: &[Vec<u8>]) -> Vec<u8> {
    parts.concat()
}

fn tlv_cases() -> Vec<(String, Vec<u8>)> {
    let mut cases: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("byte00".into(), vec![0]),
        ("byte01".into(), vec![1]),
        ("byteff".into(), vec![0xff]),
        ("sentinel".into(), vec![0, 0]),
        ("sentinel_len0".into(), vec![0, 0, 0, 0]),
        ("sentinel_then_fee".into(), cat(&[vec![0, 0, 0, 0], entry(1, 108, 1)])),
        ("tag1_only".into(), vec![1, 0]),
        ("tag1_one_len_byte".into(), vec![1, 0, 108]),
        ("tag29_only".into(), vec![29, 0]),
        ("tag29_len0".into(), vec![29, 0, 0, 0]),
        ("tagffff".into(), vec![0xff, 0xff, 2, 0, 9, 9]),
    ];
    for tag in 1u16..=28 {
        let len = fixed_size(tag).unwrap_or(10);
        cases.push((format!("entry{tag}"), entry(tag, len, tag as u8)));
    }
    cases.extend([
        ("fee_short".into(), entry(1, 107, 3)),
        ("fee_long".into(), entry(1, 109, 3)),
        ("close_long".into(), entry(3, 33, 3)),
        ("immutable_len1".into(), entry(7, 1, 3)),
        ("fee_amount_short".into(), entry(2, 7, 3)),
        ("past_end".into(), cat(&[vec![3, 0, 32, 0], pattern(31, 5)])),
        ("len_ffff_short".into(), cat(&[vec![3, 0, 0xff, 0xff], pattern(5, 5)])),
        ("close_then_fee".into(), cat(&[entry(3, 32, 4), entry(1, 108, 6)])),
        ("fee_twice".into(), cat(&[entry(1, 108, 7), entry(1, 108, 8)])),
        ("tag29_then_fee".into(), cat(&[vec![29, 0, 2, 0, 1, 1], entry(1, 108, 9)])),
        ("fee_sentinel_garbage".into(), cat(&[entry(1, 108, 10), vec![0, 0, 0xff, 0xff, 0xff]])),
        ("fee_then_byte".into(), cat(&[entry(1, 108, 11), vec![7]])),
        ("fee_then_partial_header".into(), cat(&[entry(1, 108, 12), vec![3, 0, 32]])),
        ("fee_then_tag29".into(), cat(&[entry(1, 108, 13), vec![29, 0, 0, 0]])),
        ("fee_then_past_end".into(), cat(&[entry(1, 108, 14), vec![3, 0, 32, 0, 1]])),
        (
            "account_exts".into(),
            cat(&[entry(2, 8, 15), entry(7, 0, 0), entry(8, 1, 16), entry(11, 1, 17)]),
        ),
        (
            "account_exts_dup".into(),
            cat(&[entry(7, 0, 0), entry(2, 8, 18), entry(7, 0, 0), entry(2, 8, 19)]),
        ),
        (
            "required_all".into(),
            cat(&[entry(1, 108, 20), entry(9, 0, 0), entry(14, 64, 21), entry(26, 33, 22)]),
        ),
        ("required_dup".into(), cat(&[entry(1, 108, 23), entry(1, 108, 24), entry(9, 0, 0)])),
        ("hook_then_tag29".into(), cat(&[entry(14, 64, 25), vec![29, 0, 0, 0]])),
        ("metadata_then_fee".into(), cat(&[entry(19, 40, 26), entry(1, 108, 27)])),
    ]);
    cases
}

fn mint_base(authority_tag: u32, initialized: u8, freeze_tag: u32) -> Vec<u8> {
    let mut v = authority_tag.to_le_bytes().to_vec();
    v.extend_from_slice(&k(1));
    v.extend_from_slice(&1_000_000u64.to_le_bytes());
    v.push(6);
    v.push(initialized);
    v.extend_from_slice(&freeze_tag.to_le_bytes());
    v.extend_from_slice(&k(2));
    assert_eq!(v.len(), 82);
    v
}

fn valid_mint() -> Vec<u8> {
    mint_base(1, 1, 0)
}

fn account_base(delegate_tag: u32, state: u8, native_tag: u32, close_tag: u32) -> Vec<u8> {
    let mut v = k(3).to_vec();
    v.extend_from_slice(&k(4));
    v.extend_from_slice(&42u64.to_le_bytes());
    v.extend_from_slice(&delegate_tag.to_le_bytes());
    v.extend_from_slice(&k(5));
    v.push(state);
    v.extend_from_slice(&native_tag.to_le_bytes());
    v.extend_from_slice(&2_039_280u64.to_le_bytes());
    v.extend_from_slice(&7u64.to_le_bytes());
    v.extend_from_slice(&close_tag.to_le_bytes());
    v.extend_from_slice(&k(6));
    assert_eq!(v.len(), 165);
    v
}

fn valid_account() -> Vec<u8> {
    account_base(0, 1, 0, 1)
}

/// Base, zero padding to 165 bytes, the marker, then the TLV bytes.
fn extended(base: &[u8], marker: u8, tlv: &[u8]) -> Vec<u8> {
    let mut v = base.to_vec();
    v.resize(165, 0);
    v.push(marker);
    v.extend_from_slice(tlv);
    v
}

fn mint_json(m: &Mint) -> Json {
    Json::obj([
        ("mint_authority", opt(Option::<solana_address::Address>::from(m.mint_authority), |a: solana_address::Address| key(a.as_ref()))),
        ("supply", m.supply.into()),
        ("decimals", m.decimals.into()),
        ("is_initialized", m.is_initialized.into()),
        ("freeze_authority", opt(Option::<solana_address::Address>::from(m.freeze_authority), |a: solana_address::Address| key(a.as_ref()))),
    ])
}

fn account_json(a: &Account) -> Json {
    let state = match a.state {
        AccountState::Uninitialized => "Uninitialized",
        AccountState::Initialized => "Initialized",
        AccountState::Frozen => "Frozen",
    };
    Json::obj([
        ("mint", key(a.mint.as_ref())),
        ("owner", key(a.owner.as_ref())),
        ("amount", a.amount.into()),
        ("delegate", opt(Option::<solana_address::Address>::from(a.delegate), |d: solana_address::Address| key(d.as_ref()))),
        ("state", state.into()),
        ("is_native", opt(Option::<u64>::from(a.is_native), Json::from)),
        ("delegated_amount", a.delegated_amount.into()),
        ("close_authority", opt(Option::<solana_address::Address>::from(a.close_authority), |d: solana_address::Address| key(d.as_ref()))),
    ])
}

fn tags(types: &[ExtensionType]) -> Json {
    Json::arr(types.iter(), |t| Json::from(u16::from(*t)))
}

trait Base: BaseState + solana_program_pack::Pack {
    const NAME: &'static str;
    const MARKER: u8;
    fn base() -> Vec<u8>;
    fn json(&self) -> Json;
}

impl Base for Mint {
    const NAME: &'static str = MINT;
    const MARKER: u8 = 1;
    fn base() -> Vec<u8> {
        valid_mint()
    }
    fn json(&self) -> Json {
        mint_json(self)
    }
}

impl Base for Account {
    const NAME: &'static str = ACCOUNT;
    const MARKER: u8 = 2;
    fn base() -> Vec<u8> {
        valid_account()
    }
    fn json(&self) -> Json {
        account_json(self)
    }
}

fn receiver_state(tlv: &[u8]) -> Json {
    Json::obj([("tlv", bytes(tlv)), ("address", (BASE_ADDRESS + 166).into())])
}

fn types_case<S: Base>(c: &mut Selection, name: &str, tlv: &[u8]) {
    let input = extended(&S::base(), S::MARKER, tlv);
    let state = StateWithExtensions::<S>::unpack(&input).expect("receiver construction");
    assert_eq!(state.get_tlv_data(), tlv);
    let before = Json::obj([("tlv", bytes(tlv))]);
    let r = catch(|| state.get_extension_types());
    let res = r.as_ref().map(|r| result(r, |t| tags(t))).map_err(|e| e.clone());
    // Listing does not read S: the full set of distinct results for Mint,
    // success and failure for Account.
    let class = if S::MARKER == 1 {
        format!("{}/{}", tlv_kind(name), outcome_class(&res))
    } else {
        format!("{}", matches!(r, Ok(Ok(_))))
    };
    let outcome = match res {
        Ok(j) => returned(j, before.clone()),
        Err(reason) => unwound(reason, before.clone()),
    };
    c.offer(class, Record {
        id: format!("get_extension_types/{}/{name}", if S::MARKER == 1 { "mint" } else { "account" }),
        function: "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_types",
        generics: vec![("S", S::NAME.to_string())],
        layout: None,
        state: before,
        args: Json::Null,
        outcome,
        observed: None,
    });
}

fn getter_case<S: Base, V: Extension + Pod>(
    c: &mut Selection,
    v_name: &'static str,
    case: &str,
    tlv: &[u8],
    decode: fn(&V) -> Option<Json>,
) {
    let input = extended(&S::base(), S::MARKER, tlv);
    let state = StateWithExtensions::<S>::unpack(&input).expect("receiver construction");
    let tlv_ptr = state.get_tlv_data().as_ptr() as usize;
    assert_eq!(tlv_ptr - input.as_ptr() as usize, 166);
    let before = receiver_state(tlv);
    let r = catch(|| {
        state.get_extension::<V>().map(|v: &V| {
            let raw = bytemuck::bytes_of(v);
            let offset = v as *const V as usize - tlv_ptr;
            let mut fields = vec![("offset", Json::from(offset)), ("bytes", bytes(raw))];
            if let Some(value) = decode(v) {
                fields.push(("value", value));
            }
            Json::Obj(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
        })
    });
    let res = r.as_ref().map(|r| result(r, |v| v.clone())).map_err(|e| e.clone());
    // A wrong base association is rejected before any lookup: one class.
    let wrong_base = V::TYPE.get_account_type() != S::ACCOUNT_TYPE;
    let class = if wrong_base { "wrong_base".to_string() } else { format!(
        "{}/{}",
        tlv_kind(case),
        match &r {
            Ok(Ok(v)) => format!("ok@{}", v.to_text().split(',').next().unwrap_or("")),
            Ok(Err(e)) => format!("{e:?}"),
            Err(reason) => format!("unwound:{reason}"),
        }
    ) };
    let outcome = match res {
        Ok(j) => returned(j, before.clone()),
        Err(reason) => unwound(reason, before.clone()),
    };
    c.offer(class, Record {
        id: format!(
            "get_extension/{}/{}/{case}",
            if S::MARKER == 1 { "mint" } else { "account" },
            v_name.rsplit("::").next().unwrap()
        ),
        function: "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension",
        generics: vec![("S", S::NAME.to_string()), ("V", v_name.to_string())],
        layout: None,
        state: before,
        args: Json::Null,
        outcome,
        observed: None,
    });
}

fn unpack_case<S: Base>(c: &mut Corpus, name: &str, input: &[u8]) {
    let r = catch(|| {
        StateWithExtensions::<S>::unpack(input).map(|s| {
            let tlv = s.get_tlv_data();
            let p = tlv.as_ptr() as usize;
            let start = input.as_ptr() as usize;
            // The source returns either a subslice of the input or its static
            // empty literal; the latter lies outside the input buffer.
            let tlv_ref = if p >= start && p <= start + input.len() {
                Json::obj([("offset", (p - start).into()), ("length", tlv.len().into())])
            } else {
                assert!(tlv.is_empty());
                Json::Null
            };
            Json::obj([("base", s.base.json()), ("tlv", tlv_ref)])
        })
    });
    let outcome = match r {
        Ok(r) => returned(result(&r, |v| v.clone()), Json::Null),
        Err(reason) => unwound(reason, Json::Null),
    };
    c.push(Record {
        id: format!("unpack/{}/{name}", if S::MARKER == 1 { "mint" } else { "account" }),
        function: "spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack",
        generics: vec![("S", S::NAME.to_string())],
        layout: None,
        state: Json::Null,
        args: Json::obj([("input", bytes(input))]),
        outcome,
        observed: None,
    });
}

fn account_len_case(c: &mut Selection, kind: &str, name: &str, mint: &[u8], additional: &[ExtensionType]) {
    let r = catch(|| try_calculate_account_len_from_mint_data(mint, additional));
    let res = r.as_ref().map(|r| result(r, |n: &usize| Json::from(*n))).map_err(|e| e.clone());
    let label: Vec<String> = additional.iter().map(|t| u16::from(*t).to_string()).collect();
    // Successes by mint kind, request and size; errors by kind (a mismatched
    // request is rejected before the mint is read, so it is one class).
    let class = match &r {
        Ok(Ok(n)) => format!("{kind}/[{}]/{n}", label.join(",")),
        Ok(Err(solana_program_error::ProgramError::Custom(20))) => "err:Custom(20)".into(),
        Ok(Err(e)) => format!("err:{e:?}/{kind}"),
        Err(reason) => format!("unwound:{reason}"),
    };
    let outcome = match res {
        Ok(j) => returned(j, Json::Null),
        Err(reason) => unwound(reason, Json::Null),
    };
    c.offer(class, Record {
        id: format!("account_len/{name}/[{}]", label.join(",")),
        function: "spl_token_2022_interface::extension::account_len::try_calculate_account_len_from_mint_data",
        generics: vec![],
        layout: None,
        state: Json::Null,
        args: Json::obj([("mint_data", bytes(mint)), ("additional", tags(additional))]),
        outcome,
        observed: None,
    });
}

fn no_value<V>(_: &V) -> Option<Json> {
    None
}

/// The fee configuration read through its struct fields.
fn fee_value(v: &TransferFeeConfig) -> Option<Json> {
    Some(crate::fees::config_json(v))
}

pub fn record(c: &mut Corpus) {
    let cases = tlv_cases();

    let (mut mint_types, mut account_types) = (Selection::new(), Selection::new());
    for (name, tlv) in &cases {
        types_case::<Mint>(&mut mint_types, name, tlv);
        types_case::<Account>(&mut account_types, name, tlv);
    }
    mint_types.into_corpus(c);
    account_types.into_corpus(c);

    // Lookup: every TLV case for the fee configuration; a
    // focused subset (shared boundaries plus the entry for that type with right
    // and wrong sizes) for the other value types, including a wrong base.
    let shared = ["empty", "sentinel_then_fee", "tag1_only", "tagffff", "past_end", "close_then_fee"];
    let pick = |n: &str| cases.iter().find(|(m, _)| m == n).unwrap().1.clone();
    let mut fee_config = Selection::new();
    for (name, tlv) in &cases {
        getter_case::<Mint, TransferFeeConfig>(&mut fee_config, "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig", name, tlv, fee_value);
    }
    fee_config.into_corpus(c);
    macro_rules! focused {
        ($s:ty, $v:ty, $path:expr, $tag:expr) => {{
            let size = fixed_size($tag).unwrap();
            let mut subset: Vec<(String, Vec<u8>)> =
                shared.iter().map(|n| (n.to_string(), pick(n))).collect();
            subset.push(("own".into(), entry($tag, size, 30)));
            subset.push(("own_long".into(), entry($tag, size + 1, 31)));
            if size > 0 {
                subset.push(("own_short".into(), entry($tag, size - 1, 32)));
            }
            subset.push(("tag29_then_own".into(), cat(&[vec![29, 0, 1, 0, 9], entry($tag, size, 33)])));
            subset.push(("sentinel_then_own".into(), cat(&[vec![0, 0, 0, 0], entry($tag, size, 34)])));
            subset.push(("own_twice".into(), cat(&[entry($tag, size, 35), entry($tag, size, 36)])));
            let mut sel = Selection::new();
            for (name, tlv) in &subset {
                getter_case::<$s, $v>(&mut sel, $path, name, tlv, no_value);
            }
            sel.into_corpus(c);
        }};
    }
    focused!(Account, TransferFeeAmount, "spl_token_2022_interface::extension::transfer_fee::TransferFeeAmount", 2);
    focused!(Mint, MintCloseAuthority, "spl_token_2022_interface::extension::mint_close_authority::MintCloseAuthority", 3);
    focused!(Mint, NonTransferable, "spl_token_2022_interface::extension::non_transferable::NonTransferable", 9);
    focused!(Mint, TransferHook, "spl_token_2022_interface::extension::transfer_hook::TransferHook", 14);
    focused!(Account, ImmutableOwner, "spl_token_2022_interface::extension::immutable_owner::ImmutableOwner", 7);
    focused!(Account, MemoTransfer, "spl_token_2022_interface::extension::memo_transfer::MemoTransfer", 8);
    // Wrong base association: rejected before any lookup.
    focused!(Account, TransferFeeConfig, "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig", 1);
    focused!(Mint, TransferFeeAmount, "spl_token_2022_interface::extension::transfer_fee::TransferFeeAmount", 2);

    // Unpacking.
    let mint = valid_mint();
    let mut mint_inputs: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("short81".into(), mint[..81].to_vec()),
        ("bare".into(), mint.clone()),
        ("base_plus1".into(), cat(&[mint.clone(), vec![0]])),
        ("padding_only".into(), cat(&[mint.clone(), vec![0; 83]])),
        ("marker_only".into(), extended(&mint, 1, &[])),
        ("marker_account".into(), extended(&mint, 2, &[])),
        ("marker_zero".into(), extended(&mint, 0, &[])),
        ("marker_three".into(), extended(&mint, 3, &[])),
        ("padding_first_nonzero".into(), {
            let mut v = extended(&mint, 1, &[]);
            v[82] = 1;
            v
        }),
        ("padding_last_nonzero".into(), {
            let mut v = extended(&mint, 1, &[]);
            v[164] = 0x80;
            v
        }),
        ("multisig_length".into(), extended(&mint, 1, &pattern(189, 1))),
        ("length_354".into(), extended(&mint, 1, &pattern(188, 1))),
        ("length_356".into(), extended(&mint, 1, &pattern(190, 1))),
        ("authority_tag2".into(), mint_base(2, 1, 0)),
        ("authority_tag_high".into(), mint_base(0x0100_0000, 1, 0)),
        ("uninitialized".into(), mint_base(1, 0, 0)),
        ("initialized_two".into(), mint_base(1, 2, 0)),
        ("freeze_tag2".into(), mint_base(0, 1, 2)),
        ("both_options".into(), mint_base(1, 1, 1)),
        ("uninitialized_extended".into(), extended(&mint_base(1, 0, 0), 1, &[])),
        ("base_error_bad_padding".into(), {
            let mut v = extended(&mint_base(2, 1, 0), 3, &[]);
            v[100] = 1;
            v
        }),
        ("uninitialized_multisig_length".into(), extended(&mint_base(1, 0, 0), 1, &pattern(189, 1))),
    ];
    for name in ["entry1", "required_all", "tagffff", "byte01", "past_end"] {
        mint_inputs.push((format!("extended_{name}"), extended(&mint, 1, &pick(name))));
    }
    for (name, input) in &mint_inputs {
        unpack_case::<Mint>(c, name, input);
    }
    let account = valid_account();
    let mut account_inputs: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("short164".into(), account[..164].to_vec()),
        ("bare".into(), account.clone()),
        ("frozen".into(), account_base(1, 2, 1, 0)),
        ("uninitialized".into(), account_base(0, 0, 0, 0)),
        ("state_three".into(), account_base(0, 3, 0, 0)),
        ("delegate_tag2".into(), account_base(2, 1, 0, 0)),
        ("native_tag2".into(), account_base(0, 1, 2, 0)),
        ("close_tag2".into(), account_base(0, 1, 0, 2)),
        ("marker_only".into(), extended(&account, 2, &[])),
        ("marker_mint".into(), extended(&account, 1, &[])),
        ("marker_zero".into(), extended(&account, 0, &[])),
        ("multisig_length".into(), extended(&account, 2, &pattern(189, 2))),
        ("uninitialized_extended".into(), extended(&account_base(0, 0, 0, 0), 2, &[])),
    ];
    for name in ["entry2", "account_exts", "tagffff", "byte01"] {
        account_inputs.push((format!("extended_{name}"), extended(&account, 2, &pick(name))));
    }
    for (name, input) in &account_inputs {
        unpack_case::<Account>(c, name, input);
    }

    // Account sizing from raw mint bytes.
    use ExtensionType as T;
    let mut mints: Vec<(&str, String, Vec<u8>)> = vec![
        ("bare", "bare".into(), mint.clone()),
        ("invalid_mint", "short81".into(), mint[..81].to_vec()),
        ("invalid_mint", "uninitialized".into(), mint_base(1, 0, 0)),
        ("pod_admission", "initialized_two".into(), mint_base(1, 2, 0)),
        ("pod_admission", "authority_tag5".into(), mint_base(5, 1, 7)),
        ("tlv_none", "marker_only".into(), extended(&mint, 1, &[])),
        ("invalid_mint", "marker_account".into(), extended(&mint, 2, &[])),
        ("invalid_mint", "bad_padding".into(), {
            let mut v = extended(&mint, 1, &pick("entry1"));
            v[90] = 1;
            v
        }),
        ("invalid_mint", "multisig_length".into(), extended(&mint, 1, &pattern(189, 0))),
        ("pod_admission", "pod_flags_extended".into(), extended(&mint_base(9, 3, 9), 1, &pick("entry9"))),
    ];
    for (kind, name) in [
        ("tlv_none", "empty"), ("tlv_none", "byte01"), ("tlv_none", "sentinel"),
        ("tlv_required", "entry1"), ("tlv_required", "entry9"), ("tlv_required", "entry14"),
        ("tlv_required", "entry26"), ("tlv_required", "required_all"), ("tlv_required", "required_dup"),
        ("tlv_other", "entry2"), ("tlv_other", "entry19"), ("tlv_other", "account_exts"),
        ("tlv_other", "metadata_then_fee"), ("tlv_other", "sentinel_then_fee"),
        ("tlv_error", "tagffff"), ("tlv_error", "tag29_len0"), ("tlv_error", "fee_then_tag29"),
        ("tlv_error", "fee_then_partial_header"), ("tlv_error", "fee_then_past_end"),
        ("tlv_error", "hook_then_tag29"), ("tlv_error", "tag1_only"), ("tlv_trailing", "fee_then_byte"),
    ] {
        mints.push((kind, format!("extended_{name}"), extended(&mint, 1, &pick(name))));
    }
    let additional_common: [&[ExtensionType]; 3] = [
        &[],
        &[T::TransferFeeAmount, T::ImmutableOwner, T::ImmutableOwner],
        &[T::TransferFeeConfig],
    ];
    let mut sizing = Selection::new();
    for (kind, name, m) in &mints {
        for extra in additional_common {
            account_len_case(&mut sizing, kind, name, m, extra);
        }
    }
    let additional_more: [&[ExtensionType]; 6] = [
        &[T::Uninitialized],
        &[T::TransferFeeAmount, T::TransferFeeConfig],
        &[T::ConfidentialTransferAccount],
        &[T::NonTransferableAccount, T::TransferHookAccount, T::PausableAccount],
        &[
            T::TransferFeeAmount,
            T::ConfidentialTransferAccount,
            T::ImmutableOwner,
            T::MemoTransfer,
            T::CpiGuard,
            T::NonTransferableAccount,
            T::TransferHookAccount,
            T::ConfidentialTransferFeeAmount,
            T::PausableAccount,
        ],
        &[T::TokenMetadata],
    ];
    for name in ["bare", "extended_required_all", "uninitialized", "extended_tagffff"] {
        let (kind, _, m) = mints.iter().find(|(_, n, _)| n == name).unwrap();
        for extra in additional_more {
            account_len_case(&mut sizing, kind, name, m, extra);
        }
    }
    sizing.into_corpus(c);
}
