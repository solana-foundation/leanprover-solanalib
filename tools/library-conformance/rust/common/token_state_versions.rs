//! Tiny version-selected callers of the unmodified published token APIs.
//! The shared fixture supplies ordinary borrowed TLV receivers and one explicit
//! VariableLenPack implementation; it does not replace the SDK functions.
use crate::{allocation::counted, CLONE, CORPUS, LEGACY, PACKAGE, REQUIRE_TLV, RUST_CRATE, UNPACK, VERSION};
use conformance_recorder::{bytes, err, ok, returned, variant, Corpus, Json, Record};
use solana_program_error::ProgramError;
use solana_program_pack::Pack;
use token_api::extension::{BaseStateWithExtensions, Extension, ExtensionType, StateWithExtensions};
use token_api::extension::transfer_fee::{TransferFee, TransferFeeConfig};
use token_api::state::{Account, AccountState, Mint};
use std::sync::atomic::{AtomicUsize, Ordering};

static ACCESS: AtomicUsize = AtomicUsize::new(0);
static MEASURE: AtomicUsize = AtomicUsize::new(0);
#[cfg(feature = "metadata")]
static GETTER: AtomicUsize = AtomicUsize::new(0);

struct Tlv<'a>(&'a [u8]);
impl BaseStateWithExtensions<Mint> for Tlv<'_> {
    fn get_tlv_data(&self) -> &[u8] { ACCESS.fetch_add(1, Ordering::SeqCst); self.0 }
}

// This existing driver feature selects ProgramError 2.2.2, whose Borsh error
// owns a String. The interface 3.x error has no String payload.
#[cfg(feature = "metadata")]
struct OwnedErrorTlv;
#[cfg(feature = "metadata")]
impl BaseStateWithExtensions<Mint> for OwnedErrorTlv {
    fn get_tlv_data(&self) -> &[u8] { panic!("the typed getter override must be dispatched") }
    fn get_extension<V: Extension + bytemuck::Pod>(&self) -> Result<&V, ProgramError> {
        GETTER.fetch_add(1, Ordering::SeqCst);
        Err(ProgramError::BorshIoError(String::from("owned extension error")))
    }
}

struct Variable { length: usize, error: bool }
impl Extension for Variable { const TYPE: ExtensionType = ExtensionType::TokenMetadata; }
impl tlv_api::variable_len_pack::VariableLenPack for Variable {
    fn pack_into_slice(&self, _: &mut [u8]) -> Result<(), ProgramError> { Err(ProgramError::InvalidArgument) }
    fn unpack_from_slice(_: &[u8]) -> Result<Self, ProgramError> { Err(ProgramError::InvalidArgument) }
    fn get_packed_len(&self) -> Result<usize, ProgramError> {
        assert_eq!(ACCESS.load(Ordering::SeqCst), 1, "TLV accessor must precede measurement");
        MEASURE.fetch_add(1, Ordering::SeqCst);
        if self.error { Err(ProgramError::Custom(9)) } else { Ok(self.length) }
    }
}

fn error(value: &ProgramError) -> Json {
    let name = match value {
        ProgramError::Custom(code) => return variant("Custom", vec![(*code).into()]),
        ProgramError::InvalidArgument => "InvalidArgument",
        ProgramError::InvalidAccountData => "InvalidAccountData",
        ProgramError::UninitializedAccount => "UninitializedAccount",
        other => panic!("uncovered native error {other:?}"),
    };
    variant(name, vec![])
}
fn result<T>(value: &Result<T, ProgramError>, encode: impl Fn(&T) -> Json) -> Json {
    match value { Ok(v) => ok(encode(v)), Err(e) => err(error(e)) }
}
fn option(value: Option<u64>) -> Json {
    value.map_or(Json::Null, |v| Json::obj([("some", v.into())]))
}
fn function(suffix: &str) -> &'static str { Box::leak(format!("{RUST_CRATE}::{suffix}").into_boxed_str()) }
fn heap(counts: [usize; 3]) -> Json {
    Json::obj([("allocations", counts[0].into()), ("deallocations", counts[1].into()), ("reallocations", counts[2].into())])
}
fn record(corpus: &mut Corpus, id: String, function: &'static str, state: Json, args: Json,
          value: Json, counts: [usize; 3], accesses: usize) {
    corpus.push(Record { id, function, generics: vec![], layout: None, state: state.clone(), args,
        outcome: returned(value, state), observed: Some(Json::obj([("heap", heap(counts)), ("accesses", accesses.into())])) });
}

#[cfg(feature = "metadata")]
fn error_cleanup_state(counts: [usize; 3], getter_calls: usize) -> Json {
    Json::obj([("allocations", counts[0].into()), ("deallocations", counts[1].into()),
        ("reallocations", counts[2].into()), ("getter_calls", getter_calls.into())])
}

#[cfg(feature = "metadata")]
fn owned_error_cleanup(corpus: &mut Corpus) {
    for hook in [false, true] {
        GETTER.store(0, Ordering::SeqCst);
        let (value, counts) = counted(|| if hook {
            token_api::extension::transfer_hook::get_program_id(&OwnedErrorTlv)
        } else {
            token_api::extension::permanent_delegate::get_permanent_delegate(&OwnedErrorTlv)
        });
        let getter_calls = GETTER.load(Ordering::SeqCst);
        assert!(value.is_none());
        assert_eq!(counts, [1, 1, 0], "ok must consume the returned String-backed error");
        assert_eq!(getter_calls, 1);
        let stem = if hook { "hook" } else { "delegate" };
        let path = if hook { "extension::transfer_hook::get_program_id" }
            else { "extension::permanent_delegate::get_permanent_delegate" };
        corpus.push(Record {
            id: format!("{stem}/owning_error"), function: function(path), generics: vec![], layout: None,
            state: error_cleanup_state([0; 3], 0),
            args: Json::obj([("getter", "owning_error".into())]),
            outcome: returned(Json::Null, error_cleanup_state(counts, getter_calls)), observed: None,
        });
    }
}
fn entry(tag: u16, payload: &[u8]) -> Vec<u8> {
    let mut bytes = tag.to_le_bytes().to_vec();
    bytes.extend_from_slice(&(payload.len() as u16).to_le_bytes()); bytes.extend_from_slice(payload); bytes
}
fn tlvs() -> Vec<(&'static str, Vec<u8>)> {
    vec![ ("empty", vec![]), ("realloc", vec![255]), ("sentinel", vec![0, 0]),
      ("sentinel_trailing", vec![0, 0, 255, 255]), ("short_tag", vec![7, 0]),
      ("short_length", vec![7, 0, 0]), ("past_end", vec![7, 0, 1, 0]),
      ("huge_length", vec![7, 0, 255, 255]), ("unknown", vec![28, 0, 0, 0]),
      ("unknown_after", vec![7, 0, 0, 0, 28, 0, 0, 0]),
      ("duplicates", vec![7, 0, 0, 0, 7, 0, 0, 0]),
      ("realloc_after", vec![7, 0, 0, 0, 255]),
      ("metadata", entry(19, &[7, 8])), ("immutable", entry(7, &[])),
      ("wrong_association", entry(2, &[0; 8])),
      ("delegate_zero", entry(12, &[0; 32])), ("delegate_some", entry(12, &[7; 32])),
      ("delegate_short", entry(12, &[7; 31])),
      ("hook_zero", entry(14, &[0; 64])), ("hook_some", entry(14, &[8; 64])),
      ("hook_short", entry(14, &[8; 63])),
      ("mixed_before_delegate", [entry(2, &[0; 8]), entry(12, &[9; 32])].concat()),
      ("unknown_before_delegate", [entry(28, &[]), entry(12, &[9; 32])].concat()),
      ("fee", entry(1, &[3; 108])), ("fee_short", entry(1, &[3; 107])),
    ]
}
fn mint_bytes() -> [u8; 82] { let mut b = [0; 82]; b[36..44].copy_from_slice(&12345u64.to_le_bytes()); b[44] = 9; b[45] = 1; b }
fn account_bytes() -> [u8; 165] { let mut b = [0; 165]; b[0..32].fill(3); b[32..64].fill(4); b[64..72].copy_from_slice(&987u64.to_le_bytes()); b[108] = 2; b }

fn unpack(corpus: &mut Corpus) {
    for mint in [true, false] {
        let base = if mint { mint_bytes().to_vec() } else { account_bytes().to_vec() };
        let lengths = if mint { vec![0, 81, 82, 83, 164, 165, 166, 167, 355] } else { vec![0, 164, 165, 166, 167, 355] };
        let mut inputs = Vec::new();
        for length in lengths { let mut b = base.clone(); b.resize(length, 0); if length > 165 { b[165] = if mint { 1 } else { 2 }; } inputs.push((format!("length_{length}"), b)); }
        let mut good = base.clone(); good.resize(167, 0); good[165] = if mint { 1 } else { 2 };
        for marker in [0, 1, 2, 255] { let mut b = good.clone(); b[165] = marker; inputs.push((format!("marker_{marker}"), b)); }
        if mint { let mut b = good.clone(); b[82] = 1; inputs.push(("padding".into(), b)); }
        let mut b = good.clone(); b[if mint { 45 } else { 108 }] = 0; inputs.push(("uninitialized".into(), b));
        let mut b = good.clone(); b[if mint { 45 } else { 108 }] = 255; inputs.push(("invalid_state".into(), b));
        if mint { let mut b = good; b[0] = 2; b[82] = 1; inputs.push(("base_error_before_padding".into(), b)); }
        for (id, input) in inputs {
            let (value, counts) = if mint {
                let (value, counts) = counted(|| StateWithExtensions::<Mint>::unpack(&input));
                let value = result(&value, |s| { let mut packed = [0; 82]; s.base.pack_into_slice(&mut packed);
                    Json::obj([("base", bytes(&packed)), ("tlv", bytes(s.get_tlv_data())),
                      ("origin", if input.len() == 82 { "static" } else { "input" }.into()),
                      ("offset", if input.len() == 82 { 0 } else { s.get_tlv_data().as_ptr() as usize - input.as_ptr() as usize }.into())]) });
                (value, counts)
            } else {
                let (value, counts) = counted(|| StateWithExtensions::<Account>::unpack(&input));
                let value = result(&value, |s| { let mut packed = [0; 165]; s.base.pack_into_slice(&mut packed);
                    Json::obj([("base", bytes(&packed)), ("tlv", bytes(s.get_tlv_data())),
                      ("origin", if input.len() == 165 { "static" } else { "input" }.into()),
                      ("offset", if input.len() == 165 { 0 } else { s.get_tlv_data().as_ptr() as usize - input.as_ptr() as usize }.into())]) });
                (value, counts)
            };
            record(corpus, format!("unpack/{mint}/{id}"), function("extension::StateWithExtensions::<'data, S>::unpack"),
                bytes(&input), Json::obj([("base_kind", if mint { "mint" } else { "account" }.into())]), value, counts, 0);
        }
    }
}

fn extensions(corpus: &mut Corpus) {
    if REQUIRE_TLV {
        let mut input = mint_bytes().to_vec(); input.resize(165, 0); input.extend_from_slice(&[1, 7, 0, 0, 0]);
        let state = StateWithExtensions::<Mint>::unpack(&input).unwrap();
        let (value, counts) = counted(|| state.get_tlv_data());
        let path = Box::leak(format!("<{RUST_CRATE}::extension::StateWithExtensions<'_, S> as {RUST_CRATE}::extension::BaseStateWithExtensions<S>>::get_tlv_data").into_boxed_str());
        record(corpus, "get_tlv_data/nonempty".into(), path, bytes(&input), Json::obj([("base_kind", "mint".into())]),
          Json::obj([("bytes", bytes(value)), ("offset", (value.as_ptr() as usize - input.as_ptr() as usize).into())]), counts, 0);
    }
    for (name, input) in tlvs() {
        let receiver = Tlv(&input);
        ACCESS.store(0, Ordering::SeqCst);
        let (value, counts) = counted(|| receiver.get_extension_types());
        record(corpus, format!("types/{name}"), function("extension::BaseStateWithExtensions::get_extension_types"),
          bytes(&input), Json::empty(), result(&value, |v| Json::arr(v, |e| u16::from(*e).into())), counts, ACCESS.load(Ordering::SeqCst));
        if REQUIRE_TLV {
            ACCESS.store(0, Ordering::SeqCst);
            let (value, counts) = counted(|| receiver.get_extension::<TransferFeeConfig>());
            record(corpus, format!("get_fee/{name}"), function("extension::BaseStateWithExtensions::get_extension"),
              bytes(&input), Json::obj([("tag", 1u64.into())]), result(&value, |v| Json::obj([
                ("bytes", bytes(bytemuck::bytes_of(*v))), ("offset", ((*v as *const _ as usize) - input.as_ptr() as usize).into())])), counts, ACCESS.load(Ordering::SeqCst));
            ACCESS.store(0, Ordering::SeqCst);
            let (value, counts) = counted(|| token_api::extension::permanent_delegate::get_permanent_delegate(&receiver));
            record(corpus, format!("delegate/{name}"), function("extension::permanent_delegate::get_permanent_delegate"),
              bytes(&input), Json::empty(), value.map_or(Json::Null, |p| Json::obj([("some", bytes(p.as_ref()))])), counts, ACCESS.load(Ordering::SeqCst));
            ACCESS.store(0, Ordering::SeqCst);
            let (value, counts) = counted(|| token_api::extension::transfer_hook::get_program_id(&receiver));
            record(corpus, format!("hook/{name}"), function("extension::transfer_hook::get_program_id"),
              bytes(&input), Json::empty(), value.map_or(Json::Null, |p| Json::obj([("some", bytes(p.as_ref()))])), counts, ACCESS.load(Ordering::SeqCst));
            for (length, fails) in [(0, false), (80, false), (usize::MAX, false), (80, true)] {
                ACCESS.store(0, Ordering::SeqCst); MEASURE.store(0, Ordering::SeqCst);
                let (value, counts) = counted(|| receiver.try_get_new_account_len_for_variable_len_extension(&Variable { length, error: fails }));
                assert_eq!(MEASURE.load(Ordering::SeqCst), 1);
                record(corpus, format!("new_length/{name}/{length}/{fails}"), function("extension::BaseStateWithExtensions::try_get_new_account_len_for_variable_len_extension"),
                  bytes(&input), Json::obj([("length", length.into()), ("measure_error", fails.into())]), result(&value, |v| (*v).into()), counts, ACCESS.load(Ordering::SeqCst));
            }
        }
    }
    let mut cases = vec![vec![], vec![7, 7], vec![19, 7], vec![7, 19], vec![9, 1, 9, 14, 26]];
    cases.extend((0u16..28).map(|tag| vec![tag]));
    for (index, tags) in cases.into_iter().enumerate() {
        let kinds: Vec<ExtensionType> = tags.iter().map(|tag| ExtensionType::try_from(*tag).unwrap()).collect();
        let (value, counts) = counted(|| ExtensionType::try_calculate_account_len::<Mint>(&kinds));
        record(corpus, format!("size/{index}"), function("extension::ExtensionType::try_calculate_account_len"),
          Json::Null, Json::obj([("types", Json::arr(&tags, |t| (*t).into())), ("base_length", 82u64.into())]), result(&value, |v| (*v).into()), counts, 0);
        if !REQUIRE_TLV {
            let (value, counts) = counted(|| ExtensionType::get_required_init_account_extensions(&kinds));
            record(corpus, format!("required/{index}"), function("extension::ExtensionType::get_required_init_account_extensions"),
              Json::Null, Json::obj([("types", Json::arr(&tags, |t| (*t).into()))]), Json::arr(&value, |t| u16::from(*t).into()), counts, 0);
        }
    }
}

fn fee(epoch: u64, maximum: u64, basis: u16) -> TransferFee { TransferFee { epoch: epoch.into(), maximum_fee: maximum.into(), transfer_fee_basis_points: basis.into() } }
fn fee_json(f: &TransferFee) -> Json { Json::obj([("epoch", u64::from(f.epoch).into()), ("maximum_fee", u64::from(f.maximum_fee).into()), ("transfer_fee_basis_points", u16::from(f.transfer_fee_basis_points).into())]) }
fn fees(corpus: &mut Corpus) {
    for basis in [0, 1, 250, 9999, 10000, 10001, u16::MAX] {
        for maximum in [0, 7, u64::MAX] { for amount in [0, 1, 9999, 10000, u64::MAX] {
            let receiver = fee(u64::MAX, maximum, basis);
            for inverse in [false, true] {
                if !REQUIRE_TLV { continue; }
                let (value, counts) = counted(|| if inverse { receiver.calculate_inverse_fee(amount) } else { receiver.calculate_fee(amount) });
                record(corpus, format!("fee/{inverse}/{basis}/{maximum}/{amount}"), function(if inverse { "extension::transfer_fee::TransferFee::calculate_inverse_fee" } else { "extension::transfer_fee::TransferFee::calculate_fee" }),
                  fee_json(&receiver), Json::obj([("amount", amount.into())]), option(value), counts, 0);
            }
        }}
    }
    for newer_epoch in [0, 10, u64::MAX] { for epoch in [0, 9, 10, 11, u64::MAX] {
        let config = TransferFeeConfig { older_transfer_fee: fee(u64::MAX, 3, 250), newer_transfer_fee: fee(newer_epoch, 7, 10000), ..TransferFeeConfig::default() };
        let state = bytes(bytemuck::bytes_of(&config));
        for inverse in [false, true] {
            if inverse && !REQUIRE_TLV { continue; }
            let (value, counts) = counted(|| if inverse { config.calculate_inverse_epoch_fee(epoch, 100) } else { config.calculate_epoch_fee(epoch, 100) });
            record(corpus, format!("epoch/{inverse}/{newer_epoch}/{epoch}"), function(if inverse { "extension::transfer_fee::TransferFeeConfig::calculate_inverse_epoch_fee" } else { "extension::transfer_fee::TransferFeeConfig::calculate_epoch_fee" }),
                state.clone(), Json::obj([("epoch", epoch.into()), ("amount", 100u64.into())]), option(value), counts, 0);
        }
        if REQUIRE_TLV {
            let (value, counts) = counted(|| config.get_epoch_fee(epoch));
            let field = if std::ptr::eq(value, &config.newer_transfer_fee) { "newer" } else { assert!(std::ptr::eq(value, &config.older_transfer_fee)); "older" };
            record(corpus, format!("select/{newer_epoch}/{epoch}"), function("extension::transfer_fee::TransferFeeConfig::get_epoch_fee"), state,
              Json::obj([("epoch", epoch.into())]), Json::obj([("field", field.into()), ("value", fee_json(value))]), counts, 0);
        }
    }}
    if REQUIRE_TLV {
        // The same wrapper changes from a zero-fee success before activation
        // to the checked failure of the selected record or zero shortcut at equality.
        for (case, basis, maximum, amount) in [
            ("zero_excess_rate", 10001, 0, 0),
            ("positive_excess_rate", 10001, 0, 1),
            ("full_rate_overflow", 10000, 1, u64::MAX),
            ("raw_fee_overflow", 10001, 0, u64::MAX),
        ] {
            let config = TransferFeeConfig {
                older_transfer_fee: fee(u64::MAX, 0, 0),
                newer_transfer_fee: fee(10, maximum, basis),
                ..TransferFeeConfig::default()
            };
            let state = bytes(bytemuck::bytes_of(&config));
            for epoch in [9, 10] {
                for inverse in [false, true] {
                    let (value, counts) = counted(|| {
                        if inverse {
                            config.calculate_inverse_epoch_fee(epoch, amount)
                        } else {
                            config.calculate_epoch_fee(epoch, amount)
                        }
                    });
                    record(corpus, format!("epoch_boundary/{case}/{inverse}/{epoch}"),
                        function(if inverse {
                            "extension::transfer_fee::TransferFeeConfig::calculate_inverse_epoch_fee"
                        } else {
                            "extension::transfer_fee::TransferFeeConfig::calculate_epoch_fee"
                        }), state.clone(), Json::obj([("epoch", epoch.into()), ("amount", amount.into())]),
                        option(value), counts, 0);
                }
            }
        }
    }
}

fn state(corpus: &mut Corpus) {
    if REQUIRE_TLV { for flag in [AccountState::Uninitialized, AccountState::Initialized, AccountState::Frozen] {
        let account = Account { state: flag, ..Account::default() };
        let mut packed = [0; 165]; account.pack_into_slice(&mut packed);
        let (value, counts) = counted(|| account.is_frozen());
        record(corpus, format!("is_frozen/{}", flag as u8), function("state::Account::is_frozen"), bytes(&packed), Json::empty(), value.into(), counts, 0);
    }}
    if CLONE { for supply in [0, 1, u64::MAX] {
        let mint = Mint { supply, decimals: 9, is_initialized: true, ..Mint::default() };
        let mut packed = [0; 82]; mint.pack_into_slice(&mut packed);
        let (value, counts) = counted(|| mint.clone()); let mut after = [0; 82]; value.pack_into_slice(&mut after);
        let path = Box::leak(format!("<{RUST_CRATE}::state::Mint as core::clone::Clone>::clone").into_boxed_str());
        record(corpus, format!("clone/{supply}"), path, bytes(&packed), Json::empty(), bytes(&after), counts, 0);
    }}
    #[cfg(feature = "metadata")]
    {
        let (value, counts) = counted(metadata_api::state::TokenMetadata::default);
        let raw_authority: &[u8] = bytemuck::bytes_of(&value.update_authority);
        let out = Json::obj([("authority", bytes(raw_authority)), ("mint", bytes(value.mint.as_ref())),
          ("name", value.name.clone().into()), ("symbol", value.symbol.clone().into()), ("uri", value.uri.clone().into()),
          ("additional", Json::arr(&value.additional_metadata, |(a, b)| Json::arr([a, b], |s| s.clone().into()))),
          ("capacities", Json::arr([value.name.capacity(), value.symbol.capacity(), value.uri.capacity(), value.additional_metadata.capacity()], Json::from))]);
        record(corpus, "metadata/default".into(), "<spl_token_metadata_interface::state::TokenMetadata as core::default::Default>::default", Json::Null, Json::empty(), out, counts, 0);
    }
}

pub fn main() {
    conformance_recorder::init();
    #[cfg(feature = "metadata")]
    let crates = vec![(PACKAGE, VERSION), ("spl-token-metadata-interface", "0.7.0")];
    #[cfg(not(feature = "metadata"))]
    let crates = vec![(PACKAGE, VERSION)];
    let mut corpus = Corpus::new(CORPUS, &crates);
    if UNPACK { unpack(&mut corpus); }
    if LEGACY { extensions(&mut corpus); fees(&mut corpus); }
    #[cfg(feature = "metadata")]
    owned_error_cleanup(&mut corpus);
    state(&mut corpus);
    corpus.write(&conformance_recorder::out_dir()).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn packed_fee_source_bytes_and_offsets() {
        use std::mem::{align_of, offset_of, size_of};
        assert_eq!((size_of::<TransferFee>(), align_of::<TransferFee>()), (18, 1));
        assert_eq!((offset_of!(TransferFee, epoch), offset_of!(TransferFee, maximum_fee),
            offset_of!(TransferFee, transfer_fee_basis_points)), (0, 8, 16));
        let input = fee(0x0807_0605_0403_0201, 0x100f_0e0d_0c0b_0a09, 0x1211);
        assert_eq!(bytemuck::bytes_of(&input), &(1u8..=18).collect::<Vec<_>>());
        assert_eq!((size_of::<TransferFeeConfig>(), align_of::<TransferFeeConfig>()), (108, 1));
        assert_eq!((offset_of!(TransferFeeConfig, transfer_fee_config_authority),
            offset_of!(TransferFeeConfig, withdraw_withheld_authority),
            offset_of!(TransferFeeConfig, withheld_amount),
            offset_of!(TransferFeeConfig, older_transfer_fee),
            offset_of!(TransferFeeConfig, newer_transfer_fee)), (0, 32, 64, 72, 90));
        let config = TransferFeeConfig { older_transfer_fee: input,
            newer_transfer_fee: fee(9, 0, u16::MAX), ..TransferFeeConfig::default() };
        assert_eq!(&bytemuck::bytes_of(&config)[72..90], bytemuck::bytes_of(&input));
        assert_eq!(config.get_epoch_fee(8) as *const _ as usize,
            &config as *const _ as usize + 72);
        assert_eq!(config.get_epoch_fee(9) as *const _ as usize,
            &config as *const _ as usize + 90);
    }
    #[test]
    fn copied_account_layout_is_distinct_from_pack() {
        use std::mem::{align_of, offset_of, size_of};
        assert_eq!(Account::LEN, 165);
        assert_eq!((size_of::<Account>(), align_of::<Account>()), (176, 8));
        assert_eq!((offset_of!(Account, mint), offset_of!(Account, owner),
            offset_of!(Account, amount), offset_of!(Account, delegate),
            offset_of!(Account, state), offset_of!(Account, is_native),
            offset_of!(Account, delegated_amount), offset_of!(Account, close_authority)),
            (0, 32, 64, 72, 108, 112, 128, 136));
    }
    #[test]
    #[cfg(feature = "metadata")]
    fn default_metadata_uses_exact_empty_containers() {
        use std::mem::{align_of, offset_of, size_of};
        use metadata_api::state::TokenMetadata;
        let value = TokenMetadata::default();
        assert_eq!((size_of::<TokenMetadata>(), align_of::<TokenMetadata>()), (160, 8));
        assert_eq!((offset_of!(TokenMetadata, update_authority), offset_of!(TokenMetadata, mint),
            offset_of!(TokenMetadata, name), offset_of!(TokenMetadata, symbol),
            offset_of!(TokenMetadata, uri), offset_of!(TokenMetadata, additional_metadata)),
            (96, 128, 0, 24, 48, 72));
        for text in [&value.name, &value.symbol, &value.uri] {
            assert_eq!((text.len(), text.capacity(), text.as_ptr() as usize), (0, 0, 1));
        }
        assert_eq!((value.additional_metadata.len(), value.additional_metadata.capacity(),
            value.additional_metadata.as_ptr() as usize), (0, 0, 8));
    }
    #[test]
    fn narrow_before_cap_and_zero_inverse() {
        let f = fee(0, 0, u16::MAX);
        assert_eq!(f.calculate_fee(u64::MAX), None);
        assert_eq!(f.calculate_inverse_fee(0), Some(0));
        assert_eq!(f.calculate_inverse_fee(1), None);
    }
    #[test]
    fn old_push_precedes_invalid_payload() {
        if !LEGACY { return; }
        assert!(crate::allocation::aborts_on_next_allocation(|| { let _ = Tlv(&[7, 0, 1, 0]).get_extension_types(); }));
        let (result, count) = counted(|| Tlv(&[7, 0, 1, 0]).get_extension_types());
        assert_eq!(result, Err(ProgramError::InvalidAccountData));
        assert_eq!(count, [1, 1, 0]);
    }
    #[test]
    fn dedup_allocation_precedes_variable_size_error() {
        if !LEGACY { return; }
        assert!(crate::allocation::aborts_on_next_allocation(|| {
            let _ = ExtensionType::try_calculate_account_len::<Mint>(&[ExtensionType::TokenMetadata, ExtensionType::ImmutableOwner]);
        }));
    }
    #[test]
    fn padded_mint_allocates_and_version_boundary_is_observed() {
        if !UNPACK { return; }
        let mut input = [0; 167]; input[..82].copy_from_slice(&mint_bytes()); input[165] = 1;
        assert!(crate::allocation::aborts_on_next_allocation(|| { let _ = StateWithExtensions::<Mint>::unpack(&input); }));
        let (boundary, counts) = counted(|| StateWithExtensions::<Mint>::unpack(&input[..166]));
        assert_eq!(boundary.is_ok(), !REQUIRE_TLV);
        assert_eq!(counts, if REQUIRE_TLV { [0, 0, 0] } else { [1, 1, 0] });
    }
}
