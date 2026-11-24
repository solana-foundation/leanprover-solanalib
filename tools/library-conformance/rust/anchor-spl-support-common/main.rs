use anchor_lang::{AccountDeserialize, context::CpiContext};
use anchor_lang::solana_program::{account_info::AccountInfo, instruction::Instruction,
    program_error::ProgramError, program_pack::Pack, pubkey::Pubkey};
use conformance_recorder::{Corpus, Json, Record, bytes, returned, unwound};
use std::{cell::RefCell, path::Path, rc::Rc, panic::{catch_unwind, AssertUnwindSafe}};

fn key(number: u8) -> Pubkey { let mut bytes = [0; 32]; bytes[31] = number; Pubkey::new_from_array(bytes) }
fn number(key: &Pubkey) -> u8 { key.to_bytes()[31] }
fn account(number: u8) -> AccountInfo<'static> {
    let key = Box::leak(Box::new(key(number)));
    let owner = Box::leak(Box::new(Pubkey::default()));
    let balance = Box::leak(Box::new(100u64 + number as u64));
    let data = Box::leak(vec![number, 0, 255].into_boxed_slice());
    #[cfg(feature = "legacy")]
    { AccountInfo::new(key, false, true, balance, data, owner, false, 0) }
    #[cfg(not(feature = "legacy"))]
    { AccountInfo::new(key, false, true, balance, data, owner, false) }
}
fn counts(accounts: &[AccountInfo<'_>]) -> Json {
    Json::arr(accounts, |info| Json::obj([("account", number(info.key).into()),
        ("lamports", Rc::strong_count(&info.lamports).into()), ("data", Rc::strong_count(&info.data).into())]))
}
fn account_json(info: &AccountInfo<'_>) -> Json {
    #[cfg(feature = "legacy")]
    let abi_word = info.rent_epoch;
    #[cfg(not(feature = "legacy"))]
    #[allow(deprecated)]
    let abi_word = info._unused;
    Json::obj([("key", bytes(&info.key.to_bytes())), ("owner", bytes(&info.owner.to_bytes())),
        ("signer", info.is_signer.into()), ("writable", info.is_writable.into()),
        ("executable", info.executable.into()), ("abi_word", abi_word.into()),
        ("lamports_alias", number(info.key).into()), ("data_alias", number(info.key).into()),
        ("lamports_count", Rc::strong_count(&info.lamports).into()),
        ("data_count", Rc::strong_count(&info.data).into())])
}
fn instruction_json(ix: &Instruction) -> Json {
    Json::obj([("program_id", bytes(&ix.program_id.to_bytes())),
        ("metas", Json::arr(&ix.accounts, |meta| Json::obj([("key", bytes(&meta.pubkey.to_bytes())),
            ("signer", meta.is_signer.into()), ("writable", meta.is_writable.into())]))),
        ("data", bytes(&ix.data))])
}
fn seeds_json(seeds: &[&[&[u8]]]) -> Json { Json::arr(seeds, |signer| Json::arr(*signer, |seed| bytes(seed))) }
static SEEDS: &[&[&[u8]]] = &[&[], &[&[1, 2], &[]], &[&[255]]];

// This is the complete signature mock. It never calls invoke_signed, invoke,
// a syscall wrapper, a runtime, or an instruction interpreter.
mod whole_signature {
    use super::*;
    thread_local! {
        static SCRIPT: RefCell<&'static str> = const { RefCell::new("ok") };
        static CALLS: RefCell<Vec<Json>> = const { RefCell::new(Vec::new()) };
        static EFFECT: RefCell<u64> = const { RefCell::new(0) };
    }
    pub fn reset(script: &'static str) { SCRIPT.with(|s| *s.borrow_mut() = script); CALLS.with(|s| s.borrow_mut().clear()); EFFECT.with(|e| *e.borrow_mut() = 0); }
    pub fn observed() -> (Vec<Json>, u64) { (CALLS.with(|s| s.borrow().clone()), EFFECT.with(|e| *e.borrow())) }
    pub fn invoke_signed(ix: &Instruction, accounts: &[AccountInfo<'_>], seeds: &[&[&[u8]]]) -> Result<(), ProgramError> {
        CALLS.with(|calls| calls.borrow_mut().push(Json::obj([("instruction", instruction_json(ix)),
            ("accounts", Json::arr(accounts, account_json)), ("signers", seeds_json(seeds))])));
        EFFECT.with(|effect| *effect.borrow_mut() += 1);
        match SCRIPT.with(|s| *s.borrow()) {
            "ok" => Ok(()),
            "custom" => Err(ProgramError::Custom(31)),
            #[cfg(feature = "legacy")]
            "borsh" => Err(ProgramError::BorshIoError("owned Borsh error".into())),
            "unwind" => panic!("opaque unwind"),
            _ => unreachable!(),
        }
    }
}

// PDA is a separate scripted external signature. The actual SDK constructor
// supplies the real seeds and program ID. It receives a fixed test address;
// this does not test curve arithmetic or a runtime implementation.
#[unsafe(no_mangle)]
unsafe extern "C" fn sol_try_find_program_address(_seeds: *const u8, _count: u64,
    _program: *const u8, output: *mut u8, bump: *mut u8) -> u64 {
    unsafe { std::ptr::copy_nonoverlapping(key(77).to_bytes().as_ptr(), output, 32); *bump = 254; }
    0
}

fn context<A>(accounts: A, base: &[AccountInfo<'static>]) -> CpiContext<'static, 'static, 'static, 'static, A>
where A: anchor_lang::ToAccountMetas + anchor_lang::ToAccountInfos<'static> {
    #[cfg(feature = "legacy")]
    let program = base[9].clone();
    #[cfg(not(feature = "legacy"))]
    let program = *base[9].key;
    CpiContext::new_with_signer(program, accounts, SEEDS)
        .with_remaining_accounts(vec![base[7].clone(), base[7].clone(), base[8].clone()])
}

#[cfg(feature = "metadata")]
fn metadata_data() -> anchor_spl::metadata::mpl_token_metadata::types::DataV2 {
    use anchor_spl::metadata::mpl_token_metadata::types::*;
    DataV2 { name: "Méta".into(), symbol: "SPL".into(), uri: "https://example.invalid/metadata".into(),
        seller_fee_basis_points: 375,
        creators: Some(vec![Creator { address: key(70), verified: true, share: 60 }, Creator { address: key(71), verified: false, share: 40 }]),
        collection: Some(Collection { verified: true, key: key(66) }),
        uses: Some(Uses { use_method: UseMethod::Multiple, remaining: 8, total: 13 }) }
}
fn invocation(corpus: &mut Corpus, operation: &'static str, script: &'static str, custodian: bool) {
    let base: Vec<_> = [1, 2, 3, 4, 5, 6, 7, 40, 41, 50].into_iter().map(account).collect();
    let run: Box<dyn FnOnce() -> anchor_lang::Result<()>> = match operation {
        #[cfg(feature = "associated")]
        "associated_create" | "associated_idempotent" => {
            use anchor_spl::associated_token::Create;
            let ctx = context(Create { payer: base[0].clone(), associated_token: base[1].clone(),
                authority: base[2].clone(), mint: base[3].clone(), system_program: base[4].clone(), token_program: base[5].clone() }, &base);
            #[cfg(any(feature = "v0321", feature = "v112"))]
            if operation == "associated_create" { Box::new(move || projected_associated_token::create(ctx)) } else {
                #[cfg(feature = "v112")]
                { Box::new(move || projected_associated_token::create_idempotent(ctx)) }
                #[cfg(not(feature = "v112"))]
                { unreachable!() }
            }
            #[cfg(feature = "v102")]
            { Box::new(move || projected_associated_token::create_idempotent(ctx)) }
        }
        #[cfg(feature = "memo")]
        "memo" => {
            let ctx = context(anchor_spl::memo::BuildMemo {}, &base);
            Box::new(move || projected_memo::build_memo(ctx, &[0, 255, 65, 0]))
        }
        #[cfg(feature = "metadata")]
        "metadata" => {
            use anchor_spl::metadata::{CreateMetadataAccountsV3, mpl_token_metadata::types::CollectionDetails};
            let ctx = context(CreateMetadataAccountsV3 { metadata: base[0].clone(), mint: base[1].clone(),
                mint_authority: base[2].clone(), payer: base[3].clone(), update_authority: base[4].clone(),
                system_program: base[5].clone(), rent: base[6].clone() }, &base);
            Box::new(move || projected_metadata::create_metadata_accounts_v3(ctx, metadata_data(), true, false,
                Some(CollectionDetails::V2 { padding: [1, 2, 3, 4, 5, 6, 7, 8] })))
        }
        #[cfg(feature = "v027")]
        "deactivate" => {
            let ctx = context(anchor_spl::stake::DeactivateStake { stake: base[0].clone(), staker: base[1].clone(), clock: base[2].clone() }, &base);
            Box::new(move || projected_stake::deactivate_stake(ctx))
        }
        #[cfg(feature = "v027")]
        "withdraw" => {
            let ctx = context(anchor_spl::stake::Withdraw { stake: base[0].clone(), withdrawer: base[1].clone(), to: base[2].clone(), clock: base[3].clone(), stake_history: base[4].clone() }, &base);
            let extra = custodian.then(|| base[5].clone());
            Box::new(move || projected_stake::withdraw(ctx, 42, extra))
        }
        _ => panic!("unsupported operation {operation}"),
    };
    let before = Json::obj([("counts", counts(&base)), ("effect", 0u64.into())]);
    whole_signature::reset(script);
    let result = catch_unwind(AssertUnwindSafe(run));
    let (calls, effect) = whole_signature::observed();
    let after = Json::obj([("counts", counts(&base)), ("effect", effect.into()), ("calls", Json::Arr(calls))]);
    let outcome = match result {
        Ok(Ok(())) => returned(Json::obj([("tag", "ok".into())]), after),
        Ok(Err(anchor_lang::error::Error::ProgramError(error))) => {
            let result = match error.program_error {
                ProgramError::Custom(code) => Json::obj([("kind", "custom".into()), ("value", code.into())]),
                #[cfg(feature = "legacy")]
                ProgramError::BorshIoError(ref value) => Json::obj([("kind", "borsh".into()), ("value", value.clone().into())]),
                _ => panic!("unexpected program error"),
            };
            assert!(error.error_origin.is_none() && error.compared_values.is_none());
            returned(Json::obj([("tag", "error".into()), ("program", result)]), after)
        }
        Ok(Err(_)) => panic!("unexpected AnchorError"),
        Err(_) => unwound("opaque unwind".into(), after),
    };
    let function = match operation {
        "associated_create" => "anchor_spl::associated_token::create",
        "associated_idempotent" => "anchor_spl::associated_token::create_idempotent",
        "memo" => "anchor_spl::memo::build_memo",
        "metadata" => "anchor_spl::metadata::create_metadata_accounts_v3",
        "deactivate" => "anchor_spl::stake::deactivate_stake",
        "withdraw" => "anchor_spl::stake::withdraw",
        _ => unreachable!(),
    };
    corpus.push(Record { id: format!("{operation}/{script}/custodian-{custodian}"), function, generics: vec![], layout: None,
        state: before, args: Json::obj([("operation", operation.into()), ("script", script.into()),
            ("custodian", custodian.into()), ("signers", seeds_json(SEEDS))]), outcome,
        observed: Some(Json::obj([("scope", "exact-source projected wrapper with whole-signature mock".into())])) });
}

fn token_bytes(frozen: bool, options: bool) -> Vec<u8> {
    let mut out = vec![0; 165];
    out[..32].copy_from_slice(&key(1).to_bytes()); out[32..64].copy_from_slice(&key(2).to_bytes());
    out[64..72].copy_from_slice(&42u64.to_le_bytes()); out[108] = if frozen { 2 } else { 1 };
    out[121..129].copy_from_slice(&7u64.to_le_bytes());
    if options {
        out[72..76].copy_from_slice(&1u32.to_le_bytes()); out[76..108].copy_from_slice(&key(3).to_bytes());
        out[109..113].copy_from_slice(&1u32.to_le_bytes()); out[113..121].copy_from_slice(&9u64.to_le_bytes());
        out[129..133].copy_from_slice(&1u32.to_le_bytes()); out[133..165].copy_from_slice(&key(4).to_bytes());
    }
    out
}
fn token_values(corpus: &mut Corpus) {
    for frozen in [false, true] { for options in [false, true] {
        let input = token_bytes(frozen, options);
        #[cfg(all(feature = "token", not(feature = "v029")))]
        {
            let wrapper = anchor_spl::token::TokenAccount::try_deserialize_unchecked(&mut input.as_slice()).unwrap();
            let reference = std::ops::Deref::deref(&wrapper);
            let mut encoded = vec![0; 165]; reference.pack_into_slice(&mut encoded);
            let same = (&wrapper as *const _ as usize) == (reference as *const _ as usize);
            value_record(corpus, format!("token/{frozen}/{options}"), "<anchor_spl::token::TokenAccount as core::ops::deref::Deref>::deref",
                bytes(&input), bytes(&encoded), Some(same), Some((std::mem::size_of_val(&wrapper), std::mem::align_of_val(&wrapper))));
        }
        #[cfg(feature = "interface")]
        {
            let wrapper = anchor_spl::token_interface::TokenAccount::try_deserialize_unchecked(&mut input.as_slice()).unwrap();
            let reference = std::ops::Deref::deref(&wrapper);
            let mut encoded = vec![0; 165]; reference.pack_into_slice(&mut encoded);
            let same = (&wrapper as *const _ as usize) == (reference as *const _ as usize);
            value_record(corpus, format!("interface/{frozen}/{options}"), "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref",
                bytes(&input), bytes(&encoded), Some(same), Some((std::mem::size_of_val(&wrapper), std::mem::align_of_val(&wrapper))));
        }
    }}
}
fn value_record(corpus: &mut Corpus, id: String, function: &'static str, input: Json, value: Json, same: Option<bool>, layout: Option<(usize,usize)>) {
    corpus.push(Record { id, function, generics: vec![], layout: layout.map(|(size,align)| Json::obj([("size", size.into()), ("align", align.into())])),
        state: Json::Null, args: input, outcome: returned(Json::obj([("value", value), ("same_parent", same.map(Json::from).unwrap_or(Json::Null))]), Json::Null), observed: None });
}
#[cfg(feature = "v027")]
fn stake_values(corpus: &mut Corpus) {
    use anchor_lang::solana_program::stake::state::{StakeState, Meta, Authorized, Lockup, Stake, Delegation};
    use borsh::BorshSerialize;
    let meta = Meta { rent_exempt_reserve: 40, authorized: Authorized { staker: key(1), withdrawer: key(2) },
        lockup: Lockup { unix_timestamp: -1, epoch: 5, custodian: key(3) } };
    let active = Stake { delegation: Delegation { voter_pubkey: key(4), stake: 25, activation_epoch: 6, deactivation_epoch: 9,
        warmup_cooldown_rate: f64::from_bits(0x3fd0000000000000) }, credits_observed: 17 };
    for (index, state) in [StakeState::Uninitialized, StakeState::Initialized(meta), StakeState::Stake(meta, active), StakeState::RewardsPool].into_iter().enumerate() {
        let input = state.try_to_vec().unwrap();
        let wrapper = anchor_spl::stake::StakeAccount::try_deserialize_unchecked(&mut input.as_slice()).unwrap();
        let reference = std::ops::Deref::deref(&wrapper);
        value_record(corpus, format!("stake/{index}"), "<anchor_spl::stake::StakeAccount as core::ops::deref::Deref>::deref", bytes(&input), bytes(&reference.try_to_vec().unwrap()),
            Some((&wrapper as *const _ as usize) == (reference as *const _ as usize)), Some((std::mem::size_of_val(&wrapper),std::mem::align_of_val(&wrapper))));
    }
}
fn ids(corpus: &mut Corpus) {
    #[cfg(any(feature = "v0321", feature = "v102"))]
    #[cfg(feature = "token")]
    value_record(corpus, "token-id".into(), "<anchor_spl::token::Token as anchor_lang::Id>::id", Json::Null,
        bytes(&<anchor_spl::token::Token as anchor_lang::Id>::id().to_bytes()), None, None);
    #[cfg(feature = "v102")]
    value_record(corpus, "token2022-id".into(), "<anchor_spl::token_2022::Token2022 as anchor_lang::Id>::id", Json::Null,
        bytes(&<anchor_spl::token_2022::Token2022 as anchor_lang::Id>::id().to_bytes()), None, None);
    #[cfg(feature = "v029")]
    {
        let first = <anchor_spl::token_interface::TokenInterface as anchor_lang::Ids>::ids();
        let second = <anchor_spl::token_interface::TokenInterface as anchor_lang::Ids>::ids();
        value_record(corpus, "interface-ids".into(), "<anchor_spl::token_interface::TokenInterface as anchor_lang::Ids>::ids", Json::Null,
            Json::arr(first, |id| bytes(&id.to_bytes())), Some(first.as_ptr() == second.as_ptr()), None);
    }
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut corpus = Corpus::new(CORPUS, &[("anchor-spl", VERSION), ("anchor-lang", VERSION)]);
    token_values(&mut corpus); ids(&mut corpus);
    #[cfg(feature = "v027")]
    stake_values(&mut corpus);
    let operations: Vec<&'static str> = vec![
        #[cfg(any(feature = "v0321", feature = "v112"))] #[cfg(feature = "associated")] "associated_create",
        #[cfg(any(feature = "v102", feature = "v112"))] "associated_idempotent",
        #[cfg(feature = "memo")] "memo",
        #[cfg(feature = "metadata")] "metadata",
        #[cfg(feature = "v027")] "deactivate",
        #[cfg(feature = "v027")] "withdraw",
    ];
    for operation in operations { for script in ["ok", "custom", "unwind"] {
        invocation(&mut corpus, operation, script, true);
        if operation == "withdraw" { invocation(&mut corpus, operation, script, false); }
    }
        #[cfg(feature = "legacy")]
        invocation(&mut corpus, operation, "borsh", true);
    }
    corpus.write(Path::new(&std::env::args().nth(1).expect("output directory"))).unwrap();
}
