//! Native calls at the reviewed legacy SDK and dependency versions.
#![allow(deprecated)]
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use solana_program::{clock::Clock, instruction::Instruction, program_error::ProgramError,
    program_pack::{IsInitialized, Pack, Sealed}, pubkey::Pubkey,
    stake::{instruction as ix, state::{Authorized, Delegation, Lockup, Meta, Stake, StakeAuthorize, StakeState}}};
use std::cell::RefCell;

fn key(n: u8) -> Pubkey { Pubkey::new_from_array([n; 32]) }
fn pk(p: &Pubkey) -> Json { rec::bytes(p.as_ref()) }
fn option<T>(x: Option<T>, f: impl Fn(T) -> Json) -> Json { x.map(f).unwrap_or(Json::Null) }
fn lockup(x: &Lockup) -> Json { Json::obj([
    ("unix_timestamp", x.unix_timestamp.into()), ("epoch", x.epoch.into()), ("custodian", pk(&x.custodian))]) }
fn authorized(x: &Authorized) -> Json { Json::obj([("staker", pk(&x.staker)), ("withdrawer", pk(&x.withdrawer))]) }
fn metadata(x: &Meta) -> Json { Json::obj([("rent_exempt_reserve", x.rent_exempt_reserve.into()),
    ("authorized", authorized(&x.authorized)), ("lockup", lockup(&x.lockup))]) }
fn delegation(x: &Delegation) -> Json { Json::obj([("voter_pubkey", pk(&x.voter_pubkey)),
    ("stake", x.stake.into()), ("activation_epoch", x.activation_epoch.into()),
    ("deactivation_epoch", x.deactivation_epoch.into()),
    ("warmup_cooldown_rate", format!("{:016x}", x.warmup_cooldown_rate.to_bits()).into())]) }
fn stake(x: &Stake) -> Json { Json::obj([("delegation", delegation(&x.delegation)), ("credits_observed", x.credits_observed.into())]) }
fn state(x: &StakeState) -> Json { match x {
    StakeState::Uninitialized => Json::obj([("tag", "uninitialized".into())]),
    StakeState::RewardsPool => Json::obj([("tag", "rewards_pool".into())]),
    StakeState::Initialized(m) => Json::obj([("tag", "initialized".into()), ("meta", metadata(m))]),
    StakeState::Stake(m, s) => Json::obj([("tag", "stake".into()), ("meta", metadata(m)), ("stake", stake(s))]),
} }
fn instruction(x: &Instruction) -> Json { Json::obj([("program_id", pk(&x.program_id)),
    ("accounts", Json::arr(&x.accounts, |a| Json::obj([("pubkey", pk(&a.pubkey)),
        ("is_signer", a.is_signer.into()), ("is_writable", a.is_writable.into())]))),
    ("data", rec::bytes(&x.data))]) }
fn record(c: &mut Corpus, id: String, function: &'static str, args: Json, result: Json) {
    c.push(Record { id, function, generics: vec![], layout: None, state: Json::Null,
        args, outcome: rec::returned(result, Json::Null), observed: None });
}
fn getters(c: &mut Corpus) {
    record(c, "lockup-default".into(), "<solana_program::stake::state::Lockup as core::default::Default>::default",
        Json::Null, lockup(&Lockup::default()));
    for (i, (timestamp, epoch)) in [(5, 9), (i64::MIN, 0), (i64::MAX, u64::MAX)].into_iter().enumerate() {
        let l = Lockup { unix_timestamp: timestamp, epoch, custodian: key(7) };
        for (j, (now, current_epoch)) in [(timestamp.saturating_sub(1), epoch), (timestamp, epoch),
            (timestamp.saturating_add(1), epoch), (timestamp, epoch.saturating_sub(1)),
            (timestamp, epoch.saturating_add(1))].into_iter().enumerate() {
            for (k, custodian) in [None, Some(key(7)), Some(key(8))].into_iter().enumerate() {
                let clock = Clock { unix_timestamp: now, epoch: current_epoch, ..Clock::default() };
                record(c, format!("lockup-{i}-{j}-{k}"), "solana_program::stake::state::Lockup::is_in_force",
                    Json::obj([("lockup", lockup(&l)), ("clock", Json::obj([("unix_timestamp", now.into()),
                        ("epoch", current_epoch.into())])), ("custodian", option(custodian.as_ref(), pk))]),
                    l.is_in_force(&clock, custodian.as_ref()).into());
            }
        }
    }
    let m = Meta { rent_exempt_reserve: u64::MAX, authorized: Authorized { staker: key(1), withdrawer: key(2) },
        lockup: Lockup { unix_timestamp: -19, epoch: 11, custodian: key(3) } };
    let mut states = vec![StakeState::Uninitialized, StakeState::RewardsPool, StakeState::Initialized(m)];
    for bits in [0, 0x8000000000000000, 0x3fd0000000000000, 0x7ff8000000000001, 0x7ff0000000000000] {
        states.push(StakeState::Stake(m, Stake { delegation: Delegation { voter_pubkey: key(4), stake: u64::MAX,
            activation_epoch: 5, deactivation_epoch: u64::MAX, warmup_cooldown_rate: f64::from_bits(bits) }, credits_observed: 123 }));
    }
    for (i, s) in states.into_iter().enumerate() {
        record(c, format!("delegation-{i}"), "solana_program::stake::state::StakeState::delegation", state(&s), option(s.delegation(), |d| delegation(&d)));
        record(c, format!("lockup-get-{i}"), "solana_program::stake::state::StakeState::lockup", state(&s), option(s.lockup(), |l| lockup(&l)));
        record(c, format!("meta-{i}"), "solana_program::stake::state::StakeState::meta", state(&s), option(s.meta(), |m| metadata(&m)));
    }
}
fn builders(c: &mut Corpus) {
    for base in [0u8, 1, 254] {
        let [s, a, d, new] = [key(base), key(base.wrapping_add(1)), key(base.wrapping_add(2)), key(base.wrapping_add(3))];
        let auth = Authorized { staker: a, withdrawer: d };
        let l = Lockup { unix_timestamp: -17, epoch: u64::MAX, custodian: new };
        record(c, format!("initialize-{base}"), "solana_program::stake::instruction::initialize",
            Json::obj([("stake", pk(&s)), ("authorized", authorized(&auth)), ("lockup", lockup(&l))]), instruction(&ix::initialize(&s, &auth, &l)));
        record(c, format!("delegate-{base}"), "solana_program::stake::instruction::delegate_stake",
            Json::obj([("stake", pk(&s)), ("authority", pk(&a)), ("vote", pk(&d))]), instruction(&ix::delegate_stake(&s, &a, &d)));
        record(c, format!("merge-{base}"), "solana_program::stake::instruction::merge",
            Json::obj([("destination", pk(&d)), ("source", pk(&s)), ("authority", pk(&a))]), Json::arr(ix::merge(&d, &s, &a), |v| instruction(&v)));
        for amount in [0, 1, u64::MAX] {
            record(c, format!("split-{base}-{amount}"), "solana_program::stake::instruction::split",
                Json::obj([("stake", pk(&s)), ("authority", pk(&a)), ("lamports", amount.into()), ("destination", pk(&d))]),
                Json::arr(ix::split(&s, &a, amount, &d), |v| instruction(&v)));
        }
        for (role, role_name) in [(StakeAuthorize::Staker, "staker"), (StakeAuthorize::Withdrawer, "withdrawer")] {
            for present in [false, true] {
                let custodian = present.then_some(s);
                record(c, format!("authorize-{base}-{role_name}-{present}"), "solana_program::stake::instruction::authorize",
                    Json::obj([("stake", pk(&s)), ("authority", pk(&a)), ("new_authority", pk(&new)),
                        ("role", role_name.into()), ("custodian", option(custodian.as_ref(), pk))]),
                    instruction(&ix::authorize(&s, &a, &new, role, custodian.as_ref())));
            }
        }
        for mask in 0..8u8 {
            let args = ix::LockupArgs { unix_timestamp: (mask & 1 != 0).then_some(i64::MIN),
                epoch: (mask & 2 != 0).then_some(u64::MAX), custodian: (mask & 4 != 0).then_some(new) };
            record(c, format!("set-lockup-{base}-{mask}"), "solana_program::stake::instruction::set_lockup",
                Json::obj([("stake", pk(&s)), ("custodian", pk(&a)), ("lockup", Json::obj([
                    ("unix_timestamp", option(args.unix_timestamp, Json::from)), ("epoch", option(args.epoch, Json::from)),
                    ("custodian", option(args.custodian.as_ref(), pk))]))]), instruction(&ix::set_lockup(&s, &args, &a)));
        }
    }
}
thread_local! { static EVENTS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) }; }
fn event(s: &str) { EVENTS.with(|e| e.borrow_mut().push(s.into())); }
fn events() -> Json { EVENTS.with(|e| Json::arr(e.borrow().iter(), |s| s.clone().into())) }
struct Probe(u8);
impl Sealed for Probe {}
impl IsInitialized for Probe { fn is_initialized(&self) -> bool {
    event("query"); match self.0 { 3 | 6 => panic!("query"), 5 => std::process::abort(), _ => self.0 == 1 }
} }
impl Drop for Probe { fn drop(&mut self) { event("drop"); if self.0 == 4 || self.0 == 6 { panic!("drop") } } }
impl Pack for Probe {
    const LEN: usize = 1;
    fn unpack_from_slice(src: &[u8]) -> Result<Self, ProgramError> {
        event("decode"); if src[0] == 2 { Err(ProgramError::BorshIoError("codec-error".into())) } else { Ok(Self(src[0])) }
    }
    fn pack_into_slice(&self, _: &mut [u8]) { unreachable!() }
}
struct OverrideProbe(Probe);
impl Sealed for OverrideProbe {}
impl IsInitialized for OverrideProbe { fn is_initialized(&self) -> bool { self.0.is_initialized() } }
impl Pack for OverrideProbe {
    const LEN: usize = 1;
    fn unpack_from_slice(_: &[u8]) -> Result<Self, ProgramError> { panic!("unselected") }
    fn unpack_unchecked(_: &[u8]) -> Result<Self, ProgramError> { event("override"); Ok(Self(Probe(1))) }
    fn pack_into_slice(&self, _: &mut [u8]) { unreachable!() }
}
fn pack(c: &mut Corpus) {
    for (i, bytes) in [vec![], vec![0], vec![1], vec![2], vec![3], vec![4], vec![5], vec![1, 9]].into_iter().enumerate() {
        for override_method in [false, true] {
            let outcome = shim::case(&Script::default(), || {
                EVENTS.with(|e| e.borrow_mut().clear());
                match rec::catch(|| {
                    if override_method { OverrideProbe::unpack(&bytes).map(|p| { let mode = p.0.0; std::mem::forget(p); mode }) }
                    else {
                        // Observe the returned ownership before the caller drops it.
                        let result = Probe::unpack(&bytes);
                        match result { Ok(p) => { let mode = p.0; std::mem::forget(p); Ok(mode) }, Err(e) => Err(e) }
                    }
                }) {
                    Ok(result) => rec::returned(match result { Ok(v) => rec::ok(v.into()), Err(e) => rec::err(format!("{e:?}").into()) }, events()),
                    Err(reason) => rec::unwound(reason, events()),
                }
            });
            // the owned field of OverrideProbe must likewise be observed before caller cleanup.
            c.push(Record { id: format!("pack-{i}-{override_method}"), function: "solana_program::program_pack::Pack::unpack",
                generics: vec![("Self", if override_method { "conformance_stake_codecs_legacy::OverrideProbe" } else { "conformance_stake_codecs_legacy::Probe" }.into())],
                layout: None, state: Json::Arr(vec![]), args: rec::bytes(&bytes), outcome, observed: None });
        }
    }
}
fn main() {
    rec::init();
    let mut c = Corpus::new("stake_codecs_legacy", &[("solana-program", "1.15.2"), ("bincode", "1.3.3")]);
    getters(&mut c); builders(&mut c); pack(&mut c);
    c.write(&rec::out_dir()).expect("write corpus");
}
