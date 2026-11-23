//! Shared native calls at five exact Anchor versions. Constructors only prepare
//! inputs; each record surrounds one listed observation or ownership operation.

use anchor_lang::prelude::{Account, AccountInfo, Interface, InterfaceAccount, Program,
    Pubkey, Signer, SystemAccount, UncheckedAccount};
use anchor_lang::{AccountDeserialize, AccountSerialize, Id, Ids, Key, Owner, Owners};
use anchor_lang::accounts::sysvar::Sysvar;
use anchor_lang::solana_program::program_error::ProgramError;
use anchor_lang::solana_program::sysvar::SysvarId;
#[cfg(feature = "legacy-info")]
use anchor_lang::solana_program::sysvar::Sysvar as SolanaSysvar;
#[cfg(not(feature = "legacy-info"))]
use solana_sysvar::SysvarSerialize as SolanaSysvar;
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use std::cell::RefCell;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

const OWNER: Pubkey = Pubkey::new_from_array([2; 32]);
const KEY: Pubkey = Pubkey::new_from_array([3; 32]);
const ZERO: Pubkey = Pubkey::new_from_array([0; 32]);
static MODE: AtomicUsize = AtomicUsize::new(0);
static EXPECTED_PAYLOAD: AtomicUsize = AtomicUsize::new(0);
static EXPECTED_INFO: AtomicUsize = AtomicUsize::new(0);
static DECODE_VALUE: AtomicU64 = AtomicU64::new(7);
thread_local! { static TRACE: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) }; }

fn trace(s: String) { TRACE.with(|t| t.borrow_mut().push(s)); }
fn trace_json() -> Json { TRACE.with(|t| Json::arr(t.borrow().iter(), |s| s.clone().into())) }
fn reset() { TRACE.with(|t| t.borrow_mut().clear()); MODE.store(0, Ordering::SeqCst); }
fn mode() -> usize { MODE.load(Ordering::SeqCst) }
fn terminate() -> ! { std::process::abort() }

#[derive(Debug)]
pub struct Payload(pub u64);
impl Clone for Payload {
    fn clone(&self) -> Self {
        trace(format!("clone:{}:{}", self.0,
            self as *const Self as usize == EXPECTED_PAYLOAD.load(Ordering::SeqCst)));
        match mode() { 1 => panic!("script clone"), 2 => terminate(), _ => () }
        Payload(self.0 + 10)
    }
}
impl Drop for Payload {
    fn drop(&mut self) {
        trace(format!("drop:{}:{}", self.0,
            self as *const Self as usize == EXPECTED_PAYLOAD.load(Ordering::SeqCst)));
        // One-shot: later caller cleanup is not a second injected panic.
        match MODE.swap(0, Ordering::SeqCst) {
            1 => panic!("script drop"), 2 => terminate(), _ => ()
        }
    }
}
impl AccountDeserialize for Payload {
    fn try_deserialize(buf: &mut &[u8]) -> anchor_lang::Result<Self> {
        Self::try_deserialize_unchecked(buf)
    }
    fn try_deserialize_unchecked(buf: &mut &[u8]) -> anchor_lang::Result<Self> {
        let value = u64::from_le_bytes(buf[..8].try_into().unwrap());
        *buf = &buf[8..]; Ok(Self(value))
    }
}
impl AccountSerialize for Payload {
    fn try_serialize<W: std::io::Write>(&self, writer: &mut W) -> anchor_lang::Result<()> {
        writer.write_all(&self.0.to_le_bytes()).unwrap(); Ok(())
    }
}
impl Owner for Payload { fn owner() -> Pubkey { OWNER } }
impl Owners for Payload { fn owners() -> &'static [Pubkey] { &[OWNER] } }

pub struct Tag;
impl Clone for Tag {
    fn clone(&self) -> Self { trace("tag_clone".into()); Tag }
}
impl Id for Tag { fn id() -> Pubkey { KEY } }
impl Ids for Tag { fn ids() -> &'static [Pubkey] { &[KEY] } }
impl AccountDeserialize for Tag {
    fn try_deserialize(buf: &mut &[u8]) -> anchor_lang::Result<Self> {
        Self::try_deserialize_unchecked(buf)
    }
    fn try_deserialize_unchecked(_: &mut &[u8]) -> anchor_lang::Result<Self> { Ok(Tag) }
}

#[derive(serde::Serialize, serde::Deserialize, Default)]
pub struct ProbeSysvar(pub u64);
#[cfg(not(feature = "legacy-info"))]
impl solana_sysvar::Sysvar for ProbeSysvar {}
impl SysvarId for ProbeSysvar {
    fn id() -> Pubkey { KEY }
    fn check_id(key: &Pubkey) -> bool { key == &KEY }
}
impl SolanaSysvar for ProbeSysvar {
    fn from_account_info(info: &AccountInfo) -> std::result::Result<Self, ProgramError> {
        trace(format!("from_info:{}:{}:{}",
            Rc::strong_count(&info.lamports), Rc::strong_count(&info.data),
            info as *const AccountInfo as usize == EXPECTED_INFO.load(Ordering::SeqCst)));
        match mode() {
            1 => return Err(ProgramError::Custom(81)),
            2 => panic!("script decode"),
            3 => terminate(),
            #[cfg(feature = "old-error")]
            4 => return Err(ProgramError::BorshIoError("owned sysvar error".into())),
            _ => ()
        }
        Ok(ProbeSysvar(DECODE_VALUE.load(Ordering::SeqCst)))
    }
}

fn make_info(writable: bool, owner: Pubkey, executable: bool) -> &'static AccountInfo<'static> {
    let key = Box::leak(Box::new(KEY));
    let owner = Box::leak(Box::new(owner));
    let lamports = Box::leak(Box::new(40u64));
    let data = Box::leak(Box::new(7u64.to_le_bytes()));
    #[cfg(feature = "legacy-info")]
    let info = AccountInfo::new(key, true, writable, lamports, data, owner, executable, 0);
    #[cfg(not(feature = "legacy-info"))]
    let info = AccountInfo::new(key, true, writable, lamports, data, owner, executable);
    Box::leak(Box::new(info))
}

fn account_json(info: &AccountInfo, balance: Option<u64>) -> Json {
    Json::obj([
        ("key", rec::bytes(info.key.as_ref())), ("owner", rec::bytes(info.owner.as_ref())),
        ("signer", info.is_signer.into()), ("writable", info.is_writable.into()),
        ("executable", info.executable.into()),
        ("lamports", balance.unwrap_or_else(|| **info.lamports.borrow()).into()),
        ("data", rec::bytes(&info.data.borrow())),
    ])
}
fn snapshot(value: Option<u64>, info: &AccountInfo, balance: Option<u64>, native: bool) -> Json {
    Json::obj([
        ("payload", value.map(Json::from).unwrap_or(Json::Null)),
        ("account", account_json(info, balance)),
        ("counts", Json::arr([Rc::strong_count(&info.lamports), Rc::strong_count(&info.data)], Json::from)),
        ("trace", trace_json()),
        ("syscalls", if native { shim::state() } else { Script::default().state_before() }),
    ])
}
fn info_ref<'a, W>(wrapper: &W, returned: &AccountInfo<'a>, original: &AccountInfo<'a>) -> Json {
    let start = wrapper as *const W as usize;
    let target = returned as *const AccountInfo as usize;
    Json::obj([
        ("same_input", std::ptr::eq(returned, original).into()),
        ("in_receiver", (start <= target && target + std::mem::size_of::<AccountInfo>() <= start + std::mem::size_of::<W>()).into()),
    ])
}
fn payload_ref(returned: &Payload, original: *const Payload, mutable: bool) -> Json {
    Json::obj([("same_field", std::ptr::eq(returned, original).into()),
        ("mutable", mutable.into()), ("value", returned.0.into())])
}
fn finish(result: std::result::Result<Json, String>, state: Json) -> Json {
    match result { Ok(value) => rec::returned(value, state), Err(reason) => rec::unwound(reason, state) }
}
fn record(corpus: &mut Corpus, wrapper: &str, operation: &str, case: &str,
    generics: Vec<(&'static str, String)>, state: Json, args: Json, outcome: Json) {
    corpus.push(Record { id: format!("{wrapper}/{operation}/{case}"),
        function: crate::identities::find(wrapper, operation), generics, layout: None,
        state, args, outcome, observed: None });
}
fn payload_generic() -> Vec<(&'static str, String)> {
    vec![("T", std::any::type_name::<Payload>().into())]
}

trait Decoded: Deref<Target = Payload> + DerefMut + AsRef<Payload> + AsRef<AccountInfo<'static>> + Key + Clone {
    fn take(self) -> Payload;
    fn replace(&mut self, value: Payload);
}
impl Decoded for Account<'static, Payload> {
    fn take(self) -> Payload { self.into_inner() }
    fn replace(&mut self, value: Payload) { self.set_inner(value) }
}
impl Decoded for InterfaceAccount<'static, Payload> {
    fn take(self) -> Payload { self.into_inner() }
    fn replace(&mut self, value: Payload) { self.set_inner(value) }
}

fn decoded<W: Decoded>(corpus: &mut Corpus, wrapper: &str, make: impl Fn(&'static AccountInfo<'static>) -> W) {
    for operation in ["key", "as_ref_info", "as_ref_payload", "deref", "deref_mut", "clone", "into_inner", "set_inner"] {
        let modes: &[usize] = if operation == "clone" || operation == "set_inner" { &[0, 1, 2] } else { &[0] };
        let writable_cases: &[bool] = if operation == "deref_mut" { &[true, false] } else { &[true] };
        for &writable in writable_cases { for &script_mode in modes {
            let info = make_info(writable, OWNER, false);
            // Pin the prepared receiver address before the forked call closure
            // captures it. This allocation is outside the recorded SDK call.
            let mut value = Box::new(make(info));
            reset();
            let original_payload: *const Payload = <W as AsRef<Payload>>::as_ref(&value);
            EXPECTED_PAYLOAD.store(original_payload as usize, Ordering::SeqCst);
            let before = snapshot(Some(value.0), info, None, false);
            let args = Json::obj([("mode", script_mode.into()), ("replacement", 91u64.into()), ("debug", crate::DEBUG.into())]);
            let outcome = shim::case(&Script::default(), || {
                MODE.store(script_mode, Ordering::SeqCst);
                match operation {
                    "clone" => {
                        let result = rec::catch(|| <W as Clone>::clone(&value));
                        let after = snapshot(Some(value.0), info, None, true);
                        let result = result.map(|cloned| {
                            let first: &AccountInfo = <W as AsRef<AccountInfo>>::as_ref(&value);
                            let second: &AccountInfo = <W as AsRef<AccountInfo>>::as_ref(&cloned);
                            let encoded = Json::obj([("value", cloned.0.into()),
                                ("info_same", std::ptr::eq(first, second).into()),
                                ("info_aliases", (Rc::ptr_eq(&first.lamports, &second.lamports) && Rc::ptr_eq(&first.data, &second.data)).into()),
                                ("payload_distinct", (!std::ptr::eq::<Payload>(&**value, &*cloned)).into())]);
                            std::mem::forget(cloned); encoded
                        });
                        std::mem::forget(value);
                        finish(result, after)
                    }
                    "into_inner" => {
                        let result = rec::catch(|| (*value).take());
                        let after = snapshot(None, info, None, true);
                        let result = result.map(|payload| { let n = payload.0; std::mem::forget(payload); n.into() });
                        finish(result, after)
                    }
                    _ => {
                        let result = rec::catch(|| match operation {
                            "key" => rec::bytes(value.key().as_ref()),
                            "as_ref_info" => info_ref(&*value, <W as AsRef<AccountInfo>>::as_ref(&value), info),
                            "as_ref_payload" => payload_ref(<W as AsRef<Payload>>::as_ref(&value), original_payload, false),
                            "deref" => payload_ref(Deref::deref(&*value), original_payload, false),
                            "deref_mut" => payload_ref(DerefMut::deref_mut(&mut *value), original_payload, true),
                            "set_inner" => { value.replace(Payload(91)); Json::Null }
                            _ => unreachable!(),
                        });
                        let after = snapshot(Some(value.0), info, None, true);
                        std::mem::forget(value);
                        finish(result, after)
                    }
                }
            });
            record(corpus, wrapper, operation, &format!("{writable}-{script_mode}"), payload_generic(), before, args, outcome);
        }}
    }
}

fn info_only<W>(corpus: &mut Corpus, wrapper: &str, make: impl Fn(&'static AccountInfo<'static>) -> W,
    owner: Pubkey, executable: bool, generic: bool)
where W: Deref<Target = AccountInfo<'static>> + AsRef<AccountInfo<'static>> + Key + Clone {
    for operation in ["key", "as_ref_info", "deref", "clone"] {
        let info = make_info(true, owner, executable);
        let value = make(info);
        reset();
        let before = snapshot(None, info, None, false);
        let outcome = shim::case(&Script::default(), || {
            let result = match operation {
                "key" => rec::bytes(value.key().as_ref()),
                "as_ref_info" => info_ref(&value, value.as_ref(), info),
                "deref" => info_ref(&value, Deref::deref(&value), info),
                "clone" => {
                    let cloned = value.clone();
                    let first = value.as_ref(); let second = cloned.as_ref();
                    let result = Json::obj([("info_same", std::ptr::eq(first, second).into()),
                        ("info_aliases", (Rc::ptr_eq(&first.lamports, &second.lamports) && Rc::ptr_eq(&first.data, &second.data)).into())]);
                    let after = snapshot(None, info, None, true);
                    std::mem::forget(cloned);
                    return rec::returned(result, after);
                }
                _ => unreachable!(),
            };
            rec::returned(result, snapshot(None, info, None, true))
        });
        let generics = if generic { vec![("T", std::any::type_name::<Tag>().into())] } else { vec![] };
        record(corpus, wrapper, operation, "normal", generics, before, Json::empty(), outcome);
    }
}

fn sysvars(corpus: &mut Corpus) {
    for operation in ["key", "as_ref_info", "deref", "deref_mut", "clone"] {
        let modes: &[usize] = if operation == "clone" {
            #[cfg(feature = "old-error")] { &[0, 1, 2, 3, 4] }
            #[cfg(not(feature = "old-error"))] { &[0, 1, 2, 3] }
        } else { &[0] };
        for &script_mode in modes {
            let info = make_info(false, OWNER, false);
            reset(); DECODE_VALUE.store(7, Ordering::SeqCst);
            let mut value = Box::new(Sysvar::<ProbeSysvar>::from_account_info(info).unwrap());
            reset(); DECODE_VALUE.store(23, Ordering::SeqCst);
            EXPECTED_INFO.store(<Sysvar<ProbeSysvar> as AsRef<AccountInfo>>::as_ref(&value) as *const AccountInfo as usize, Ordering::SeqCst);
            let payload_pointer: *const ProbeSysvar = &**value;
            let before = snapshot(Some(value.0), info, None, false);
            let outcome = shim::case(&Script::default(), || {
                MODE.store(script_mode, Ordering::SeqCst);
                if operation == "clone" {
                    let result = rec::catch(|| <Sysvar<ProbeSysvar> as Clone>::clone(&value));
                    let after = snapshot(Some(value.0), info, None, true);
                    let result = result.map(|cloned| {
                        let result = Json::obj([("value", cloned.0.into()),
                            ("info_same", std::ptr::eq(<Sysvar<ProbeSysvar> as AsRef<AccountInfo>>::as_ref(&value), cloned.as_ref()).into()),
                            ("info_aliases", (Rc::ptr_eq(&<Sysvar<ProbeSysvar> as AsRef<AccountInfo>>::as_ref(&value).lamports, &cloned.as_ref().lamports) && Rc::ptr_eq(&<Sysvar<ProbeSysvar> as AsRef<AccountInfo>>::as_ref(&value).data, &cloned.as_ref().data)).into()),
                            ("payload_distinct", (!std::ptr::eq::<ProbeSysvar>(&**value, &*cloned)).into())]);
                        std::mem::forget(cloned); result
                    });
                    finish(result, after)
                } else {
                    let result = rec::catch(|| match operation {
                        "key" => rec::bytes(value.key().as_ref()),
                        "as_ref_info" => info_ref(&*value, <Sysvar<ProbeSysvar> as AsRef<AccountInfo>>::as_ref(&value), info),
                        "deref" => { let r = Deref::deref(&*value); Json::obj([("same_field", std::ptr::eq(r, payload_pointer).into()), ("mutable", false.into()), ("value", r.0.into())]) }
                        "deref_mut" => { let r = DerefMut::deref_mut(&mut *value); Json::obj([("same_field", std::ptr::eq(r, payload_pointer).into()), ("mutable", true.into()), ("value", r.0.into())]) }
                        _ => unreachable!(),
                    });
                    finish(result, snapshot(Some(value.0), info, None, true))
                }
            });
            record(corpus, "sysvar", operation, &script_mode.to_string(),
                vec![("T", std::any::type_name::<ProbeSysvar>().into())], before,
                Json::obj([("mode", script_mode.into())]), outcome);
        }
    }
}

#[cfg(feature = "lamports")]
struct Holder { info: &'static AccountInfo<'static>, change: bool, panics: bool }
#[cfg(feature = "lamports")]
impl AsRef<AccountInfo<'static>> for Holder {
    fn as_ref(&self) -> &AccountInfo<'static> {
        trace("as_ref".into());
        if self.change { **self.info.lamports.borrow_mut() = 99; }
        if self.panics { panic!("script as_ref"); }
        self.info
    }
}
#[cfg(feature = "lamports")]
fn lamports(corpus: &mut Corpus) {
    use anchor_lang::Lamports;
    for (case, change, panics, conflict) in [("normal", false, false, false),
        ("mutates", true, false, false), ("panics", true, true, false), ("conflict", false, false, true)] {
        let info = make_info(true, OWNER, false);
        let holder = Holder { info, change, panics };
        let held = conflict.then(|| info.lamports.borrow_mut());
        reset();
        let before = snapshot(None, info, Some(40), false);
        let outcome = shim::case(&Script::default(), || {
            let result = rec::catch(|| holder.get_lamports()).map(Json::from);
            let balance = if let Some(ref h) = held { ***h } else { **info.lamports.borrow() };
            finish(result, snapshot(None, info, Some(balance), true))
        });
        record(corpus, "lib", "get_lamports", case,
            vec![("Self", std::any::type_name::<Holder>().into())], before,
            Json::obj([("change", change.into()), ("panics", panics.into()), ("conflict", conflict.into())]), outcome);
    }
}

pub fn run() {
    rec::init();
    let mut corpus = Corpus::new(crate::CORPUS, &[("anchor-lang", crate::VERSION)]);
    decoded(&mut corpus, "account", |info| Account::<Payload>::try_from(info).unwrap());
    decoded(&mut corpus, "interface_account", |info| InterfaceAccount::<Payload>::try_from(info).unwrap());
    info_only(&mut corpus, "program", |info| Program::<Tag>::try_from(info).unwrap(), OWNER, true, true);
    info_only(&mut corpus, "interface", |info| Interface::<Tag>::try_from(info).unwrap(), OWNER, true, true);
    info_only(&mut corpus, "signer", |info| Signer::try_from(info).unwrap(), OWNER, false, false);
    info_only(&mut corpus, "system_account", |info| SystemAccount::try_from(info).unwrap(), ZERO, false, false);
    #[cfg(feature = "owned-info")]
    info_only(&mut corpus, "unchecked_account", |info| UncheckedAccount::try_from(info.clone()), OWNER, false, false);
    #[cfg(not(feature = "owned-info"))]
    info_only(&mut corpus, "unchecked_account", UncheckedAccount::try_from, OWNER, false, false);
    sysvars(&mut corpus);
    reset();
    for key in [KEY, Pubkey::new_from_array([255; 32]), ZERO] {
        let state = Json::Null;
        let outcome = rec::returned(rec::bytes(Key::key(&key).as_ref()), Json::Null);
        record(&mut corpus, "lib", "key", &rec::hex_plain(key.as_ref()), vec![], state,
            Json::obj([("key", rec::bytes(key.as_ref()))]), outcome);
    }
    #[cfg(feature = "lamports")] lamports(&mut corpus);
    corpus.write(&rec::out_dir()).expect("write native Anchor views");
}
