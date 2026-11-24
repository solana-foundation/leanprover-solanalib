use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Script};
use pinocchio::account_info::{AccountInfo, Ref, RefMut};
use core::{mem::MaybeUninit, ops::{Deref, DerefMut}};

const KEY: &str = "pinocchio::account_info::AccountInfo::key";
const OWNER: &str = "pinocchio::account_info::AccountInfo::owner";
const SIGNER: &str = "pinocchio::account_info::AccountInfo::is_signer";
const WRITABLE: &str = "pinocchio::account_info::AccountInfo::is_writable";
const OWNED: &str = "pinocchio::account_info::AccountInfo::is_owned_by";
const LAMPORTS: &str = "pinocchio::account_info::AccountInfo::lamports";
const LEN: &str = "pinocchio::account_info::AccountInfo::data_len";
const SHARED: &str = "pinocchio::account_info::AccountInfo::try_borrow_data";
const MUT_DATA: &str = "pinocchio::account_info::AccountInfo::try_borrow_mut_data";
const MUT_LAMPORTS: &str = "pinocchio::account_info::AccountInfo::try_borrow_mut_lamports";
const RESIZE: &str = "pinocchio::account_info::AccountInfo::resize";
const DEREF: &str = "<pinocchio::account_info::Ref<'_, T> as core::ops::deref::Deref>::deref";
const DEREF_MUT_SHARED: &str = "<pinocchio::account_info::RefMut<'_, T> as core::ops::deref::Deref>::deref";
const DEREF_MUT: &str = "<pinocchio::account_info::RefMut<'_, T> as core::ops::deref::DerefMut>::deref_mut";
const DROP: &str = "<pinocchio::account_info::Ref<'_, T> as core::ops::drop::Drop>::drop";
const DROP_MUT: &str = "<pinocchio::account_info::RefMut<'_, T> as core::ops::drop::Drop>::drop";
const MAP: &str = "pinocchio::account_info::RefMut::<'a, T>::map";

#[derive(Clone)]
struct Slot { field: &'static str, mode: &'static str, generation: usize, offset: usize, len: usize }
impl Slot {
    fn json(&self) -> Json { Json::obj([("field", self.field.into()), ("mode", self.mode.into()),
        ("generation", self.generation.into()), ("offset", self.offset.into()), ("len", self.len.into())]) }
}

struct World { region: Region, slots: Vec<Option<Slot>>, events: Vec<&'static str> }
impl World {
    fn new(flags: [u8; 3], data: Vec<u8>) -> (Self, [AccountInfo; 2]) {
        let input = Input { entries: vec![Entry::Account(Account { key: [1; 32], owner: [2; 32], lamports: 40,
            data, is_signer: false, is_writable: false, executable: false, rent_epoch: 7 }), Entry::Duplicate(0)],
            instruction_data: vec![8, 9], program_id: [3; 32] };
        let mut region = input.serialize();
        let mut accounts: [MaybeUninit<AccountInfo>; 2] = [const { MaybeUninit::uninit() }; 2];
        unsafe {
            let (_, count, _) = pinocchio::entrypoint::deserialize(region.as_mut_ptr(), &mut accounts);
            assert_eq!(count, 2);
            let ptr = region.account_ptr(0);
            core::ptr::copy_nonoverlapping(flags.as_ptr(), ptr.add(1), 3);
            let infos = [accounts[0].assume_init(), accounts[1].assume_init()];
            (World { region, slots: vec![], events: vec![] }, infos)
        }
    }
    fn state(&self, syscalls: Json) -> Json { Json::obj([
        ("input", self.region.read_back()),
        ("guards", Json::arr(self.slots.iter(), |s| s.as_ref().map_or(Json::Null, Slot::json))),
        ("events", Json::arr(self.events.iter(), |s| (*s).into())), ("syscalls", syscalls)]) }
    fn slot(&mut self, field: &'static str, mode: &'static str, len: usize) -> usize {
        let id = self.slots.len(); self.slots.push(Some(Slot { field, mode, generation: 0, offset: 0, len })); id
    }
    fn data_base(&mut self) -> usize { self.region.account_ptr(0) as usize + 88 }
}

enum Held<'a> { Shared(Ref<'a, [u8]>), Data(RefMut<'a, [u8]>), Lamports(RefMut<'a, u64>) }
fn hold<'a>(w: &mut World, info: &'a AccountInfo, shared: usize, data: bool, lamports: bool) -> Vec<Held<'a>> {
    let mut result = vec![];
    for _ in 0..shared { let g = info.try_borrow_data().unwrap(); w.slot("data", "shared", g.len()); result.push(Held::Shared(g)); }
    if data { let g = info.try_borrow_mut_data().unwrap(); w.slot("data", "exclusive", g.len()); result.push(Held::Data(g)); }
    if lamports { let g = info.try_borrow_mut_lamports().unwrap(); w.slot("lamports", "exclusive", 8); result.push(Held::Lamports(g)); }
    result
}
fn reference(id: usize, generation: usize, offset: usize, writable: bool, bytes: &[u8]) -> Json {
    Json::obj([("guard", id.into()), ("generation", generation.into()), ("offset", offset.into()),
        ("writable", writable.into()), ("bytes", rec::bytes(bytes)), ("len", bytes.len().into())])
}
fn record(c: &mut Corpus, id: String, function: &'static str, state: Json, args: Json, outcome: Json, target: bool) {
    c.push(Record { id, function, generics: if target { vec![("T", "[u8]".into())] } else { vec![] },
        layout: None, state, args, outcome, observed: None });
}
fn simple(c: &mut Corpus, function: &'static str, label: &str, flags: [u8; 3], alias: usize, held_data: bool, other: bool) {
    let (mut w, infos) = World::new(flags, vec![10, 20, 30]);
    let held = hold(&mut w, &infos[0], 0, held_data, false);
    let script = Script::default(); let before = w.state(script.state_before());
    let args = Json::obj([("account", alias.into()), ("key", rec::bytes(&[if other { 8 } else { 2 }; 32]))]);
    let outcome = shim::case(&script, || {
        let i = &infos[alias];
        let result = match function {
            KEY | OWNER => { let ptr = if function == KEY { i.key() } else { i.owner() };
                let offset = ptr.as_ptr() as usize - w.region.account_ptr(0) as usize;
                Json::obj([("offset", offset.into()), ("bytes", rec::bytes(ptr))]) }
            SIGNER => i.is_signer().into(), WRITABLE => i.is_writable().into(),
            OWNED => i.is_owned_by(&[if other { 8 } else { 2 }; 32]).into(),
            LAMPORTS => i.lamports().into(), LEN => i.data_len().into(), _ => unreachable!()
        }; rec::returned(result, w.state(shim::state()))
    });
    record(c, format!("{}/{label}", function.rsplit("::").next().unwrap()), function, before, args, outcome, false);
    drop(held);
}
fn borrow(c: &mut Corpus, function: &'static str, label: &str, shared: usize, data: bool, lamports: bool) {
    let (mut w, infos) = World::new([0, 0, 0], vec![10, 20, 30]);
    let held = hold(&mut w, &infos[0], shared, data, lamports);
    let script = Script::default(); let before = w.state(script.state_before());
    let outcome = shim::case(&script, || {
        // Keep the returned guard live until after the recorded state.
        let result: Result<Held<'_>, _> = match function {
            SHARED => infos[1].try_borrow_data().map(Held::Shared),
            MUT_DATA => infos[1].try_borrow_mut_data().map(Held::Data),
            MUT_LAMPORTS => infos[1].try_borrow_mut_lamports().map(Held::Lamports), _ => unreachable!()
        };
        let value = match &result {
            Err(e) => rec::err(format!("{e:?}").into()),
            Ok(g) => { let (field, mode, len) = match g {
                Held::Shared(g) => ("data", "shared", g.len()), Held::Data(g) => ("data", "exclusive", g.len()),
                Held::Lamports(g) => { assert_eq!(**g, 40); ("lamports", "exclusive", 8) }
            }; let id = w.slot(field, mode, len); rec::ok(Json::obj([("guard", id.into()), ("generation", 0usize.into())])) }
        }; let after = w.state(shim::state()); rec::returned(value, after)
    });
    record(c, format!("{}/{label}", function.rsplit("::").next().unwrap()), function, before,
        Json::obj([("account", 1usize.into())]), outcome, false); drop(held);
}
fn resize(c: &mut Corpus, label: &str, new_len: usize, shared: usize, data: bool, balance: bool, shrunk: bool) {
    let (mut w, infos) = World::new([0, 1, 0], vec![10, 20, 30]);
    if shrunk { infos[0].resize(1).unwrap(); }
    let held = hold(&mut w, &infos[0], shared, data, balance);
    let script = Script::default(); let before = w.state(script.state_before());
    let outcome = shim::case(&script, || {
        let r = infos[1].resize(new_len);
        rec::returned(crate::syscall_cases::program_error(&r, |_| Json::Null), w.state(shim::state()))
    });
    record(c, format!("resize/{label}"), RESIZE, before,
        Json::obj([("account", 1usize.into()), ("new_len", new_len.into())]), outcome, false); drop(held);
}
fn guard(c: &mut Corpus, function: &'static str, label: &str) {
    let (mut w, infos) = World::new([0, 0, 0], vec![10, 20, 30]); let is_shared = function == DEREF || function == DROP;
    let mut held = hold(&mut w, &infos[0], usize::from(is_shared), !is_shared, false);
    let script = Script::default(); let before = w.state(script.state_before());
    let outcome = shim::case(&script, || {
        let value = if function == DROP || function == DROP_MUT { drop(held.pop().unwrap()); w.slots[0] = None; Json::Null }
        else { let base = w.data_base(); let bytes: &[u8] = match &mut held[0] {
            Held::Shared(g) => Ref::deref(g), Held::Data(g) => if function == DEREF_MUT { RefMut::deref_mut(g) } else { RefMut::deref(g) },
            _ => unreachable!()
        }; reference(0, 0, bytes.as_ptr() as usize - base, function == DEREF_MUT, bytes) };
        rec::returned(value, w.state(shim::state()))
    });
    record(c, format!("guard/{label}"), function, before, Json::obj([("guard", 0usize.into()), ("generation", 0usize.into())]), outcome, true);
    drop(held);
}
fn map(c: &mut Corpus, label: &str, panics: bool, mutate: bool, start: usize, len: usize) {
    let (mut w, infos) = World::new([0, 1, 0], vec![10, 20, 30]);
    let g = infos[0].try_borrow_mut_data().unwrap(); w.slot("data", "exclusive", g.len());
    let script = Script::default(); let before = w.state(script.state_before());
    let outcome = shim::case(&script, || {
        let r = rec::catch(|| RefMut::map(g, |bytes| {
            w.events.push("map"); if mutate { bytes[0] = 99; }
            if panics { panic!("map callback"); }
            &mut bytes[start..start + len]
        }));
        match r {
            Ok(mapped) => { let offset = mapped.as_ptr() as usize - w.data_base();
                w.slots[0] = Some(Slot { field: "data", mode: "exclusive", generation: 1, offset, len: mapped.len() });
                let value = Json::obj([("guard", 0usize.into()), ("generation", 1usize.into())]);
                let after = w.state(shim::state()); rec::returned(value, after) }
            Err(reason) => { w.slots[0] = None; rec::unwound(reason, w.state(shim::state())) }
        }
    });
    record(c, format!("map/{label}"), MAP, before, Json::obj([("guard", 0usize.into()), ("generation", 0usize.into()),
        ("panics", panics.into()), ("mutate", mutate.into()), ("start", start.into()), ("len", len.into())]), outcome, true);
}
pub fn corpus() -> Corpus {
    let mut c = Corpus::new("pinocchio_0_9_2_accounts", &[("pinocchio", "0.9.2")]);
    for f in [KEY, OWNER, SIGNER, WRITABLE, OWNED, LAMPORTS, LEN] {
        simple(&mut c, f, "ordinary", [1, 1, 0], 0, false, false);
        simple(&mut c, f, "alias_exclusive_noncanonical_flags", [2, 3, 0], 1, true, false);
        simple(&mut c, f, "zero_flags_different_owner", [0, 0, 0], 1, false, true);
    }
    for f in [SHARED, MUT_DATA, MUT_LAMPORTS] {
        for (label, shares, data, lamports) in [("free", 0, false, false), ("shared1", 1, false, false),
            ("shared7", 7, false, false), ("exclusive_data", 0, true, false), ("exclusive_lamports", 0, false, true)] {
            borrow(&mut c, f, label, shares, data, lamports);
        }
    }
    for (label, n, shares, data, balance, shrunk) in [("equal",3,0,false,false,false), ("shrink",1,0,false,false,false),
        ("zero",0,0,false,false,false), ("grow",5,0,false,false,false), ("limit",10243,0,false,false,false),
        ("over_limit",10244,0,false,false,false), ("i32_conversion",1usize<<31,0,false,false,false),
        ("borrow_before_conversion",usize::MAX,0,true,false,false), ("shared_even_equal",3,1,false,false,false),
        ("balance_independent",5,0,false,true,false), ("regrow",4,0,false,false,true)] {
        resize(&mut c,label,n,shares,data,balance,shrunk);
    }
    for (f,label) in [(DEREF,"shared"),(DEREF_MUT_SHARED,"exclusive_shared_view"),(DEREF_MUT,"exclusive_mutable_view"),
        (DROP,"drop_shared"),(DROP_MUT,"drop_exclusive")] { guard(&mut c,f,label); }
    map(&mut c,"subslice",false,false,1,2); map(&mut c,"empty",false,false,3,0);
    map(&mut c,"mutated",false,true,1,1); map(&mut c,"unwind_leaks_lease",true,true,0,3);
    c
}
