//! Records solana-account-view 2.0.0 over loader-serialized input regions.
//!
//! Each case serializes an account list with `conformance-accounts` (ABI v1,
//! aligned), makes `AccountView`s of the instruction accounts from the
//! addresses of their first occurrences, brings the region into a borrow
//! configuration through the library itself (unrecorded setup calls), then
//! records one call: the state before, the arguments and the outcome with the
//! state after. The state and its meaning are described in the family
//! `SolanalibTest/Conformance/Library/Families/AccountsV2/Projection.lean`.
//!
//! `Ref::try_map`/`RefMut::try_map` closures are scripted: effects
//! (`set_lamports` through a captured view, writes through `&mut [u8]`), then an
//! ending (a sub-reference of the input, `Err(u8)` or a panic). The script is
//! the record `callback` argument.

mod world;

use conformance_accounts::{Account, Entry, Input};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use core::ops::{Deref, DerefMut};
use solana_account_view::{AccountView, Ref, RefMut, RuntimeAccount};
use solana_address::Address;
use world::{Held, Mode, World};

const CORPUS: &str = "solana_account_view_2_0_0";

const F_ADDRESS: &str = "solana_account_view::AccountView::address";
const F_CLOSE: &str = "solana_account_view::AccountView::close";
const F_DATA_LEN: &str = "solana_account_view::AccountView::data_len";
const F_IS_SIGNER: &str = "solana_account_view::AccountView::is_signer";
const F_LAMPORTS: &str = "solana_account_view::AccountView::lamports";
const F_OWNED_BY: &str = "solana_account_view::AccountView::owned_by";
const F_SET_LAMPORTS: &str = "solana_account_view::AccountView::set_lamports";
const F_TRY_BORROW: &str = "solana_account_view::AccountView::try_borrow";
const F_TRY_BORROW_MUT: &str = "solana_account_view::AccountView::try_borrow_mut";
const F_REF_DEREF: &str = "<solana_account_view::Ref<'_, T> as core::ops::deref::Deref>::deref";
const F_REF_DROP: &str = "<solana_account_view::Ref<'_, T> as core::ops::drop::Drop>::drop";
const F_REF_TRY_MAP: &str = "solana_account_view::Ref::<'a, T>::try_map";
const F_MUT_DEREF: &str = "<solana_account_view::RefMut<'_, T> as core::ops::deref::Deref>::deref";
const F_MUT_DEREF_MUT: &str = "<solana_account_view::RefMut<'_, T> as core::ops::deref::DerefMut>::deref_mut";
const F_MUT_DROP: &str = "<solana_account_view::RefMut<'_, T> as core::ops::drop::Drop>::drop";
const F_MUT_TRY_MAP: &str = "solana_account_view::RefMut::<'a, T>::try_map";

// ---------------------------------------------------------------------------
// Accounts
// ---------------------------------------------------------------------------

fn key(b: u8) -> [u8; 32] {
    [b; 32]
}

const P1: u8 = 0x51;
const P2: u8 = 0x52;

fn account_a() -> Account {
    Account {
        key: key(0xa1),
        owner: key(P1),
        lamports: 1_000_000_000,
        data: (1..=8).collect(),
        is_signer: true,
        is_writable: true,
        executable: false,
        rent_epoch: u64::MAX,
    }
}

fn account_b() -> Account {
    Account {
        key: key(0xb2),
        owner: key(P2),
        lamports: 0,
        data: vec![],
        is_signer: false,
        is_writable: true,
        executable: false,
        rent_epoch: 0,
    }
}

fn account_c() -> Account {
    Account {
        key: key(0xc3),
        owner: [0; 32],
        lamports: u64::MAX,
        data: (0..13).map(|i| 0x30 + i).collect(),
        is_signer: false,
        is_writable: false,
        executable: true,
        rent_epoch: 361,
    }
}

/// `ab`: A, B and a duplicate of A (instruction account 2 aliases cell 0).
/// `c`: C and a duplicate of C.
fn input(name: &str) -> Input {
    let entries = match name {
        "ab" => vec![Entry::Account(account_a()), Entry::Account(account_b()), Entry::Duplicate(0)],
        "c" => vec![Entry::Account(account_c()), Entry::Duplicate(0)],
        _ => unreachable!(),
    };
    Input { entries, instruction_data: vec![0x01, 0x02], program_id: key(0x99) }
}

// ---------------------------------------------------------------------------
// Scripted try_map closures
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum Effect {
    /// `set_lamports` through a captured view of an instruction account.
    SetLamports(usize, u64),
    /// A write through the closure `&mut [u8]`, at an offset of its input.
    Write(usize, Vec<u8>),
}

#[derive(Clone)]
enum Ending {
    /// A sub-reference `[offset, length]` of the input (length 1 for `U = u8`).
    Ok(usize, usize),
    Err(u8),
    Panic(&'static str),
}

#[derive(Clone)]
struct Script {
    effects: Vec<Effect>,
    ending: Ending,
}

fn script(effects: Vec<Effect>, ending: Ending) -> Script {
    Script { effects, ending }
}

impl Script {
    fn to_json(&self) -> Json {
        let effects = Json::arr(self.effects.iter(), |e| match e {
            Effect::SetLamports(i, v) => Json::obj([("set_lamports", Json::Arr(vec![Json::from(*i), Json::from(*v)]))]),
            Effect::Write(o, b) => Json::obj([("write", Json::Arr(vec![Json::from(*o), rec::bytes(b)]))]),
        });
        let result = match &self.ending {
            Ending::Ok(o, l) => Json::obj([("ok", Json::Arr(vec![Json::from(*o), Json::from(*l)]))]),
            Ending::Err(e) => Json::obj([("err", Json::from(*e))]),
            Ending::Panic(m) => Json::obj([("panic", Json::from(*m))]),
        };
        Json::obj([("effects", effects), ("result", result)])
    }
}

fn set_lamports_effects(effects: &[Effect], ptrs: &[*mut RuntimeAccount]) {
    for effect in effects {
        match effect {
            Effect::SetLamports(i, v) => unsafe { AccountView::new_unchecked(ptrs[*i]) }.set_lamports(*v),
            Effect::Write(..) => panic!("a shared closure cannot write"),
        }
    }
}

fn mut_effects(effects: &[Effect], data: &mut [u8], ptrs: &[*mut RuntimeAccount]) {
    for effect in effects {
        match effect {
            Effect::SetLamports(i, v) => unsafe { AccountView::new_unchecked(ptrs[*i]) }.set_lamports(*v),
            Effect::Write(o, b) => data[*o..*o + b.len()].copy_from_slice(b),
        }
    }
}

fn end_slice<'b>(d: &'b [u8], ending: &Ending) -> Result<&'b [u8], u8> {
    match ending {
        Ending::Ok(o, l) => Ok(&d[*o..*o + *l]),
        Ending::Err(e) => Err(*e),
        Ending::Panic(m) => panic!("{}", m),
    }
}

fn end_byte<'b>(d: &'b [u8], ending: &Ending) -> Result<&'b u8, u8> {
    match ending {
        Ending::Ok(o, 1) => Ok(&d[*o]),
        Ending::Ok(..) => panic!("a u8 target has length 1"),
        Ending::Err(e) => Err(*e),
        Ending::Panic(m) => panic!("{}", m),
    }
}

fn end_slice_mut<'b>(d: &'b mut [u8], ending: &Ending) -> Result<&'b mut [u8], u8> {
    match ending {
        Ending::Ok(o, l) => Ok(&mut d[*o..*o + *l]),
        Ending::Err(e) => Err(*e),
        Ending::Panic(m) => panic!("{}", m),
    }
}

fn end_byte_mut<'b>(d: &'b mut [u8], ending: &Ending) -> Result<&'b mut u8, u8> {
    match ending {
        Ending::Ok(o, 1) => Ok(&mut d[*o]),
        Ending::Ok(..) => panic!("a u8 target has length 1"),
        Ending::Err(e) => Err(*e),
        Ending::Panic(m) => panic!("{}", m),
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Target {
    Bytes,
    Byte,
}

impl Target {
    fn name(self) -> &'static str {
        match self {
            Target::Bytes => "[u8]",
            Target::Byte => "u8",
        }
    }
}

// ---------------------------------------------------------------------------
// Operations: one library call each, returning its result (or panic message)
// and updating the driver guards and ghost epochs
// ---------------------------------------------------------------------------

type Out = Result<Json, String>;

fn error_name(e: &solana_program_error::ProgramError) -> Json {
    Json::from(format!("{e:?}"))
}

fn op_address(w: &mut World, i: usize) -> Out {
    let v = w.view(i);
    let addr = rec::catch(move || v.address() as *const Address as usize)?;
    Ok(Json::obj([("cell", w.address_cell(addr).map_or(Json::Null, Json::from))]))
}

fn op_lamports(w: &mut World, i: usize) -> Out {
    let v = w.view(i);
    rec::catch(move || v.lamports()).map(Json::from)
}

fn op_data_len(w: &mut World, i: usize) -> Out {
    let v = w.view(i);
    rec::catch(move || v.data_len()).map(Json::from)
}

fn op_is_signer(w: &mut World, i: usize) -> Out {
    let v = w.view(i);
    rec::catch(move || v.is_signer()).map(Json::from)
}

fn op_owned_by(w: &mut World, i: usize, program: [u8; 32]) -> Out {
    let v = w.view(i);
    let program = Address::new_from_array(program);
    rec::catch(move || v.owned_by(&program)).map(Json::from)
}

fn op_set_lamports(w: &mut World, i: usize, lamports: u64) -> Out {
    let v = w.view(i);
    rec::catch(move || v.set_lamports(lamports)).map(|()| Json::Null)
}

fn op_close(w: &mut World, i: usize) -> Out {
    let v = w.view(i);
    match rec::catch(move || v.close())? {
        Ok(()) => {
            let cell = w.cell_of(i);
            w.epochs[cell] += 1;
            Ok(rec::ok(Json::Null))
        }
        Err(e) => Ok(rec::err(error_name(&e))),
    }
}

fn acquired(w: &mut World, held: Held) -> Json {
    let k = w.push(held);
    rec::ok(Json::obj([("guard", w.token(k)), ("bytes", rec::bytes(&w.target_bytes(k)))]))
}

fn op_try_borrow(w: &mut World, i: usize) -> Out {
    let v: &'static AccountView = w.view(i);
    match rec::catch(move || v.try_borrow())? {
        Ok(r) => Ok(acquired(w, Held::SharedBytes(r))),
        Err(e) => Ok(rec::err(error_name(&e))),
    }
}

fn op_try_borrow_mut(w: &mut World, i: usize) -> Out {
    let v = w.view(i);
    match rec::catch(move || v.try_borrow_mut())? {
        Ok(r) => Ok(acquired(w, Held::ExclusiveBytes(r))),
        Err(e) => Ok(rec::err(error_name(&e))),
    }
}

/// A reference returned by a dereference: the cell and offset it addresses,
/// its length and its mutability.
fn reference(w: &World, addr: usize, length: usize, mutable: bool) -> Json {
    let (cell, offset) = match w.locate(addr) {
        Some((c, o)) => (Json::from(c), o),
        None => (Json::Null, 0),
    };
    Json::obj([("cell", cell), ("offset", Json::from(offset)), ("length", Json::from(length)), ("mutable", Json::from(mutable))])
}

fn op_ref_deref(w: &mut World, k: usize) -> Out {
    let (addr, len) = match &w.guards[k].held {
        Held::SharedBytes(r) => rec::catch(|| {
            let s: &[u8] = <Ref<'_, [u8]> as Deref>::deref(r);
            (s.as_ptr() as usize, s.len())
        })?,
        Held::SharedByte(r) => rec::catch(|| {
            let b: &u8 = <Ref<'_, u8> as Deref>::deref(r);
            (b as *const u8 as usize, core::mem::size_of_val(b))
        })?,
        _ => panic!("guard {k} is not a Ref"),
    };
    Ok(reference(w, addr, len, false))
}

fn op_mut_deref(w: &mut World, k: usize) -> Out {
    let (addr, len) = match &w.guards[k].held {
        Held::ExclusiveBytes(r) => rec::catch(|| {
            let s: &[u8] = <RefMut<'_, [u8]> as Deref>::deref(r);
            (s.as_ptr() as usize, s.len())
        })?,
        Held::ExclusiveByte(r) => rec::catch(|| {
            let b: &u8 = <RefMut<'_, u8> as Deref>::deref(r);
            (b as *const u8 as usize, core::mem::size_of_val(b))
        })?,
        _ => panic!("guard {k} is not a RefMut"),
    };
    Ok(reference(w, addr, len, false))
}

fn op_mut_deref_mut(w: &mut World, k: usize) -> Out {
    let (addr, len) = match &mut w.guards[k].held {
        Held::ExclusiveBytes(r) => rec::catch(|| {
            let s: &mut [u8] = <RefMut<'_, [u8]> as DerefMut>::deref_mut(r);
            (s.as_mut_ptr() as usize, s.len())
        })?,
        Held::ExclusiveByte(r) => rec::catch(|| {
            let b: &mut u8 = <RefMut<'_, u8> as DerefMut>::deref_mut(r);
            (b as *mut u8 as usize, core::mem::size_of_val(b))
        })?,
        _ => panic!("guard {k} is not a RefMut"),
    };
    Ok(reference(w, addr, len, true))
}

fn op_drop(w: &mut World, k: usize) -> Out {
    let held = w.take(k);
    assert!(matches!(
        held,
        Held::SharedBytes(_) | Held::SharedByte(_) | Held::ExclusiveBytes(_) | Held::ExclusiveByte(_)
    ));
    let result = rec::catch(move || drop(held));
    w.guards[k].held = Held::Dropped;
    result.map(|()| Json::Null)
}

fn ptrs(w: &World) -> Vec<*mut RuntimeAccount> {
    (0..w.input.entries.len()).map(|e| w.account_ptr(e)).collect()
}

/// After a `try_map`: the new guard or the returned original under the next
/// generation, or a leaked lease if the closure unwound.
fn mapped(w: &mut World, k: usize, before: (usize, Mode, usize, usize), result: Result<Result<Held, (Held, u8)>, String>) -> Out {
    w.guards[k].generation += 1;
    match result {
        Ok(Ok(new)) => {
            w.guards[k].held = new;
            Ok(rec::ok(w.token(k)))
        }
        Ok(Err((orig, e))) => {
            w.guards[k].held = orig;
            Ok(rec::err(Json::Arr(vec![w.token(k), Json::from(e)])))
        }
        Err(message) => {
            let (cell, mode, offset, length) = before;
            w.guards[k].held = Held::Leaked { cell, mode, offset, length };
            Err(message)
        }
    }
}

fn op_ref_try_map(w: &mut World, k: usize, s: &Script, target: Target) -> Out {
    let before = w.observe(&w.guards[k].held).unwrap();
    let orig = match w.take(k) {
        Held::SharedBytes(r) => r,
        _ => panic!("guard {k} is not a Ref<[u8]>"),
    };
    let ptrs = ptrs(w);
    let s = s.clone();
    let result = rec::catch(move || match target {
        Target::Bytes => Ref::try_map(orig, |d: &[u8]| {
            set_lamports_effects(&s.effects, &ptrs);
            end_slice(d, &s.ending)
        })
        .map(Held::SharedBytes)
        .map_err(|(o, e)| (Held::SharedBytes(o), e)),
        Target::Byte => Ref::try_map(orig, |d: &[u8]| {
            set_lamports_effects(&s.effects, &ptrs);
            end_byte(d, &s.ending)
        })
        .map(Held::SharedByte)
        .map_err(|(o, e)| (Held::SharedBytes(o), e)),
    });
    mapped(w, k, before, result)
}

fn op_mut_try_map(w: &mut World, k: usize, s: &Script, target: Target) -> Out {
    let before = w.observe(&w.guards[k].held).unwrap();
    let orig = match w.take(k) {
        Held::ExclusiveBytes(r) => r,
        _ => panic!("guard {k} is not a RefMut<[u8]>"),
    };
    let ptrs = ptrs(w);
    let s = s.clone();
    let result = rec::catch(move || match target {
        Target::Bytes => RefMut::try_map(orig, |d: &mut [u8]| {
            mut_effects(&s.effects, d, &ptrs);
            end_slice_mut(d, &s.ending)
        })
        .map(Held::ExclusiveBytes)
        .map_err(|(o, e)| (Held::ExclusiveBytes(o), e)),
        Target::Byte => RefMut::try_map(orig, |d: &mut [u8]| {
            mut_effects(&s.effects, d, &ptrs);
            end_byte_mut(d, &s.ending)
        })
        .map(Held::ExclusiveByte)
        .map_err(|(o, e)| (Held::ExclusiveBytes(o), e)),
    });
    mapped(w, k, before, result)
}

// ---------------------------------------------------------------------------
// Borrow configurations reached before the recorded call (unrecorded setup)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Prefix {
    Free,
    /// `n` shared guards on the target, acquired through it.
    Shared(usize),
    Exclusive,
    /// A shared guard mapped to `[offset, length]` of the data.
    MappedShared(usize, usize),
    MappedExclusive(usize, usize),
    /// A shared/exclusive guard leaked by an unwinding `try_map` closure.
    LeakedShared,
    LeakedExclusive,
    /// A successful `close` of the target.
    Closed,
    /// An exclusive guard on another account (instruction account 1).
    OtherExclusive,
    /// A shared guard acquired and dropped again.
    Released,
}

impl Prefix {
    fn name(self) -> String {
        match self {
            Prefix::Free => "free".into(),
            Prefix::Shared(n) => format!("shared{n}"),
            Prefix::Exclusive => "exclusive".into(),
            Prefix::MappedShared(o, l) => format!("mapped_shared_{o}_{l}"),
            Prefix::MappedExclusive(o, l) => format!("mapped_exclusive_{o}_{l}"),
            Prefix::LeakedShared => "leaked_shared".into(),
            Prefix::LeakedExclusive => "leaked_exclusive".into(),
            Prefix::Closed => "closed".into(),
            Prefix::OtherExclusive => "other_exclusive".into(),
            Prefix::Released => "released".into(),
        }
    }
}

fn ok(out: Out) -> Json {
    let json = out.expect("setup call unwound");
    json
}

fn guard_of(result: Json) -> usize {
    match result {
        Json::Obj(fields) if fields[0].0 == "ok" => match &fields[0].1 {
            Json::Obj(inner) => match &inner[0].1 {
                Json::Arr(token) => match token[0] {
                    Json::Int(k) => k as usize,
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        },
        other => panic!("setup acquisition failed: {}", other.to_text()),
    }
}

fn borrow(w: &mut World, i: usize) -> usize {
    guard_of(ok(op_try_borrow(w, i)))
}

fn borrow_mut(w: &mut World, i: usize) -> usize {
    guard_of(ok(op_try_borrow_mut(w, i)))
}

fn setup(w: &mut World, i: usize, prefix: Prefix) {
    match prefix {
        Prefix::Free => {}
        Prefix::Shared(n) => {
            for _ in 0..n {
                borrow(w, i);
            }
        }
        Prefix::Exclusive => {
            borrow_mut(w, i);
        }
        Prefix::MappedShared(o, l) => {
            let k = borrow(w, i);
            ok(op_ref_try_map(w, k, &script(vec![], Ending::Ok(o, l)), Target::Bytes));
        }
        Prefix::MappedExclusive(o, l) => {
            let k = borrow_mut(w, i);
            ok(op_mut_try_map(w, k, &script(vec![], Ending::Ok(o, l)), Target::Bytes));
        }
        Prefix::LeakedShared => {
            let k = borrow(w, i);
            assert!(op_ref_try_map(w, k, &script(vec![], Ending::Panic("setup panic")), Target::Bytes).is_err());
        }
        Prefix::LeakedExclusive => {
            let k = borrow_mut(w, i);
            assert!(op_mut_try_map(w, k, &script(vec![], Ending::Panic("setup panic")), Target::Bytes).is_err());
        }
        Prefix::Closed => {
            ok(op_close(w, i));
        }
        Prefix::OtherExclusive => {
            borrow_mut(w, 1);
        }
        Prefix::Released => {
            let k = borrow(w, i);
            ok(op_drop(w, k));
        }
    }
}

// ---------------------------------------------------------------------------
// Recording
// ---------------------------------------------------------------------------

struct Recorder {
    corpus: Corpus,
}

impl Recorder {
    /// Record one call on `w`: the state before, the arguments, and the
    /// outcome with the state after.
    fn record(
        &mut self,
        id: String,
        function: &'static str,
        generics: Vec<(&'static str, String)>,
        w: &mut World,
        args: Json,
        call: impl FnOnce(&mut World) -> Out,
    ) {
        let state = w.state();
        let result = call(w);
        let after = w.state();
        let outcome = match result {
            Ok(result) => rec::returned(result, after),
            Err(reason) => rec::unwound(reason, after),
        };
        self.corpus.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
    }

    fn view_call(&mut self, op: &str, function: &'static str, input_name: &str, i: usize, prefix: Prefix,
                 extra: Vec<(&'static str, Json)>, tag: &str, call: impl FnOnce(&mut World) -> Out) {
        let mut w = World::new(input(input_name));
        setup(&mut w, i, prefix);
        let mut args = vec![("account".to_string(), Json::from(i))];
        args.extend(extra.into_iter().map(|(k, v)| (k.to_string(), v)));
        let id = format!("{op}/{input_name}/{i}/{}{tag}", prefix.name());
        self.record(id, function, vec![], &mut w, Json::Obj(args), call);
    }
}

fn guard_args(w: &World, k: usize) -> Json {
    Json::obj([("guard", w.token(k))])
}

fn t(name: &str) -> Vec<(&'static str, String)> {
    vec![("T", name.to_string())]
}

fn map_generics(target: Target) -> Vec<(&'static str, String)> {
    vec![("T", "[u8]".to_string()), ("U", target.name().to_string()), ("E", "u8".to_string())]
}

fn held_target(w: &World, k: usize) -> Target {
    match w.guards[k].held {
        Held::SharedByte(_) | Held::ExclusiveByte(_) => Target::Byte,
        _ => Target::Bytes,
    }
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    let mut r = Recorder {
        corpus: Corpus::new(CORPUS, &[("solana-account-view", "2.0.0")]),
    };

    use Prefix::*;

    // Scalar observations: aliases, every lease state, closed accounts.
    let scalar_cases: Vec<(&str, usize, Prefix)> = vec![
        ("ab", 0, Free), ("ab", 0, Shared(1)), ("ab", 0, Exclusive), ("ab", 0, Closed),
        ("ab", 0, LeakedExclusive), ("ab", 1, Free), ("ab", 2, Free), ("ab", 2, Exclusive),
        ("c", 0, Free), ("c", 1, Shared(2)),
    ];
    for &(inp, i, p) in &scalar_cases {
        r.view_call("address", F_ADDRESS, inp, i, p, vec![], "", |w| op_address(w, i));
        r.view_call("lamports", F_LAMPORTS, inp, i, p, vec![], "", |w| op_lamports(w, i));
        r.view_call("data_len", F_DATA_LEN, inp, i, p, vec![], "", |w| op_data_len(w, i));
        r.view_call("is_signer", F_IS_SIGNER, inp, i, p, vec![], "", |w| op_is_signer(w, i));
    }

    // owned_by: matching, other and zero programs.
    let owned_cases: Vec<(&str, usize, Prefix, u8)> = vec![
        ("ab", 0, Free, P1), ("ab", 0, Free, P2), ("ab", 0, Free, 0), ("ab", 1, Free, P2),
        ("ab", 1, Exclusive, P1), ("ab", 2, Shared(1), P1), ("ab", 0, Closed, 0), ("ab", 0, Closed, P1),
        ("c", 0, Free, 0), ("c", 1, Free, P1),
    ];
    for &(inp, i, p, prog) in &owned_cases {
        r.view_call("owned_by", F_OWNED_BY, inp, i, p, vec![("program", rec::bytes(&key(prog)))],
                    &format!("/{prog:02x}"), |w| op_owned_by(w, i, key(prog)));
    }

    // set_lamports: boundary values, under every lease, through an alias.
    let set_cases: Vec<(&str, usize, Prefix, u64)> = vec![
        ("ab", 0, Free, 0), ("ab", 0, Free, 1), ("ab", 0, Free, 999_999_999), ("ab", 0, Free, u64::MAX),
        ("ab", 0, Shared(1), 5), ("ab", 0, Exclusive, 6), ("ab", 0, LeakedShared, 7), ("ab", 2, Free, 8),
        ("ab", 1, Free, u64::MAX), ("ab", 0, Closed, 9), ("c", 1, Free, 0),
    ];
    for &(inp, i, p, v) in &set_cases {
        r.view_call("set_lamports", F_SET_LAMPORTS, inp, i, p, vec![("lamports", Json::from(v))],
                    &format!("/{v}"), |w| op_set_lamports(w, i, v));
    }

    // close: rejected under every live lease of the account, accepted otherwise.
    let close_cases: Vec<(&str, usize, Prefix)> = vec![
        ("ab", 0, Free), ("ab", 1, Free), ("ab", 2, Free), ("ab", 0, Shared(1)), ("ab", 0, Shared(254)),
        ("ab", 0, Exclusive), ("ab", 0, MappedShared(2, 4)), ("ab", 0, LeakedShared), ("ab", 0, LeakedExclusive),
        ("ab", 0, Closed), ("ab", 0, OtherExclusive), ("ab", 0, Released), ("ab", 2, Shared(1)),
        ("c", 0, Free), ("c", 1, Exclusive),
    ];
    for &(inp, i, p) in &close_cases {
        r.view_call("close", F_CLOSE, inp, i, p, vec![], "", |w| op_close(w, i));
    }

    // try_borrow: the shared limit (254), conflicts, leaks, aliases, empty data.
    let borrow_cases: Vec<(&str, usize, Prefix)> = vec![
        ("ab", 0, Free), ("ab", 0, Shared(1)), ("ab", 0, Shared(2)), ("ab", 0, Shared(253)), ("ab", 0, Shared(254)),
        ("ab", 0, Exclusive), ("ab", 0, MappedShared(2, 4)), ("ab", 0, MappedExclusive(0, 8)),
        ("ab", 0, LeakedShared), ("ab", 0, LeakedExclusive), ("ab", 0, Closed), ("ab", 0, OtherExclusive),
        ("ab", 0, Released), ("ab", 1, Free), ("ab", 2, Free), ("ab", 2, Shared(1)), ("ab", 2, Exclusive),
        ("c", 0, Free), ("c", 1, Shared(1)),
    ];
    for &(inp, i, p) in &borrow_cases {
        r.view_call("try_borrow", F_TRY_BORROW, inp, i, p, vec![], "", |w| op_try_borrow(w, i));
    }

    // try_borrow_mut: free only.
    let borrow_mut_cases: Vec<(&str, usize, Prefix)> = vec![
        ("ab", 0, Free), ("ab", 0, Shared(1)), ("ab", 0, Shared(254)), ("ab", 0, Exclusive),
        ("ab", 0, MappedShared(0, 0)), ("ab", 0, LeakedShared), ("ab", 0, LeakedExclusive), ("ab", 0, Closed),
        ("ab", 0, OtherExclusive), ("ab", 0, Released), ("ab", 1, Free), ("ab", 2, Free), ("ab", 2, Shared(1)),
        ("ab", 2, Exclusive), ("c", 0, Free), ("c", 1, LeakedShared),
    ];
    for &(inp, i, p) in &borrow_mut_cases {
        r.view_call("try_borrow_mut", F_TRY_BORROW_MUT, inp, i, p, vec![], "", |w| op_try_borrow_mut(w, i));
    }

    guard_cases(&mut r);
    map_cases(&mut r);

    let n = r.corpus.len();
    r.corpus.write(&out).expect("write corpus");
    eprintln!("{CORPUS}: {n} records");
}

/// A world with guards prepared by `prepare`, which returns the guard the
/// recorded call uses.
fn prepared(input_name: &str, prepare: impl FnOnce(&mut World) -> usize) -> (World, usize) {
    let mut w = World::new(input(input_name));
    let k = prepare(&mut w);
    (w, k)
}

fn map_bytes(w: &mut World, k: usize, o: usize, l: usize) {
    ok(op_ref_try_map(w, k, &script(vec![], Ending::Ok(o, l)), Target::Bytes));
}

fn map_byte(w: &mut World, k: usize, o: usize) {
    ok(op_ref_try_map(w, k, &script(vec![], Ending::Ok(o, 1)), Target::Byte));
}

fn mut_map_bytes(w: &mut World, k: usize, o: usize, l: usize) {
    ok(op_mut_try_map(w, k, &script(vec![], Ending::Ok(o, l)), Target::Bytes));
}

fn mut_map_byte(w: &mut World, k: usize, o: usize) {
    ok(op_mut_try_map(w, k, &script(vec![], Ending::Ok(o, 1)), Target::Byte));
}

type Prepare = Box<dyn Fn(&mut World) -> usize>;

/// Dereference and release of shared and exclusive guards.
fn guard_cases(r: &mut Recorder) {
    let shared: Vec<(&str, &str, Prepare)> = vec![
        ("whole", "ab", Box::new(|w| borrow(w, 0))),
        ("empty_data", "ab", Box::new(|w| borrow(w, 1))),
        ("alias", "ab", Box::new(|w| borrow(w, 2))),
        ("second_of_two", "ab", Box::new(|w| { borrow(w, 0); borrow(w, 0) })),
        ("first_of_two", "ab", Box::new(|w| { let k = borrow(w, 0); borrow(w, 2); k })),
        ("of_254", "ab", Box::new(|w| { for _ in 0..253 { borrow(w, 0); } borrow(w, 0) })),
        ("mapped", "ab", Box::new(|w| { let k = borrow(w, 0); map_bytes(w, k, 2, 4); k })),
        ("mapped_twice", "ab", Box::new(|w| { let k = borrow(w, 0); map_bytes(w, k, 2, 4); map_bytes(w, k, 1, 2); k })),
        ("after_map_error", "ab", Box::new(|w| {
            let k = borrow(w, 0);
            ok(op_ref_try_map(w, k, &script(vec![], Ending::Err(3)), Target::Bytes));
            k
        })),
        ("beside_leaked", "ab", Box::new(|w| { setup(w, 0, Prefix::LeakedShared); borrow(w, 0) })),
        ("after_close", "ab", Box::new(|w| { ok(op_close(w, 0)); borrow(w, 0) })),
        ("odd_length", "c", Box::new(|w| borrow(w, 1))),
        ("byte", "ab", Box::new(|w| { let k = borrow(w, 0); map_byte(w, k, 3); k })),
        ("byte_last", "c", Box::new(|w| { let k = borrow(w, 0); map_byte(w, k, 12); k })),
    ];
    for (name, inp, prepare) in &shared {
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let tn = held_target(&w, k).name();
        // The 254-guard state is recorded for release only: a dereference does not read the count.
        if *name != "of_254" {
            let args = guard_args(&w, k);
            r.record(format!("ref_deref/{inp}/{name}"), F_REF_DEREF, t(tn), &mut w, args, |w| op_ref_deref(w, k));
        }
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let args = guard_args(&w, k);
        r.record(format!("ref_drop/{inp}/{name}"), F_REF_DROP, t(tn), &mut w, args, |w| op_drop(w, k));
    }

    let exclusive: Vec<(&str, &str, Prepare)> = vec![
        ("whole", "ab", Box::new(|w| borrow_mut(w, 0))),
        ("empty_data", "ab", Box::new(|w| borrow_mut(w, 1))),
        ("alias", "ab", Box::new(|w| borrow_mut(w, 2))),
        ("beside_other", "ab", Box::new(|w| { borrow(w, 1); borrow_mut(w, 0) })),
        ("mapped", "ab", Box::new(|w| { let k = borrow_mut(w, 0); mut_map_bytes(w, k, 1, 5); k })),
        ("after_write", "ab", Box::new(|w| {
            let k = borrow_mut(w, 0);
            ok(op_mut_try_map(w, k, &script(vec![Effect::Write(4, vec![0xee, 0xff])], Ending::Ok(0, 8)), Target::Bytes));
            k
        })),
        ("after_map_error", "ab", Box::new(|w| {
            let k = borrow_mut(w, 0);
            ok(op_mut_try_map(w, k, &script(vec![Effect::Write(0, vec![0x77])], Ending::Err(1)), Target::Bytes));
            k
        })),
        ("after_close", "ab", Box::new(|w| { ok(op_close(w, 0)); borrow_mut(w, 0) })),
        ("odd_length", "c", Box::new(|w| borrow_mut(w, 0))),
        ("byte", "ab", Box::new(|w| { let k = borrow_mut(w, 0); mut_map_byte(w, k, 5); k })),
        ("byte_first", "c", Box::new(|w| { let k = borrow_mut(w, 1); mut_map_byte(w, k, 0); k })),
    ];
    for (name, inp, prepare) in &exclusive {
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let tn = held_target(&w, k).name();
        let args = guard_args(&w, k);
        r.record(format!("refmut_deref/{inp}/{name}"), F_MUT_DEREF, t(tn), &mut w, args, |w| op_mut_deref(w, k));
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let args = guard_args(&w, k);
        r.record(format!("refmut_deref_mut/{inp}/{name}"), F_MUT_DEREF_MUT, t(tn), &mut w, args, |w| op_mut_deref_mut(w, k));
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let args = guard_args(&w, k);
        r.record(format!("refmut_drop/{inp}/{name}"), F_MUT_DROP, t(tn), &mut w, args, |w| op_drop(w, k));
    }
}

/// Scripted `try_map` calls.
fn map_cases(r: &mut Recorder) {
    use Effect::*;
    use Ending::*;
    let lam = |i: usize, v: u64| SetLamports(i, v);

    // (name, input, prepare, script, target)
    let shared: Vec<(&str, &str, Prepare, Script, Target)> = vec![
        ("whole", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(0, 8)), Target::Bytes),
        ("middle", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(2, 4)), Target::Bytes),
        ("empty_end", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(8, 0)), Target::Bytes),
        ("empty_start", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(0, 0)), Target::Bytes),
        ("empty_data", "ab", Box::new(|w| borrow(w, 1)), script(vec![], Ok(0, 0)), Target::Bytes),
        ("err_0", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Err(0)), Target::Bytes),
        ("err_255", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Err(255)), Target::Bytes),
        ("panic", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Panic("scripted callback panic")), Target::Bytes),
        ("lamports_held", "ab", Box::new(|w| borrow(w, 0)), script(vec![lam(0, 42)], Ok(1, 3)), Target::Bytes),
        ("lamports_other", "ab", Box::new(|w| borrow(w, 0)), script(vec![lam(1, 43)], Ok(0, 8)), Target::Bytes),
        ("lamports_alias_err", "ab", Box::new(|w| borrow(w, 0)), script(vec![lam(2, 44)], Err(7)), Target::Bytes),
        ("lamports_panic", "ab", Box::new(|w| borrow(w, 0)), script(vec![lam(0, 45), lam(1, 46)], Panic("after effects")), Target::Bytes),
        ("second_of_two", "ab", Box::new(|w| { borrow(w, 2); borrow(w, 0) }), script(vec![], Ok(4, 4)), Target::Bytes),
        ("mapped_again", "ab", Box::new(|w| { let k = borrow(w, 0); map_bytes(w, k, 2, 5); k }), script(vec![], Ok(1, 3)), Target::Bytes),
        ("after_error", "ab", Box::new(|w| {
            let k = borrow(w, 0);
            ok(op_ref_try_map(w, k, &script(vec![], Err(2)), Target::Bytes));
            k
        }), script(vec![], Ok(6, 2)), Target::Bytes),
        ("odd_length", "c", Box::new(|w| borrow(w, 0)), script(vec![], Ok(5, 8)), Target::Bytes),
        ("byte_first", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(0, 1)), Target::Byte),
        ("byte_last", "ab", Box::new(|w| borrow(w, 0)), script(vec![lam(1, 1)], Ok(7, 1)), Target::Byte),
        ("byte_err", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Err(9)), Target::Byte),
        ("byte_panic", "c", Box::new(|w| borrow(w, 1)), script(vec![lam(0, 0)], Panic("byte panic")), Target::Byte),
        ("byte_of_mapped", "ab", Box::new(|w| { let k = borrow(w, 0); map_bytes(w, k, 3, 3); k }), script(vec![], Ok(2, 1)), Target::Byte),
        // Targets outside the closure input slice: indexing within the closure panics.
        ("target_beyond", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(6, 4)), Target::Bytes),
        ("start_beyond", "ab", Box::new(|w| { let k = borrow(w, 0); map_bytes(w, k, 2, 4); k }), script(vec![lam(1, 2)], Ok(5, 0)), Target::Bytes),
        ("byte_beyond", "ab", Box::new(|w| borrow(w, 0)), script(vec![], Ok(8, 1)), Target::Byte),
    ];
    for (name, inp, prepare, s, target) in &shared {
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let args = Json::obj([("guard", w.token(k)), ("callback", s.to_json())]);
        r.record(format!("ref_try_map/{inp}/{name}"), F_REF_TRY_MAP, map_generics(*target), &mut w, args,
                 |w| op_ref_try_map(w, k, s, *target));
    }

    let exclusive: Vec<(&str, &str, Prepare, Script, Target)> = vec![
        ("whole", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![], Ok(0, 8)), Target::Bytes),
        ("middle", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![], Ok(3, 2)), Target::Bytes),
        ("empty_data", "ab", Box::new(|w| borrow_mut(w, 1)), script(vec![], Ok(0, 0)), Target::Bytes),
        ("write", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![Write(1, vec![0xaa, 0xbb, 0xcc])], Ok(1, 3)), Target::Bytes),
        ("write_err", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![Write(6, vec![0x00, 0x00])], Err(4)), Target::Bytes),
        ("write_panic", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![Write(0, vec![0x11])], Panic("write then panic")), Target::Bytes),
        ("err", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![], Err(200)), Target::Bytes),
        ("panic", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![], Panic("scripted callback panic")), Target::Bytes),
        ("lamports_and_write", "ab", Box::new(|w| borrow_mut(w, 0)),
         script(vec![lam(0, 3), Write(7, vec![0x99]), lam(1, 4)], Ok(5, 3)), Target::Bytes),
        ("beside_shared_other", "ab", Box::new(|w| { borrow(w, 1); borrow_mut(w, 0) }), script(vec![lam(1, 12)], Ok(0, 4)), Target::Bytes),
        ("mapped_again", "ab", Box::new(|w| { let k = borrow_mut(w, 0); mut_map_bytes(w, k, 2, 6); k }),
         script(vec![Write(0, vec![0x5a])], Ok(2, 4)), Target::Bytes),
        ("odd_length", "c", Box::new(|w| borrow_mut(w, 1)), script(vec![Write(12, vec![0xf0])], Ok(0, 13)), Target::Bytes),
        ("byte", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![Write(2, vec![0x42])], Ok(2, 1)), Target::Byte),
        ("byte_err", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![Write(3, vec![0x43])], Err(5)), Target::Byte),
        ("byte_panic", "ab", Box::new(|w| borrow_mut(w, 0)), script(vec![], Panic("byte panic")), Target::Byte),
        // A write outside the closure input slice panics after the earlier effects.
        ("write_beyond", "ab", Box::new(|w| borrow_mut(w, 0)),
         script(vec![lam(1, 5), Write(0, vec![0x66]), Write(6, vec![1, 2, 3])], Ok(0, 1)), Target::Bytes),
    ];
    for (name, inp, prepare, s, target) in &exclusive {
        let (mut w, k) = prepared(inp, |w| prepare(w));
        let args = Json::obj([("guard", w.token(k)), ("callback", s.to_json())]);
        r.record(format!("refmut_try_map/{inp}/{name}"), F_MUT_TRY_MAP, map_generics(*target), &mut w, args,
                 |w| op_mut_try_map(w, k, s, *target));
    }
}
