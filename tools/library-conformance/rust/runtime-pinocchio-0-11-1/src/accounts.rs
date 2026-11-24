//! pinocchio 0.11.1 over loader-serialized accounts (`conformance-accounts`): `Rent::
//! from_account_view`, `Instructions::try_from` and, on the `Instructions<Ref<[u8]>>` it
//! returns, `load_current_index`, `load_instruction_at`, and `get_program_id` and
//! `get_instruction_data` of the introspected instructions.
//!
//! A record state is the shape the AccountsV2 projection reads:
//! `{"input": <Region::read_back>, "backing": [hex], "guards": [entry], "owner_epochs": [n]}`,
//! where `backing[c]` is the data area of the c-th non-duplicate account up to its serialized length
//! (read through the region) and `guards[k]` is the k-th acquired guard as
//! `[cell, mode, generation, offset, length]` (`null` once dropped). An argument
//! `{"account": i}` is the `AccountView` of instruction account `i` (a duplicate denotes its
//! first occurrence). An `Instructions` value is `{"guard": [id, generation]}`; an introspected
//! instruction, program id or data reference is its offset from the guarded slice base.

use conformance_accounts::{Account, Entry, Input, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use pinocchio::account::{AccountView, Ref, RuntimeAccount};
use pinocchio::sysvars::instructions::{Instructions, IntrospectedInstruction, INSTRUCTIONS_ID};
use pinocchio::sysvars::rent::{Rent, RENT_ID};

const FROM_ACCOUNT_VIEW: &str = "pinocchio::sysvars::rent::Rent::from_account_view";
const TRY_FROM: &str = "<pinocchio::sysvars::instructions::Instructions<solana_account_view::Ref<'a, [u8]>> as core::convert::TryFrom<&'a solana_account_view::AccountView>>::try_from";
const CURRENT: &str = "pinocchio::sysvars::instructions::Instructions::<T>::load_current_index";
const AT: &str = "pinocchio::sysvars::instructions::Instructions::<T>::load_instruction_at";
const PROGRAM_ID: &str = "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_program_id";
const DATA: &str = "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_instruction_data";
pub const REF: &str = "solana_account_view::Ref<'_, [u8]>";
const HEADER: usize = 88;

#[derive(Clone, Copy)]
struct GuardEntry {
    cell: usize,
    exclusive: bool,
    offset: usize,
    length: usize,
}

struct World {
    input: Input,
    region: Region,
    guards: Vec<Option<GuardEntry>>,
}

impl World {
    fn new(input: Input) -> World {
        let region = input.serialize();
        World { input, region, guards: vec![] }
    }

    /// The first occurrence of instruction account `i`.
    fn first(&self, i: usize) -> usize {
        match self.input.entries[i] {
            Entry::Account(_) => i,
            Entry::Duplicate(j) => j as usize,
        }
    }

    /// The cell of instruction account `i`: its first occurrence among non-duplicates.
    fn cell(&self, i: usize) -> usize {
        let f = self.first(i);
        self.input.entries[..f].iter().filter(|e| matches!(e, Entry::Account(_))).count()
    }

    fn account_index_of_cell(&self, cell: usize) -> usize {
        self.input.entries.iter().enumerate().filter(|(_, e)| matches!(e, Entry::Account(_))).nth(cell).unwrap().0
    }

    fn view(&mut self, i: usize) -> AccountView {
        let p = self.region.account_ptr(self.first(i)) as *mut RuntimeAccount;
        unsafe { AccountView::new_unchecked(p) }
    }

    fn data_ptr(&mut self, i: usize) -> usize {
        self.region.account_ptr(self.first(i)) as usize + HEADER
    }

    fn state(&self) -> Json {
        let bytes = self.region.bytes();
        let backing = Json::arr(self.input.entries.iter().enumerate().filter_map(|(i, e)| match e {
            Entry::Account(a) => Some((i, a.data.len())),
            Entry::Duplicate(_) => None,
        }), |(i, len)| {
            let start = self.region.account_offset(i) + HEADER;
            rec::bytes(&bytes[start..start + len])
        });
        let cells = self.input.entries.iter().filter(|e| matches!(e, Entry::Account(_))).count();
        Json::obj([
            ("input", self.region.read_back()),
            ("backing", backing),
            ("guards", Json::arr(self.guards.iter(), |g| match g {
                None => Json::Null,
                Some(g) => Json::Arr(vec![
                    g.cell.into(),
                    (if g.exclusive { "exclusive" } else { "shared" }).into(),
                    0u64.into(),
                    g.offset.into(),
                    g.length.into(),
                ]),
            })),
            ("owner_epochs", Json::arr(0..cells, |_| Json::from(0u64))),
        ])
    }
}

fn account(key: [u8; 32], data: Vec<u8>) -> Account {
    Account { key, owner: crate::instructions::key(6), lamports: 1_000_000, data, is_signer: false, is_writable: false, executable: false, rent_epoch: u64::MAX }
}

fn input(entries: Vec<Entry>) -> Input {
    Input { entries, instruction_data: vec![1, 2, 3], program_id: [9; 32] }
}

fn push(c: &mut Corpus, id: String, function: &'static str, generic: bool, state: Json, args: Json, outcome: Json) {
    let generics = if generic { vec![("T", REF.to_string())] } else { vec![] };
    c.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
}

fn program_error<T>(r: &Result<T, pinocchio::error::ProgramError>, ok: impl Fn(&T) -> Json) -> Json {
    match r {
        Ok(v) => rec::ok(ok(v)),
        Err(e) => rec::err(format!("{e:?}").into()),
    }
}

/// A live guard acquired before the call, held while it runs.
#[allow(dead_code)]
enum Held<'a> {
    None,
    Shared(Ref<'a, [u8]>),
    Exclusive(pinocchio::account::RefMut<'a, [u8]>),
}

/// Acquire a guard on instruction account `i` before the call, through account-view
/// `try_borrow`/`try_borrow_mut`, and record it in the world guard list.
fn hold<'a>(w: &mut World, view: &'a mut AccountView, i: usize, mode: &str) -> Held<'a> {
    let cell = w.cell(i);
    let len = view.data_len();
    match mode {
        "shared" => {
            let g = view.try_borrow().expect("free account");
            w.guards.push(Some(GuardEntry { cell, exclusive: false, offset: 0, length: len }));
            Held::Shared(g)
        }
        "exclusive" => {
            let g = view.try_borrow_mut().expect("free account");
            w.guards.push(Some(GuardEntry { cell, exclusive: true, offset: 0, length: len }));
            Held::Exclusive(g)
        }
        _ => Held::None,
    }
}

fn rent_case(c: &mut Corpus, id: &str, entries: Vec<Entry>, i: usize, mode: &str) {
    let mut w = World::new(input(entries));
    let mut holder = w.view(i);
    // SAFETY: the holder outlives the call; the guard is released after the record.
    let holder_ref: &'static mut AccountView = unsafe { &mut *(&mut holder as *mut AccountView) };
    let held = hold(&mut w, holder_ref, i, mode);
    let view = w.view(i);
    let before = w.state();
    let result = rec::catch(|| Rent::from_account_view(&view));
    let after = w.state();
    let outcome = match result {
        Ok(r) => rec::returned(program_error(&r, |rent| {
            // `Rent` is `repr(C)` with its private rate as the only field.
            Json::obj([("lamports_per_byte", unsafe { *(rent as *const Rent as *const u64) }.into())])
        }), after),
        Err(reason) => rec::unwound(reason, after),
    };
    drop(held);
    push(c, format!("from_account_view/{id}"), FROM_ACCOUNT_VIEW, false, before, Json::obj([("account", i.into())]), outcome);
}

fn guard_json(id: usize) -> Json {
    Json::obj([("guard", Json::Arr(vec![id.into(), 0u64.into()]))])
}

/// Read back the guard an `Instructions<Ref<[u8]>>` holds: its slice (pointer, length) and
/// its borrow-state pointer, found among the machine words storing the value (the field order of `Ref` is not
/// fixed by its declaration).
fn held_guard(w: &mut World, i: usize, ix: &Instructions<Ref<'_, [u8]>>) -> GuardEntry {
    assert_eq!(core::mem::size_of::<Instructions<Ref<'_, [u8]>>>(), 24);
    let words: [usize; 3] = unsafe { core::mem::transmute_copy(ix) };
    let state = w.region.account_ptr(w.first(i)) as usize;
    let data = w.data_ptr(i);
    let si = words.iter().position(|&x| x == state).expect("borrow-state pointer");
    let others: Vec<usize> = (0..3).filter(|&k| k != si).collect();
    let is_pointer = |x: usize| x >= data && x - data < (1 << 24);
    let (p, l) = if is_pointer(words[others[0]]) {
        (words[others[0]], words[others[1]])
    } else {
        (words[others[1]], words[others[0]])
    };
    assert!(is_pointer(p) && !is_pointer(l), "unexpected Ref layout");
    GuardEntry { cell: w.cell(i), exclusive: false, offset: p - data, length: l }
}

fn instructions_case(c: &mut Corpus, id: &str, entries: Vec<Entry>, i: usize, mode: &str, follow: Follow) {
    let mut w = World::new(input(entries));
    let mut holder = w.view(i);
    let holder_ref: &'static mut AccountView = unsafe { &mut *(&mut holder as *mut AccountView) };
    let held = hold(&mut w, holder_ref, i, mode);
    let view: &'static AccountView = Box::leak(Box::new(w.view(i)));
    let before = w.state();
    let result = rec::catch(|| Instructions::try_from(view));
    let args = Json::obj([("account", i.into())]);
    let (outcome, ix) = match result {
        Ok(Ok(ix)) => {
            let g = held_guard(&mut w, i, &ix);
            w.guards.push(Some(g));
            (rec::returned(rec::ok(guard_json(w.guards.len() - 1)), w.state()), Some(ix))
        }
        Ok(Err(e)) => (rec::returned(rec::err(format!("{e:?}").into()), w.state()), None),
        Err(reason) => (rec::unwound(reason, w.state()), None),
    };
    push(c, format!("try_from/{id}"), TRY_FROM, false, before, args, outcome);
    if let (false, Some(ix)) = (matches!(follow, Follow::None), ix) {
        let source = guard_json(w.guards.len() - 1);
        let base = w.data_ptr(i);
        follow_up(c, id, &w, &ix, &source, base, matches!(follow, Follow::Full));
    }
    drop(held);
}

/// The calls recorded on the `Instructions` that `try_from` returned: none; the current index
/// and the first entry; or also the last entry in range, the first out of range and the
/// largest index, with the program id and data of the first and last entries.
#[derive(Clone, Copy)]
enum Follow {
    None,
    Brief,
    Full,
}

fn follow_up(c: &mut Corpus, id: &str, w: &World, ix: &Instructions<Ref<'_, [u8]>>, source: &Json, base: usize,
             full: bool) {
    let state = w.state();
    let r = rec::catch(|| ix.load_current_index());
    let outcome = match r {
        Ok(v) => rec::returned(Json::from(v), w.state()),
        Err(reason) => rec::unwound(reason, w.state()),
    };
    push(c, format!("load_current_index/{id}"), CURRENT, true, state.clone(), Json::obj([("source", source.clone())]), outcome);
    let n = ix.num_instructions();
    let indices: Vec<usize> = if full { vec![0, n - 1, n, usize::MAX] } else { vec![0] };
    for index in indices {
        let r = rec::catch(|| ix.load_instruction_at(index).map(|x| {
            // SAFETY: `IntrospectedInstruction` is `repr(C)` with its raw pointer first.
            (unsafe { core::mem::transmute::<IntrospectedInstruction<'_>, *const u8>(x) }) as usize - base
        }));
        let outcome = match r {
            Ok(res) => rec::returned(
                program_error(&res, |off| Json::obj([("source", source.clone()), ("offset", (*off).into())])),
                w.state(),
            ),
            Err(reason) => rec::unwound(reason, w.state()),
        };
        let args = Json::obj([("source", source.clone()), ("index", index.into())]);
        push(c, format!("load_instruction_at/{id}/index{}", if index == usize::MAX { "_max".to_string() } else { index.to_string() }),
            AT, true, state.clone(), args, outcome);
        if index < n && (full || index == 0) {
            let x = ix.load_instruction_at(index).unwrap();
            let off = (unsafe { core::mem::transmute::<IntrospectedInstruction<'_>, *const u8>(x.clone()) }) as usize - base;
            let instruction = Json::obj([("source", source.clone()), ("offset", off.into())]);
            let r = rec::catch(|| x.get_program_id() as *const _ as usize - base);
            let outcome = match r {
                Ok(p) => rec::returned(Json::obj([("source", source.clone()), ("offset", p.into())]), w.state()),
                Err(reason) => rec::unwound(reason, w.state()),
            };
            push(c, format!("get_program_id/{id}/entry{index}"), PROGRAM_ID, false, state.clone(),
                Json::obj([("instruction", instruction.clone())]), outcome);
            let r = rec::catch(|| {
                let d = x.get_instruction_data();
                (d.as_ptr() as usize - base, d.len())
            });
            let outcome = match r {
                Ok((p, l)) => rec::returned(
                    Json::obj([("source", source.clone()), ("offset", p.into()), ("length", l.into())]),
                    w.state(),
                ),
                Err(reason) => rec::unwound(reason, w.state()),
            };
            push(c, format!("get_instruction_data/{id}/entry{index}"), DATA, false, state.clone(),
                Json::obj([("instruction", instruction)]), outcome);
        }
    }
    let _ = w.account_index_of_cell(0);
}

pub fn corpus() -> Corpus {
    use crate::instructions::{entry, key, serialize, Ix};
    let mut c = Corpus::new("pinocchio_0_11_1_accounts", &[("pinocchio", "0.11.1"), ("solana-account-view", "2.0.0")]);
    let rent_id: [u8; 32] = RENT_ID.to_bytes();
    let ix_id: [u8; 32] = INSTRUCTIONS_ID.to_bytes();
    let other = key(200);

    // Rent::from_account_view: exclusive lease first, then the address, then an unaligned
    // eight-byte read; no guard is acquired.
    let rent8 = 6960u64.to_le_bytes().to_vec();
    let mut rent17 = 3480u64.to_le_bytes().to_vec();
    rent17.extend_from_slice(&2.0f64.to_le_bytes());
    rent17.push(50);
    let a = |k: [u8; 32], d: &Vec<u8>| Entry::Account(account(k, d.clone()));
    rent_case(&mut c, "rate", vec![a(rent_id, &rent8)], 0, "none");
    rent_case(&mut c, "sdk_layout", vec![a(rent_id, &rent17)], 0, "none");
    rent_case(&mut c, "max_rate", vec![a(rent_id, &u64::MAX.to_le_bytes().to_vec())], 0, "none");
    rent_case(&mut c, "exclusive", vec![a(rent_id, &rent8)], 0, "exclusive");
    rent_case(&mut c, "shared", vec![a(rent_id, &rent8)], 0, "shared");
    rent_case(&mut c, "wrong_address", vec![a(other, &rent8)], 0, "none");
    rent_case(&mut c, "wrong_address_exclusive", vec![a(other, &rent8)], 0, "exclusive");
    rent_case(&mut c, "wrong_address_short", vec![a(other, &vec![1])], 0, "none");
    rent_case(&mut c, "second", vec![a(other, &rent8), a(rent_id, &rent17)], 1, "none");
    rent_case(&mut c, "duplicate", vec![a(rent_id, &rent17), Entry::Duplicate(0)], 1, "none");
    rent_case(&mut c, "duplicate_exclusive", vec![a(rent_id, &rent17), Entry::Duplicate(0)], 1, "exclusive");

    // Instructions::try_from: the address first, then a shared acquisition; no size check.
    let ixs = vec![
        Ix { accounts: vec![], program: key(1), data: vec![] },
        Ix { accounts: vec![(3, key(2)), (0, key(3))], program: key(4), data: vec![9, 8, 7] },
        Ix { accounts: vec![(1, key(5))], program: key(6), data: (1..=6u8).collect() },
    ];
    let three = serialize(&ixs, 2);
    let one = serialize(&ixs[1..2], 0);
    let _ = entry(&ixs[0]);
    instructions_case(&mut c, "three", vec![a(ix_id, &three)], 0, "none", Follow::Full);
    instructions_case(&mut c, "one_second", vec![a(other, &one), a(ix_id, &one)], 1, "none", Follow::Brief);
    instructions_case(&mut c, "duplicate", vec![a(ix_id, &one), Entry::Duplicate(0)], 1, "none", Follow::Brief);
    instructions_case(&mut c, "shared", vec![a(ix_id, &one)], 0, "shared", Follow::Brief);
    instructions_case(&mut c, "empty", vec![a(ix_id, &vec![])], 0, "none", Follow::None);
    instructions_case(&mut c, "exclusive", vec![a(ix_id, &one)], 0, "exclusive", Follow::None);
    instructions_case(&mut c, "wrong_address", vec![a(other, &one)], 0, "none", Follow::None);
    instructions_case(&mut c, "wrong_address_exclusive", vec![a(other, &one)], 0, "exclusive", Follow::None);
    c
}
