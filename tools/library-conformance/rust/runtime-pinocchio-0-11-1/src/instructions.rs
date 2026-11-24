//! pinocchio 0.11.1 Instructions sysvar over a generic `Deref<Target = [u8]>` receiver.
//!
//! `Instructions::<T>::load_current_index` and `load_instruction_at` are recorded at
//! `T = ScriptedDeref`, whose k-th `deref` returns the k-th scripted slice or panics with the
//! scripted message, so the number and order of the derefs, which slice supplies which length
//! or pointer, and a panic in any of them are observable. `IntrospectedInstruction::
//! get_program_id` and `get_instruction_data` are recorded on instructions at chosen offsets.
//!
//! Memory: every buffer lives in its own 64 KiB region of one 16-aligned arena, so a pointer
//! maps back to its buffer (allocation index) and offset, and the records are independent of
//! the arena address. The state records the buffers and the number of derefs so far. Cases
//! stay inside the admitted model domains (every load is in bounds and the native u16 table
//! load is 2-aligned); outside them the native code has undefined behavior.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use core::cell::Cell;
use std::rc::Rc;
use core::ops::Deref;
use pinocchio::sysvars::instructions::{Instructions, IntrospectedInstruction};

const REGION: usize = 1 << 16;
pub const RECEIVER: &str = "conformance_runtime_pinocchio_0_11_1::instructions::ScriptedDeref<'_>";
const CURRENT: &str = "pinocchio::sysvars::instructions::Instructions::<T>::load_current_index";
const AT: &str = "pinocchio::sysvars::instructions::Instructions::<T>::load_instruction_at";
const PROGRAM_ID: &str = "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_program_id";
const DATA: &str = "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_instruction_data";

pub struct Arena {
    words: Vec<u128>,
    lengths: Vec<usize>,
    contents: Vec<Vec<u8>>,
}

impl Arena {
    pub fn new(buffers: &[Vec<u8>]) -> Arena {
        assert!(buffers.iter().all(|b| b.len() < REGION));
        let mut words = vec![0u128; REGION * buffers.len() / 16 + 1];
        let base = words.as_mut_ptr() as *mut u8;
        for (k, b) in buffers.iter().enumerate() {
            unsafe { core::ptr::copy_nonoverlapping(b.as_ptr(), base.add(REGION * k), b.len()) };
        }
        Arena { words, lengths: buffers.iter().map(Vec::len).collect(), contents: buffers.to_vec() }
    }

    fn base(&self) -> *const u8 {
        self.words.as_ptr() as *const u8
    }

    pub fn ptr(&self, alloc: usize, offset: usize) -> *const u8 {
        assert!(offset <= self.lengths[alloc]);
        unsafe { self.base().add(REGION * alloc + offset) }
    }

    pub fn slice(&self, alloc: usize, offset: usize, len: usize) -> &[u8] {
        assert!(offset + len <= self.lengths[alloc]);
        unsafe { core::slice::from_raw_parts(self.ptr(alloc, offset), len) }
    }

    /// The buffer and offset of a pointer into (or one past the end of) a buffer.
    pub fn locate(&self, p: *const u8) -> (usize, usize) {
        let d = (p as usize).checked_sub(self.base() as usize).expect("pointer below the arena");
        let (alloc, offset) = (d / REGION, d % REGION);
        assert!(alloc < self.lengths.len() && offset <= self.lengths[alloc], "pointer outside every buffer");
        (alloc, offset)
    }

    pub fn state(&self, derefs: Option<usize>) -> Json {
        let memory = Json::arr(self.contents.iter(), |b| rec::bytes(b));
        match derefs {
            Some(n) => Json::obj([("memory", memory), ("derefs", n.into())]),
            None => Json::obj([("memory", memory)]),
        }
    }
}

pub fn pointer_json(p: (usize, usize)) -> Json {
    Json::obj([("allocation", p.0.into()), ("offset", p.1.into())])
}

#[derive(Clone)]
pub enum Reply {
    Slice(usize, usize, usize),
    Panic(String),
}

impl Reply {
    fn json(&self) -> Json {
        match self {
            Reply::Slice(a, o, l) => Json::obj([(
                "slice",
                Json::obj([("allocation", (*a).into()), ("offset", (*o).into()), ("length", (*l).into())]),
            )]),
            Reply::Panic(m) => Json::obj([("panic", m.as_str().into())]),
        }
    }
}

/// The generic receiver: its k-th `deref` returns the k-th scripted reply. A missing reply
/// panics with a fixed message.
pub struct ScriptedDeref<'a> {
    arena: &'a Arena,
    script: Vec<Reply>,
    calls: Rc<Cell<usize>>,
}

pub const EXHAUSTED: &str = "deref script exhausted";

impl Deref for ScriptedDeref<'_> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        let n = self.calls.get();
        self.calls.set(n + 1);
        match self.script.get(n) {
            Some(Reply::Slice(a, o, l)) => self.arena.slice(*a, *o, *l),
            Some(Reply::Panic(m)) => panic!("{}", m),
            None => panic!("{}", EXHAUSTED),
        }
    }
}

/// The Instructions sysvar serialization: count, offset table, entries (account count,
/// accounts as flag byte and key, program id, data length, data), then the current index.
pub struct Ix {
    pub accounts: Vec<(u8, [u8; 32])>,
    pub program: [u8; 32],
    pub data: Vec<u8>,
}

/// An address that is zero except its first and last bytes (cheap under zero-run encoding).
pub fn key(seed: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = seed;
    k[31] = seed ^ 0x80;
    k
}

pub fn entry(ix: &Ix) -> Vec<u8> {
    let mut out = (ix.accounts.len() as u16).to_le_bytes().to_vec();
    for (flags, k) in &ix.accounts {
        out.push(*flags);
        out.extend_from_slice(k);
    }
    out.extend_from_slice(&ix.program);
    out.extend_from_slice(&(ix.data.len() as u16).to_le_bytes());
    out.extend_from_slice(&ix.data);
    out
}

pub fn serialize(ixs: &[Ix], current: u16) -> Vec<u8> {
    let mut out = (ixs.len() as u16).to_le_bytes().to_vec();
    out.resize(2 + 2 * ixs.len(), 0);
    for (i, ix) in ixs.iter().enumerate() {
        let offset = out.len() as u16;
        out[2 + 2 * i..4 + 2 * i].copy_from_slice(&offset.to_le_bytes());
        out.extend(entry(ix));
    }
    out.extend_from_slice(&current.to_le_bytes());
    out
}

fn sample_ixs() -> Vec<Ix> {
    vec![
        Ix { accounts: vec![], program: key(1), data: vec![] },
        Ix { accounts: vec![(3, key(2)), (0, key(3))], program: key(4), data: vec![9, 8, 7] },
        Ix { accounts: vec![(1, key(5))], program: key(6), data: (1..=6u8).collect() },
    ]
}

fn push(c: &mut Corpus, id: String, function: &'static str, generic: bool, state: Json, args: Json, outcome: Json) {
    let generics = if generic { vec![("T", RECEIVER.to_string())] } else { vec![] };
    c.push(Record { id, function, generics, layout: None, state, args, outcome, observed: None });
}

/// The receiver and a handle on its deref counter (`Instructions` keeps the receiver private).
fn receiver<'a>(arena: &'a Arena, script: &[Reply]) -> (Instructions<ScriptedDeref<'a>>, Rc<Cell<usize>>) {
    let calls = Rc::new(Cell::new(0));
    let data = ScriptedDeref { arena, script: script.to_vec(), calls: calls.clone() };
    // SAFETY: `new_unchecked` only stores the receiver; every case keeps the reads in bounds.
    (unsafe { Instructions::new_unchecked(data) }, calls)
}

fn current_case(c: &mut Corpus, id: &str, arena: &Arena, script: Vec<Reply>) {
    let (i, calls) = receiver(arena, &script);
    let args = Json::obj([("receiver", Json::arr(script.iter(), Reply::json))]);
    let result = rec::catch(|| i.load_current_index());
    let after = arena.state(Some(calls.get()));
    let outcome = match result {
        Ok(v) => rec::returned(Json::from(v), after),
        Err(reason) => rec::unwound(reason, after),
    };
    push(c, format!("load_current_index/{id}"), CURRENT, true, arena.state(Some(0)), args, outcome);
}

fn at_case(c: &mut Corpus, id: &str, arena: &Arena, script: Vec<Reply>, index: usize) {
    let (i, calls) = receiver(arena, &script);
    let args = Json::obj([("receiver", Json::arr(script.iter(), Reply::json)), ("index", index.into())]);
    let result = rec::catch(|| {
        i.load_instruction_at(index).map(|ix| {
            // SAFETY: `IntrospectedInstruction` is `repr(C)` with its raw pointer first and a
            // zero-sized marker; its private pointer is read back here.
            arena.locate(unsafe { core::mem::transmute::<IntrospectedInstruction<'_>, *const u8>(ix) })
        })
    });
    let after = arena.state(Some(calls.get()));
    let outcome = match result {
        Ok(Ok(p)) => rec::returned(rec::ok(pointer_json(p)), after),
        Ok(Err(e)) => rec::returned(rec::err(format!("{e:?}").into()), after),
        Err(reason) => rec::unwound(reason, after),
    };
    push(c, format!("load_instruction_at/{id}"), AT, true, arena.state(Some(0)), args, outcome);
}

fn introspected(arena: &Arena, at: (usize, usize)) -> IntrospectedInstruction<'_> {
    // SAFETY: see `at_case`; the pointer is in bounds of the arena.
    unsafe { core::mem::transmute::<*const u8, IntrospectedInstruction<'_>>(arena.ptr(at.0, at.1)) }
}

fn program_case(c: &mut Corpus, id: &str, arena: &Arena, at: (usize, usize)) {
    let ix = introspected(arena, at);
    let result = rec::catch(|| arena.locate(ix.get_program_id() as *const _ as *const u8));
    let outcome = match result {
        Ok(p) => rec::returned(pointer_json(p), arena.state(None)),
        Err(reason) => rec::unwound(reason, arena.state(None)),
    };
    let args = Json::obj([("instruction", pointer_json(at))]);
    push(c, format!("get_program_id/{id}"), PROGRAM_ID, false, arena.state(None), args, outcome);
}

fn data_case(c: &mut Corpus, id: &str, arena: &Arena, at: (usize, usize)) {
    let ix = introspected(arena, at);
    let result = rec::catch(|| {
        let d = ix.get_instruction_data();
        (arena.locate(d.as_ptr()), d.len())
    });
    let outcome = match result {
        Ok((p, len)) => rec::returned(
            Json::obj([("pointer", pointer_json(p)), ("length", len.into())]),
            arena.state(None),
        ),
        Err(reason) => rec::unwound(reason, arena.state(None)),
    };
    let args = Json::obj([("instruction", pointer_json(at))]);
    push(c, format!("get_instruction_data/{id}"), DATA, false, arena.state(None), args, outcome);
}

fn whole(bufs: &[&Vec<u8>], k: usize) -> Reply {
    Reply::Slice(k, 0, bufs[k].len())
}

fn arena(bufs: &[&Vec<u8>]) -> Arena {
    Arena::new(&bufs.iter().map(|b| (*b).clone()).collect::<Vec<_>>())
}

pub fn record(c: &mut Corpus) {
    let ixs = sample_ixs();
    let none = serialize(&[], 0);
    let one = serialize(&ixs[..1], 0);
    let three = serialize(&ixs, 2);
    let max_index = serialize(&ixs[1..2], u16::MAX);
    // Entries at an odd offset of a raw buffer, and a two-byte buffer.
    let mut odd = vec![0xee];
    odd.extend(entry(&ixs[1]));
    odd.extend(entry(&ixs[2]));
    let footer2 = vec![0x34, 0x12];

    // load_current_index: two derefs, the length from the first, the pointer from the second.
    for (name, b) in [("none", &none), ("three", &three), ("max_index", &max_index), ("two_bytes", &footer2)] {
        let bufs = [b];
        current_case(c, name, &arena(&bufs), vec![whole(&bufs, 0), whole(&bufs, 0)]);
    }
    let t = [&three];
    current_case(c, "subslice", &arena(&t), vec![Reply::Slice(0, 3, 10), Reply::Slice(0, 3, 10)]);
    let o = [&odd];
    current_case(c, "odd_subslice", &arena(&o), vec![Reply::Slice(0, 1, 7), Reply::Slice(0, 1, 7)]);
    let ot = [&one, &three];
    current_case(c, "length_first_pointer_second", &arena(&ot), vec![whole(&ot, 0), whole(&ot, 1)]);
    let ft = [&footer2, &three];
    current_case(c, "shorter_first", &arena(&ft), vec![Reply::Slice(0, 0, 2), Reply::Slice(1, 6, 30)]);
    current_case(c, "panic_first", &arena(&t), vec![Reply::Panic("deref panic 0".into())]);
    current_case(c, "panic_second", &arena(&t), vec![whole(&t, 0), Reply::Panic("deref panic 1".into())]);
    current_case(c, "exhausted_second", &arena(&t), vec![whole(&t, 0)]);
    let m = [&max_index];
    current_case(c, "extra_replies", &arena(&m), vec![whole(&m, 0), whole(&m, 0), Reply::Panic("unused".into())]);

    // load_instruction_at: one deref for the count; on success two more, for the table and the
    // returned base. Per buffer: the first and last index in range, the first out of range and
    // the largest index.
    for (name, b, indices) in [("none", &none, vec![0, usize::MAX]), ("one", &one, vec![0, 1]),
                               ("three", &three, vec![0, 2, 3, usize::MAX])] {
        let bufs = [b];
        for index in indices {
            let label = if index == usize::MAX { "index_max".to_string() } else { format!("index{index}") };
            at_case(c, &format!("{name}/{label}"), &arena(&bufs), vec![whole(&bufs, 0); 3], index);
        }
    }
    at_case(c, "out_of_range_one_deref", &arena(&t), vec![whole(&t, 0)], 3);
    at_case(c, "panic_first", &arena(&t), vec![Reply::Panic("deref panic 0".into())], 0);
    at_case(c, "panic_second", &arena(&t), vec![whole(&t, 0), Reply::Panic("deref panic 1".into())], 1);
    at_case(c, "panic_third", &arena(&t), vec![whole(&t, 0), whole(&t, 0), Reply::Panic("deref panic 2".into())], 2);
    at_case(c, "exhausted_third", &arena(&t), vec![whole(&t, 0), whole(&t, 0)], 0);
    // The count and table from `three`, the returned base from `odd`.
    let to = [&three, &odd];
    at_case(c, "base_from_third", &arena(&to), vec![whole(&to, 0), whole(&to, 0), whole(&to, 1)], 0);
    // The count from `three`, the table from `one` (one entry at offset 4), the base from
    // `max_index`.
    let tom = [&three, &one, &max_index];
    at_case(c, "table_from_second", &arena(&tom), vec![whole(&tom, 0), whole(&tom, 1), whole(&tom, 2)], 0);
    // An even subslice of `three` as count and table: its first word is the offset of entry 0,
    // so the count is large and the table is read past the real one; the base is the subslice.
    at_case(c, "even_subslice", &arena(&t), vec![Reply::Slice(0, 2, 40); 3], 1);

    // get_program_id and get_instruction_data: the first and last entry of `three` (no
    // accounts and no data; one account and data), and entries at odd offsets.
    for i in [0usize, 2] {
        let at = (0, u16::from_le_bytes([three[2 + 2 * i], three[3 + 2 * i]]) as usize);
        program_case(c, &format!("three/entry{i}"), &arena(&t), at);
        data_case(c, &format!("three/entry{i}"), &arena(&t), at);
    }
    for (i, at) in [1, 1 + entry(&ixs[1]).len()].into_iter().enumerate() {
        program_case(c, &format!("odd/entry{i}"), &arena(&o), (0, at));
        data_case(c, &format!("odd/entry{i}"), &arena(&o), (0, at));
    }
}
