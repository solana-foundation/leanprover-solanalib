//! Scripted trait callbacks for the generic Anchor constructors: `Owner`,
//! `CheckOwner` and `AccountDeserialize` of `Scripted`, `Owner` of the
//! zero-copy types. The k-th call of a callback runs step k of its script:
//! log the call, apply the effects of the step (owner assignment, lamports store),
//! then panic with `"script <callback>"` or return. An exhausted script panics
//! with `"script exhausted"`. The Lean checker instantiates the models'
//! callbacks with the same scripts.

use std::cell::RefCell;

use anchor_lang::error::Error;
use anchor_lang::prelude::*;
use anchor_lang::solana_program::program_error::ProgramError;
use conformance_recorder::{self as rec, Json};

use crate::enc;
use crate::world::World;

#[derive(Clone, Default)]
pub struct OwnerStep {
    pub returns: [u8; 32],
    pub assign: Option<[u8; 32]>,
    pub panic: bool,
}

#[derive(Clone)]
pub struct CheckStep {
    pub err: Option<ProgramError>,
    pub assign: Option<[u8; 32]>,
    pub panic: bool,
}

#[derive(Clone)]
pub struct DecodeStep {
    pub result: std::result::Result<u64, ProgramError>,
    pub assign: Option<[u8; 32]>,
    pub lamports: Option<u64>,
    pub panic: bool,
}

#[derive(Clone, Default)]
pub struct Script {
    pub owner: Vec<OwnerStep>,
    pub check: Vec<CheckStep>,
    pub decode: Vec<DecodeStep>,
}

pub fn owner_returns(key: [u8; 32]) -> OwnerStep {
    OwnerStep { returns: key, assign: None, panic: false }
}

pub fn check_ok() -> CheckStep {
    CheckStep { err: None, assign: None, panic: false }
}

pub fn decode_ok(n: u64) -> DecodeStep {
    DecodeStep { result: Ok(n), assign: None, lamports: None, panic: false }
}

fn opt_key(k: &Option<[u8; 32]>) -> Json {
    match k {
        Some(k) => rec::bytes(k),
        None => Json::Null,
    }
}

impl Script {
    pub fn json(&self) -> Json {
        Json::obj([
            ("owner", Json::arr(self.owner.iter(), |s| Json::obj([
                ("returns", rec::bytes(&s.returns)), ("assign", opt_key(&s.assign)), ("panic", s.panic.into())]))),
            ("check_owner", Json::arr(self.check.iter(), |s| Json::obj([
                ("err", match &s.err { Some(e) => enc::program_error(e), None => Json::Null }),
                ("assign", opt_key(&s.assign)), ("panic", s.panic.into())]))),
            ("deserialize", Json::arr(self.decode.iter(), |s| Json::obj([
                ("result", match &s.result { Ok(n) => rec::ok((*n).into()), Err(e) => rec::err(enc::program_error(e)) }),
                ("assign", opt_key(&s.assign)),
                ("lamports", match s.lamports { Some(l) => l.into(), None => Json::Null }),
                ("panic", s.panic.into())]))),
        ])
    }
}

struct Active {
    script: Script,
    calls: [usize; 3],
    log: Vec<Json>,
    world: Option<&'static World>,
    target: Option<&'static AccountInfo<'static>>,
}

thread_local! {
    static ACTIVE: RefCell<Active> = const { RefCell::new(Active { script: Script { owner: vec![], check: vec![], decode: vec![] }, calls: [0; 3], log: vec![], world: None, target: None }) };
}

/// Install a script whose effects apply to `target` (the account under construction).
pub fn install(script: Script, world: &'static World, target: &'static AccountInfo<'static>) {
    ACTIVE.with(|a| {
        let mut a = a.borrow_mut();
        a.script = script;
        a.calls = [0; 3];
        a.log.clear();
        a.world = Some(world);
        a.target = Some(target);
    });
}

pub fn log() -> Json {
    ACTIVE.with(|a| Json::Arr(a.borrow().log.clone()))
}

fn push(event: Json) {
    ACTIVE.with(|a| a.borrow_mut().log.push(event));
}

fn target() -> &'static AccountInfo<'static> {
    ACTIVE.with(|a| a.borrow().target.expect("no script target"))
}

fn assign(key: &Option<[u8; 32]>) {
    if let Some(k) = key {
        target().assign(&Pubkey::new_from_array(*k));
    }
}

fn step<T: Clone>(which: usize, pick: impl Fn(&Script) -> &Vec<T>) -> T {
    let s = ACTIVE.with(|a| {
        let mut a = a.borrow_mut();
        let k = a.calls[which];
        a.calls[which] += 1;
        pick(&a.script).get(k).cloned()
    });
    match s {
        Some(s) => s,
        None => panic!("script exhausted"),
    }
}

pub fn owner() -> Pubkey {
    push(Json::obj([("owner", Json::Null)]));
    let s = step(0, |sc| &sc.owner);
    assign(&s.assign);
    if s.panic {
        panic!("script owner");
    }
    Pubkey::new_from_array(s.returns)
}

pub fn check_owner(owner: &Pubkey) -> anchor_lang::Result<()> {
    let world = ACTIVE.with(|a| a.borrow().world.expect("no world"));
    push(Json::obj([("check_owner", world.owner_ref(owner).into())]));
    let s = step(1, |sc| &sc.check);
    assign(&s.assign);
    if s.panic {
        panic!("script check_owner");
    }
    match s.err {
        None => Ok(()),
        Some(e) => Err(Error::from(e)),
    }
}

pub fn deserialize(buf: &mut &[u8]) -> anchor_lang::Result<Scripted> {
    deserialize_logged("deserialize", buf)
}

/// `try_deserialize_unchecked` logs its own event: the constructors under test
/// must call `try_deserialize`.
pub fn deserialize_unchecked(buf: &mut &[u8]) -> anchor_lang::Result<Scripted> {
    deserialize_logged("deserialize_unchecked", buf)
}

fn deserialize_logged(event: &str, buf: &mut &[u8]) -> anchor_lang::Result<Scripted> {
    push(Json::obj([(event, rec::bytes(buf))]));
    let s = step(2, |sc| &sc.decode);
    assign(&s.assign);
    if let Some(l) = s.lamports {
        **target().lamports.borrow_mut() = l;
    }
    if s.panic {
        panic!("script deserialize");
    }
    match s.result {
        Ok(n) => Ok(Scripted(n)),
        Err(e) => Err(Error::from(e)),
    }
}

/// The payload type of the scripted `Account`/`InterfaceAccount` cases.
#[derive(Clone)]
pub struct Scripted(pub u64);

impl Owner for Scripted {
    fn owner() -> Pubkey {
        owner()
    }
}

impl anchor_lang::CheckOwner for Scripted {
    fn check_owner(o: &Pubkey) -> anchor_lang::Result<()> {
        check_owner(o)
    }
}

impl AccountDeserialize for Scripted {
    fn try_deserialize(buf: &mut &[u8]) -> anchor_lang::Result<Self> {
        deserialize(buf)
    }
    fn try_deserialize_unchecked(buf: &mut &[u8]) -> anchor_lang::Result<Self> {
        deserialize_unchecked(buf)
    }
}

impl AccountSerialize for Scripted {}

pub const DISCRIMINATOR: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

/// A 16-byte, 8-aligned zero-copy payload.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Zc {
    pub a: u64,
    pub b: u64,
}

unsafe impl anchor_lang::__private::bytemuck::Zeroable for Zc {}
unsafe impl anchor_lang::__private::bytemuck::Pod for Zc {}

impl Discriminator for Zc {
    const DISCRIMINATOR: &'static [u8] = &DISCRIMINATOR;
}

impl anchor_lang::ZeroCopy for Zc {}

impl Owner for Zc {
    fn owner() -> Pubkey {
        owner()
    }
}

/// A 32-byte, 16-aligned zero-copy payload: after the 8-byte discriminator
/// the loader 16-aligned data start leaves it misaligned.
#[derive(Clone, Copy)]
#[repr(C, align(16))]
pub struct Zc16 {
    pub a: u128,
    pub b: u128,
}

unsafe impl anchor_lang::__private::bytemuck::Zeroable for Zc16 {}
unsafe impl anchor_lang::__private::bytemuck::Pod for Zc16 {}

impl Discriminator for Zc16 {
    const DISCRIMINATOR: &'static [u8] = &DISCRIMINATOR;
}

impl anchor_lang::ZeroCopy for Zc16 {}

impl Owner for Zc16 {
    fn owner() -> Pubkey {
        owner()
    }
}
