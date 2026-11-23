//! Actual effectful Owner implementations, selected independently for each call.

use std::cell::RefCell;
use anchor_lang::prelude::*;
use conformance_recorder::{self as rec, Json};

pub const DISC: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
pub const PROGRAM: [u8; 32] = [0x77; 32];

#[derive(Clone)]
pub struct Step {
    pub returns: [u8; 32],
    pub assign: Option<[u8; 32]>,
    pub panic: bool,
}

pub fn returns(key: [u8; 32]) -> Step { Step { returns: key, assign: None, panic: false } }

pub fn json(steps: &[Step]) -> Json {
    Json::obj([
        ("owner", Json::arr(steps, |step| Json::obj([
            ("returns", rec::bytes(&step.returns)),
            ("assign", step.assign.map_or(Json::Null, |key| rec::bytes(&key))),
            ("panic", step.panic.into()),
        ]))),
        ("check_owner", Json::Arr(vec![])),
        ("deserialize", Json::Arr(vec![])),
    ])
}

struct Active {
    steps: Vec<Step>,
    cursor: usize,
    target: Option<&'static AccountInfo<'static>>,
    log: Vec<Json>,
}

thread_local! {
    static ACTIVE: RefCell<Active> = const { RefCell::new(Active {
        steps: vec![], cursor: 0, target: None, log: vec![],
    }) };
}

pub fn install(steps: Vec<Step>, target: Option<&'static AccountInfo<'static>>) {
    ACTIVE.with(|cell| *cell.borrow_mut() = Active { steps, target, cursor: 0, log: vec![] });
}

pub fn log() -> Json { ACTIVE.with(|cell| Json::Arr(cell.borrow().log.clone())) }

pub fn owner() -> Pubkey {
    let (step, target) = ACTIVE.with(|cell| {
        let mut active = cell.borrow_mut();
        active.log.push(Json::obj([("owner", Json::Null)]));
        let step = active.steps.get(active.cursor).cloned();
        active.cursor += 1;
        (step, active.target)
    });
    let step = step.expect("script exhausted");
    if let Some(key) = step.assign {
        target.expect("script target").assign(&Pubkey::new_from_array(key));
    }
    if step.panic { panic!("script owner"); }
    Pubkey::new_from_array(step.returns)
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Zc { pub a: u64, pub b: u64 }
unsafe impl anchor_lang::__private::bytemuck::Zeroable for Zc {}
unsafe impl anchor_lang::__private::bytemuck::Pod for Zc {}
impl Discriminator for Zc { const DISCRIMINATOR: &'static [u8] = &DISC; }
impl anchor_lang::ZeroCopy for Zc {}
impl Owner for Zc { fn owner() -> Pubkey { owner() } }

#[derive(Clone, Copy)]
#[repr(C, align(16))]
pub struct Zc16 { pub a: u128, pub b: u128 }
unsafe impl anchor_lang::__private::bytemuck::Zeroable for Zc16 {}
unsafe impl anchor_lang::__private::bytemuck::Pod for Zc16 {}
impl Discriminator for Zc16 { const DISCRIMINATOR: &'static [u8] = &DISC; }
impl anchor_lang::ZeroCopy for Zc16 {}
impl Owner for Zc16 { fn owner() -> Pubkey { owner() } }
