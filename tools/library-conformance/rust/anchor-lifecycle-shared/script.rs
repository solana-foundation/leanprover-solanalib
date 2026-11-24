//! Actual generic trait callbacks. Scripts are inputs to the experiment;
//! results and callback arguments are recorded independently after invocation.

use std::{cell::RefCell, collections::BTreeSet, io::Write, rc::Rc};
use anchor_lang::{prelude::*, solana_program::program_error::ProgramError};
use conformance_recorder::{self as rec, Json};
use crate::{enc, track, world::World};

pub const PROGRAM: [u8; 32] = [0x77; 32];
pub const DISC: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

#[derive(Clone)]
pub struct Step {
    pub key: [u8; 32],
    pub assign: Option<[u8; 32]>,
    pub lamports: Option<u64>,
    pub value: u64,
    pub error: u32,
    pub panic: bool,
    pub bytes: Vec<u8>,
}

impl Default for Step {
    fn default() -> Self {
        Self { key: PROGRAM, assign: None, lamports: None, value: 41,
            error: 0, panic: false, bytes: vec![21, 22, 23, 24, 25] }
    }
}

impl Step {
    pub fn json(&self) -> Json {
        Json::obj([
            ("key", rec::bytes(&self.key)),
            ("assign", self.assign.map_or(Json::Null, |value| rec::bytes(&value))),
            ("lamports", self.lamports.map_or(Json::Null, Json::from)),
            ("value", self.value.into()), ("error", self.error.into()),
            ("panic", self.panic.into()), ("bytes", rec::bytes(&self.bytes)),
        ])
    }
}

#[derive(Clone, Default)]
pub struct Script {
    pub owner: Vec<Step>,
    pub check_owner: Vec<Step>,
    pub id: Vec<Step>,
    pub check_id: Vec<Step>,
    pub decode: Vec<Step>,
    pub serialize: Vec<Step>,
    pub drop_payload: Vec<Step>,
    pub sysvar: Vec<Step>,
    pub inner: Vec<Step>,
}

impl Script {
    pub fn normal() -> Self {
        let step = vec![Step::default()];
        Self { owner: vec![Step::default(), Step::default()],
            check_owner: step.clone(), id: vec![Step::default(), Step::default()],
            check_id: step.clone(), decode: step.clone(), serialize: step.clone(),
            drop_payload: step.clone(), sysvar: step.clone(), inner: step }
    }
    pub fn json(&self) -> Json {
        Json::obj([
            ("owner", Json::arr(&self.owner, Step::json)),
            ("check_owner", Json::arr(&self.check_owner, Step::json)),
            ("id", Json::arr(&self.id, Step::json)),
            ("check_id", Json::arr(&self.check_id, Step::json)),
            ("decode", Json::arr(&self.decode, Step::json)),
            ("serialize", Json::arr(&self.serialize, Step::json)),
            ("drop_payload", Json::arr(&self.drop_payload, Step::json)),
            ("sysvar", Json::arr(&self.sysvar, Step::json)),
            ("inner", Json::arr(&self.inner, Step::json)),
        ])
    }
}

struct Active {
    script: Script,
    calls: [usize; 9],
    world: Option<&'static World>,
    target: usize,
    log: Vec<Json>,
    drop_enabled: bool,
    program_string: Option<usize>,
}

thread_local! {
    static ACTIVE: RefCell<Active> = const { RefCell::new(Active {
        script: Script { owner: vec![], check_owner: vec![], id: vec![], check_id: vec![],
            decode: vec![], serialize: vec![], drop_payload: vec![], sysvar: vec![], inner: vec![] },
        calls: [0; 9], world: None, target: 0, log: vec![], drop_enabled: false,
        program_string: None,
    }) };
}

pub fn install(script: Script, world: &'static World, target: usize, drop_enabled: bool) {
    ACTIVE.with(|active| *active.borrow_mut() = Active {
        script, calls: [0; 9], world: Some(world), target, log: vec![], drop_enabled,
        program_string: None,
    });
}

pub fn world() -> &'static World {
    ACTIVE.with(|active| active.borrow().world.expect("callback world"))
}

pub fn target() -> &'static AccountInfo<'static> {
    ACTIVE.with(|active| {
        let active = active.borrow();
        active.world.expect("callback world").info(active.target)
    })
}

pub fn log() -> Json { ACTIVE.with(|active| Json::Arr(active.borrow().log.clone())) }

pub fn program_string_dropped(log: &track::Log) -> Json {
    ACTIVE.with(|active| active.borrow().program_string
        .map_or(Json::Null, |address| log.frees.contains(&address).into()))
}

fn step(index: usize, pick: impl FnOnce(&Script) -> &Vec<Step>) -> Step {
    track::untracked(|| ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let cursor = active.calls[index];
        active.calls[index] += 1;
        pick(&active.script).get(cursor).cloned()
    })).expect("script exhausted")
}

fn push(name: &str, argument: impl FnOnce() -> Json) {
    track::untracked(|| {
        let argument = argument();
        let counts = if world().infos.is_empty() { Json::Arr(vec![]) } else {
            let info = target();
            Json::Arr(vec![Rc::strong_count(&info.lamports).into(), Rc::strong_count(&info.data).into()])
        };
        let leases = world().leases();
        ACTIVE.with(|active| active.borrow_mut().log.push(Json::obj([
            ("call", name.into()), ("argument", argument),
            ("ref_counts", counts), ("leases", leases),
        ])));
    });
}

fn effects(step: &Step) {
    if let Some(key) = step.assign { target().assign(&Pubkey::new_from_array(key)); }
    if let Some(balance) = step.lamports { **target().lamports.borrow_mut() = balance; }
}

fn returned(step: &Step) -> Result<()> {
    if step.error == 0 { Ok(()) } else { Err(ProgramError::Custom(step.error).into()) }
}

pub fn owner() -> Pubkey {
    push("owner", || Json::Null);
    let step = step(0, |script| &script.owner);
    effects(&step);
    if step.panic { panic!("script owner"); }
    Pubkey::new_from_array(step.key)
}

fn check_owner(owner: &Pubkey) -> Result<()> {
    push("check_owner", || world().owner_ref(owner).into());
    let step = step(1, |script| &script.check_owner);
    effects(&step);
    if step.panic { panic!("script check_owner"); }
    returned(&step)
}

pub struct ProgramTag;
impl Id for ProgramTag {
    fn id() -> Pubkey {
        push("id", || Json::Null);
        let step = step(2, |script| &script.id);
        effects(&step);
        if step.panic { panic!("script id"); }
        Pubkey::new_from_array(step.key)
    }
}
impl anchor_lang::CheckId for ProgramTag {
    fn check_id(key: &Pubkey) -> Result<()> {
        push("check_id", || rec::bytes(key.as_ref()));
        let step = step(3, |script| &script.check_id);
        effects(&step);
        if step.panic { panic!("script check_id"); }
        returned(&step)
    }
}

#[derive(Clone)]
pub struct Payload(pub u64);

impl Owner for Payload { fn owner() -> Pubkey { owner() } }
impl anchor_lang::CheckOwner for Payload {
    fn check_owner(owner: &Pubkey) -> Result<()> { check_owner(owner) }
}

fn decode(checked: bool, bytes: &mut &[u8]) -> Result<Payload> {
    push(if checked { "deserialize" } else { "deserialize_unchecked" }, || rec::bytes(bytes));
    let step = step(4, |script| &script.decode);
    effects(&step);
    if step.panic { panic!("script deserialize"); }
    returned(&step)?;
    // This concrete codec checks its discriminator. The library model treats
    // the selected trait method as a callback and must forward the whole slice.
    if checked && !bytes.starts_with(&DISC) {
        return Err(anchor_lang::error::ErrorCode::AccountDiscriminatorMismatch.into());
    }
    let consumed = bytes.len().min(8);
    *bytes = &bytes[consumed..];
    Ok(Payload(step.value))
}

impl AccountDeserialize for Payload {
    fn try_deserialize(bytes: &mut &[u8]) -> Result<Self> { decode(true, bytes) }
    fn try_deserialize_unchecked(bytes: &mut &[u8]) -> Result<Self> { decode(false, bytes) }
}

impl AccountSerialize for Payload {
    fn try_serialize<W: Write>(&self, writer: &mut W) -> Result<()> {
        push("serialize", || self.0.into());
        let step = step(5, |script| &script.serialize);
        effects(&step);
        // The concrete BpfWriter::write only copies bytes and advances its
        // cursor. Exclude the memory shim JSON log allocations from the
        // measured library heap; the complete syscall request stays recorded.
        let written = track::untracked(|| writer.write(&step.bytes));
        let count = written.expect("BpfWriter::write");
        push("write", || count.into());
        if step.panic { panic!("script serialize"); }
        returned(&step)
    }
}

impl Drop for Payload {
    fn drop(&mut self) {
        let enabled = ACTIVE.with(|active| active.borrow().drop_enabled);
        if !enabled { return; }
        push("drop_payload", || self.0.into());
        let step = step(6, |script| &script.drop_payload);
        effects(&step);
        if step.panic { panic!("script drop_payload"); }
    }
}

/// The bound on Exit requires Owners, while the constructor tests above use a
/// deliberately effectful CheckOwner implementation. Keep the instances exact.
#[derive(Clone)]
pub struct ExitPayload(pub Payload);
impl Owner for ExitPayload { fn owner() -> Pubkey { owner() } }
impl anchor_lang::Owners for ExitPayload {
    fn owners() -> &'static [Pubkey] { const KEYS: [Pubkey; 1] = [Pubkey::new_from_array(PROGRAM)]; &KEYS }
}
impl AccountDeserialize for ExitPayload {
    fn try_deserialize(bytes: &mut &[u8]) -> Result<Self> { decode(true, bytes).map(Self) }
    fn try_deserialize_unchecked(bytes: &mut &[u8]) -> Result<Self> { decode(false, bytes).map(Self) }
}
impl AccountSerialize for ExitPayload {
    fn try_serialize<W: Write>(&self, writer: &mut W) -> Result<()> { self.0.try_serialize(writer) }
}

#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct Var(pub u64);

fn from_account_info(info: &AccountInfo) -> std::result::Result<Var, ProgramError> {
    let record = world().infos.iter().position(|candidate| std::ptr::eq(
        candidate as *const _ as *const u8, info as *const _ as *const u8)).expect("original sysvar record");
    push("from_account_info", || record.into());
    let step = step(7, |script| &script.sysvar);
    effects(&step);
    if step.panic { panic!("script from_account_info"); }
    if step.error == 1 {
        #[cfg(feature = "legacy-program-error")]
        {
            let text = "owned syscall decoder failure".to_string();
            ACTIVE.with(|active| active.borrow_mut().program_string = Some(text.as_ptr() as usize));
            return Err(ProgramError::BorshIoError(text));
        }
        #[cfg(not(feature = "legacy-program-error"))]
        { return Err(ProgramError::BorshIoError); }
    }
    if step.error != 0 { return Err(ProgramError::Custom(step.error)); }
    Ok(Var(step.value))
}

#[cfg(feature = "split-sysvar")]
impl solana_sysvar::Sysvar for Var {}
#[cfg(feature = "split-sysvar")]
impl solana_sysvar::SysvarSerialize for Var {
    fn from_account_info(info: &AccountInfo) -> std::result::Result<Self, ProgramError> { from_account_info(info) }
}
#[cfg(feature = "split-sysvar")]
impl solana_sysvar_id::SysvarId for Var {
    fn id() -> Pubkey { Pubkey::new_from_array([0x53; 32]) }
    fn check_id(key: &Pubkey) -> bool { *key == Self::id() }
}
#[cfg(not(feature = "split-sysvar"))]
impl anchor_lang::solana_program::sysvar::Sysvar for Var {
    fn from_account_info(info: &AccountInfo) -> std::result::Result<Self, ProgramError> { from_account_info(info) }
}
#[cfg(not(feature = "split-sysvar"))]
impl anchor_lang::solana_program::sysvar::SysvarId for Var {
    fn id() -> Pubkey { Pubkey::new_from_array([0x53; 32]) }
    fn check_id(key: &Pubkey) -> bool { *key == Self::id() }
}

#[cfg(feature = "legacy-anchor")]
pub type Bumps = std::collections::BTreeMap<String, u8>;
#[cfg(not(feature = "legacy-anchor"))]
pub type Bumps = u64;

pub fn initial_bumps() -> Bumps {
    #[cfg(feature = "legacy-anchor")]
    { std::collections::BTreeMap::from([("seed".to_string(), 17)]) }
    #[cfg(not(feature = "legacy-anchor"))]
    { 17 }
}
pub fn bumps_json(bumps: &Bumps) -> Json {
    #[cfg(feature = "legacy-anchor")]
    { Json::arr(bumps, |(name, value)| Json::Arr(vec![name.as_str().into(), (*value).into()])) }
    #[cfg(not(feature = "legacy-anchor"))]
    { (*bumps).into() }
}

pub struct Inner(pub u64);
impl ToAccountMetas for Inner {
    fn to_account_metas(&self, _: Option<bool>) -> Vec<anchor_lang::solana_program::instruction::AccountMeta> { vec![] }
}
impl<'info> ToAccountInfos<'info> for Inner {
    fn to_account_infos(&self) -> Vec<AccountInfo<'info>> { vec![] }
}

fn inner_accounts<'info>(program: &Pubkey, accounts: &mut &[AccountInfo<'info>], bytes: &[u8],
    bumps: &mut Bumps, reallocs: &mut BTreeSet<Pubkey>) -> Result<Inner> {
    push("inner_accounts", || Json::obj([
        ("program_id", rec::bytes(program.as_ref())), ("instruction_data", rec::bytes(bytes)),
        ("remaining", accounts.len().into()),
    ]));
    let step = step(8, |script| &script.inner);
    if !accounts.is_empty() { *accounts = &accounts[1..]; }
    #[cfg(feature = "legacy-anchor")]
    { *bumps.get_mut("seed").expect("initial bump") += 1; }
    #[cfg(not(feature = "legacy-anchor"))]
    { *bumps += 1; }
    reallocs.insert(Pubkey::new_from_array([0x32; 32]));
    effects(&step);
    if step.panic { panic!("script inner"); }
    returned(&step)?;
    Ok(Inner(step.value))
}

#[cfg(feature = "legacy-anchor")]
impl<'info> Accounts<'info> for Inner {
    fn try_accounts(program: &Pubkey, accounts: &mut &[AccountInfo<'info>], bytes: &[u8],
        bumps: &mut Bumps, reallocs: &mut BTreeSet<Pubkey>) -> Result<Self> {
        inner_accounts(program, accounts, bytes, bumps, reallocs)
    }
}
#[cfg(not(feature = "legacy-anchor"))]
impl<'info> Accounts<'info, Bumps> for Inner {
    fn try_accounts(program: &Pubkey, accounts: &mut &'info [AccountInfo<'info>], bytes: &[u8],
        bumps: &mut Bumps, reallocs: &mut BTreeSet<Pubkey>) -> Result<Self> {
        inner_accounts(program, accounts, bytes, bumps, reallocs)
    }
}

impl<'info> AccountsExit<'info> for Inner {
    fn exit(&self, program: &Pubkey) -> Result<()> {
        push("inner_exit", || Json::obj([("value", self.0.into()), ("program_id", rec::bytes(program.as_ref()))]));
        let step = step(8, |script| &script.inner); effects(&step);
        if step.panic { panic!("script inner"); }
        returned(&step)
    }
}
impl<'info> AccountsClose<'info> for Inner {
    fn close(&self, destination: AccountInfo<'info>) -> Result<()> {
        push("inner_close", || Json::obj([("value", self.0.into()), ("destination", world().info_json(&destination))]));
        let step = step(8, |script| &script.inner); effects(&step);
        if step.panic { panic!("script inner"); }
        returned(&step)
    }
}

pub struct DefaultExit;
impl ToAccountMetas for DefaultExit {
    fn to_account_metas(&self, _: Option<bool>) -> Vec<anchor_lang::solana_program::instruction::AccountMeta> { vec![] }
}
impl<'info> ToAccountInfos<'info> for DefaultExit { fn to_account_infos(&self) -> Vec<AccountInfo<'info>> { vec![] } }
impl<'info> AccountsExit<'info> for DefaultExit {}

pub fn keep<T>(value: Result<T>, project: impl FnOnce(&T) -> Json) -> Json {
    let value = std::mem::ManuallyDrop::new(value);
    track::untracked(|| enc::result(&value, project))
}
