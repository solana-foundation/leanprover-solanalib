// The complete extern signature is mocked. No SDK invocation body runs.
// VM descriptors below are explicit caller fixtures, not legacy SDK layouts.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::mem::{align_of, offset_of, size_of};

#[repr(C)]
struct StableVec<T> { pointer: *const T, capacity: usize, length: usize }
#[repr(C)]
struct Meta { key: [u8; 32], signer: bool, writable: bool }
#[repr(C)]
struct Instruction { accounts: StableVec<Meta>, data: StableVec<u8>, program_id: [u8; 32] }
#[repr(C)]
struct Account<'a> {
    key: &'a [u8; 32], lamports: Rc<RefCell<&'a mut u64>>, data: Rc<RefCell<&'a mut [u8]>>,
    owner: &'a [u8; 32], rent_epoch: u64, signer: bool, writable: bool, executable: bool,
}
impl Clone for Account<'_> {
    fn clone(&self) -> Self {
        Self { key: self.key, lamports: self.lamports.clone(), data: self.data.clone(), owner: self.owner,
            rent_epoch: self.rent_epoch, signer: self.signer, writable: self.writable, executable: self.executable }
    }
}
#[repr(C)]
struct Slice<T> { pointer: *const T, length: usize }

thread_local! {
    static TERMINAL: Cell<bool> = const { Cell::new(false) };
    static LOG: RefCell<Vec<Json>> = const { RefCell::new(Vec::new()) };
}

fn request(instruction: &Instruction, accounts: &[Account<'_>], seeds: &[Slice<Slice<u8>>]) -> Json {
    let mut lamports = Vec::new(); let mut data = Vec::new();
    let infos = accounts.iter().map(|account| {
        let lp = Rc::as_ptr(&account.lamports); let dp = Rc::as_ptr(&account.data);
        let li = lamports.iter().position(|p| *p == lp).unwrap_or_else(|| {lamports.push(lp); lamports.len() - 1});
        let di = data.iter().position(|p| *p == dp).unwrap_or_else(|| {data.push(dp); data.len() - 1});
        Json::obj([("key", rec::bytes(account.key)), ("lamports_cell", li.into()),
            ("data_cell", di.into()), ("is_signer", account.signer.into()),
            ("is_writable", account.writable.into()), ("executable", account.executable.into())])
    }).collect();
    let metas = unsafe { std::slice::from_raw_parts(instruction.accounts.pointer, instruction.accounts.length) };
    let bytes = unsafe { std::slice::from_raw_parts(instruction.data.pointer, instruction.data.length) };
    Json::obj([
        ("instruction", Json::obj([("program_id", rec::bytes(&instruction.program_id)),
            ("accounts", Json::arr(metas, |meta| Json::obj([("pubkey", rec::bytes(&meta.key)),
                ("is_signer", meta.signer.into()), ("is_writable", meta.writable.into())]))),
            ("data", rec::bytes(bytes))])),
        ("accounts", Json::Arr(infos)),
        ("signers", Json::arr(seeds, |group| {
            let seeds = unsafe { std::slice::from_raw_parts(group.pointer, group.length) };
            Json::arr(seeds, |seed| rec::bytes(unsafe {std::slice::from_raw_parts(seed.pointer, seed.length)}))
        })),
    ])
}

unsafe extern "C" fn invoke_mock(instruction: *const u8, accounts: *const u8, count: u64,
    seeds: *const u8, seed_count: u64) -> u64 {
    let args = request(&*instruction.cast::<Instruction>(),
        std::slice::from_raw_parts(accounts.cast(), count as usize),
        std::slice::from_raw_parts(seeds.cast(), seed_count as usize));
    if TERMINAL.get() { println!("{}", args.to_text()); std::process::exit(83); }
    LOG.with(|log| log.borrow_mut().push(args)); 0
}

fn call_mock(instruction: &Instruction, accounts: &[Account<'_>], seeds: &[Slice<Slice<u8>>]) -> u64 {
    let boundary: unsafe extern "C" fn(*const u8, *const u8, u64, *const u8, u64) -> u64 = invoke_mock;
    unsafe { boundary((instruction as *const Instruction).cast(), accounts.as_ptr().cast(),
        accounts.len() as u64, seeds.as_ptr().cast(), seeds.len() as u64) }
}

fn source(accounts: &[Account<'_>]) -> Json {
    Json::obj([("scope", "whole-signature-mock".into()), ("profile", PROFILE.into()),
        ("descriptor_origin", "explicit-vm-fixture".into()),
        ("accounts", Json::arr(accounts, |a| Json::obj([
            ("lamports", (**a.lamports.borrow()).into()), ("data", rec::bytes(&a.data.borrow())),
            ("owner", rec::bytes(a.owner)), ("rent_epoch", a.rent_epoch.into())])))])
}

fn layouts() -> Json {
    Json::obj([("descriptor_origin", "explicit-vm-fixture".into()),
        ("instruction", Json::arr([size_of::<Instruction>(), align_of::<Instruction>(),
            offset_of!(Instruction, accounts), offset_of!(Instruction, data), offset_of!(Instruction, program_id)], Json::from)),
        ("account_info", Json::arr([size_of::<Account<'_>>(), align_of::<Account<'_>>(), offset_of!(Account<'_>, key),
            offset_of!(Account<'_>, lamports), offset_of!(Account<'_>, data), offset_of!(Account<'_>, owner),
            offset_of!(Account<'_>, rent_epoch), offset_of!(Account<'_>, signer), offset_of!(Account<'_>, writable),
            offset_of!(Account<'_>, executable)], Json::from)),
        ("meta", Json::arr([size_of::<Meta>(), align_of::<Meta>(), offset_of!(Meta, signer), offset_of!(Meta, writable)], Json::from)),
        ("stable_vec", Json::arr([size_of::<StableVec<u8>>(), offset_of!(StableVec<u8>, pointer),
            offset_of!(StableVec<u8>, capacity), offset_of!(StableVec<u8>, length)], Json::from)),
        ("seed", Json::arr([size_of::<Slice<u8>>(), align_of::<Slice<u8>>()], Json::from))])
}

fn main() {
    assert!(!cfg!(feature = "signature-check"), "signature checks are compile-only");
    rec::init();
    if std::env::args().nth(1).as_deref() == Some("--build-config") {
        println!("{}", Json::obj([("scope", "whole-signature-mock".into()),
            ("panic", if cfg!(panic = "abort") {"abort"} else {"unwind"}.into()),
            ("debug_assertions", cfg!(debug_assertions).into()), ("solana_cfg", cfg!(target_os = "solana").into()),
            ("pointer_width", (size_of::<usize>() * 8).into()), ("little_endian", cfg!(target_endian = "little").into()),
            ("signature_check_enabled", cfg!(feature = "signature-check").into())]).to_text()); return;
    }
    let mut program=[0;32]; program[31]=17; let owner=[0;32];
    let mut lamports_a=11; let mut lamports_b=29;
    let mut bytes_a=[7,3]; let mut bytes_b=[5,9,8];
    let a=Account {key:&program,lamports:Rc::new(RefCell::new(&mut lamports_a)),data:Rc::new(RefCell::new(&mut bytes_a)),
        owner:&owner,rent_epoch:0,signer:false,writable:false,executable:true};
    let b=Account {key:&program,lamports:Rc::new(RefCell::new(&mut lamports_b)),data:Rc::new(RefCell::new(&mut bytes_b)),
        owner:&owner,rent_epoch:0,signer:false,writable:false,executable:true};
    let accounts=[a.clone(),b,a]; let leaf=[4,6]; let empty:[u8;0]=[];
    let group=[Slice {pointer:empty.as_ptr(),length:0},Slice {pointer:leaf.as_ptr(),length:2},Slice {pointer:leaf.as_ptr(),length:2}];
    let no_seeds:[Slice<u8>;0]=[];
    let seeds=[Slice {pointer:no_seeds.as_ptr(),length:0},Slice {pointer:group.as_ptr(),length:3},Slice {pointer:no_seeds.as_ptr(),length:0}];
    let excessive:Vec<_>=(0..17).map(|_|Slice {pointer:leaf.as_ptr(),length:2}).collect();
    let excess=[Slice {pointer:excessive.as_ptr(),length:17}];
    let data=[7,9]; let no_metas:[Meta;0]=[];
    let make=|metas:&[Meta]| Instruction {accounts:StableVec {pointer:metas.as_ptr(),capacity:metas.len(),length:metas.len()},
        data:StableVec {pointer:data.as_ptr(),capacity:data.len(),length:data.len()},program_id:program};
    if std::env::args().nth(1).as_deref()==Some("--terminal") { TERMINAL.set(true); call_mock(&make(&no_metas),&accounts,&excess); unreachable!(); }
    let mut corpus=Corpus::new(CORPUS, CRATES);
    for (label,count,with_seeds) in [("aliases",0,true),("repeated_metadata",2,true),("empty_signers",0,false)] {
        let metas:Vec<_>=(0..count).map(|_|Meta {key:program,signer:false,writable:false}).collect();
        let instruction=make(&metas); let seeds=if with_seeds {&seeds[..]} else {&[]};
        let args=request(&instruction,&accounts,seeds); let before=source(&accounts);
        LOG.with(|log|log.borrow_mut().clear()); let result=call_mock(&instruction,&accounts,seeds);
        let after=Json::obj([("source",source(&accounts)),("requests",LOG.with(|log|Json::Arr(log.borrow().clone())))]);
        corpus.push(Record {id:label.into(),function:FUNCTION,generics:vec![],layout:Some(layouts()),state:before,args,
            outcome:rec::returned(result.into(),after),observed:None});
    }
    let child=std::process::Command::new(std::env::current_exe().unwrap()).arg("--terminal").output().unwrap();
    assert_eq!(child.status.code(),Some(83)); assert!(child.stderr.is_empty());
    let logged=String::from_utf8(child.stdout).unwrap();let args=request(&make(&no_metas),&accounts,&excess);
    assert_eq!(logged.trim(),args.to_text());
    corpus.push(Record {id:"too_many_seeds".into(),function:FUNCTION,generics:vec![],layout:Some(layouts()),state:source(&accounts),args,
        outcome:Json::obj([("exit","terminated".into()),("reason","MaxSeedLengthExceeded".into()),
            ("requests",Json::Arr(vec![Json::Raw(logged.trim().to_owned())]))]),observed:None});
    corpus.write(&rec::out_dir()).unwrap();
}
