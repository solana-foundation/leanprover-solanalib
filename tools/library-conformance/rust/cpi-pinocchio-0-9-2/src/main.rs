//! Whole-signature mocks over exact Pinocchio types. No invocation body runs.
use conformance_accounts::{Account as InputAccount, Entry, Input, Region};
use conformance_recorder::{self as rec, Corpus, Json, Record};
use pinocchio::{account_info::AccountInfo, instruction::{Account, AccountMeta, Instruction, Seed, Signer}};
use std::cell::{Cell, RefCell};
use std::mem::{align_of, offset_of, size_of, MaybeUninit};

const UNCHECKED: &str = "pinocchio::cpi::invoke_signed_unchecked";
const RAW: &str = "pinocchio::syscalls::sol_invoke_signed_c";
thread_local! {
    static TERMINAL: Cell<bool> = const { Cell::new(false) };
    static LOG: RefCell<Vec<Json>> = const { RefCell::new(Vec::new()) };
}

#[cfg(feature = "signature-check")]
fn source_signatures() {
    let _: unsafe fn(&Instruction<'_, '_, '_, '_>, &[Account<'_>], &[Signer<'_, '_>])
        = pinocchio::cpi::invoke_signed_unchecked;
    let _: unsafe extern "C" fn(*const u8, *const u8, u64, *const u8, u64) -> u64
        = pinocchio::syscalls::sol_invoke_signed_c;
}

// These transparent observations follow the exact repr(C) public type source.
// Only initialized fields are read; padding is never read as a Rust byte.
#[repr(C)]
struct AccountFields {
    key: *const [u8; 32], lamports: *const u64, data_len: u64, data: *const u8,
    owner: *const [u8; 32], rent_epoch: u64, is_signer: bool, is_writable: bool, executable: bool,
}
#[repr(C)]
struct SliceFields<T> { pointer: *const T, length: u64 }
#[repr(C)]
struct CInstruction<'a> {
    program_id: *const [u8; 32], accounts: *const AccountMeta<'a>, accounts_len: u64,
    data: *const u8, data_len: u64,
}

fn request(instruction: &Instruction<'_, '_, '_, '_>, accounts: &[Account<'_>],
    signers: &[Signer<'_, '_>]) -> Json {
    let mut lamports = Vec::new();
    let mut data = Vec::new();
    let accounts = accounts.iter().map(|account| {
        assert_eq!(size_of::<Account<'_>>(), size_of::<AccountFields>());
        let fields = unsafe { &*(account as *const Account<'_>).cast::<AccountFields>() };
        let li = lamports.iter().position(|pointer| *pointer == fields.lamports).unwrap_or_else(|| {
            lamports.push(fields.lamports); lamports.len() - 1
        });
        let di = data.iter().position(|pointer| *pointer == fields.data).unwrap_or_else(|| {
            data.push(fields.data); data.len() - 1
        });
        Json::obj([
            ("key", rec::bytes(unsafe { &*fields.key })),
            ("lamports_cell", li.into()), ("data_cell", di.into()),
            ("is_signer", fields.is_signer.into()), ("is_writable", fields.is_writable.into()),
            ("executable", fields.executable.into()),
        ])
    }).collect();
    Json::obj([
        ("instruction", Json::obj([
            ("program_id", rec::bytes(instruction.program_id)),
            ("accounts", Json::arr(instruction.accounts, |meta| Json::obj([
                ("pubkey", rec::bytes(meta.pubkey)), ("is_signer", meta.is_signer.into()),
                ("is_writable", meta.is_writable.into()),
            ]))), ("data", rec::bytes(instruction.data)),
        ])),
        ("accounts", Json::Arr(accounts)),
        ("signers", Json::arr(signers, |signer| {
            assert_eq!(size_of::<Signer<'_, '_>>(), size_of::<SliceFields<Seed<'_>>>());
            let fields = unsafe { &*(signer as *const Signer<'_, '_>).cast::<SliceFields<Seed<'_>>>() };
            let seeds = unsafe { std::slice::from_raw_parts(fields.pointer, fields.length as usize) };
            Json::arr(seeds, |seed| rec::bytes(seed))
        })),
    ])
}

fn record_request(value: Json) {
    if TERMINAL.get() {
        println!("{}", value.to_text());
        std::process::exit(83);
    }
    LOG.with(|log| log.borrow_mut().push(value));
}

unsafe fn unchecked_mock(instruction: &Instruction<'_, '_, '_, '_>, accounts: &[Account<'_>],
    signers: &[Signer<'_, '_>]) {
    record_request(request(instruction, accounts, signers));
}

unsafe extern "C" fn raw_mock(instruction: *const u8, accounts: *const u8, count: u64,
    signers: *const u8, signers_count: u64) -> u64 {
    // The complete raw signature is the mock boundary. Its caller builds these
    // explicit typed descriptors; no Pinocchio invocation preparation runs.
    let raw = &*instruction.cast::<CInstruction<'_>>();
    let instruction = Instruction { program_id: &*raw.program_id,
        accounts: std::slice::from_raw_parts(raw.accounts, raw.accounts_len as usize),
        data: std::slice::from_raw_parts(raw.data, raw.data_len as usize) };
    record_request(request(&instruction, std::slice::from_raw_parts(accounts.cast(), count as usize),
        std::slice::from_raw_parts(signers.cast(), signers_count as usize)));
    0
}

fn call_mock(raw: bool, instruction: &Instruction<'_, '_, '_, '_>, accounts: &[Account<'_>],
    signers: &[Signer<'_, '_>]) -> Json {
    unsafe {
        if raw {
            let descriptor = CInstruction { program_id: instruction.program_id,
                accounts: instruction.accounts.as_ptr(), accounts_len: instruction.accounts.len() as u64,
                data: instruction.data.as_ptr(), data_len: instruction.data.len() as u64 };
            let provider: unsafe extern "C" fn(*const u8, *const u8, u64, *const u8, u64) -> u64 = raw_mock;
            provider((&descriptor as *const CInstruction<'_>).cast(), accounts.as_ptr().cast(),
                accounts.len() as u64, signers.as_ptr().cast(), signers.len() as u64).into()
        } else {
            let provider: unsafe fn(&Instruction<'_, '_, '_, '_>, &[Account<'_>], &[Signer<'_, '_>])
                = unchecked_mock;
            provider(instruction, accounts, signers);
            Json::Null
        }
    }
}

fn source(region: &Region) -> Json {
    Json::obj([("scope", "whole-signature-mock".into()), ("profile", "pinocchio-0.9.2".into()),
        ("input", region.read_back())])
}

fn layouts() -> Json {
    Json::obj([
        ("instruction", Json::arr([size_of::<Instruction<'_, '_, '_, '_>>(),
            align_of::<Instruction<'_, '_, '_, '_>>(), offset_of!(Instruction<'_, '_, '_, '_>, accounts),
            offset_of!(Instruction<'_, '_, '_, '_>, data), offset_of!(Instruction<'_, '_, '_, '_>, program_id)], Json::from)),
        ("account", Json::arr([size_of::<Account<'_>>(), align_of::<Account<'_>>()], Json::from)),
        ("account_meta", Json::arr([size_of::<AccountMeta<'_>>(), align_of::<AccountMeta<'_>>(),
            offset_of!(AccountMeta<'_>, pubkey), offset_of!(AccountMeta<'_>, is_writable),
            offset_of!(AccountMeta<'_>, is_signer)], Json::from)),
        ("seed", Json::arr([size_of::<Seed<'_>>(), align_of::<Seed<'_>>()], Json::from)),
        ("signer", Json::arr([size_of::<Signer<'_, '_>>(), align_of::<Signer<'_, '_>>()], Json::from)),
    ])
}

fn main() {
    assert!(!cfg!(feature = "signature-check"), "signature checks are compile-only");
    rec::init();
    if std::env::args().nth(1).as_deref() == Some("--build-config") {
        println!("{}", Json::obj([
            ("scope", "whole-signature-mock".into()),
            ("panic", if cfg!(panic = "abort") { "abort" } else { "unwind" }.into()),
            ("debug_assertions", cfg!(debug_assertions).into()),
            ("solana_cfg", cfg!(target_os = "solana").into()),
            ("pointer_width", (size_of::<usize>() * 8).into()),
            ("little_endian", cfg!(target_endian = "little").into()),
            ("signature_check_enabled", cfg!(feature = "signature-check").into()),
        ]).to_text());
        return;
    }
    let mut program = [0; 32]; program[31] = 17;
    let account = |lamports, data| InputAccount { key: program, owner: [0; 32], lamports, data,
        executable: true, ..InputAccount::default() };
    let mut region = Input { entries: vec![Entry::Account(account(11, vec![7, 3])),
        Entry::Account(account(29, vec![5, 9, 8])), Entry::Duplicate(0)],
        instruction_data: vec![7, 9], program_id: [0; 32] }.serialize();
    let mut slots: [MaybeUninit<AccountInfo>; 3] = [const { MaybeUninit::uninit() }; 3];
    let infos = unsafe {
        let (_, count, _) = pinocchio::entrypoint::deserialize(region.as_mut_ptr(), &mut slots);
        assert_eq!(count, 3);
        [slots[0].assume_init(), slots[1].assume_init(), slots[2].assume_init()]
    };
    let accounts: Vec<Account<'_>> = infos.iter().map(Account::from).collect();
    let seed = [4, 6];
    let group = [Seed::from(&[]), Seed::from(&seed), Seed::from(&seed)];
    let empty: [Seed<'_>; 0] = [];
    let signers = [Signer::from(&empty), Signer::from(&group), Signer::from(&empty)];
    let excessive: Vec<Seed<'_>> = (0..17).map(|_| Seed::from(&seed)).collect();
    let excessive_signers = [Signer::from(excessive.as_slice())];
    let argument = std::env::args().nth(1).unwrap_or_default();
    if argument == "--terminal-unit" || argument == "--terminal-raw" {
        TERMINAL.set(true);
        let instruction = Instruction { program_id: &program, accounts: &[], data: &[7, 9] };
        call_mock(argument == "--terminal-raw", &instruction, &accounts, &excessive_signers);
        unreachable!();
    }
    let mut corpus = Corpus::new("cpi_pinocchio_0_9_2", &[("pinocchio", "0.9.2")]);
    for raw in [false, true] {
        let prefix = if raw { "raw_c" } else { "unchecked" };
        let function = if raw { RAW } else { UNCHECKED };
        for (label, count, with_signers) in [("aliases", 0, true), ("repeated_metadata", 2, true),
            ("empty_signers", 0, false)] {
            let metas: Vec<_> = (0..count).map(|_| AccountMeta::readonly(&program)).collect();
            let instruction = Instruction { program_id: &program, accounts: &metas, data: &[7, 9] };
            let signers = if with_signers { &signers[..] } else { &[] };
            let args = request(&instruction, &accounts, signers);
            let before = source(&region);
            LOG.with(|log| log.borrow_mut().clear());
            let result = call_mock(raw, &instruction, &accounts, signers);
            let after = Json::obj([("source", source(&region)),
                ("requests", LOG.with(|log| Json::Arr(log.borrow().clone())))]);
            corpus.push(Record { id: format!("{prefix}/{label}"), function, generics: vec![],
                layout: Some(layouts()), state: before, args, outcome: rec::returned(result, after), observed: None });
        }
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .arg(if raw { "--terminal-raw" } else { "--terminal-unit" }).output().unwrap();
        assert_eq!(child.status.code(), Some(83)); assert!(child.stderr.is_empty());
        let logged = String::from_utf8(child.stdout).unwrap();
        let instruction = Instruction { program_id: &program, accounts: &[], data: &[7, 9] };
        let args = request(&instruction, &accounts, &excessive_signers);
        assert_eq!(logged.trim(), args.to_text());
        corpus.push(Record { id: format!("{prefix}/too_many_seeds"), function, generics: vec![],
            layout: Some(layouts()), state: source(&region), args,
            outcome: Json::obj([("exit", "terminated".into()), ("reason", "MaxSeedLengthExceeded".into()),
                ("requests", Json::Arr(vec![Json::Raw(logged.trim().to_owned())]))]), observed: None });
    }
    corpus.write(&rec::out_dir()).unwrap();
}
