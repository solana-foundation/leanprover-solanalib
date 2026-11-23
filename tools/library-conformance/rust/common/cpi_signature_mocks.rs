// Whole-signature mock controls. This file never calls or projects an SDK
// invocation implementation. The actual SDK types and ordinary constructors
// remain linked; the recording provider replaces the complete signature.
use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::cell::{Cell, RefCell};
use std::mem::{align_of, offset_of, size_of};
use std::rc::Rc;

thread_local! {
    static PLAN: Cell<u8> = const { Cell::new(0) };
    static LOG: RefCell<Vec<Json>> = const { RefCell::new(Vec::new()) };
}

fn instruction_json(instruction: &Instruction) -> Json {
    Json::obj([
        ("program_id", rec::bytes(instruction.program_id.as_ref())),
        ("accounts", Json::arr(&instruction.accounts, |meta| Json::obj([
            ("pubkey", rec::bytes(meta.pubkey.as_ref())),
            ("is_signer", meta.is_signer.into()),
            ("is_writable", meta.is_writable.into()),
        ]))),
        ("data", rec::bytes(&instruction.data)),
    ])
}

fn request_json(instruction: &Instruction, accounts: &[AccountInfo<'_>],
    signers: &[&[&[u8]]]) -> Json {
    let mut lamports = Vec::new();
    let mut data = Vec::new();
    Json::obj([
        ("instruction", instruction_json(instruction)),
        ("accounts", Json::Arr(accounts.iter().map(|account| {
            let lp = Rc::as_ptr(&account.lamports).cast::<()>();
            let dp = Rc::as_ptr(&account.data).cast::<()>();
            let li = lamports.iter().position(|p| *p == lp).unwrap_or_else(|| {
                lamports.push(lp); lamports.len() - 1
            });
            let di = data.iter().position(|p| *p == dp).unwrap_or_else(|| {
                data.push(dp); data.len() - 1
            });
            Json::obj([
                ("key", rec::bytes(account.key.as_ref())),
                ("lamports_cell", li.into()), ("data_cell", di.into()),
                ("is_signer", account.is_signer.into()),
                ("is_writable", account.is_writable.into()),
                ("executable", account.executable.into()),
            ])
        }).collect())),
        ("signers", Json::arr(signers, |group| Json::arr(*group, |seed| rec::bytes(seed)))),
    ])
}

fn signed_mock(instruction: &Instruction, accounts: &[AccountInfo<'_>],
    signers: &[&[&[u8]]]) -> Result<(), ProgramError> {
    let request = request_json(instruction, accounts, signers);
    LOG.with(|log| log.borrow_mut().push(request.clone()));
    match PLAN.get() {
        0 => Ok(()),
        1 => Err(ProgramError::AccountBorrowFailed),
        2 => {
            // A typed mock termination occurs in a separate process. It is
            // neither an unwind nor execution of a runtime invocation body.
            println!("{}", request.to_text());
            std::process::exit(83)
        }
        _ => unreachable!(),
    }
}

fn unsigned_mock(instruction: &Instruction, accounts: &[AccountInfo<'_>])
    -> Result<(), ProgramError> {
    signed_mock(instruction, accounts, &[])
}

fn source_state(borrow: i32, accounts: &[AccountInfo<'_>]) -> Json {
    let counts = Json::arr(accounts, |account| {
        // These ordinary RefCell observations are outside the invocation
        // boundary. Each successful temporary probe is dropped immediately.
        let lamports_mutable = account.lamports.try_borrow_mut().is_ok();
        let lamports_shared = account.lamports.try_borrow().is_ok();
        let data_mutable = account.data.try_borrow_mut().is_ok();
        let data_shared = account.data.try_borrow().is_ok();
        Json::arr([lamports_mutable, lamports_shared, data_mutable, data_shared], Json::from)
    });
    Json::obj([
        ("scope", "whole-signature-mock".into()),
        ("profile", PROFILE.into()), ("borrow", borrow.into()),
        ("borrow_observations", counts),
    ])
}

fn layouts(instruction: &Instruction) -> Json {
    let mut bytes = Vec::<u8>::with_capacity(23);
    bytes.extend_from_slice(&[1, 2, 3, 4, 5]);
    // The three initialized Vec words are inspected only as a type control.
    // No enum padding, invocation pointer or callee memory is read here.
    let words = unsafe {
        std::slice::from_raw_parts((&bytes as *const Vec<u8>).cast::<usize>(), 3)
    };
    let order = Json::arr(words, |word| Json::from(
        if *word == bytes.as_ptr() as usize { "pointer" }
        else if *word == bytes.len() { "length" }
        else if *word == bytes.capacity() { "capacity" }
        else { panic!("unexpected Vec representation") }
    ));
    Json::obj([
        ("constructor_control", constructor_control(instruction)),
        ("vec_words", order),
        ("instruction", Json::arr([
            size_of::<Instruction>(), align_of::<Instruction>(),
            offset_of!(Instruction, accounts), offset_of!(Instruction, data),
            offset_of!(Instruction, program_id),
        ], Json::from)),
        ("account_info", Json::arr([
            size_of::<AccountInfo<'_>>(), align_of::<AccountInfo<'_>>(),
            offset_of!(AccountInfo<'_>, key), offset_of!(AccountInfo<'_>, lamports),
            offset_of!(AccountInfo<'_>, data), offset_of!(AccountInfo<'_>, owner),
            rent_offset(), offset_of!(AccountInfo<'_>, is_signer),
            offset_of!(AccountInfo<'_>, is_writable), offset_of!(AccountInfo<'_>, executable),
        ], Json::from)),
        ("program_error", Json::arr([
            size_of::<ProgramError>(), align_of::<ProgramError>(),
            size_of::<Result<(), ProgramError>>(), align_of::<Result<(), ProgramError>>(),
        ], Json::from)),
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
    let mut program_bytes = [0; 32];
    program_bytes[31] = 17;
    let program = program_bytes.into();
    let owner = [0; 32].into();
    let mut balance_a = 11;
    let mut balance_b = 29;
    let mut bytes_a = [7, 3];
    let mut bytes_b = [5, 9, 8];
    let account_a = new_account!(&program, &mut balance_a, &mut bytes_a, &owner);
    let account_b = new_account!(&program, &mut balance_b, &mut bytes_b, &owner);
    let accounts = [account_a.clone(), account_b.clone(), account_a.clone()];
    let seed = [4, 6];
    let empty: &[&[u8]] = &[];
    let group: &[&[u8]] = &[&[], &seed, &seed];
    let signers: &[&[&[u8]]] = &[empty, group, empty];
    let excessive: Vec<&[u8]> = vec![&seed; 17];
    let excessive_signers: &[&[&[u8]]] = &[&excessive];

    if std::env::args().nth(1).as_deref() == Some("--mock-terminal") {
        PLAN.set(2);
        let instruction = Instruction { program_id: program, accounts: vec![], data: vec![7, 9] };
        let _ = signed_mock(&instruction, &accounts, excessive_signers);
        unreachable!();
    }

    let mut corpus = Corpus::new(CORPUS, CRATES);
    for (id, signed, metas, borrow, plan) in [
        ("signed_aliases", true, 0, 0, 0),
        ("unsigned_aliases", false, 0, 0, 0),
        ("repeated_metadata", true, 2, 0, 0),
        ("readonly_shared", true, 1, 1, 0),
        ("first_duplicate_lamports_error", true, 1, 2, 1),
        ("first_duplicate_data_error", true, 1, 3, 1),
    ] {
        let instruction = Instruction { program_id: program,
            accounts: (0..metas).map(|_| AccountMeta::new_readonly(program, false)).collect(),
            data: vec![7, 9] };
        let lamports_shared = (borrow == 1).then(|| account_a.lamports.borrow());
        let lamports_exclusive = (borrow == 2).then(|| account_a.lamports.borrow_mut());
        let data_exclusive = (borrow == 3).then(|| account_a.data.borrow_mut());
        let selected = if signed { signers } else { &[] };
        let request = request_json(&instruction, &accounts, selected);
        let state = source_state(borrow, &accounts);
        LOG.with(|log| log.borrow_mut().clear());
        PLAN.set(plan);
        let result = if signed {
            let mock: fn(&Instruction, &[AccountInfo<'_>], &[&[&[u8]]])
                -> Result<(), ProgramError> = signed_mock;
            mock(&instruction, &accounts, selected)
        } else {
            let mock: fn(&Instruction, &[AccountInfo<'_>]) -> Result<(), ProgramError>
                = unsigned_mock;
            mock(&instruction, &accounts)
        };
        let log = LOG.with(|log| Json::Arr(log.borrow().clone()));
        let result = match result {
            Ok(()) => rec::ok(Json::Null),
            Err(ProgramError::AccountBorrowFailed) => rec::err("AccountBorrowFailed".into()),
            Err(error) => panic!("unexpected mock error: {error:?}"),
        };
        let after = Json::obj([("source", source_state(borrow, &accounts)), ("requests", log)]);
        corpus.push(Record { id: id.into(), function: if signed { SIGNED } else { UNSIGNED },
            generics: vec![], layout: Some(layouts(&instruction)), state,
            args: request, outcome: rec::returned(result, after), observed: None });
        drop(data_exclusive);
        drop(lamports_exclusive);
        drop(lamports_shared);
    }
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .arg("--mock-terminal").output().unwrap();
    assert_eq!(child.status.code(), Some(83));
    assert!(child.stderr.is_empty());
    let logged = String::from_utf8(child.stdout).unwrap();
    let instruction = Instruction { program_id: program, accounts: vec![], data: vec![7, 9] };
    let request = request_json(&instruction, &accounts, excessive_signers);
    assert_eq!(logged.trim(), request.to_text());
    corpus.push(Record { id: "too_many_seeds_terminal".into(), function: SIGNED,
        generics: vec![], layout: Some(layouts(&instruction)), state: source_state(0, &accounts),
        args: request, outcome: Json::obj([
            ("exit", "terminated".into()), ("reason", "MaxSeedLengthExceeded".into()),
            ("requests", Json::Arr(vec![Json::Raw(logged.trim().to_owned())])),
        ]), observed: None });
    corpus.write(&rec::out_dir()).unwrap();
}
