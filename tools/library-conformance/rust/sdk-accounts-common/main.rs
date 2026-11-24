// Calls the unmodified pinned AccountInfo APIs over loader-created aliases.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use std::sync::{atomic::{AtomicBool, Ordering}, Mutex};

static MEMSETS: Mutex<Vec<(usize, u8, usize)>> = Mutex::new(Vec::new());
static ZERO_ABORT: AtomicBool = AtomicBool::new(false);

/// The native provider validates the program-side memory call and performs its
/// specified writes. The terminal child exits at the same reached boundary.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sol_memset_(data: *mut u8, byte: u8, n: u64) {
    if ZERO_ABORT.load(Ordering::SeqCst) {
        println!("zeroing:{byte}:{n}");
        std::process::exit(91);
    }
    MEMSETS.lock().unwrap().push((data as usize, byte, n as usize));
    unsafe { std::ptr::write_bytes(data, byte, n as usize) };
}

fn sparse(bytes: &[u8]) -> Json {
    let used = bytes.iter().rposition(|b| *b != 0).map_or(0, |i| i + 1);
    Json::obj([("prefix", rec::bytes(&bytes[..used])), ("zeros", (bytes.len() - used).into())])
}

#[allow(deprecated)]
fn resize(info: &AccountInfo<'_>, len: usize, zero: bool, convenience: bool) -> Result<(), ProgramError> {
    #[cfg(feature = "resize-api")]
    if convenience {
        return info.resize(len);
    }
    #[cfg(feature = "realloc-api")]
    { let _ = convenience; info.realloc(len, zero) }
    #[cfg(not(feature = "realloc-api"))]
    { assert!(zero); info.resize(len) }
}

#[path = "world.rs"]
mod world;
use world::*;

fn method(call: &Call) -> &'static str {
    match call {
        Call::Lamports(_) => "lamports", Call::DataLen(_) => "data_len",
        Call::Empty(_) => "data_is_empty", Call::TryLen(_) => "try_data_len",
        Call::Borrow(_, true, false) => "try_borrow_lamports",
        Call::Borrow(_, true, true) => "try_borrow_mut_lamports",
        Call::Borrow(_, false, false) => "try_borrow_data",
        Call::Borrow(_, false, true) => "try_borrow_mut_data",
        Call::Clone(_) => "clone", Call::AsRef(_) => "as_ref", Call::Assign(_) => "assign",
        Call::Resize(_, _, _, true) => "resize", Call::Resize(_, _, _, false) => "realloc",
    }
}

fn selected(method: &str) -> bool { METHODS.contains(&method) }

fn position(call: &Call) -> usize {
    match call {
        Call::Lamports(p) | Call::DataLen(p) | Call::Empty(p) | Call::TryLen(p) |
        Call::Borrow(p, _, _) | Call::Clone(p) | Call::AsRef(p) | Call::Assign(p) |
        Call::Resize(p, _, _, _) => *p,
    }
}

fn function(method: &str) -> &'static str {
    let name = match method {
        "clone" => format!("<{TYPE_PATH}<'a> as core::clone::Clone>::clone"),
        "as_ref" => format!("<{TYPE_PATH}<'a> as core::convert::AsRef<{TYPE_PATH}<'a>>>::as_ref"),
        m => format!("{TYPE_PATH}::<'a>::{m}"),
    };
    Box::leak(name.into_boxed_str())
}

fn args(world: &World<'_, '_>, call: &Call) -> Json {
    let mut fields = match world.args(position(call)) { Json::Obj(fields) => fields, _ => unreachable!() };
    fields.push(("reference".into(), position(call).into()));
    if let Call::Resize(_, len, zero, _) = call {
        fields.push(("new_len".into(), (*len).into()));
        fields.push(("zero_init".into(), (*zero).into()));
    }
    if let Call::Assign(_) = call {
        fields.push(("new_owner".into(), rec::bytes(&[99; 32])));
    }
    Json::Obj(fields)
}

fn record_case(corpus: &mut Corpus, id: &str, entries: &[region::Entry], setup: &[Setup], call: &Call) {
    if !selected(method(call)) { return; }
    let region = region::Region::new(&region::input(entries.to_vec()));
    let (_, infos, _) = unsafe { deserialize(region.base()) };
    let mut world = World { region: &region, infos: &infos, slots: vec![], kept: vec![] };
    for step in setup { world.apply(step); }
    MEMSETS.lock().unwrap().clear();
    let state = world.state(true);
    let arguments = args(&world, call);
    let p = position(call);
    let result = rec::catch(|| -> Json {
        match call {
            Call::Lamports(_) => infos[p].lamports().into(),
            Call::DataLen(_) => infos[p].data_len().into(),
            Call::Empty(_) => infos[p].data_is_empty().into(),
            Call::TryLen(_) => match infos[p].try_data_len() { Ok(n) => rec::ok(n.into()), Err(e) => rec::err(program_error(&e)) },
            Call::Borrow(_, lamports, mutable) => {
                let result = match (*lamports, *mutable) {
                    (true, false) => infos[p].try_borrow_lamports().map(Obj::LamportsShared),
                    (true, true) => infos[p].try_borrow_mut_lamports().map(Obj::LamportsExclusive),
                    (false, false) => infos[p].try_borrow_data().map(Obj::DataShared),
                    (false, true) => infos[p].try_borrow_mut_data().map(Obj::DataExclusive),
                };
                match result {
                    Ok(guard) => {
                        let id = world.slots.len(); world.slots.push(Some(guard));
                        rec::ok(Json::obj([("guard", id.into())]))
                    }
                    Err(e) => rec::err(program_error(&e)),
                }
            }
            Call::AsRef(_) => {
                let reference: &AccountInfo<'_> = infos[p].as_ref();
                assert!(std::ptr::eq(reference, &infos[p]));
                Json::obj([("reference", p.into())])
            }
            Call::Clone(_) => {
                world.kept.push(infos[p].clone());
                world.info_json(world.kept.last().unwrap())
            }
            Call::Assign(_) => { infos[p].assign(&Pubkey::from([99; 32])); Json::Null }
            Call::Resize(_, len, zero, convenience) => match resize(&infos[p], *len, *zero, *convenience) {
                Ok(()) => rec::ok(Json::Null), Err(e) => rec::err(program_error(&e)),
            },
        }
    });
    let outcome = match result {
        Ok(value) => rec::returned(value, world.state(false)),
        Err(reason) => rec::unwound(reason, world.state(false)),
    };
    corpus.push(Record { id: format!("{}/{id}", method(call)), function: function(method(call)),
        generics: vec![], layout: None, state, args: arguments, outcome, observed: None });
}

fn entry(len: usize) -> region::Entry {
    region::Entry::Account(region::Account { key: [1; 32], owner: [2; 32], lamports: 40,
        data: (0..len).map(|n| 10 + (n % 100) as u8).collect(),
        is_signer: false, is_writable: false, executable: false, rent_epoch: 7 })
}

fn terminal_child() {
    let region = region::Region::new(&region::input(vec![entry(3), region::Entry::Duplicate(0)]));
    let (_, infos, _) = unsafe { deserialize(region.base()) };
    resize(&infos[0], 1, true, false).unwrap();
    ZERO_ABORT.store(true, Ordering::SeqCst);
    resize(&infos[1], 3, true, selected("resize")).unwrap();
    panic!("terminal zeroing unexpectedly returned");
}

fn record_terminal(corpus: &mut Corpus) {
    let method = if selected("resize") { "resize" } else { "realloc" };
    let region = region::Region::new(&region::input(vec![entry(3), region::Entry::Duplicate(0)]));
    let (_, infos, _) = unsafe { deserialize(region.base()) };
    resize(&infos[0], 1, true, false).unwrap();
    MEMSETS.lock().unwrap().clear();
    let world = World { region: &region, infos: &infos, slots: vec![], kept: vec![] };
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .arg("--zeroing-child").output().unwrap();
    assert_eq!(output.status.code(), Some(91));
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "zeroing:0:2\n");
    corpus.push(Record { id: format!("{method}/zeroing-terminates"), function: function(method),
        generics: vec![], layout: None, state: world.state(true),
        args: args(&world, &Call::Resize(1, 3, true, method == "resize")),
        outcome: Json::obj([("exit", "terminated".into()), ("reason", "zeroing".into()),
            ("detail", Json::obj([("status", 91.into()), ("byte", 0.into()), ("length", 2.into())]))]), observed: None });
}

fn run() {
    rec::init();
    if std::env::args().nth(1).as_deref() == Some("--zeroing-child") { terminal_child(); return; }
    let mut corpus = Corpus::new(CORPUS, CRATES);
    let aliases = vec![entry(3), region::Entry::Duplicate(0)];
    let operations = [Call::Lamports(1), Call::DataLen(1), Call::Empty(1), Call::TryLen(1),
        Call::Borrow(1, true, false), Call::Borrow(1, true, true), Call::Borrow(1, false, false),
        Call::Borrow(1, false, true), Call::Clone(1), Call::AsRef(1), Call::Assign(1)];
    let setups = [vec![], vec![Setup::BorrowData(0)], vec![Setup::BorrowMutData(0)],
        vec![Setup::BorrowLamports(0)], vec![Setup::BorrowMutLamports(0)],
        vec![Setup::BorrowMutData(0), Setup::Drop(0)], vec![Setup::Clone(0)]];
    for call in &operations {
        for (k, setup) in setups.iter().enumerate() { record_case(&mut corpus, &format!("aliases-{k}"), &aliases, setup, call); }
        record_case(&mut corpus, "empty", &[entry(0), region::Entry::Duplicate(0)], &[], call);
    }
    for convenience in [false, true] {
        for (id, len, zero, setup) in [
            ("same", 3, true, vec![]), ("shrink", 1, true, vec![]), ("zero", 0, true, vec![]),
            ("grow-zero", 5, true, vec![]), ("grow-stale", 5, false, vec![]),
            ("limit", 10243, true, vec![]), ("past-limit", 10244, true, vec![]),
            ("busy-same", 3, true, vec![Setup::BorrowData(0)]),
            ("busy-past-limit", 10244, true, vec![Setup::BorrowMutData(0)]),
            ("lamports-busy", 5, true, vec![Setup::BorrowMutLamports(0)]),
            ("regrow-zero", 3, true, vec![Setup::Resize(0, 1, true)]),
            ("regrow-stale", 3, false, vec![Setup::Resize(0, 1, true)]),
        ] {
            if convenience && !zero { continue; }
            record_case(&mut corpus, id, &aliases, &setup, &Call::Resize(1, len, zero, convenience));
        }
    }
    record_terminal(&mut corpus);
    corpus.write(&rec::out_dir()).unwrap();
}
