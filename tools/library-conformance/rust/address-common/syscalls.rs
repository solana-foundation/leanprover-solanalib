//! solana-address 2.6.x on the selected Solana branch through the `sol_*`
//! test shim: `try_find_program_address` and `find_program_address`
//! (`sol_try_find_program_address`), and `is_on_curve`
//! (`sol_curve_validate_point`, 2.6.0 only).
//!
//! Each case runs in `conformance_shim::case` with a scripted reply. The
//! record state is `{"syscalls": {"replies", "log"}}` before and after the
//! call; a reply marked `terminate` ends the call with a terminated outcome.
//! Replies cover status zero with an address (bump written, left at its
//! initial value, zero), nonzero statuses with and without written outputs,
//! statuses above 32 bits, partial and over-long address data, unconsumed
//! extra replies and terminal syscalls. Status zero without a full address is
//! excluded: the `assume_init` call in the wrapper would read uninitialized memory,
//! which model admission (`SuccessInitialized`) rules out.

use conformance_recorder::{self as rec, Corpus, Json, Record};
use conformance_shim::{self as shim, Reply, Script};
use solana_address::Address;

pub const TRY_FIND: &str = "solana_address::syscalls::<impl solana_address::Address>::try_find_program_address";
pub const FIND: &str = "solana_address::syscalls::<impl solana_address::Address>::find_program_address";
pub const IS_ON_CURVE: &str = "solana_address::Address::is_on_curve";

const PDA: &str = "sol_try_find_program_address";
const CURVE: &str = "sol_curve_validate_point";

fn address(bytes: [u8; 32]) -> Address {
    // SAFETY: `Address` is `#[repr(transparent)]` over `[u8; 32]`.
    unsafe { core::mem::transmute::<[u8; 32], Address>(bytes) }
}

fn bytes_of(a: &Address) -> [u8; 32] {
    // SAFETY: as above.
    unsafe { *(a as *const Address as *const [u8; 32]) }
}

fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(53).wrapping_add(seed)).collect()
}

fn pattern32(seed: u8) -> [u8; 32] {
    pattern(32, seed).try_into().unwrap()
}

fn found(r: &(Address, u8)) -> Json {
    Json::obj([("address", rec::bytes(&bytes_of(&r.0))), ("bump", r.1.into())])
}

fn state(script: &Script) -> Json {
    Json::obj([("syscalls", script.state_before())])
}

fn after() -> Json {
    Json::obj([("syscalls", shim::state())])
}

fn push(c: &mut Corpus, id: String, function: &'static str, script: &Script, args: Json, outcome: Json) {
    c.push(Record { id, function, generics: vec![], layout: None, state: state(script), args, outcome, observed: None });
}

/// The PDA replies: (name, script).
fn pda_scripts() -> Vec<(&'static str, Script)> {
    let a = pattern32(201);
    let long: Vec<u8> = pattern(40, 7);
    let one = |r: Reply| Script::new(vec![r]);
    vec![
        ("ok_bump254", one(Reply::new(PDA, 0).data(&a).bump(254))),
        ("ok_bump_unwritten", one(Reply::new(PDA, 0).data(&a))),
        ("ok_bump0", one(Reply::new(PDA, 0).data(&a).bump(0))),
        ("ok_long_data", one(Reply::new(PDA, 0).data(&long).bump(9))),
        ("err1_unwritten", one(Reply::new(PDA, 1))),
        ("err1_written", one(Reply::new(PDA, 1).data(&a).bump(7))),
        ("err1_partial", one(Reply::new(PDA, 1).data(&a[..5]))),
        ("err_max", one(Reply::new(PDA, u64::MAX).data(&a).bump(255))),
        ("err_high_bits", one(Reply::new(PDA, 1 << 32))),
        ("ok_extra_reply", Script::new(vec![
            Reply::new(PDA, 0).data(&a).bump(250),
            Reply::new(PDA, 1),
        ])),
        ("terminate", one(Reply::new(PDA, 0).data(&a).bump(1).terminate("compute budget exceeded"))),
    ]
}

/// PDA inputs: (name, seeds, program id). The wrapper does not check the
/// runtime seed limits, so 17 seeds and a 33-byte seed reach the syscall.
fn pda_inputs() -> Vec<(&'static str, Vec<Vec<u8>>, [u8; 32])> {
    let pid = pattern32(3);
    vec![
        ("no_seeds", vec![], pid),
        ("vault", vec![b"vault".to_vec()], pid),
        ("mixed", vec![vec![], b"x".to_vec(), pattern(32, 1)], [0; 32]),
        ("seeds_17", (0..17).map(|i| vec![i as u8]).collect(), pid),
        ("seed_len_33", vec![pattern(33, 2)], pid),
    ]
}

fn pda_args(seeds: &[Vec<u8>], pid: &[u8; 32]) -> Json {
    Json::obj([("seeds", Json::arr(seeds.iter(), |s| rec::bytes(s))), ("program_id", rec::bytes(pid))])
}

pub fn record_pda(c: &mut Corpus) {
    let inputs = pda_inputs();
    for (sname, script) in pda_scripts() {
        // Every script at the first input; the remaining inputs at a success
        // and a failure.
        let selected: Vec<_> = if sname == "ok_bump254" || sname == "err1_written" {
            inputs.iter().collect()
        } else {
            inputs.iter().take(1).collect()
        };
        for (iname, seeds, pid) in selected {
            let slices: Vec<&[u8]> = seeds.iter().map(|s| s.as_slice()).collect();
            let p = address(*pid);
            let outcome = shim::case(&script, || {
                let r = Address::try_find_program_address(&slices, &p);
                rec::returned(rec::option(&r, found), after())
            });
            push(c, format!("try_find_program_address/{sname}/{iname}"), TRY_FIND, &script, pda_args(seeds, pid), outcome);
            let outcome = shim::case(&script, || {
                let r = Address::find_program_address(&slices, &p);
                rec::returned(found(&r), after())
            });
            push(c, format!("find_program_address/{sname}/{iname}"), FIND, &script, pda_args(seeds, pid), outcome);
        }
    }
}

/// `Address::is_on_curve` (2.6.0): statuses 0, 1, 2, `u64::MAX`, a terminal
/// syscall, and an unconsumed extra reply.
pub fn record_curve(c: &mut Corpus) {
    let one = |r: Reply| Script::new(vec![r]);
    let scripts = vec![
        ("on", one(Reply::new(CURVE, 0))),
        ("off", one(Reply::new(CURVE, 1))),
        ("status2", one(Reply::new(CURVE, 2))),
        ("status_max", one(Reply::new(CURVE, u64::MAX))),
        ("extra_reply", Script::new(vec![Reply::new(CURVE, 0), Reply::new(CURVE, 1)])),
        ("terminate", one(Reply::new(CURVE, 0).terminate("compute budget exceeded"))),
    ];
    let points = [("zero", [0u8; 32]), ("ones", [0xff; 32]), ("pattern", pattern32(17))];
    for (sname, script) in &scripts {
        for (pname, bytes) in &points {
            if *sname != "on" && *sname != "off" && *pname != "pattern" {
                continue;
            }
            let a = address(*bytes);
            let outcome = shim::case(script, || rec::returned(a.is_on_curve().into(), after()));
            push(c, format!("is_on_curve/{sname}/{pname}"), IS_ON_CURVE, script,
                 Json::obj([("self", rec::bytes(bytes))]), outcome);
        }
    }
}
