//! Records the runtime helpers at the pinned versions: pinocchio 0.10.2
//! `Rent::try_minimum_balance`, `Clock::get` and `Rent::get`, solana-msg 3.1.0 `sol_log`,
//! solana-program 4.0.0 `sol_log_data` and `set_return_data`, solana-sha256-hasher 3.1.0
//! `hashv`, solana-curve25519 3.1.12 `validate_edwards`, solana-hash 4.5.0 `Hash::to_bytes`,
//! solana-sdk-ids 3.1.0 `system_program::id`, solana-zero-copy 1.2.0 `From<U64> for u64` and
//! solana-program-option 3.1.0 `COption::is_some`.

#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[path = "../../runtime-common/rent_pinocchio_0_10_2.rs"]
mod rent_pinocchio_0_10_2;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;
mod syscalls;
mod values;

use conformance_shim as _;

use conformance_recorder::{self as rec, Corpus};

fn pinocchio_corpus() -> Corpus {
    let mut c = Corpus::new("pinocchio_0_10_2", &[("pinocchio", "0.10.2")]);
    rent_pinocchio_0_10_2::record(&mut c, false);
    syscalls::pinocchio_getters(&mut c);
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    for corpus in [
        pinocchio_corpus(),
        syscalls::msg_corpus(),
        syscalls::program_corpus(),
        syscalls::sha256_corpus(),
        syscalls::curve_corpus(),
        values::hash_corpus(),
        values::sdk_ids_corpus(),
        values::zero_copy_corpus(),
        values::program_option_corpus(),
    ] {
        corpus.write(&out).expect("write corpus");
    }
}
