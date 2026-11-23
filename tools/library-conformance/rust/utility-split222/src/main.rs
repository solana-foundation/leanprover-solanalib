#[allow(dead_code)]
#[path = "../../utility-common/sysvar_scripts.rs"]
mod sysvar_scripts;
#[allow(dead_code)]
#[path = "../../anchor/src/track.rs"]
mod track;
#[global_allocator]
static ALLOCATOR: track::Tracking = track::Tracking;
use solana_sysvar::__private::ProgramError;
#[allow(dead_code)]
#[path = "../../runtime-common/rent_cases.rs"]
mod rent_cases;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;
#[allow(dead_code)]
#[path = "../../utility-common/rent.rs"]
mod rent_cases_native;
#[allow(dead_code)]
#[path = "../../utility-common/sysvar.rs"]
mod sysvar_cases;
#[allow(dead_code)]
#[path = "../../utility-common/hash.rs"]
mod hash_cases;
#[allow(dead_code)]
#[path = "../../utility-common/log.rs"]
mod log_cases;
use solana_sysvar::{clock::Clock,Sysvar};
use solana_rent::Rent;
use solana_sha256_hasher::{hash,hashv};

fn main() {
    use conformance_recorder::{self as rec, Corpus};
    rec::init();
    let mut corpus = Corpus::new("utility_split222", &[("solana-sysvar", "2.2.2"), ("solana-rent", "2.2.1"), ("solana-sha256-hasher", "2.3.0"), ("solana-msg", "2.2.1")]);
    sysvar_cases::record(&mut corpus, Some("solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"), Some("solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get"));
    rent_cases_native::record(&mut corpus, None, "solana_rent::Rent::is_exempt");
    hash_cases::record(&mut corpus, "solana_sha256_hasher::hash", Some("solana_sha256_hasher::hashv"), true);
    log_cases::text(&mut corpus, "solana_msg::sol_log", solana_msg::sol_log);
    corpus.write(&rec::out_dir()).expect("write utility corpus");
}
