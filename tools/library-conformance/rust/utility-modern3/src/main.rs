#[allow(dead_code)]
#[path = "../../utility-common/sysvar_scripts.rs"]
mod sysvar_scripts;
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
#[path = "../../utility-common/epoch.rs"]
mod epoch_cases;
#[allow(dead_code)]
#[path = "../../utility-common/hash.rs"]
mod hash_cases;
use solana_rent::Rent;
use solana_sysvar::Sysvar;
use solana_epoch_schedule::EpochSchedule;
use solana_sha256_hasher::{hash,hashv};

fn main() {
    use conformance_recorder::{self as rec, Corpus};
    rec::init();
    let mut corpus = Corpus::new("utility_modern3", &[("solana-rent", "3.0.0"), ("solana-sysvar", "3.1.1"), ("solana-epoch-schedule", "3.0.0"), ("solana-sha256-hasher", "3.1.0")]);
    rent_cases_native::record(&mut corpus, None, "solana_rent::Rent::is_exempt");
    epoch_cases::queries(&mut corpus, Some("solana_epoch_schedule::EpochSchedule::get_first_slot_in_epoch"), None);
    epoch_cases::getter(&mut corpus, "solana_sysvar::epoch_schedule::<impl solana_sysvar::Sysvar for solana_epoch_schedule::EpochSchedule>::get");
    hash_cases::record(&mut corpus, "solana_sha256_hasher::hash", None, false);
    corpus.write(&rec::out_dir()).expect("write utility corpus");
}
