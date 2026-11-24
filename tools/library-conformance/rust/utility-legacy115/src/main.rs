#[allow(dead_code)]
#[path = "../../utility-common/sysvar_scripts.rs"]
mod sysvar_scripts;
#[allow(dead_code)]
#[path = "../../anchor/src/track.rs"]
mod track;
#[global_allocator]
static ALLOCATOR: track::Tracking = track::Tracking;
use solana_program::program_error::ProgramError;
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
#[path = "../../utility-common/log.rs"]
mod log_cases;
#[allow(dead_code)]
#[path = "../../utility-common/epoch.rs"]
mod epoch_cases;
use solana_program::{rent::Rent,clock::Clock,sysvar::Sysvar,epoch_schedule::EpochSchedule};

fn main() {
    use conformance_recorder::{self as rec, Corpus};
    rec::init();
    let mut corpus = Corpus::new("utility_legacy115", &[("solana-program", "1.15.2")]);
    rent_cases_native::record(&mut corpus, Some("solana_program::rent::Rent::minimum_balance"), "solana_program::rent::Rent::is_exempt");
    sysvar_cases::record(&mut corpus, None, Some("solana_program::sysvar::rent::<impl solana_program::sysvar::Sysvar for solana_program::rent::Rent>::get"));
    log_cases::text(&mut corpus, "solana_program::log::sol_log", solana_program::log::sol_log);
    epoch_cases::queries(&mut corpus, None, Some("solana_program::epoch_schedule::EpochSchedule::get_last_slot_in_epoch"));
    log_cases::compute(&mut corpus, "solana_program::log::sol_log_compute_units", solana_program::log::sol_log_compute_units);
    corpus.write(&rec::out_dir()).expect("write utility corpus");
}
