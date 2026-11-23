//! Native values and logger calls with the established scripted syscall shim.
mod logger;
mod values;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;
use conformance_recorder as rec;
fn main() {
    rec::init();
    let out = rec::out_dir();
    values::corpus().write(&out).expect("value corpus");
    logger::corpus().write(&out).expect("logger corpus");
}
