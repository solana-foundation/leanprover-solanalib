//! Native account calls with the established scripted syscall shim.
mod accounts;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;
use conformance_recorder as rec;
fn main() {
    rec::init();
    accounts::corpus().write(&rec::out_dir()).expect("account corpus");
}
