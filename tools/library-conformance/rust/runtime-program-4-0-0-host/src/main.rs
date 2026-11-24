//! Records the host branches of solana-program 4.0.0 at the pinned versions: `sol_log_data` and
//! `set_return_data` call the overridable `program_stubs` (target `hostStub`).
#![feature(internal_output_capture)]

#[allow(dead_code)]
#[path = "../../runtime-common/host_stubs.rs"]
mod host_stubs;
#[allow(dead_code)]
#[path = "../../runtime-common/syscall_cases.rs"]
mod syscall_cases;

use conformance_recorder::{self as rec, Corpus, Json};
use host_stubs::*;
use solana_program::program_stubs;
use syscall_cases::{hex_fields, sparse};

fn program_corpus() -> Corpus {
    let mut c = Corpus::new("solana_program_4_0_0_host", &[("solana-program", "4.0.0")]);
    let field_sets: Vec<(&str, Vec<Vec<u8>>)> =
        vec![("none", vec![]), ("three", vec![vec![1, 2], vec![], vec![3]]), ("large", vec![sparse(1024, 7)])];
    for (name, fields) in field_sets {
        let args = Json::obj([("fields", hex_fields(&fields))]);
        let slices: Vec<&[u8]> = fields.iter().map(|f| f.as_slice()).collect();
        host_case(&mut c, format!("sol_log_data/{name}"), "solana_program::log::sol_log_data", args, vec![],
            || solana_program::log::sol_log_data(&slices), |_| Json::Null);
    }
    for (name, data) in [("empty", vec![]), ("three", vec![1u8, 2, 3]), ("over_max", sparse(1025, 4))] {
        let args = Json::obj([("data", rec::bytes(&data))]);
        host_case(&mut c, format!("set_return_data/{name}"), "solana_program::program::set_return_data", args, vec![],
            || solana_program::program::set_return_data(&data), |_| Json::Null);
    }
    c
}

fn main() {
    rec::init();
    let out = rec::out_dir();
    program_corpus().write(&out).expect("write corpus");
}
