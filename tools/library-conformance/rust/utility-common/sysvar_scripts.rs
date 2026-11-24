//! Shared exact builtin and noncanonical status scripts.
use crate::syscall_cases::getter_scripts;
use conformance_shim::{Reply, Script};

pub fn scripts(syscall: &str, values: &[(&'static str, Vec<u8>)]) -> Vec<(String, Script)> {
    let mut scripts = getter_scripts(syscall, values);
    for tag in [15u64, 21, 22, 24, 25, 26, 27] {
        scripts.push((format!("builtin{tag}"), Script::new(vec![Reply::new(syscall, tag << 32)])));
    }
    scripts.push(("noncanonical_builtin".into(), Script::new(vec![Reply::new(syscall, (15 << 32) | 7)])));
    scripts
}
