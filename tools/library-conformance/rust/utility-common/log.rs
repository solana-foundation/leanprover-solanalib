use crate::syscall_cases::syscall_case;
use conformance_recorder::{Corpus, Json};
use conformance_shim::Script;

pub fn text(c: &mut Corpus, function: &'static str, call: fn(&str)) {
    for (n, message) in ["", "Solana", "a\0b", "λ☀️\n"].iter().enumerate() {
        syscall_case(c, format!("log/{n}"), function, (*message).into(), Script::new(vec![]),
            || call(message), |_| Json::Null);
    }
}
pub fn compute(c: &mut Corpus, function: &'static str, call: fn()) {
    syscall_case(c, "compute".into(), function, Json::Null, Script::new(vec![]), call, |_| Json::Null);
}
