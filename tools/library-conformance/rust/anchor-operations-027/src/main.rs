//! Calls the exact Anchor 0.27.0 operations; invocation functions are never entered.
#[path = "../../anchor/src/track.rs"] mod track;
#[path = "../../anchor-operations-common/enc.rs"] mod enc;
#[path = "../../anchor-operations-common/errors.rs"] mod errors;
#[path = "../../anchor-operations-common/codecs.rs"] mod codecs;
#[path = "../../anchor-operations-common/contexts.rs"] mod contexts;
mod codes;
mod identities;
mod private_bpf_writer;
use conformance_recorder::{self as rec, Corpus};
#[global_allocator]
static GLOBAL: track::Tracking = track::Tracking;
fn main() {
    rec::init();
    if std::env::var_os("CONFORMANCE_DEBUG").is_some() { std::panic::set_hook(Box::new(|info| eprintln!("{info}"))); }
    let out = rec::out_dir();
    let mut corpus = Corpus::new("anchor_operations_0_27_0", &[("anchor-lang", "0.27.0")]);
    errors::record_all(&mut corpus);
    codecs::record_all(&mut corpus);
    contexts::record_all(&mut corpus);
    corpus.write(&out).expect("write corpus");
}
