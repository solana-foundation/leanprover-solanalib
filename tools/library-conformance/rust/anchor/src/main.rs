//! Records anchor-lang 1.0.2 and anchor-spl 1.0.2 (the exact pinned versions) for the Anchor library models.

mod accounts;
mod enc;
mod errors;
mod json;
mod misc;
mod script;
mod spl;
mod track;
mod world;

use conformance_recorder::{self as rec, Corpus};
use conformance_shim as _;

#[global_allocator]
static GLOBAL: track::Tracking = track::Tracking;

fn main() {
    rec::init();
    let out = rec::out_dir();
    let mut lang = Corpus::new("anchor_lang_1_0_2", &[("anchor-lang", "1.0.2")]);
    errors::record_all(&mut lang);
    accounts::record_all(&mut lang);
    misc::record_all(&mut lang);
    lang.write(&out).expect("write corpus");
    let mut spl = Corpus::new("anchor_spl_1_0_2", &[("anchor-spl", "1.0.2"), ("anchor-lang", "1.0.2")]);
    spl::record_all(&mut spl);
    spl.write(&out).expect("write corpus");
}
