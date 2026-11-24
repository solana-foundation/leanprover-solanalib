//! Native calls to the exact Anchor 1.1.2 SDK.
#[path = "../../anchor-loader-shared/enc.rs"] mod enc;
#[path = "../../anchor-account-world/world.rs"] mod world;
#[path = "../../anchor-loader-shared/script.rs"] mod script;
#[path = "../../anchor-loader-shared/cases.rs"] mod cases;

fn main() {
    conformance_recorder::init();
    let mut corpus = conformance_recorder::Corpus::new("anchor_loader_1_1_2", &[("anchor-lang", "1.1.2")]);
    cases::record(&mut corpus, false);
    corpus.write(&conformance_recorder::out_dir()).expect("write loader corpus");
}
