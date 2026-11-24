//! Records solana-account-view 1.0.0 and solana-account-info 3.1.1, the
//! the pinned versions, over loader-serialized input regions.

mod info;
mod region;
mod view;

use conformance_recorder::{self as rec, Corpus};

fn main() {
    if std::env::var_os("ACCOUNTS_V1_VERBOSE").is_none() {
        rec::init();
    }
    let out = rec::out_dir();
    let mut v = Corpus::new("solana_account_view_1_0_0", &[("solana-account-view", "1.0.0"), ("pinocchio", "0.10.2")]);
    view::record(&mut v);
    let mut f =
        Corpus::new("solana_account_view_1_0_0_forged", &[("solana-account-view", "1.0.0"), ("pinocchio", "0.10.2")]);
    view::record_forged(&mut f);
    let mut i = Corpus::new(
        "solana_account_info_3_1_1",
        &[("solana-account-info", "3.1.1"), ("solana-program-entrypoint", "3.1.1")],
    );
    info::record(&mut i);
    for corpus in [v, f, i] {
        corpus.write(&out).expect("write corpus");
    }
}
