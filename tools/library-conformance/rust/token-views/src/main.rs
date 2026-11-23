//! Records pinocchio-token 0.6.0 and pinocchio-token-2022 0.3.1 natively (host
//! build of the Solana branches; see `.cargo/config.toml`) over loader input
//! regions (`conformance-accounts`), with the syscall shim
//! (`conformance-shim`) answering `sol_invoke_signed_c`. Writes two corpus
//! files into the directory given as the first argument.

mod batch;
mod common;
mod request;
mod state;

use conformance_recorder::Corpus;

fn main() {
    conformance_recorder::init();
    // Every CPI path recorded here initializes its CPI accounts with
    // `CpiAccount::init_from_account_view` in solana-instruction-view 2.1.0, which
    // copies the four header bytes as one word, so the raw bytes are deterministic.
    conformance_shim::log_cpi_raw_header(true);
    let out = conformance_recorder::out_dir();

    let mut legacy = Corpus::new("pinocchio_token_0_6_0", &[("pinocchio-token", "0.6.0")]);
    state::record_version(&mut legacy, &state::Version {
        krate: "pinocchio_token",
        id: pinocchio_token::ID.to_bytes(),
        other_id: pinocchio_token_2022::ID.to_bytes(),
        token2022: false,
        account_from: pinocchio_token::state::Account::from_account_view,
        mint_from: pinocchio_token::state::Mint::from_account_view,
        amount: pinocchio_token::state::Account::amount,
        mint: pinocchio_token::state::Account::mint,
        owner: pinocchio_token::state::Account::owner,
        state: pinocchio_token::state::Account::state,
        decimals: pinocchio_token::state::Mint::decimals,
    });
    batch::record_all(&mut legacy);
    legacy.write(&out).unwrap();

    let mut token2022 = Corpus::new("pinocchio_token_2022_0_3_1", &[("pinocchio-token-2022", "0.3.1")]);
    state::record_version(&mut token2022, &state::Version {
        krate: "pinocchio_token_2022",
        id: pinocchio_token_2022::ID.to_bytes(),
        other_id: pinocchio_token::ID.to_bytes(),
        token2022: true,
        account_from: pinocchio_token_2022::state::Account::from_account_view,
        mint_from: pinocchio_token_2022::state::Mint::from_account_view,
        amount: pinocchio_token_2022::state::Account::amount,
        mint: pinocchio_token_2022::state::Account::mint,
        owner: pinocchio_token_2022::state::Account::owner,
        state: pinocchio_token_2022::state::Account::state,
        decimals: pinocchio_token_2022::state::Mint::decimals,
    });
    request::record_all(&mut token2022);
    token2022.write(&out).unwrap();
}
