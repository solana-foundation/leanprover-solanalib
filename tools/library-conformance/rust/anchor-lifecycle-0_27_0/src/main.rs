#[path = "../../anchor-account-world/world.rs"] mod world;
#[path = "../../anchor/src/track.rs"] mod track;
#[path = "../../anchor-lifecycle-shared/enc.rs"] mod enc;
#[path = "../../anchor-lifecycle-shared/script.rs"] mod script;
#[path = "../../anchor-lifecycle-shared/cases.rs"] mod cases;

#[global_allocator]
static ALLOCATOR: track::Tracking = track::Tracking;

static APIS: &[cases::Api] = &[
    cases::Api { object: "account", method: "try_accounts", function: "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::Accounts<'info>>::try_accounts" },
    cases::Api { object: "account", method: "close", function: "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::AccountsClose<'info>>::close" },
    cases::Api { object: "account", method: "exit", function: "<anchor_lang::accounts::account::Account<'info, T> as anchor_lang::AccountsExit<'info>>::exit" },
    cases::Api { object: "program", method: "try_accounts", function: "<anchor_lang::accounts::program::Program<'info, T> as anchor_lang::Accounts<'info>>::try_accounts" },
    cases::Api { object: "signer", method: "try_accounts", function: "<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Accounts<'info>>::try_accounts" },
    cases::Api { object: "system_account", method: "try_accounts", function: "<anchor_lang::accounts::system_account::SystemAccount<'info> as anchor_lang::Accounts<'info>>::try_accounts" },
    cases::Api { object: "sysvar", method: "try_accounts", function: "<anchor_lang::accounts::sysvar::Sysvar<'info, T> as anchor_lang::Accounts<'info>>::try_accounts" },
    cases::Api { object: "unchecked_account", method: "try_accounts", function: "<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as anchor_lang::Accounts<'info>>::try_accounts" },
    cases::Api { object: "default", method: "exit", function: "anchor_lang::AccountsExit::exit" },
    cases::Api { object: "account", method: "reload", function: "anchor_lang::accounts::account::Account::<'a, T>::reload" },
    cases::Api { object: "account", method: "try_from", function: "anchor_lang::accounts::account::Account::<'a, T>::try_from" },
    cases::Api { object: "account", method: "try_from_unchecked", function: "anchor_lang::accounts::account::Account::<'a, T>::try_from_unchecked" },
    cases::Api { object: "account_info", method: "try_accounts", function: "anchor_lang::accounts::account_info::<impl anchor_lang::Accounts<'info> for solana_program::account_info::AccountInfo<'info>>::try_accounts" },
    cases::Api { object: "boxed", method: "try_accounts", function: "anchor_lang::accounts::boxed::<impl anchor_lang::Accounts<'info> for alloc::boxed::Box<T>>::try_accounts" },
    cases::Api { object: "boxed", method: "exit", function: "anchor_lang::accounts::boxed::<impl anchor_lang::AccountsExit<'info> for alloc::boxed::Box<T>>::exit" },
    cases::Api { object: "unchecked_account", method: "try_from", function: "anchor_lang::accounts::unchecked_account::UncheckedAccount::<'info>::try_from" }
];
fn main() {
    conformance_recorder::init();
    let mut corpus = conformance_recorder::Corpus::new("anchor_lifecycle_0_27_0", &[("anchor-lang", "0.27.0")]);
    cases::record(&mut corpus, APIS);
    corpus.write(&conformance_recorder::out_dir()).expect("write lifecycle corpus");
}
