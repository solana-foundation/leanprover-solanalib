use crate::driver::*;
use crate::anchor_lang::solana_program::account_info::AccountInfo;
use spl_token_2022_interface as spl_token_2022;
fn authority_type(code: u8) -> spl_token_2022::instruction::AuthorityType {
    use spl_token_2022::instruction::AuthorityType as A;
    match code { 0 => A::MintTokens, 3 => A::CloseAccount, 16 => A::Pause, _ => panic!("unselected authority case") }
}
pub const FUNCTIONS: &[(&str, &str)] = &[
    ("burn_checked", "anchor_spl::token_2022::burn_checked"),
    ("mint_to_checked", "anchor_spl::token_2022::mint_to_checked"),
    ("set_authority", "anchor_spl::token_2022::set_authority"),
    ("transfer_checked", "anchor_spl::token_2022::transfer_checked"),
];
pub fn field_count(operation: &str) -> usize { match operation {
    "burn_checked" => 3,
    "mint_to_checked" => 3,
    "set_authority" => 2,
    "transfer_checked" => 4,
    _ => panic!("unknown operation"),
} }
pub fn enum_size(operation: &str) -> usize {
    let _ = operation; std::mem::size_of::<spl_token_2022::instruction::TokenInstruction>()
}
pub fn run<'a, 'b, 'c>(case: &Case, base: &[AccountInfo<'static>], ids: &[usize],
    remaining: Vec<AccountInfo<'static>>, seeds: &'a [&'b [&'c [u8]]]) -> Run {
    match case.operation {
        "burn_checked" => {
            let accounts = anchor_spl::token_2022::BurnChecked { mint: base[ids[0]].clone(), from: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::burn_checked(ctx, case.amount, case.decimals).map(|()| None))
        }
        "mint_to_checked" => {
            let accounts = anchor_spl::token_2022::MintToChecked { mint: base[ids[0]].clone(), to: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::mint_to_checked(ctx, case.amount, case.decimals).map(|()| None))
        }
        "set_authority" => {
            let accounts = anchor_spl::token_2022::SetAuthority { current_authority: base[ids[0]].clone(), account_or_mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::set_authority(ctx, authority_type(case.authority_type), case.option1).map(|()| None))
        }
        "transfer_checked" => {
            let accounts = anchor_spl::token_2022::TransferChecked { from: base[ids[0]].clone(), mint: base[ids[1]].clone(), to: base[ids[2]].clone(), authority: base[ids[3]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::transfer_checked(ctx, case.amount, case.decimals).map(|()| None))
        }
        _ => panic!("unknown wrapper"),
    }
}
