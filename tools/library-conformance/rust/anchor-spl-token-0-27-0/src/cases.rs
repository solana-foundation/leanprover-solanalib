use crate::driver::*;
use crate::anchor_lang::solana_program::account_info::AccountInfo;
pub const FUNCTIONS: &[(&str, &str)] = &[
    ("burn", "anchor_spl::token::burn"),
    ("mint_to", "anchor_spl::token::mint_to"),
    ("transfer", "anchor_spl::token::transfer"),
];
pub fn field_count(operation: &str) -> usize { match operation {
    "burn" => 3,
    "mint_to" => 3,
    "transfer" => 3,
    _ => panic!("unknown operation"),
} }
pub fn enum_size(operation: &str) -> usize {
    let _ = operation; std::mem::size_of::<spl_token::instruction::TokenInstruction>()
}
pub fn run<'a, 'b, 'c>(case: &Case, base: &[AccountInfo<'static>], ids: &[usize],
    remaining: Vec<AccountInfo<'static>>, seeds: &'a [&'b [&'c [u8]]]) -> Run {
    match case.operation {
        "burn" => {
            let accounts = anchor_spl::token::Burn { mint: base[ids[0]].clone(), from: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::burn(ctx, case.amount).map(|()| None))
        }
        "mint_to" => {
            let accounts = anchor_spl::token::MintTo { mint: base[ids[0]].clone(), to: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::mint_to(ctx, case.amount).map(|()| None))
        }
        "transfer" => {
            let accounts = anchor_spl::token::Transfer { from: base[ids[0]].clone(), to: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::transfer(ctx, case.amount).map(|()| None))
        }
        _ => panic!("unknown wrapper"),
    }
}
