use crate::driver::*;
use crate::anchor_lang::solana_program::account_info::AccountInfo;
pub const FUNCTIONS: &[(&str, &str)] = &[
    ("transfer_checked", "anchor_spl::token_2022::transfer_checked"),
];
pub fn field_count(operation: &str) -> usize { match operation {
    "transfer_checked" => 4,
    _ => panic!("unknown operation"),
} }
pub fn enum_size(operation: &str) -> usize {
    let _ = operation; std::mem::size_of::<spl_token_2022::instruction::TokenInstruction>()
}
pub fn run<'a, 'b, 'c>(case: &Case, base: &[AccountInfo<'static>], ids: &[usize],
    remaining: Vec<AccountInfo<'static>>, seeds: &'a [&'b [&'c [u8]]]) -> Run {
    match case.operation {
        "transfer_checked" => {
            let accounts = anchor_spl::token_2022::TransferChecked { from: base[ids[0]].clone(), mint: base[ids[1]].clone(), to: base[ids[2]].clone(), authority: base[ids[3]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::transfer_checked(ctx, case.amount, case.decimals).map(|()| None))
        }
        _ => panic!("unknown wrapper"),
    }
}
