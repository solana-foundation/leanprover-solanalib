use crate::driver::*;
use crate::anchor_lang::solana_program::account_info::AccountInfo;
fn authority_type(code: u8) -> spl_token_2022::instruction::AuthorityType {
    use spl_token_2022::instruction::AuthorityType as A;
    match code { 0 => A::MintTokens, 3 => A::CloseAccount, 16 => A::Pause, _ => panic!("unselected authority case") }
}
fn extension_types(wide: bool) -> Vec<spl_token_2022::extension::ExtensionType> {
    use spl_token_2022::extension::ExtensionType as E;
    if wide { vec![E::Uninitialized, E::PausableAccount, E::PausableAccount] } else { vec![E::ImmutableOwner, E::PermanentDelegate] }
}
pub const FUNCTIONS: &[(&str, &str)] = &[
    ("transfer", "anchor_spl::token::transfer"),
    ("burn", "anchor_spl::token_2022::burn"),
    ("close_account", "anchor_spl::token_2022::close_account"),
    ("get_account_data_size", "anchor_spl::token_2022::get_account_data_size"),
    ("initialize_account3", "anchor_spl::token_2022::initialize_account3"),
    ("initialize_immutable_owner", "anchor_spl::token_2022::initialize_immutable_owner"),
    ("initialize_mint2", "anchor_spl::token_2022::initialize_mint2"),
    ("mint_to", "anchor_spl::token_2022::mint_to"),
    ("set_authority", "anchor_spl::token_2022::set_authority"),
    ("transfer_checked", "anchor_spl::token_2022::transfer_checked"),
    ("group_member_pointer_initialize", "anchor_spl::token_2022_extensions::group_member_pointer::group_member_pointer_initialize"),
    ("group_pointer_initialize", "anchor_spl::token_2022_extensions::group_pointer::group_pointer_initialize"),
    ("metadata_pointer_initialize", "anchor_spl::token_2022_extensions::metadata_pointer::metadata_pointer_initialize"),
    ("mint_close_authority_initialize", "anchor_spl::token_2022_extensions::mint_close_authority::mint_close_authority_initialize"),
    ("non_transferable_mint_initialize", "anchor_spl::token_2022_extensions::non_transferable::non_transferable_mint_initialize"),
    ("permanent_delegate_initialize", "anchor_spl::token_2022_extensions::permanent_delegate::permanent_delegate_initialize"),
    ("transfer_hook_initialize", "anchor_spl::token_2022_extensions::transfer_hook::transfer_hook_initialize"),
];
pub fn field_count(operation: &str) -> usize { match operation {
    "transfer" => 3,
    "burn" => 3,
    "close_account" => 3,
    "get_account_data_size" => 1,
    "initialize_account3" => 3,
    "initialize_immutable_owner" => 1,
    "initialize_mint2" => 1,
    "mint_to" => 3,
    "set_authority" => 2,
    "transfer_checked" => 4,
    "group_member_pointer_initialize" => 2,
    "group_pointer_initialize" => 2,
    "metadata_pointer_initialize" => 2,
    "mint_close_authority_initialize" => 2,
    "non_transferable_mint_initialize" => 2,
    "permanent_delegate_initialize" => 2,
    "transfer_hook_initialize" => 2,
    _ => panic!("unknown operation"),
} }
pub fn enum_size(operation: &str) -> usize {
    if operation == "transfer" { std::mem::size_of::<spl_token::instruction::TokenInstruction>() } else { std::mem::size_of::<spl_token_2022::instruction::TokenInstruction>() }
}
pub fn run<'a, 'b, 'c>(case: &Case, base: &[AccountInfo<'static>], ids: &[usize],
    remaining: Vec<AccountInfo<'static>>, seeds: &'a [&'b [&'c [u8]]]) -> Run {
    match case.operation {
        "transfer" => {
            let accounts = anchor_spl::token::Transfer { from: base[ids[0]].clone(), to: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::transfer(ctx, case.amount).map(|()| None))
        }
        "burn" => {
            let accounts = anchor_spl::token_2022::Burn { mint: base[ids[0]].clone(), from: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::burn(ctx, case.amount).map(|()| None))
        }
        "close_account" => {
            let accounts = anchor_spl::token_2022::CloseAccount { account: base[ids[0]].clone(), destination: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::close_account(ctx).map(|()| None))
        }
        "get_account_data_size" => {
            let extensions = extension_types(case.extensions);
            let accounts = anchor_spl::token_2022::GetAccountDataSize { mint: base[ids[0]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::get_account_data_size(ctx, &extensions).map(Some))
        }
        "initialize_account3" => {
            let accounts = anchor_spl::token_2022::InitializeAccount3 { account: base[ids[0]].clone(), mint: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::initialize_account3(ctx).map(|()| None))
        }
        "initialize_immutable_owner" => {
            let accounts = anchor_spl::token_2022::InitializeImmutableOwner { account: base[ids[0]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::initialize_immutable_owner(ctx).map(|()| None))
        }
        "initialize_mint2" => {
            let accounts = anchor_spl::token_2022::InitializeMint2 { mint: base[ids[0]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::initialize_mint2(ctx, case.decimals, &key(81), case.option2.as_ref()).map(|()| None))
        }
        "mint_to" => {
            let accounts = anchor_spl::token_2022::MintTo { mint: base[ids[0]].clone(), to: base[ids[1]].clone(), authority: base[ids[2]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::mint_to(ctx, case.amount).map(|()| None))
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
        "group_member_pointer_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::group_member_pointer::GroupMemberPointerInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::group_member_pointer_initialize(ctx, case.option1, case.option2).map(|()| None))
        }
        "group_pointer_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::group_pointer::GroupPointerInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::group_pointer_initialize(ctx, case.option1, case.option2).map(|()| None))
        }
        "metadata_pointer_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::metadata_pointer::MetadataPointerInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::metadata_pointer_initialize(ctx, case.option1, case.option2).map(|()| None))
        }
        "mint_close_authority_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::mint_close_authority::MintCloseAuthorityInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::mint_close_authority_initialize(ctx, case.option1.as_ref()).map(|()| None))
        }
        "non_transferable_mint_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::non_transferable::NonTransferableMintInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::non_transferable_mint_initialize(ctx).map(|()| None))
        }
        "permanent_delegate_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::permanent_delegate::PermanentDelegateInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::permanent_delegate_initialize(ctx, &case.option1.unwrap_or_default()).map(|()| None))
        }
        "transfer_hook_initialize" => {
            let accounts = anchor_spl::token_2022_extensions::transfer_hook::TransferHookInitialize { token_program_id: base[ids[0]].clone(), mint: base[ids[1]].clone() };
            let ctx = context(accounts, base, remaining, seeds);
            execute(ctx, base, |ctx| crate::projected::transfer_hook_initialize(ctx, case.option1, case.option2).map(|()| None))
        }
        _ => panic!("unknown wrapper"),
    }
}
