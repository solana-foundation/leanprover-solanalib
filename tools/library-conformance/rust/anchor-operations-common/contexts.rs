//! Reference identity, moved fields and actual remaining Vec destruction.
use crate::{errors::record, track};
use anchor_lang::context::{Context, CpiContext};
use anchor_lang::prelude::{AccountInfo, Pubkey};
use anchor_lang::solana_program::instruction::AccountMeta;
use anchor_lang::{Accounts, ToAccountInfos, ToAccountMetas};
use conformance_recorder::{self as rec, Corpus, Json};
use conformance_shim as shim;
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

#[derive(Debug)]
struct AccountsValue(u64);
impl ToAccountMetas for AccountsValue {
    fn to_account_metas(&self, _: Option<bool>) -> Vec<AccountMeta> {
        panic!("unexpected ToAccountMetas");
    }
}
impl<'info> ToAccountInfos<'info> for AccountsValue {
    fn to_account_infos(&self) -> Vec<AccountInfo<'info>> {
        panic!("unexpected ToAccountInfos");
    }
}
#[cfg(not(feature = "v027"))]
impl anchor_lang::Bumps for AccountsValue {
    type Bumps = BTreeMap<String, u8>;
}
#[cfg(feature = "v027")]
impl<'info> Accounts<'info> for AccountsValue {
    fn try_accounts(
        _: &Pubkey,
        _: &mut &[AccountInfo<'info>],
        _: &[u8],
        _: &mut BTreeMap<String, u8>,
        _: &mut BTreeSet<Pubkey>,
    ) -> anchor_lang::Result<Self> {
        panic!("unexpected Accounts");
    }
}
#[cfg(not(feature = "v027"))]
impl<'info> Accounts<'info, BTreeMap<String, u8>> for AccountsValue {
    fn try_accounts(
        _: &Pubkey,
        _: &mut &'info [AccountInfo<'info>],
        _: &[u8],
        _: &mut BTreeMap<String, u8>,
        _: &mut BTreeSet<Pubkey>,
    ) -> anchor_lang::Result<Self> {
        panic!("unexpected Accounts");
    }
}
fn account() -> AccountInfo<'static> {
    let key = Box::leak(Box::new(Pubkey::new_from_array([3; 32])));
    let owner = Box::leak(Box::new(Pubkey::new_from_array([4; 32])));
    let lamports = Box::leak(Box::new(23));
    let data = Box::leak(vec![1, 2, 3].into_boxed_slice());
    #[cfg(feature = "legacy")]
    {
        AccountInfo::new(key, true, true, lamports, data, owner, false, 0)
    }
    #[cfg(not(feature = "legacy"))]
    {
        AccountInfo::new(key, true, true, lamports, data, owner, false)
    }
}
fn context_case(c: &mut Corpus) {
    let program: &'static Pubkey = Box::leak(Box::new(Pubkey::new_from_array([9; 32])));
    let accounts: &'static mut AccountsValue = Box::leak(Box::new(AccountsValue(23)));
    let remaining: &'static [AccountInfo<'static>] = Box::leak(vec![account()].into_boxed_slice());
    let program_ptr = program as *const _;
    let accounts_ptr = accounts as *const _;
    let remaining_ptr = remaining.as_ptr();
    let mut bumps = BTreeMap::new();
    bumps.insert("first".to_string(), 3);
    bumps.insert("second".to_string(), 255);
    let output = shim::case(&shim::Script::new(vec![]), || {
        let (r, log) = track::tracked(|| Context::new(program, accounts, remaining, bumps));
        let value = r.expect("Context new");
        let result = Json::obj([
            (
                "program_identity",
                std::ptr::eq(value.program_id, program_ptr).into(),
            ),
            (
                "accounts_identity",
                std::ptr::eq(value.accounts, accounts_ptr).into(),
            ),
            (
                "remaining_identity",
                (value.remaining_accounts.as_ptr() == remaining_ptr).into(),
            ),
            ("remaining_length", value.remaining_accounts.len().into()),
            ("accounts_value", value.accounts.0.into()),
            (
                "bumps",
                Json::arr(value.bumps.iter(), |(s, b)| {
                    Json::arr([s.as_str().into(), (*b).into()], |j| j)
                }),
            ),
        ]);
        std::mem::forget(value);
        rec::returned(
            result,
            Json::obj([
                ("fresh_live", log.fresh_live.len().into()),
                ("syscalls", shim::state()),
            ]),
        )
    });
    record(
        c,
        "context/new".to_string(),
        crate::identities::CONTEXT_NEW,
        Json::Null,
        Json::Null,
        output,
    );
}
fn cpi_cases(c: &mut Corpus) {
    for operation in 0..4 {
        let input_account = account();
        let kept = input_account.clone();
        let bytes = [1, 2, 3];
        let one: &[&[u8]] = &[&bytes];
        let seeds: &[&[&[u8]]] = &[one];
        let newbytes = [7, 8];
        let newone: &[&[u8]] = &[&newbytes];
        let newseeds: &[&[&[u8]]] = &[newone];
        #[cfg(feature = "legacy")]
        let mut program = Some(input_account);
        #[cfg(not(feature = "legacy"))]
        let mut program = Some(*input_account.key);
        let mut current = if operation >= 2 {
            Some(CpiContext::new_with_signer(
                program.take().unwrap(),
                AccountsValue(29),
                seeds,
            ))
        } else {
            None
        };
        if operation == 3 {
            current = Some(
                current
                    .take()
                    .unwrap()
                    .with_remaining_accounts(vec![kept.clone(), kept.clone()]),
            );
        }
        let next = if operation == 3 {
            vec![kept.clone()]
        } else {
            vec![]
        };
        let counts = (
            Rc::strong_count(&kept.data),
            Rc::strong_count(&kept.lamports),
        );
        let old_ptr = current
            .as_ref()
            .map(|v| v.remaining_accounts.as_ptr() as usize);
        let next_ptr = next.as_ptr();
        let output = shim::case(&shim::Script::new(vec![]), || {
            let (r, log) = track::tracked(|| match operation {
                0 => CpiContext::new(program.take().unwrap(), AccountsValue(29)),
                1 => CpiContext::new_with_signer(program.take().unwrap(), AccountsValue(29), seeds),
                2 => current.take().unwrap().with_signer(newseeds),
                3 => current.take().unwrap().with_remaining_accounts(next),
                _ => unreachable!(),
            });
            let value = r.expect("CpiContext operation");
            let expected = if operation == 0 {
                &[]
            } else if operation == 2 {
                newseeds
            } else {
                seeds
            };
            #[cfg(feature = "legacy")]
            let program_same = std::ptr::eq(value.program.key, kept.key)
                && Rc::ptr_eq(&value.program.data, &kept.data)
                && Rc::ptr_eq(&value.program.lamports, &kept.lamports);
            #[cfg(not(feature = "legacy"))]
            let program_same = value.program_id == *kept.key;
            let result = Json::obj([
                ("accounts_value", value.accounts.0.into()),
                ("program_identity", program_same.into()),
                (
                    "seed_identity",
                    (expected.is_empty() && value.signer_seeds.is_empty()
                        || expected.as_ptr() == value.signer_seeds.as_ptr())
                    .into(),
                ),
                ("seed_count", value.signer_seeds.len().into()),
                ("remaining_length", value.remaining_accounts.len().into()),
                (
                    "remaining_capacity",
                    value.remaining_accounts.capacity().into(),
                ),
                (
                    "remaining_identity",
                    (operation != 3 || value.remaining_accounts.as_ptr() == next_ptr).into(),
                ),
            ]);
            let state = Json::obj([
                ("data_count", Rc::strong_count(&kept.data).into()),
                ("lamports_count", Rc::strong_count(&kept.lamports).into()),
                ("fresh_live", log.fresh_live.len().into()),
                (
                    "old_remaining_freed",
                    (operation == 3 && old_ptr.is_some_and(|p| log.frees.contains(&p))).into(),
                ),
                ("syscalls", shim::state()),
            ]);
            std::mem::forget(value);
            rec::returned(result, state)
        });
        let function = match operation {
            0 => crate::identities::CPI_NEW,
            1 => crate::identities::CPI_SIGNED,
            2 => crate::identities::CPI_WITH_SIGNER,
            _ => crate::identities::CPI_WITH_REMAINING,
        };
        record(
            c,
            format!("cpi_context/{operation}"),
            function,
            Json::obj([
                ("data_count", counts.0.into()),
                ("lamports_count", counts.1.into()),
            ]),
            Json::obj([("operation", operation.into())]),
            output,
        );
    }
}
pub fn record_all(c: &mut Corpus) {
    context_case(c);
    cpi_cases(c);
}

#[cfg(all(test, feature = "v032"))]
mod tests {
    use super::*;

    #[test]
    fn signer_replacement_keeps_nonempty_remaining_and_rc_owners() {
        let program = account();
        let kept = program.clone();
        let first_bytes = [1, 2, 3];
        let first_group: &[&[u8]] = &[&first_bytes];
        let first_seeds: &[&[&[u8]]] = &[first_group];
        let next_bytes = [7, 8];
        let next_group: &[&[u8]] = &[&next_bytes, &next_bytes];
        let next_seeds: &[&[&[u8]]] = &[next_group, next_group];
        let context = CpiContext::new_with_signer(program, AccountsValue(29), first_seeds)
            .with_remaining_accounts(vec![kept.clone(), kept.clone()]);
        let remaining = context.remaining_accounts.as_ptr();
        let capacity = context.remaining_accounts.capacity();
        let counts = (
            Rc::strong_count(&kept.data),
            Rc::strong_count(&kept.lamports),
        );

        let changed = context.with_signer(next_seeds);

        assert_eq!(changed.accounts.0, 29);
        assert_eq!(changed.remaining_accounts.as_ptr(), remaining);
        assert_eq!(changed.remaining_accounts.len(), 2);
        assert_eq!(changed.remaining_accounts.capacity(), capacity);
        assert_eq!(changed.signer_seeds.as_ptr(), next_seeds.as_ptr());
        assert_eq!(changed.signer_seeds.len(), 2);
        assert_eq!(changed.signer_seeds[0].as_ptr(), next_group.as_ptr());
        assert_eq!(changed.signer_seeds[1].as_ptr(), next_group.as_ptr());
        assert!(std::ptr::eq(changed.program.key, kept.key));
        assert!(std::ptr::eq(changed.program.owner, kept.owner));
        assert!(Rc::ptr_eq(&changed.program.data, &kept.data));
        assert!(Rc::ptr_eq(&changed.program.lamports, &kept.lamports));
        assert!(changed
            .remaining_accounts
            .iter()
            .all(|info| Rc::ptr_eq(&info.data, &kept.data)
                && Rc::ptr_eq(&info.lamports, &kept.lamports)));
        assert_eq!(
            (
                Rc::strong_count(&kept.data),
                Rc::strong_count(&kept.lamports)
            ),
            counts
        );

        drop(changed);
        assert_eq!(Rc::strong_count(&kept.data), 1);
        assert_eq!(Rc::strong_count(&kept.lamports), 1);
    }
}
