"""Select exact checker keys after authenticating the complete native corpus.

The recorded files and their driver manifests are never rewritten.  Omission
rows must equal the reviewed finite identities below. Every other record needs a
checker. The Lean runner then checks exact identity and multiplicity again.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

SCHEMA = "solana-library-conformance/checker-selection/v1"

# Exact reviewed identities; source selection and native model coverage are separate.
# Keep strict equality. Remove an ID when its checker is added; never infer this table at runtime.
KNOWN_OMISSIONS = {
    'anchor_views_0_32_1': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("<anchor_lang::accounts::account::Account<'_, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/deref/true-0',
            )),
            ("<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/key/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/clone/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/deref/normal',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref_mut/true-0', 'interface_account/deref_mut/false-0',
            )),
            ("<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/key/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key", (), (
                'signer/key/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'_> as anchor_lang::Key>::key", (), (
                'system_account/key/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::clone::Clone>::clone", (), (
                'system_account/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (), (
                'system_account/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::ops::deref::Deref>::deref", (), (
                'system_account/deref/normal',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/key/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/clone/0', 'sysvar/clone/1', 'sysvar/clone/2',
                'sysvar/clone/3', 'sysvar/clone/4',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref_mut/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/as_ref_info/0',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/set_inner/true-0', 'account/set_inner/true-1', 'account/set_inner/true-2',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/set_inner/true-0', 'interface_account/set_inner/true-1', 'interface_account/set_inner/true-2',
            )),
        )
        for rid in ids
    ),
    'anchor_views_1_1_2': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("<anchor_lang::accounts::account::Account<'_, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/deref/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/clone/true-0', 'account/clone/true-1', 'account/clone/true-2',
            )),
            ("<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/key/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/clone/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/deref/normal',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/clone/true-0', 'interface_account/clone/true-1', 'interface_account/clone/true-2',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/clone/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'info> as core::clone::Clone>::clone", (), (
                'signer/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'_> as anchor_lang::Key>::key", (), (
                'system_account/key/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::clone::Clone>::clone", (), (
                'system_account/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (), (
                'system_account/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/key/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/clone/0', 'sysvar/clone/1', 'sysvar/clone/2',
                'sysvar/clone/3',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref_mut/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/as_ref_info/0',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as core::clone::Clone>::clone", (), (
                'unchecked_account/clone/normal',
            )),
            ('anchor_lang::Lamports::get_lamports', (('Self', 'conformance_anchor_views::cases::Holder'),), (
                'lib/get_lamports/normal', 'lib/get_lamports/mutates', 'lib/get_lamports/panics',
                'lib/get_lamports/conflict',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/set_inner/true-0', 'account/set_inner/true-1', 'account/set_inner/true-2',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/set_inner/true-0', 'interface_account/set_inner/true-1', 'interface_account/set_inner/true-2',
            )),
        )
        for rid in ids
    ),
    'cpi_program_2_3_0': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ('solana_program::program::invoke', (), (
                'unsigned_aliases',
            )),
        )
        for rid in ids
    ),
    'instruction_extensions_wincode': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ('<solana_instruction::Instruction as core::clone::Clone>::clone', (), (
                'clone/empty', 'clone/data-only', 'clone/metas-only',
                'clone/duplicates', 'clone/oom/1', 'clone/oom/2',
            )),
        )
        for rid in ids
    ),
    'pinocchio_0_9_2_accounts': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("<pinocchio::account_info::Ref<'_, T> as core::ops::drop::Drop>::drop", (('T', '[u8]'),), (
                'guard/drop_shared',
            )),
            ("<pinocchio::account_info::RefMut<'_, T> as core::ops::drop::Drop>::drop", (('T', '[u8]'),), (
                'guard/drop_exclusive',
            )),
        )
        for rid in ids
    ),
    'raw_runtime_solana_define_syscall_5_1_0': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ('solana_define_syscall::definitions::sol_get_clock_sysvar', (), (
                'clock',
            )),
            ('solana_define_syscall::definitions::sol_get_epoch_schedule_sysvar', (), (
                'epoch',
            )),
            ('solana_define_syscall::definitions::sol_get_rent_sysvar', (), (
                'rent',
            )),
            ('solana_define_syscall::definitions::sol_get_return_data', (), (
                'get-return/0', 'get-return/1', 'get-return/2',
                'get-return/5', 'get-return/empty', 'get-return/overlap',
                'input-region/get-return/0', 'input-region/get-return/5',
            )),
            ('solana_define_syscall::definitions::sol_memcpy_', (), (
                'copy/nonempty', 'copy/overlap', 'copy/zero-null',
                'input-region/copy/nonempty', 'input-region/copy/zero-null',
            )),
            ('solana_define_syscall::definitions::sol_memset_', (), (
                'input-region/set/high-byte', 'input-region/set/zero-null', 'set/high-byte',
                'set/zero-byte', 'set/zero-null',
            )),
            ('solana_define_syscall::definitions::sol_sha256', (), (
                'sha256/empty', 'sha256/segmented',
            )),
            ('solana_define_syscall::definitions::sol_try_find_program_address', (), (
                'find/count-16', 'find/count-17', 'find/empty-seeds',
                'find/on-curve-null', 'find/overlap-failure', 'find/overlap-success',
                'find/seed-32', 'find/seed-33', 'find/success',
                'input-region/find/count-16', 'input-region/find/success',
            )),
        )
        for rid in ids
    ),
    'sdk_accounts_3_1_1': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("solana_account_info::AccountInfo::<'a>::try_borrow_lamports", (), (
                'try_borrow_lamports/aliases-0', 'try_borrow_lamports/aliases-1', 'try_borrow_lamports/aliases-2',
                'try_borrow_lamports/aliases-3', 'try_borrow_lamports/aliases-4', 'try_borrow_lamports/aliases-5',
                'try_borrow_lamports/aliases-6', 'try_borrow_lamports/empty',
            )),
        )
        for rid in ids
    ),
    'spl_token_2022_8_0_1_instructions': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ('spl_token_2022::native_mint::id', (), (
                'native_id',
            )),
        )
        for rid in ids
    ),
    'spl_token_8_0_0_instructions': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ('spl_token::native_mint::id', (), (
                'native_id',
            )),
        )
        for rid in ids
    ),
    'anchor_views_1_0_2': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("<anchor_lang::accounts::account::Account<'_, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/deref/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'_, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/deref_mut/false-0', 'account/deref_mut/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/clone/true-0', 'account/clone/true-1', 'account/clone/true-2',
            )),
            ("<anchor_lang::accounts::interface::Interface<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/key/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/clone/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/deref/normal',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref_mut/false-0', 'interface_account/deref_mut/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/clone/true-0', 'interface_account/clone/true-1', 'interface_account/clone/true-2',
            )),
            ("<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/key/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/clone/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key", (), (
                'signer/key/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'info> as core::clone::Clone>::clone", (), (
                'signer/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::clone::Clone>::clone", (), (
                'system_account/clone/normal',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/key/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/clone/0', 'sysvar/clone/1', 'sysvar/clone/2',
                'sysvar/clone/3',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'_, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref_mut/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/as_ref_info/0',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as core::clone::Clone>::clone", (), (
                'unchecked_account/clone/normal',
            )),
            ('anchor_lang::Lamports::get_lamports', (('Self', 'conformance_anchor_views::cases::Holder'),), (
                'lib/get_lamports/conflict', 'lib/get_lamports/mutates', 'lib/get_lamports/normal',
                'lib/get_lamports/panics',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/set_inner/true-0', 'account/set_inner/true-1', 'account/set_inner/true-2',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/set_inner/true-0', 'interface_account/set_inner/true-1', 'interface_account/set_inner/true-2',
            )),
        )
        for rid in ids
    ),
    'instruction_extensions_bincode': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ('<solana_instruction::Instruction as core::clone::Clone>::clone', (), (
                'clone/data-only', 'clone/duplicates', 'clone/empty',
                'clone/metas-only', 'clone/oom/1', 'clone/oom/2',
            )),
            ('solana_system_interface::instruction::create_account_allow_prefund', (), (
                'prefund/alias-zero/max', 'prefund/alias-zero/zero', 'prefund/distinct-one/max',
                'prefund/distinct-one/zero', 'prefund/max/max', 'prefund/max/zero',
                'prefund/none/max', 'prefund/none/zero', 'prefund/pattern/max',
                'prefund/pattern/zero', 'system/oom/1', 'system/oom/2',
                'system/oom/3',
            )),
        )
        for rid in ids
    ),
    'anchor_views_0_29_0': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("<anchor_lang::accounts::account::Account<'a, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/deref/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'info, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/key/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/clone/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/deref/normal',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'a, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/clone/true-0', 'interface_account/clone/true-1', 'interface_account/clone/true-2',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/key/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/clone/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Key>::key", (), (
                'signer/key/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'info> as core::clone::Clone>::clone", (), (
                'signer/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as anchor_lang::Key>::key", (), (
                'system_account/key/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::clone::Clone>::clone", (), (
                'system_account/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (), (
                'system_account/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::ops::deref::Deref>::deref", (), (
                'system_account/deref/normal',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'a, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'a, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref_mut/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/key/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/clone/0', 'sysvar/clone/1', 'sysvar/clone/2',
                'sysvar/clone/3', 'sysvar/clone/4',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/as_ref_info/0',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as anchor_lang::Key>::key", (), (
                'unchecked_account/key/normal',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as core::clone::Clone>::clone", (), (
                'unchecked_account/clone/normal',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (), (
                'unchecked_account/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as core::ops::deref::Deref>::deref", (), (
                'unchecked_account/deref/normal',
            )),
            ('anchor_lang::Lamports::get_lamports', (('Self', 'conformance_anchor_views::cases::Holder'),), (
                'lib/get_lamports/conflict', 'lib/get_lamports/mutates', 'lib/get_lamports/normal',
                'lib/get_lamports/panics',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/set_inner/true-0', 'account/set_inner/true-1', 'account/set_inner/true-2',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/set_inner/true-0', 'interface_account/set_inner/true-1', 'interface_account/set_inner/true-2',
            )),
        )
        for rid in ids
    ),
    'anchor_views_0_27_0': frozenset(
        (rid, function, generics)
        for function, generics, ids in (
            ("<anchor_lang::accounts::account::Account<'a, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/deref/true-0',
            )),
            ("<anchor_lang::accounts::account::Account<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/clone/true-0', 'account/clone/true-1', 'account/clone/true-2',
            )),
            ("<anchor_lang::accounts::account::Account<'info, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/key/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/clone/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::interface::Interface<'info, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'interface/deref/normal',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'a, T> as core::ops::deref::Deref>::deref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'a, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/deref_mut/false-0', 'interface_account/deref_mut/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/key/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/clone/true-0', 'interface_account/clone/true-1', 'interface_account/clone/true-2',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::convert::AsRef<T>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/as_ref_payload/true-0',
            )),
            ("<anchor_lang::accounts::interface_account::InterfaceAccount<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/as_ref_info/true-0',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/key/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/clone/normal',
            )),
            ("<anchor_lang::accounts::program::Program<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::Tag'),), (
                'program/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'info> as anchor_lang::Key>::key", (), (
                'signer/key/normal',
            )),
            ("<anchor_lang::accounts::signer::Signer<'info> as core::clone::Clone>::clone", (), (
                'signer/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::clone::Clone>::clone", (), (
                'system_account/clone/normal',
            )),
            ("<anchor_lang::accounts::system_account::SystemAccount<'info> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (), (
                'system_account/as_ref_info/normal',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'a, T> as core::ops::deref::DerefMut>::deref_mut", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/deref_mut/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as anchor_lang::Key>::key", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/key/0',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::clone::Clone>::clone", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/clone/0', 'sysvar/clone/1', 'sysvar/clone/2',
                'sysvar/clone/3', 'sysvar/clone/4',
            )),
            ("<anchor_lang::accounts::sysvar::Sysvar<'info, T> as core::convert::AsRef<solana_program::account_info::AccountInfo<'info>>>::as_ref", (('T', 'conformance_anchor_views::cases::ProbeSysvar'),), (
                'sysvar/as_ref_info/0',
            )),
            ("<anchor_lang::accounts::unchecked_account::UncheckedAccount<'info> as core::clone::Clone>::clone", (), (
                'unchecked_account/clone/normal',
            )),
            ("anchor_lang::accounts::account::Account::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::into_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/into_inner/true-0',
            )),
            ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::set_inner", (('T', 'conformance_anchor_views::cases::Payload'),), (
                'interface_account/set_inner/true-0', 'interface_account/set_inner/true-1', 'interface_account/set_inner/true-2',
            )),
        )
        for rid in ids
    ),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def key(function: str, generics: dict) -> tuple:
    require(isinstance(function, str) and bool(function), "empty or malformed checker function")
    require(isinstance(generics, dict) and all(isinstance(k, str) and isinstance(v, str)
                                             for k, v in generics.items()),
            "malformed checker generic arguments")
    return function, tuple(sorted(generics.items()))


def prepare(corpus: Path, authentication: dict, descriptors: list[dict], only: set[str],
            *, complete: bool = False) -> dict:
    """Join compiled checker keys to complete, already authenticated files.

The manifest hash is checked again here, closing the gap between authentication
and selection. Generic argument order has no semantic significance. A complete
registry replay may also account for whole authenticated corpora without any
registered keys only when their exact identities have explicit reviewed exceptions.
Those files never enter the Lean checker or its count report.
"""
    require(bool(only), "checker selection must name at least one corpus")
    expected = {}
    for manifest in authentication["manifests"].values():
        for name, entry in manifest["corpora"].items():
            require(name not in expected, f"duplicate authenticated corpus {name}")
            expected[name] = entry
    omitted_corpora = set()
    if complete:
        require(set(expected) == set(authentication["summaries"]),
                "complete checker selection requires every authenticated corpus summary")
        authenticated_names = {Path(name).stem for name in expected}
        require(set(KNOWN_OMISSIONS) <= authenticated_names,
                "reviewed omission corpora missing from complete authentication: "
                f"{sorted(set(KNOWN_OMISSIONS) - authenticated_names)}")
        omitted_corpora = authenticated_names - only
    requested = {name: {} for name in only | omitted_corpora}
    for descriptor in descriptors:
        name = descriptor["corpus"]
        require(not complete or name in only,
                f"{name}: registered checker excluded from complete selection")
        if name not in only:
            continue
        ident = key(descriptor["function"], descriptor["generics"])
        require(ident not in requested[name], f"duplicate checker selection in {name}: {ident}")
        requested[name][ident] = descriptor
    summaries, corpora, omissions = {}, {}, []
    for name in sorted(requested):
        require(bool(requested[name]) or name in omitted_corpora,
                f"{name}: no registered checker keys selected")
        file = name + ".json"
        require(file in expected and file in authentication["summaries"],
                f"{name}: missing complete corpus authentication")
        raw = (corpus / file).read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        require(digest == expected[file]["sha256"],
                f"{name}: corpus changed after complete authentication")
        data = json.loads(raw)
        require(data["corpus"] == name, f"{name}: corpus name changed")
        require(len(data["records"]) == expected[file]["records"],
                f"{name}: authenticated record count differs")
        require(name not in omitted_corpora or name in KNOWN_OMISSIONS,
                f"{name}: wholly omitted corpus has no reviewed exception")
        counts = {ident: 0 for ident in requested[name]}
        selected, omitted, seen = [], [], set()
        unmatched = set()
        for record in data["records"]:
            rid = record["id"]
            require(isinstance(rid, str) and bool(rid) and rid not in seen,
                    f"{name}: duplicate or malformed record id {rid!r}")
            seen.add(rid)
            ident = key(record["function"], record["generics"])
            if ident in counts:
                counts[ident] += 1
                selected.append(rid)
            else:
                unmatched.add((rid, *ident))
                omitted.append(rid)
                omissions.append({"corpus": name, "id": rid, "function": record["function"],
                                  "generics": record["generics"]})
        for ident, count in counts.items():
            require(count > 0, f"{name}: no records for selected checker {ident}")
        allowed = KNOWN_OMISSIONS.get(name, frozenset())
        require(unmatched == allowed,
                f"{name}: unreviewed or stale record omissions: "
                f"unexpected={sorted(unmatched - allowed)}; missing={sorted(allowed - unmatched)}")
        if name not in omitted_corpora:
            summaries[file] = {**authentication["summaries"][file], "records": len(selected)}
        corpora[name] = {"source_sha256": digest, "authenticated_records": len(seen),
                         "selected_records": len(selected), "omitted_records": len(omitted),
                         "selected_ids": selected, "omitted_ids": omitted,
                         "checkers": [dict(requested[name][ident], records=count)
                                      for ident, count in counts.items()]}
    selection = {"schema": SCHEMA, "corpora": corpora, "omissions": omissions,
                 "selected_summaries": summaries, "complete": complete,
                 "omitted_corpora": sorted(omitted_corpora)}
    if complete:
        check_corpus_files(corpus, selection)
    return selection


def check_corpus_files(corpus: Path, selection: dict) -> None:
    """Keep global file-set validation when Lean checks only registered corpora.

Whole-corpus omissions retain their authenticated bytes, including every
identity, outcome and count. Selected files may be mutated by negative controls;
their record identities and multiplicities are checked by the Lean runner.
"""
    expected = set(selection["corpora"])
    present = {path.stem for path in corpus.glob("*.json")}
    require(present == expected,
            f"corpus files without registered checkers or authenticated omissions: {sorted(present - expected)}; "
            f"authenticated corpora without a file: {sorted(expected - present)}")
    for name in selection["omitted_corpora"]:
        digest = hashlib.sha256((corpus / (name + ".json")).read_bytes()).hexdigest()
        require(digest == selection["corpora"][name]["source_sha256"],
                f"{name}: wholly omitted corpus changed after complete authentication")


def check_omissions(output: str, selection: dict) -> None:
    """Account for in-corpus omissions in Lean; whole files are checked above."""
    actual = {}
    for line in output.splitlines():
        if not line.startswith("OMITTED\t"):
            continue
        fields = line.split("\t")
        require(len(fields) == 3 and fields[1] not in actual and fields[2].isdigit(),
                "malformed or duplicate omitted-record report")
        actual[fields[1]] = int(fields[2])
    expected = {name: row["omitted_records"] for name, row in selection["corpora"].items()
                if row["omitted_records"] and row["selected_records"]}
    require(actual == expected, f"omitted-record counts differ: {actual}, expected {expected}")
