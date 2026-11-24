"""Alter actual loader observations; each change must be rejected by the model.

The complete backing is checked on close, including old data reclassified as
spare. Guards, record identities, popped accounts and destination Rc ownership
are distinct observables.
"""

from common import flip_spare, hex_bytes, hex_text, on_record, outside_precondition


def after(record):
    return record["outcome"]["state"]


def region(record, index=0):
    return after(record)["input"]["accounts"][index]


def wrong_record(record):
    record["outcome"]["result"]["record"] = 0


def clone_rc(record):
    after(record)["ref_counts"][0][0] += 1


def owner_effect_lost(record):
    region(record)["owner"] = "66" * 32


def pop_lost(record):
    after(record)["remaining"] = record["state"]["remaining"][:]


def bumps_changed(record):
    after(record)["bumps"] += 1


def wrong_code(record):
    record["outcome"]["result"]["err"]["AnchorError"]["code"] += 1


def initialization_wrote(record):
    data = bytearray(hex_bytes(region(record)["data"]))
    data[:8] = bytes(range(1, 9))
    region(record)["data"] = hex_text(data)


def mapped_offset(record):
    record["outcome"]["result"]["ok"]["offset"] = 0


def mapped_guard_freed(record):
    after(record)["leases"][1] = "free"


def panic_guard_kept(record):
    after(record)["leases"][1] = "exclusive"


def partial_write_rolled_back(record):
    region(record)["data"] = record["state"]["input"]["accounts"][0]["data"]


def copy_not_called(record):
    after(record)["syscalls"]["log"] = []


def changed_lamports(record):
    region(record)["lamports"] += 1


def credit_lost(record):
    region(record, 1)["lamports"] -= 1


def owner_not_closed(record):
    region(record)["owner"] = record["state"]["input"]["accounts"][0]["owner"]


def drop_omitted(record):
    after(record)["ref_counts"] = [row[:] for row in record["state"]["ref_counts"]]


def syscall_added(record):
    after(record)["syscalls"]["log"].append({"syscall": "sol_log_", "bytes": "61"})


def stray_borrow(record):
    record["state"]["borrows"].append({"cell": 99, "mode": "shared"})


CORPUS = "anchor_loader_1_0_2"
ROOT = "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader."

# The generic 0 -> 1 mutation targets a singleton record table and is rejected
# by its reader before model comparison. Use the two real alias records here:
# both identifiers are valid, but only the original borrowed record is right.
SEMANTIC = [
    (corpus, on_record("as_ref/duplicate", wrong_record),
     "compare distinct valid AccountInfo records that alias the same cells")
    for corpus in ["anchor_loader_0_32_1", "anchor_loader_1_0_2", "anchor_loader_1_1_2"]
] + [
    (CORPUS, on_record("clone/duplicate", wrong_record),
     "compare distinct valid AccountInfo records instead of a missing record ID")
]

CONTROLS = [
    ("as_ref preserves distinct record identity", CORPUS, on_record("as_ref/duplicate", wrong_record)),
    ("clone does not clone AccountInfo Rc fields", CORPUS, on_record("clone/duplicate", clone_rc)),
    ("unchecked keeps actual Owner assignment", CORPUS,
     on_record("try_from_unchecked/owner_assigns_match", owner_effect_lost)),
    ("unchecked mismatch keeps exact diagnostic", CORPUS,
     on_record("try_from_unchecked/wrong_owner", wrong_code)),
    ("account pop precedes Owner unwind", CORPUS,
     on_record("try_accounts/first_owner_panics", pop_lost)),
    ("loader does not change bumps", CORPUS, on_record("try_accounts/ok", bumps_changed)),
    ("initialization does not write discriminator", CORPUS,
     on_record("load_init/zero_prefix", initialization_wrote)),
    ("initialization maps exact offset", CORPUS, on_record("load_init/zero_prefix", mapped_offset)),
    ("initialization retains returned exclusive guard", CORPUS,
     on_record("load_init/zero_prefix", mapped_guard_freed)),
    ("already-set error has code 3000", CORPUS, on_record("load_init/nonzero_prefix", wrong_code)),
    ("short-prefix unwind releases guard", CORPUS, on_record("load_init/short_prefix", panic_guard_kept)),
    ("short exit preserves partial write", CORPUS, on_record("exit/short_write", partial_write_rolled_back)),
    ("exit performs actual discriminator copy", CORPUS, on_record("exit/write_discriminator", copy_not_called)),
    ("closed exit preserves balances", CORPUS, on_record("exit/closed_account", changed_lamports)),
    ("close credits destination", CORPUS, on_record("close/success", credit_lost)),
    ("self-close ends with zero after credit", CORPUS, on_record("close/alias", changed_lamports)),
    ("close keeps hidden backing bytes", CORPUS, on_record("close/success", lambda r: flip_spare(region(r), 8))),
    ("close assigns before resize error", CORPUS, on_record("close/resize_conflict", owner_not_closed)),
    ("close drops actual destination Rc fields", CORPUS, on_record("close/success", drop_omitted)),
    ("close unwind drops actual destination Rc fields", CORPUS, on_record("close/overflow", drop_omitted)),
    ("unchecked does not invoke a syscall", CORPUS, on_record("try_from_unchecked/ok", syscall_added)),
    ("checked loader rejects invalid reached borrow state", CORPUS,
     outside_precondition("try_accounts/ok", stray_borrow),
     '"requires_violated":["' + ROOT + 'try_accounts_run"]'),
    ("close rejects invalid reached resize state", CORPUS,
     outside_precondition("close/success", stray_borrow),
     '"requires_violated":["' + ROOT + 'close_run"]'),
]


# Retain the recorded calls of the same reviewed model family.
CONTROLS = [(entry[0], selected_corpus, *entry[2:])
    for selected_corpus, selected_ids in (('anchor_loader_0_32_1', ('as_ref/duplicate', 'as_ref/original', 'exit/borrow_error', 'exit/borrow_exclusive', 'exit/closed_account', 'exit/closed_check_shared_then_conflict', 'exit/closed_check_unwinds', 'exit/empty_write', 'exit/owner_makes_closed', 'exit/owner_panics', 'exit/owner_type_mismatch', 'exit/readonly_is_not_checked', 'exit/short_write', 'exit/write_discriminator', 'load_init/discriminator_only', 'load_init/empty_data', 'load_init/exclusive_conflict', 'load_init/nonzero_prefix', 'load_init/owner_not_rechecked', 'load_init/readonly_before_borrow', 'load_init/shared_conflict', 'load_init/short_payload', 'load_init/short_prefix', 'load_init/trailing_capacity', 'load_init/zero_prefix', 'load_init_16/short_payload', 'load_init_16/zero_prefix', 'try_accounts/data_exclusive', 'try_accounts/data_shared', 'try_accounts/duplicate_record', 'try_accounts/empty_accounts', 'try_accounts/empty_data', 'try_accounts/first_owner_panics', 'try_accounts/ok', 'try_accounts/owner_assigns_match', 'try_accounts/readonly_program_ignored', 'try_accounts/second_owner_panics', 'try_accounts/short_payload', 'try_accounts/short_prefix', 'try_accounts/wrong_discriminator', 'try_accounts/wrong_owner', 'try_from_unchecked/data_exclusive', 'try_from_unchecked/data_shared', 'try_from_unchecked/duplicate_record', 'try_from_unchecked/empty_data', 'try_from_unchecked/first_owner_panics', 'try_from_unchecked/ok', 'try_from_unchecked/owner_assigns_match', 'try_from_unchecked/readonly_program_ignored', 'try_from_unchecked/second_owner_panics', 'try_from_unchecked/short_payload', 'try_from_unchecked/short_prefix', 'try_from_unchecked/wrong_discriminator', 'try_from_unchecked/wrong_owner')), ('anchor_loader_1_0_2', ('as_ref/duplicate', 'as_ref/original', 'clone/duplicate', 'clone/original', 'close/alias', 'close/destination_read_conflict', 'close/destination_write_conflict', 'close/overflow', 'close/resize_conflict', 'close/source_read_conflict', 'close/source_write_conflict', 'close/success', 'close/zero_source', 'exit/borrow_error', 'exit/borrow_exclusive', 'exit/closed_account', 'exit/closed_check_shared_then_conflict', 'exit/closed_check_unwinds', 'exit/empty_write', 'exit/owner_makes_closed', 'exit/owner_panics', 'exit/owner_type_mismatch', 'exit/readonly_is_not_checked', 'exit/short_write', 'exit/write_discriminator', 'load_init/discriminator_only', 'load_init/empty_data', 'load_init/exclusive_conflict', 'load_init/nonzero_prefix', 'load_init/owner_not_rechecked', 'load_init/readonly_before_borrow', 'load_init/shared_conflict', 'load_init/short_payload', 'load_init/short_prefix', 'load_init/trailing_capacity', 'load_init/zero_prefix', 'load_init_16/short_payload', 'load_init_16/zero_prefix', 'try_accounts/data_exclusive', 'try_accounts/data_shared', 'try_accounts/duplicate_record', 'try_accounts/empty_accounts', 'try_accounts/empty_data', 'try_accounts/first_owner_panics', 'try_accounts/ok', 'try_accounts/owner_assigns_match', 'try_accounts/readonly_program_ignored', 'try_accounts/second_owner_panics', 'try_accounts/short_payload', 'try_accounts/short_prefix', 'try_accounts/wrong_discriminator', 'try_accounts/wrong_owner', 'try_from_unchecked/data_exclusive', 'try_from_unchecked/data_shared', 'try_from_unchecked/duplicate_record', 'try_from_unchecked/empty_data', 'try_from_unchecked/first_owner_panics', 'try_from_unchecked/ok', 'try_from_unchecked/owner_assigns_match', 'try_from_unchecked/readonly_program_ignored', 'try_from_unchecked/second_owner_panics', 'try_from_unchecked/short_payload', 'try_from_unchecked/short_prefix', 'try_from_unchecked/wrong_discriminator', 'try_from_unchecked/wrong_owner')), ('anchor_loader_1_1_2', ('as_ref/duplicate', 'as_ref/original', 'exit/borrow_error', 'exit/borrow_exclusive', 'exit/closed_account', 'exit/closed_check_shared_then_conflict', 'exit/closed_check_unwinds', 'exit/empty_write', 'exit/owner_makes_closed', 'exit/owner_panics', 'exit/owner_type_mismatch', 'exit/readonly_is_not_checked', 'exit/short_write', 'exit/write_discriminator', 'load_init/discriminator_only', 'load_init/empty_data', 'load_init/exclusive_conflict', 'load_init/nonzero_prefix', 'load_init/owner_not_rechecked', 'load_init/readonly_before_borrow', 'load_init/shared_conflict', 'load_init/short_payload', 'load_init/short_prefix', 'load_init/trailing_capacity', 'load_init/zero_prefix', 'load_init_16/short_payload', 'load_init_16/zero_prefix', 'try_accounts/data_exclusive', 'try_accounts/data_shared', 'try_accounts/duplicate_record', 'try_accounts/empty_accounts', 'try_accounts/empty_data', 'try_accounts/first_owner_panics', 'try_accounts/ok', 'try_accounts/owner_assigns_match', 'try_accounts/readonly_program_ignored', 'try_accounts/second_owner_panics', 'try_accounts/short_payload', 'try_accounts/short_prefix', 'try_accounts/wrong_discriminator', 'try_accounts/wrong_owner', 'try_from_unchecked/data_exclusive', 'try_from_unchecked/data_shared', 'try_from_unchecked/duplicate_record', 'try_from_unchecked/empty_data', 'try_from_unchecked/first_owner_panics', 'try_from_unchecked/ok', 'try_from_unchecked/owner_assigns_match', 'try_from_unchecked/readonly_program_ignored', 'try_from_unchecked/second_owner_panics', 'try_from_unchecked/short_payload', 'try_from_unchecked/short_prefix', 'try_from_unchecked/wrong_discriminator', 'try_from_unchecked/wrong_owner')))
    for entry in CONTROLS if entry[2].record_id in selected_ids]
SEMANTIC = [entry for entry in SEMANTIC if entry[0] in ('anchor_loader_0_32_1', 'anchor_loader_1_0_2', 'anchor_loader_1_1_2')]
