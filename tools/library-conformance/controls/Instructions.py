"""Family Instructions: semantic corruptions of its records; each must be rejected as a MISMATCH.

They cover every checker kind: value constructors, the operational builders (serializer bytes,
moved accounts, the unwrap panic), the System constructors in both serializer builds, the borsh
callback composition and the log of the scripted callback, the projection of switchboard, the check order and panic of the Pyth getter, and the result, request log, signer seeds of the CPI wrappers, callee writes and
terminal exits.
"""

from common import on_record


def ok_to_err(error):
    def change(r):
        r["outcome"]["result"] = {"err": error}
    return change


def err_to(error):
    def change(r):
        r["outcome"]["result"]["err"] = error
    return change


def err_to_ok(r):
    r["outcome"]["result"] = {"ok": None}


def last_call(r):
    return r["outcome"]["state"]["syscalls"]["log"][-1]


def info_lamports(r): last_call(r)["account_infos"][0]["lamports"] += 1
def meta_signer(r): m = last_call(r)["instruction"]["accounts"][0]; m["is_signer"] = not m["is_signer"]
def drop_call(r): r["outcome"]["state"]["syscalls"]["log"].pop()
def extra_seed(r): last_call(r)["signers_seeds"].append([])
def cpi_data(r): last_call(r)["instruction"]["data"] += "00"


def undo_writes(r):
    """Restore the callee-written account to its state before the call."""
    before = r["state"]["region"]["accounts"]
    after = r["outcome"]["state"]["region"]["accounts"]
    changed = [i for i, (b, a) in enumerate(zip(before, after)) if b != a]
    if not changed:
        raise ValueError("no account was written")
    after[changed[0]] = dict(before[changed[0]])


def terminated_to_ok(r):
    r["outcome"] = {"exit": "returned", "result": {"ok": None},
                    "state": {"region": r["state"]["region"], "syscalls": r["outcome"]["syscalls"]}}


def flip_byte(key):
    def change(r):
        d = r["outcome"]["result"][key]
        r["outcome"]["result"][key] = ("01" if d[:2] == "00" else "00") + d[2:]
    return change


def flip_last_byte(r):
    d = r["outcome"]["result"]["data"]
    r["outcome"]["result"]["data"] = d[:-2] + ("01" if d[-2:] == "00" else "00")


def pop_account(r): r["outcome"]["result"]["accounts"].pop()
def custom_to_kustom(r): r["outcome"]["reason"] = r["outcome"]["reason"].replace("Custom", "Kustom")
def reason_suffix(r): r["outcome"]["reason"] += "!"
def not_writable(r): r["outcome"]["result"]["is_writable"] = False
def drop_seed_byte(r): r["outcome"]["result"] = r["outcome"]["result"][2:]
def reverse_seeds(r): r["outcome"]["result"].reverse()
def ok_plus_one(r): r["outcome"]["result"]["ok"] += 1
def log_extra(r): r["outcome"]["state"]["log"].append("")
def log_drop(r): r["outcome"]["state"]["log"].pop()
def sb_offset(r): r["outcome"]["result"]["ok"]["offset"] = 16
def sb_borrow_free(r): r["outcome"]["state"]["borrow"] = "free"


def term_call(r): return r["outcome"]["syscalls"]["log"][-1]
def term_log_pop(r): r["outcome"]["syscalls"]["log"].pop()
def term_program_id(r): term_call(r)["instruction"]["program_id"] = "11" * 32
def term_data(r): term_call(r)["instruction"]["data"] = "ff"
def term_info_key(r): term_call(r)["account_infos"][0]["key"] = "22" * 32
def term_detail(r): r["outcome"]["detail"] += "!"
def term_reply_left(r): r["outcome"]["syscalls"]["replies"].append({"syscall": "sol_invoke_signed_c", "return": 0, "data": ""})
def sb_after_drop_shared(r): r["outcome"]["state"]["after_drop"] = "shared"
def sb_two_shares(r): r["outcome"]["state"]["borrow"] = "shared 2"


def sb_cell_free(r): r["state"]["borrow"] = "free"


def sb_data(r):
    d = r["outcome"]["state"]["data"]
    r["outcome"]["state"]["data"] = ("01" if d[:2] == "00" else "00") + d[2:]


def header_padding(r): last_call(r)["account_infos"][0]["header"][3] ^= 1
def header_flag(r): last_call(r)["account_infos"][0]["header"][0] = 1


def as_ref_drop_call(r): r["outcome"]["state"]["as_ref"]["calls"].pop()
def as_ref_extra_call(r): r["outcome"]["state"]["as_ref"]["calls"].append(0)


def as_ref_consume_script(r):
    s = r["outcome"]["state"]["as_ref"]
    s["script"].pop(0)
    s["calls"].append(0)


def info_key_from_meta(r):
    call = last_call(r)
    call["account_infos"][0]["key"] = call["instruction"]["accounts"][0]["pubkey"]


def unwound_to_borrow_error(r):
    r["outcome"] = {"exit": "returned", "result": {"err": "AccountBorrowFailed"}, "state": r["outcome"]["state"]}


CONTROLS = [
    # solana-instruction 3.4.0
    ("AccountMeta::new writable flag", "solana_instruction_3_4_0", on_record("new/k10/signer_true", not_writable)),
    ("new_with_bincode data byte", "solana_instruction_3_4_0",
     on_record("bincode/u64/pattern/dup/p80", flip_byte("data"))),
    ("new_with_bincode moved accounts", "solana_instruction_3_4_0",
     on_record("bincode/u64/pattern/dup/p80", pop_account)),
    ("new_with_bincode unwrap panic message", "solana_instruction_3_4_0",
     on_record("bincode/scripted/fail/one", custom_to_kustom)),
    ("new_with_wincode data byte", "solana_instruction_3_4_0_wincode",
     on_record("wincode/u64/pattern/dup", flip_byte("data"))),
    ("new_with_wincode unwrap panic message", "solana_instruction_3_4_0_wincode",
     on_record("wincode/scripted/fail/one", custom_to_kustom)),
    # solana-system-interface 3.2.0
    ("transfer value data", "solana_system_interface_3_2_0", on_record("transfer/distinct/max", flip_last_byte)),
    ("create_account value data", "solana_system_interface_3_2_0",
     on_record("create_account/distinct/pattern/10240/owner_zero", flip_last_byte)),
    ("transfer operational (bincode) data", "solana_system_interface_3_2_0_bincode",
     on_record("transfer/distinct/max", flip_last_byte)),
    ("create_account operational (wincode) accounts", "solana_system_interface_3_2_0_wincode",
     on_record("create_account/alias/pattern/10240/owner_zero", pop_account)),
    # solana-borsh 3.0.2
    ("try_from_slice_unchecked u32 value", "solana_borsh_3_0_2", on_record("u32/exact", ok_plus_one)),
    ("scripted deserializer log", "solana_borsh_3_0_2", on_record("scripted/ok_exact/prior_call", log_extra)),
    ("scripted deserializer unwind state", "solana_borsh_3_0_2", on_record("scripted/panic/fresh", log_drop)),
    # switchboard-on-demand 0.12.1
    ("parse returned range", "switchboard_on_demand_0_12_1", on_record("exact", sb_offset)),
    ("parse borrow after success", "switchboard_on_demand_0_12_1", on_record("exact", sb_borrow_free)),
    ("parse alignment error", "switchboard_on_demand_0_12_1", on_record("exact/offset1", err_to("InvalidData"))),
    ("parse share count", "switchboard_on_demand_0_12_1", on_record("exact", sb_two_shares)),
    ("parse precondition: argument guard not live", "switchboard_on_demand_0_12_1",
     on_record("exact", sb_cell_free), "outside the precondition"),
    ("parse borrow after dropping the Ref", "switchboard_on_demand_0_12_1", on_record("trailing2", sb_after_drop_shared)),
    ("parse data after success", "switchboard_on_demand_0_12_1", on_record("exact", sb_data)),
    ("parse data after an error", "switchboard_on_demand_0_12_1", on_record("disc_wrong_full", sb_data)),
    # pyth-solana-receiver-sdk 2.0.0 getter
    ("getter check order", "pyth_solana_receiver_sdk_2_0_0_getter", on_record("feed_mismatch", err_to("PriceTooOld"))),
    ("getter inclusive boundary", "pyth_solana_receiver_sdk_2_0_0_getter",
     on_record("boundary_equal", ok_to_err("PriceTooOld"))),
    ("getter conversion panic", "pyth_solana_receiver_sdk_2_0_0_getter",
     on_record("age_2pow63_panics", reason_suffix)),
    # solana-instruction-view 2.1.0
    ("Seed::from(&[u8; 33]) bytes", "solana_instruction_view_2_1_0", on_record("seed_from_array/seed33", drop_seed_byte)),
    ("Signer::from(&[Seed; 3]) order", "solana_instruction_view_2_1_0",
     on_record("signer_from_array/three_with_duplicate", lambda r: r["outcome"]["result"].insert(0, "00"))),
    ("invoke_signed address error", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/address_mismatch_second", err_to("AccountBorrowFailed"))),
    ("invoke_signed read-only borrow (no check in v2)", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/readonly_exclusive_borrow_ok", ok_to_err("AccountBorrowFailed"))),
    ("invoke_signed account info", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/ok_asymmetric_flags", info_lamports)),
    ("invoke_signed signer seeds", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/ok_asymmetric_flags", extra_seed)),
    ("invoke_signed recording AsRef call order", "solana_instruction_view_2_1_0",
     on_record("invoke_signed_recording/identity_call_order", as_ref_drop_call)),
    ("invoke_signed initialization uses its own as_ref answer", "solana_instruction_view_2_1_0",
     on_record("invoke_signed_recording/init_returns_other_account", info_key_from_meta)),
    ("invoke_signed read-only meta has no borrow call", "solana_instruction_view_2_1_0",
     on_record("invoke_signed_recording/readonly_has_no_borrow_call", as_ref_extra_call)),
    ("invoke_signed as_ref unwind state", "solana_instruction_view_2_1_0",
     on_record("invoke_signed_recording/panic_on_second_init", as_ref_drop_call)),
    ("invoke_signed as_ref panic to error", "solana_instruction_view_2_1_0",
     on_record("invoke_signed_recording/panic_on_borrow_call", unwound_to_borrow_error)),
    ("invoke_signed count check before as_ref", "solana_instruction_view_2_1_0",
     on_record("invoke_signed_recording/count_check_before_any_call", as_ref_consume_script)),
    ("invoke_signed terminal: request logged", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/callee_fails", term_log_pop)),
    ("invoke_signed terminal: instruction data", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/callee_fails", term_data)),
    ("invoke_signed copied padding byte", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/raw_header_padding", header_padding)),
    ("invoke_signed raw flag byte (not normalized)", "solana_instruction_view_2_1_0",
     on_record("invoke_signed/raw_header_noncanonical_flags", header_flag)),
    ("Transfer copied padding byte", "pinocchio_system_0_6_0", on_record("transfer/raw_header_padding", header_padding)),
    # solana-instruction-view 1.0.0
    ("Signer::from(&[Seed]) order", "solana_instruction_view_1_0_0",
     on_record("signer_from_slice/two", reverse_seeds)),
    ("invoke_signed_with_slice read-only exclusive borrow", "solana_instruction_view_1_0_0",
     on_record("invoke_signed_with_slice/readonly_exclusive_borrow", err_to_ok)),
    ("invoke_signed_with_slice maximum before count", "solana_instruction_view_1_0_0",
     on_record("invoke_signed_with_slice/over_max_129_metas", err_to("NotEnoughAccountKeys"))),
    ("invoke_with_slice empty signers", "solana_instruction_view_1_0_0",
     on_record("invoke_with_slice/ok_asymmetric_flags", extra_seed)),
    ("invoke_signed_with_slice terminal: program id", "solana_instruction_view_1_0_0",
     on_record("invoke_signed_with_slice/callee_fails", term_program_id)),
    ("invoke_with_slice terminal: request logged", "solana_instruction_view_1_0_0",
     on_record("invoke_with_slice/callee_fails", term_log_pop)),
    ("invoke_signed_with_slice callee writes", "solana_instruction_view_1_0_0",
     on_record("invoke_signed_with_slice/data_accounts_callee_writes", undo_writes)),
    # pinocchio-system 0.6.0
    ("Transfer account info lamports", "pinocchio_system_0_6_0", on_record("transfer/ok", info_lamports)),
    ("Transfer meta flag", "pinocchio_system_0_6_0", on_record("transfer/ok", meta_signer)),
    ("Transfer request dropped", "pinocchio_system_0_6_0", on_record("transfer/ok", drop_call)),
    ("Transfer instruction data", "pinocchio_system_0_6_0", on_record("transfer/max_lamports", cpi_data)),
    ("Transfer borrow error", "pinocchio_system_0_6_0", on_record("transfer/from_shared_borrow", err_to_ok)),
    ("Transfer callee writes", "pinocchio_system_0_6_0", on_record("transfer/callee_writes", undo_writes)),
    ("Transfer terminal: request logged", "pinocchio_system_0_6_0", on_record("transfer/callee_fails", term_log_pop)),
    ("Transfer terminal: instruction data", "pinocchio_system_0_6_0", on_record("transfer/callee_fails", term_data)),
    ("Transfer terminal: detail", "pinocchio_system_0_6_0", on_record("transfer/callee_fails", term_detail)),
    ("Allocate terminal: program id", "pinocchio_system_0_6_0", on_record("allocate/callee_fails", term_program_id)),
    ("Allocate terminal: unconsumed replies", "pinocchio_system_0_6_0", on_record("allocate/callee_fails", term_reply_left)),
    ("Allocate signer seeds", "pinocchio_system_0_6_0", on_record("allocate/ok_nested_signers", extra_seed)),
    ("Assign instruction data", "pinocchio_system_0_6_0", on_record("assign/ok_no_signers", cpi_data)),
    # pinocchio-associated-token-account 0.4.0
    ("CreateIdempotent terminal callee", "pinocchio_associated_token_account_0_4_0",
     on_record("create_idempotent/callee_fails", terminated_to_ok)),
    ("CreateIdempotent terminal: request logged", "pinocchio_associated_token_account_0_4_0",
     on_record("create_idempotent/callee_fails", term_log_pop)),
    ("CreateIdempotent terminal: program id", "pinocchio_associated_token_account_0_4_0",
     on_record("create_idempotent/callee_fails", term_program_id)),
    ("CreateIdempotent terminal: account info", "pinocchio_associated_token_account_0_4_0",
     on_record("create_idempotent/callee_fails", term_info_key)),
    ("CreateIdempotent read-only mint borrow", "pinocchio_associated_token_account_0_4_0",
     on_record("create_idempotent/readonly_mint_exclusive_borrow", ok_to_err("AccountBorrowFailed"))),
    ("CreateIdempotent meta flag", "pinocchio_associated_token_account_0_4_0",
     on_record("create_idempotent/wallet_is_funding", meta_signer)),
]
