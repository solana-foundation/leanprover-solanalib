"""Family TokenViews: semantic corruptions of `pinocchio_token_0_6_0` and `pinocchio_token_2022_0_3_1` records.

Each must be rejected as a MISMATCH of its record: admission results and their order, borrow-state
effects (acquisition, release after a token-2022 layout error, saturation), returned views and field
references, getter values and the state panic, Batch buffers, committed lengths, retained partial writes
and callback logs, the CPI requests the shim logs, and the unmodelled frame.
"""

from common import flip_spare, hex_bytes, hex_text, on_record, outside_precondition

L = "pinocchio_token_0_6_0"
T = "pinocchio_token_2022_0_3_1"


def after(r):
    return r["outcome"]["state"]


def account_after(r, i=0):
    return after(r)["region"]["accounts"][i]


def call(r, i=0):
    return after(r)["syscalls"]["log"][i]


def set_err(name):
    def change(r):
        r["outcome"]["result"] = {"err": name}
    return change


def marker_minus_one(r): account_after(r)["marker"] -= 1
def marker_of_1_free(r): account_after(r, 1)["marker"] = 255
def view_offset(r): r["outcome"]["result"]["ok"]["offset"] = 1
def view_len(r): r["outcome"]["result"]["ok"]["len"] = 82
def saturated_ok(r): r["outcome"]["result"] = {"ok": {"account": 0, "offset": 0, "len": 165}}
def amount_minus_one(r): r["outcome"]["result"] -= 1
def key_value(r): r["outcome"]["result"]["value"] = "ff" * 32
def key_offset(r): r["outcome"]["result"]["offset"] = 0
def state_frozen(r): r["outcome"]["result"] = "Frozen"
def panic_message(r): r["outcome"]["reason"] += "!"


def panic_as_return(r):
    r["outcome"] = {"exit": "returned", "result": "Initialized", "state": r["outcome"]["state"]}


def decimals_plus_one(r): r["outcome"]["result"] = (r["outcome"]["result"] + 1) % 256
def new_lengths(r): r["outcome"]["result"]["ok"]["data"] = 2
def no_discriminator(r): after(r)["buffers"]["data"] = r["state"]["buffers"]["data"]
def empty_data_ok(r): r["outcome"]["result"] = {"ok": {"data": 1, "accounts": 0, "instruction_accounts": 0}}
def transfer_amount(r): r["outcome"]["result"]["amount"] ^= 1
def lengths_accounts(r): after(r)["lengths"]["accounts"] += 1
def entry_account(r): after(r)["buffers"]["accounts"][4][0] = 0
def meta_signer(r): after(r)["buffers"]["instruction_accounts"][3][1] ^= 1
def drop_data_writes(r): after(r)["buffers"]["data"] = r["state"]["buffers"]["data"]
def drop_account_writes(r): after(r)["buffers"]["accounts"] = r["state"]["buffers"]["accounts"]


def commit_on_error(r):
    lengths = after(r)["lengths"]
    lengths["accounts"] += 6
    lengths["instruction_accounts"] += 6


def asref_log(r): after(r)["asref_log"].pop()
def unwind_reason(r): r["outcome"]["reason"] = "other"
def ok_to_err(r): r["outcome"]["result"] = {"err": "InvalidArgument"}
def info_lamports(r): call(r)["account_infos"][0]["lamports"] += 1
def instruction_data(r): call(r)["instruction"]["data"] = "fe"
def seeds_dropped(r): call(r)["signers_seeds"].pop()
def lengths_before(r): r["state"]["lengths"]["data"] += 1
def uncommitted_entry(r): call(r)["account_infos"].append(dict(call(r)["account_infos"][-1]))
def meta_writable(r): call(r)["instruction"]["accounts"][1]["is_writable"] = True
def err_to_ok(r): r["outcome"]["result"] = {"ok": None}
def program_id(r): call(r)["instruction"]["program_id"] = "00" * 32
def info_signer(r): call(r)["account_infos"][3]["is_signer"] = False
def replies_left(r): after(r)["syscalls"]["replies"] = r["state"]["syscalls"]["replies"]
def close_tag(r): call(r)["instruction"]["data"] = "0a"
def alias_key(r): call(r)["account_infos"][0]["key"] = call(r)["account_infos"][1]["key"]
def header_flag_normalized(r): call(r)["account_infos"][0]["header"][0] = 1
def header_padding(r): call(r)["account_infos"][2]["header"][3] = 0
def header_executable(r): call(r)["account_infos"][1]["header"][2] = 1
def batch_header_padding(r): call(r)["account_infos"][0]["header"][3] = 1
def region_raw_flag(r): r["state"]["region"]["accounts"][3]["is_signer"] = 1


def terminal_log_emptied(r): r["outcome"]["syscalls"]["log"] = []
def terminal_instruction_data(r): r["outcome"]["syscalls"]["log"][0]["instruction"]["data"] = "ff"
def terminal_seeds(r): r["outcome"]["syscalls"]["log"][0]["signers_seeds"] = []
def terminal_replies(r): r["outcome"]["syscalls"]["replies"] = r["state"]["syscalls"]["replies"]
def terminal_detail(r): r["outcome"]["detail"] = "other"
def terminal_header(r): r["outcome"]["syscalls"]["log"][0]["account_infos"][0]["header"][0] ^= 1
def region_lamports(r): account_after(r)["lamports"] += 1
def cpi_rent_epoch_copied(r): after(r)["buffers"]["accounts"][0][2] = r["state"]["region"]["accounts"][1]["rent_epoch"]
def info_rent_epoch(r): call(r)["account_infos"][0]["rent_epoch"] = r["state"]["region"]["accounts"][0]["rent_epoch"]


def shrink(account, n):
    """Lower `data_len` to `n`: the bytes of the region stay, the cut bytes join `spare`."""
    full = hex_bytes(account["data"]) + hex_bytes(account["spare"])
    account["data"], account["spare"], account["data_len"] = hex_text(full[:n]), hex_text(full[n:]), n
    first = next((i for i, b in enumerate(full[n:]) if b), None)
    account["spare_nonzero_at"] = None if first is None else n + first


def unreadable(n):
    """Shrink the account of the typed view below its view, before and after alike: the fallback value of the reference (0) equals the recorded one, so only the decided `requires` (AccountReadable /
    MintReadable) can reject the record."""
    def change(r):
        shrink(r["state"]["region"]["accounts"][0], n)
        shrink(account_after(r), n)
    return change


def committed_past_buffer(r):
    """A committed data length beyond the data buffer, before and after alike: outside
    `InvocationReady`, the requires of the invocation family."""
    n = len(hex_bytes(r["state"]["buffers"]["data"])) + 1
    r["state"]["lengths"]["data"] = n
    after(r)["lengths"]["data"] = n


def marker_400(r): r["state"]["region"]["accounts"][0]["marker"] = 400
def flag_300(r): r["state"]["region"]["accounts"][0]["is_signer"] = 300
def dangling(key, value):
    def change(r):
        r["args"][key] = value
    return change


def rent_epoch(r): account_after(r)["rent_epoch"] += 1
def spare_byte(r): flip_spare(account_after(r), 3)
def frame_program_id(r): after(r)["region"]["program_id"] = "11" * 32
def extra_syscall(r): after(r)["syscalls"]["log"].append({"syscall": "sol_log_", "bytes": ""})


CONTROLS = [
    ("parser borrow marker", L, on_record("account_from_view/01_base_free", marker_minus_one)),
    ("parser account owner error kind", L, on_record("account_from_view/03_wrong_owner", set_err("InvalidAccountOwner"))),
    ("legacy length before owner", L, on_record("mint_from_view/07_wrong_owner_and_length", set_err("InvalidAccountOwner"))),
    ("token-2022 owner before layout", T, on_record("mint_from_view/11_wrong_owner_and_length", set_err("InvalidAccountData"))),
    ("token-2022 guard released after layout error", T, on_record("account_from_view/14_bad_type_shared_1", marker_minus_one)),
    ("shared-borrow saturation", L, on_record("account_from_view/14_shared_254", saturated_ok)),
    ("token-2022 extended layout admitted", T, on_record("account_from_view/09_len_356_type_2", set_err("InvalidAccountData"))),
    ("returned view offset", T, on_record("mint_from_view/01_base_free", view_offset)),
    ("returned view length", T, on_record("account_from_view/01_base_free", view_len)),
    ("amount value", L, on_record("amount/03_18446744073709551615", amount_minus_one)),
    ("mint field bytes", T, on_record("mint/02_extended", key_value)),
    ("owner field offset", L, on_record("owner/00", key_offset)),
    ("state value", L, on_record("state/byte_001", state_frozen)),
    ("state panic message", T, on_record("state/byte_003", panic_message)),
    ("state panic as a return", T, on_record("state/byte_255", panic_as_return)),
    ("decimals value", T, on_record("decimals/04_extended_mint", decimals_plus_one)),
    ("Batch::new lengths", L, on_record("batch_new/data_1", new_lengths)),
    ("Batch::new discriminator", L, on_record("batch_new/data_3_accounts_2", no_discriminator)),
    ("Batch::new empty data", L, on_record("batch_new/data_0", empty_data_ok)),
    ("TransferChecked::new amount", L, on_record("transfer_checked_new/distinct", transfer_amount)),
    ("into_batch committed length", L, on_record("into_batch_identity/single_owner", lengths_accounts)),
    ("into_batch CPI entry account", L, on_record("into_batch_identity/duplicate_signers", entry_account)),
    ("into_batch authority signer flag", L, on_record("into_batch_identity/aliased_accounts_max_values", meta_signer)),
    ("into_batch partial data write retained", L, on_record("into_batch_identity/accounts_room_missing", drop_data_writes)),
    ("into_batch no commit after an error", L, on_record("into_batch_identity/metas_room_missing", commit_on_error)),
    ("into_batch result", L, on_record("into_batch_identity/after_one_instruction", ok_to_err)),
    ("into_batch world unchanged", L, on_record("into_batch_identity/source_shared_borrow", marker_of_1_free)),
    ("into_batch as_ref log", L, on_record("into_batch_scripted/pass_dependent_accounts", asref_log)),
    ("into_batch unwind reason", L, on_record("into_batch_scripted/panic_first_call", unwind_reason)),
    ("into_batch writes retained on unwind", L, on_record("into_batch_scripted/panic_second_call", drop_account_writes)),
    ("invoke_signed account info", L, on_record("batch_invoke_signed/one_instruction", info_lamports)),
    ("invoke_signed instruction data", L, on_record("batch_invoke_signed/empty_batch", instruction_data)),
    ("invoke_signed signer seeds", L, on_record("batch_invoke_signed/two_instructions_seeds", seeds_dropped)),
    ("invoke_signed lengths before", L, on_record("batch_invoke_signed/borrowed_accounts", lengths_before)),
    ("invoke_signed uncommitted entry", L, on_record("batch_invoke_signed/after_failed_push", uncommitted_entry)),
    ("token-2022 mint readonly", T, on_record("transfer_invoke/free", meta_writable)),
    ("token-2022 writable borrow check", T, on_record("transfer_invoke_signed/first_writable_shared", err_to_ok)),
    ("token-2022 readonly not checked", T, on_record("transfer_invoke/readonly_borrowed", set_err("AccountBorrowFailed"))),
    ("token-2022 supplied program id", T, on_record("close_invoke_signed/other_program_id", program_id)),
    ("token-2022 copied signer flag", T, on_record("transfer_invoke_signed/free", info_signer)),
    ("token-2022 reply consumed", T, on_record("transfer_invoke/return_code_ignored", replies_left)),
    ("token-2022 close tag", T, on_record("close_invoke_signed/free", close_tag)),
    ("token-2022 aliased accounts", T, on_record("transfer_invoke_signed/aliased", alias_key)),
    ("token-2022 raw signer byte copied, not normalized", T, on_record("transfer_invoke_signed/raw_header", header_flag_normalized)),
    ("token-2022 copied padding byte", T, on_record("close_invoke_signed/raw_header", header_padding)),
    ("token-2022 raw executable byte", T, on_record("transfer_invoke/raw_header", header_executable)),
    ("token-2022 raw header from the state before", T, on_record("transfer_invoke/raw_header", region_raw_flag)),
    ("Batch copied padding byte", L, on_record("batch_invoke_signed/one_instruction", batch_header_padding)),
    ("terminal CPI log emptied", L, on_record("batch_invoke_signed/callee_fails", terminal_log_emptied)),
    ("terminal CPI instruction data", L, on_record("batch_invoke_signed/callee_fails", terminal_instruction_data)),
    ("terminal reply text", L, on_record("batch_invoke_signed/callee_fails", terminal_detail)),
    ("token-2022 terminal CPI log emptied", T, on_record("close_invoke_signed/callee_fails", terminal_log_emptied)),
    ("token-2022 terminal CPI instruction data", T, on_record("close_invoke_signed/callee_fails", terminal_instruction_data)),
    ("token-2022 terminal signer seeds", T, on_record("close_invoke_signed/callee_fails", terminal_seeds)),
    ("token-2022 terminal unconsumed replies", T, on_record("close_invoke_signed/callee_fails", terminal_replies)),
    ("token-2022 terminal raw header", T, on_record("close_invoke_signed/callee_fails", terminal_header)),
    ("region lamports after", L, on_record("account_from_view/12_shared_1", region_lamports)),
    ("token-2022 region lamports after", T, on_record("transfer_invoke/free", region_lamports)),
    ("CPI entry rent epoch copied", L, on_record("into_batch_identity/single_owner", cpi_rent_epoch_copied)),
    ("token-2022 account info rent epoch copied", T, on_record("transfer_invoke_signed/free", info_rent_epoch)),
    ("amount requires AccountReadable", L, outside_precondition("amount/00_0", unreadable(100)),
     "outside the precondition AccountReadable"),
    ("decimals requires MintReadable", L, outside_precondition("decimals/00_0", unreadable(40)),
     "outside the precondition MintReadable"),
    ("token-2022 amount requires AccountReadable", T, outside_precondition("amount/00_0", unreadable(164)),
     "outside the precondition AccountReadable"),
    ("token-2022 decimals requires MintReadable", T, outside_precondition("decimals/00_0", unreadable(81)),
     "outside the precondition MintReadable"),
    # Frame changes are rejected by the frame of the checker (MISMATCH) or, first, by the check of the runner
    # of region bytes no model represents (FAIL); either names the record.
    ("state requires AccountReadable", L, outside_precondition("state/byte_001", unreadable(100)),
     "outside the precondition AccountReadable"),
    ("token-2022 state requires AccountReadable", T, outside_precondition("state/byte_002", unreadable(164)),
     "outside the precondition AccountReadable"),
    ("invoke_signed requires InvocationReady", L,
     outside_precondition("batch_invoke_signed/empty_batch", committed_past_buffer),
     "outside the precondition InvocationReady"),
    # Malformed records the checker refuses to read (FAIL names the record).
    ("marker above a byte", L, on_record("account_from_view/01_base_free", marker_400),
     "pinocchio_token_0_6_0/account_from_view/01_base_free"),
    ("getter marker above a byte", L, on_record("amount/00_0", marker_400), "pinocchio_token_0_6_0/amount/00_0"),
    ("token-2022 raw flag above a byte", T, on_record("transfer_invoke/raw_header", flag_300),
     "pinocchio_token_2022_0_3_1/transfer_invoke/raw_header"),
    ("dangling parser handle", L, on_record("account_from_view/03_wrong_owner", dangling("account", 1)),
     "pinocchio_token_0_6_0/account_from_view/03_wrong_owner"),
    ("token-2022 dangling parser handle", T, on_record("mint_from_view/02_wrong_owner", dangling("account", 1)),
     "pinocchio_token_2022_0_3_1/mint_from_view/02_wrong_owner"),
    ("into_batch dangling handle", L, on_record("into_batch_identity/header_room_missing", dangling("mint", 50)),
     "pinocchio_token_0_6_0/into_batch_identity/header_room_missing"),
    ("TransferChecked::new dangling handle", L, on_record("transfer_checked_new/distinct", dangling("to", 50)),
     "pinocchio_token_0_6_0/transfer_checked_new/distinct"),
    ("token-2022 dangling CPI handle", T, on_record("transfer_invoke_signed/first_writable_shared",
     dangling("authority", 9)), "pinocchio_token_2022_0_3_1/transfer_invoke_signed/first_writable_shared"),
    ("frame rent epoch", L, on_record("amount/01_1", rent_epoch), "pinocchio_token_0_6_0/amount/01_1"),
    ("frame spare bytes", T, on_record("mint_from_view/01_base_free", spare_byte),
     "pinocchio_token_2022_0_3_1/mint_from_view/01_base_free"),
    ("frame program id", L, on_record("into_batch_identity/data_exact_13", frame_program_id),
     "pinocchio_token_0_6_0/into_batch_identity/data_exact_13"),
    ("frame syscalls", L, on_record("state/byte_000", extra_syscall)),
]
