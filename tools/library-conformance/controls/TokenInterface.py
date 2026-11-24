"""Family TokenInterface: semantic corruptions the checkers must reject.

Each mutation changes one recorded observation that one of the decided
models fixes (instruction bytes and flags, heap counts of the operational
constructors, fee arithmetic, the selected fee field, listing, lookup offsets
and values, the unpacked base, the identity of the returned TLV slice, and the
Rc counts, scripted replies and CPI request of `invoke_transfer_checked`).
Every `invoke_transfer_checked` control names the models that must reject
the record; corruption shared by both models must be rejected by each.
"""

from common import on_record

LEGACY = "spl_token_interface_2_0_0"
TOKEN = "spl_token_2022_interface_3_1_1"
FEE = "spl_token_2022_interface_3_1_1_fee"
EXT = "spl_token_2022_interface_3_1_1_extension"
ONCHAIN = "spl_token_2022_11_0_0"
ONCHAIN_FAMILY = "Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_reference"
ONCHAIN_VALUE = "Solanalib.Specs.SplToken2022.onchain.invoke_transfer_checked_value_reference"


def rejected_by(record_id, *models):
    """The report line of an `invoke_transfer_checked` record rejected by exactly `models`, in the order of the
    checker (the operational family, then the value observation)."""
    return (f"MISMATCH {ONCHAIN}/{record_id} ({ONCHAIN_FAMILY}+{ONCHAIN_VALUE}; "
            f"rejected by [{', '.join(models)}])")


def onchain(label, record_id, change, *models):
    """A control of `invoke_transfer_checked` that exactly `models` must reject."""
    return (f"invoke_transfer_checked: {label}", ONCHAIN, on_record(record_id, change),
            rejected_by(record_id, *models))


def ok(r):
    return r["outcome"]["result"]["ok"]


def allocations_three(r): r["outcome"]["state"]["allocations"] = 3
def error_path_allocates(r): r["outcome"]["state"].update(allocations=1, deallocations=1)
def drop_retired(r): r["outcome"]["state"]["deallocations"] = 1
def signer_flag(r): ok(r)["accounts"][2]["is_signer"] = not ok(r)["accounts"][2]["is_signer"]
def writable_flag(r): ok(r)["accounts"][0]["is_writable"] = False
def data_byte(r): ok(r)["data"] = "13" + ok(r)["data"][2:]
def drop_signer(r): ok(r)["accounts"].pop()
def error_variant(r): r["outcome"]["result"]["err"]["variant"] = "InvalidArgument"
def check_rejects(r): r["outcome"]["result"] = {"err": {"variant": "IncorrectProgramId", "fields": []}}


def withdraw_legacy_accepted(r):
    # The only constructor that rejects the legacy program.
    a = r["args"]
    r["outcome"] = {"exit": "returned", "state": {"allocations": 2, "deallocations": 0}, "result": {"ok": {
        "program_id": a["program_id"],
        "accounts": [{"pubkey": a["source"], "is_signer": False, "is_writable": True},
                     {"pubkey": a["destination"], "is_signer": False, "is_writable": True},
                     {"pubkey": a["authority"], "is_signer": True, "is_writable": False}],
        "data": "26"}}}


def some_plus_one(r): r["outcome"]["result"]["some"] += 1
def none_to_zero(r): r["outcome"]["result"] = {"some": 0}
def receiver_changed(r): r["outcome"]["state"]["epoch"] = 0 if r["outcome"]["state"]["epoch"] else 1
def field_older(r): r["outcome"]["result"]["field"] = "older"
def fee_value(r): r["outcome"]["result"]["value"]["maximum_fee"] += 1
def length_plus_one(r): r["outcome"]["result"]["ok"] += 1
def types_drop_last(r): ok(r).pop()
def types_swap(r): ok(r).reverse()
def getter_offset(r): ok(r)["offset"] += 1
def getter_withheld(r): ok(r)["value"]["withheld_amount"] += 1
def getter_bytes(r): ok(r)["bytes"] = "ff" + ok(r)["bytes"][2:]
def unpack_literal_to_range(r): ok(r)["tlv"] = {"offset": 82, "length": 0}
def unpack_range_to_literal(r): ok(r)["tlv"] = None
def unpack_supply(r): ok(r)["base"]["supply"] += 1
def unpack_frozen(r): ok(r)["base"]["state"] = "Frozen"


def cpi(r):
    return r["outcome"]["state"]["syscalls"]["log"][0]["call"]


def cpi_signer_flag(r): cpi(r)["instruction"]["accounts"][3]["is_signer"] = True
def cpi_signer_dropped(r): cpi(r)["instruction"]["accounts"].pop()
def cpi_account_identity(r): cpi(r)["account_infos"][0]["cells"] = 2
def cpi_seeds(r): cpi(r)["signers_seeds"] = []
def cpi_result_ok(r): r["outcome"]["result"] = {"ok": None}
def borrow_released(r): r["outcome"]["state"]["borrows"] = []
def mint_data_changed(r): r["outcome"]["state"]["accounts"][1]["lamports"] += 1
def panic_kind(r): r["outcome"]["reason"] = "range end index 12 out of range for slice of length 11"


def pda_seed_changed(r):
    entry = [e for e in r["outcome"]["state"]["syscalls"]["log"] if e["syscall"] == "sol_try_find_program_address"][0]
    entry["seeds"][0] = "00" + entry["seeds"][0][2:]


def hook_program_meta_dropped(r): cpi_of_hook(r)["instruction"]["accounts"].pop()
def extra_meta_readonly(r): cpi_of_hook(r)["instruction"]["accounts"][4]["is_writable"] = False


def cpi_of_hook(r):
    return [e for e in r["outcome"]["state"]["syscalls"]["log"] if e["syscall"] == "sol_invoke_signed_rust"][0]["call"]


def search_duplicated(r):
    log = r["outcome"]["state"]["syscalls"]["log"]
    i = next(k for k, e in enumerate(log) if e["syscall"] == "sol_try_find_program_address")
    log.insert(i, dict(log[i]))
    replies = r["state"]["syscalls"]["replies"]
    j = next(k for k, e in enumerate(replies) if e["syscall"] == "sol_try_find_program_address")
    replies.insert(j, dict(replies[j]))


def reply_left_over(r):
    r["outcome"]["state"]["syscalls"]["replies"].append(dict(r["state"]["syscalls"]["replies"][-1]))


def search_removed(r):
    log = r["outcome"]["state"]["syscalls"]["log"]
    log[:] = [e for e in log if e["syscall"] != "sol_try_find_program_address"]


def owner_after(r): r["outcome"]["state"]["accounts"][0]["owner"] = "ff" * 32


def key_and_signer_after(r):
    a = r["outcome"]["state"]["accounts"][1]
    a["key"] = "ee" + a["key"][2:]
    a["is_signer"] = not a["is_signer"]


def log_reversed(r): r["outcome"]["state"]["syscalls"]["log"].reverse()


def initial_bump(r):
    entry = [e for e in r["outcome"]["state"]["syscalls"]["log"] if e["syscall"] == "sol_try_find_program_address"][0]
    entry["bump"] = 0


def panic_indices(r): r["outcome"]["reason"] = "range end index 99 out of range for slice of length 3"
def panic_borrow_kind(r): r["outcome"]["reason"] = "RefCell already borrowed"


def cpi_missing(r):
    r["outcome"]["state"]["syscalls"]["log"] = []


def replies(r):
    return r["state"]["syscalls"]["replies"]


def search_reply(r):
    return [e for e in replies(r) if e["syscall"] == "sol_try_find_program_address"][0]


def counts_at(r, where):
    """The recorded Rc counts before the call, at the CPI or after the call."""
    if where == "before":
        return r["state"]["counts"]
    if where == "cpi":
        return cpi_of_hook(r)["counts"]
    return r["outcome"]["state"]["counts"]


def count_moved(where, cell, delta):
    def change(r): counts_at(r, where)[cell] += delta
    return change


def cpi_counts_truncated(r): counts_at(r, "cpi").pop()
def cpi_data_byte(r): cpi_of_hook(r)["instruction"]["data"] = "0d" + cpi_of_hook(r)["instruction"]["data"][2:]
def search_reply_status(r): search_reply(r)["return"] = 1
def search_reply_address(r): search_reply(r)["data"] = "49" + search_reply(r)["data"][2:]
def cpi_reply_success(r): [e for e in replies(r) if e["syscall"] == "sol_invoke_signed_rust"][0]["return"] = 0


def exit_unwound(r):
    r["outcome"]["exit"] = "unwound"
    del r["outcome"]["result"]
    r["outcome"]["reason"] = "RefCell already mutably borrowed"


CONTROLS = [
    ("transfer_checked: heap allocations", TOKEN, on_record("transfer_checked/legacy/none/0/0", allocations_three)),
    ("transfer_checked: a retired vector", TOKEN, on_record("transfer_checked/legacy/none/0/0", drop_retired)),
    ("close_account: rejection allocates", TOKEN, on_record("close_account/zero/none", error_path_allocates)),
    ("withdraw_excess_lamports: authority signer flag", TOKEN,
     on_record("withdraw_excess_lamports/token2022/one", signer_flag)),
    ("withdraw_excess_lamports: signer dropped", TOKEN,
     on_record("withdraw_excess_lamports/token2022/one", drop_signer)),
    ("withdraw_excess_lamports: legacy program accepted", TOKEN,
     on_record("withdraw_excess_lamports/legacy/none", withdraw_legacy_accepted)),
    ("check_spl_token_program_account: legacy rejected", TOKEN,
     on_record("check_spl_token_program_account/legacy", check_rejects)),
    ("transfer: writable flag", LEGACY, on_record("transfer/legacy/none/0", writable_flag)),
    ("transfer: instruction tag", LEGACY, on_record("transfer/legacy/none/0", data_byte)),
    ("transfer: error variant", LEGACY, on_record("transfer/token2022/none/0", error_variant)),
    ("calculate_pre_fee_amount: value", FEE, on_record("calculate_pre_fee_amount/0/0/0", some_plus_one)),
    ("calculate_fee: overflow becomes zero", FEE,
     on_record("calculate_fee/10001/0/18446744073709551614", none_to_zero)),
    ("calculate_post_fee_amount: receiver changed", FEE,
     on_record("calculate_post_fee_amount/0/18446744073709551615/18446744073709551615", receiver_changed)),
    ("get_epoch_fee: selected field only", FEE, on_record("get_epoch_fee/0/0/0", field_older)),
    ("get_epoch_fee: copied value only", FEE, on_record("get_epoch_fee/0/0/0", fee_value)),
    ("account_len: size", EXT, on_record("account_len/bare/[]", length_plus_one)),
    ("get_extension_types: last type dropped", EXT,
     on_record("get_extension_types/mint/close_then_fee", types_drop_last)),
    ("get_extension_types: order", EXT, on_record("get_extension_types/mint/close_then_fee", types_swap)),
    ("get_extension: offset", EXT, on_record("get_extension/mint/TransferFeeConfig/entry1", getter_offset)),
    ("get_extension: fee config field", EXT,
     on_record("get_extension/mint/TransferFeeConfig/entry1", getter_withheld)),
    ("get_extension: raw bytes", EXT, on_record("get_extension/account/TransferFeeAmount/own", getter_bytes)),
    ("unpack: static empty literal reported as input range", EXT,
     on_record("unpack/mint/bare", unpack_literal_to_range)),
    ("unpack: empty input range reported as literal", EXT,
     on_record("unpack/mint/marker_only", unpack_range_to_literal)),
    ("unpack: mint supply", EXT, on_record("unpack/mint/bare", unpack_supply)),
    ("unpack: account state", EXT, on_record("unpack/account/bare", unpack_frozen)),
    onchain("multisig authority signer flag", "multisig_signers", cpi_signer_flag,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("multisig signer dropped", "multisig_signers", cpi_signer_dropped,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("account info identity", "source_is_destination", cpi_account_identity,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("signer seeds", "multisig_signers", cpi_seeds,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("CPI error reported as success", "bare_mint_cpi_error", cpi_result_ok,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("CPI not made", "extended_mint_no_hook", cpi_missing,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("held borrow released", "mint_data_borrowed", borrow_released,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("mint lamports changed", "mint_uninitialized", mint_data_changed,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("panic reason", "multisig_data_borrowed", panic_kind,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("validation address searched with other seeds", "hook_without_validation", pda_seed_changed,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("hook program meta dropped", "hook_without_validation", hook_program_meta_dropped,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("resolved extra account readonly", "hook_validation_fixed_extra", extra_meta_readonly,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("address search duplicated", "hook_validation_fixed_extra", search_duplicated,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("consumed reply left over", "hook_validation_fixed_extra", reply_left_over,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("CPI reply left over", "legacy_program_bare_mint", reply_left_over,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("address search not logged", "hook_program_missing", search_removed,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("owner after the call", "legacy_program_bare_mint", owner_after,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("key and signer flag after the call", "extended_mint_no_hook", key_and_signer_after,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("CPI logged before the address search", "hook_validation_fixed_extra", log_reversed,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("initial bump of the address search", "hook_without_validation", initial_bump,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("slice panic indices", "multisig_n_out_of_range", panic_indices,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("failing borrow kind", "multisig_data_borrowed", panic_borrow_kind,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("Rc count at the CPI", "multisig_signers", count_moved("cpi", 8, 1), ONCHAIN_FAMILY),
    onchain("Rc count at the CPI of an aliased account", "source_is_destination", count_moved("cpi", 0, -1),
            ONCHAIN_FAMILY),
    onchain("Rc counts at the CPI truncated", "hook_validation_fixed_extra", cpi_counts_truncated, ONCHAIN_FAMILY),
    onchain("Rc count after the call", "extended_mint_no_hook", count_moved("after", 2, 1), ONCHAIN_FAMILY),
    onchain("Rc count after an unwind", "multisig_data_borrowed", count_moved("after", 8, -1), ONCHAIN_FAMILY),
    onchain("Rc count before the call", "hook_validation_fixed_extra", count_moved("before", 12, 1), ONCHAIN_FAMILY),
    onchain("CPI request data", "legacy_program_bare_mint", cpi_data_byte, ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("address search reply status", "hook_without_validation", search_reply_status, ONCHAIN_FAMILY),
    onchain("address search reply address", "hook_validation_fixed_extra", search_reply_address,
            ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("CPI reply", "bare_mint_cpi_error", cpi_reply_success, ONCHAIN_FAMILY, ONCHAIN_VALUE),
    onchain("exit", "extended_mint_no_hook", exit_unwound, ONCHAIN_FAMILY, ONCHAIN_VALUE),
]
