"""Reject changed observations of the exact projected Anchor SPL wrappers.

The native wrappers keep real constructors, context/account types, ownership
and cleanup. Only the complete invocation/getter signatures are scripted.
These controls exercise returned, unwound and terminal provider observations.
"""

from common import on_record


def state(record):
    return record["outcome"]["state"]


def call(record):
    return state(record)["calls"][0]


def instruction_tag(record):
    instruction = call(record)["instruction"]
    data = instruction["data"]
    instruction["data"] = f"{int(data[:2], 16) ^ 1:02x}" + data[2:]


def cell_effect(record):
    state(record)["cells"][0]["lamports"] += 1


def retained_owner(record):
    state(record)["counts"][0][0] += 1


def cleanup_order(record):
    state(record)["freed"].reverse()


def meta_flag(record):
    meta = call(record)["instruction"]["metas"][0]
    meta["writable"] = not meta["writable"]


def account_order(record):
    accounts = call(record)["accounts"]
    accounts[0], accounts[1] = accounts[1], accounts[0]


def alias_count(record):
    call(record)["counts"][0][0] += 1


def seed_identity(record):
    value = call(record)["seed_reference"]
    call(record)["seed_reference"] = 1 if value is not None else 0


def seed_groups(record):
    call(record)["signers"].append([])


def error_storage(record):
    error = record["outcome"]["result"]["err"]
    error["boxed"] = not error["boxed"]


def error_code(record):
    record["outcome"]["result"]["err"]["program_error"]["custom"] += 1


def copied_string(record):
    state(record)["same_string"] = False


def leaked_heap(record):
    state(record)["heap"]["live"] += 1


def terminal_call(record):
    record["outcome"]["detail"]["calls"][0]["accounts"][0] += 1


def terminal_after_state(record):
    record["outcome"]["state"] = {"counts": record["state"]["counts"]}


def terminal_kind(record):
    record["outcome"]["reason"] = "opaque getter terminal"


def size_mint_still_owned(record):
    state(record)["getters"][0]["counts"][0][0] += 1


def size_instruction_freed(record):
    state(record)["getters"][0]["metas_live"] = False


def size_data_freed(record):
    state(record)["getters"][0]["data_live"] = False


def returned_vector_leaked(record):
    state(record)["returned_freed"] = False


def conversion_before_free(record):
    state(record)["conversion_after_return_free"] = False


def length_before_key(record):
    record["outcome"]["result"]["err"]["program_error"] = "invalid_instruction_data"


def size_accepted(record):
    record["outcome"]["result"] = {"ok": 165}


def size_value(record):
    record["outcome"]["result"]["ok"] += 1


def getter_terminal_array(record):
    record["outcome"]["detail"]["getters"][0]["counts"][0][0] += 1


def constructor_error(record):
    record["outcome"]["result"]["err"]["program_error"] = "invalid_instruction_data"


def constructor_allocation(record):
    state(record)["heap"]["allocations"] += 1


PROFILES = {
    "0_27_0": ["burn", "mint_to", "transfer"],
    "0_29_0": ["transfer_checked"],
    "0_32_1": [
        "transfer", "burn", "close_account", "get_account_data_size", "initialize_account3",
        "initialize_immutable_owner", "initialize_mint2", "mint_to", "set_authority", "transfer_checked",
        "group_member_pointer_initialize", "group_pointer_initialize", "metadata_pointer_initialize",
        "mint_close_authority_initialize", "non_transferable_mint_initialize", "permanent_delegate_initialize",
        "transfer_hook_initialize",
    ],
    "1_0_2": ["initialize_account3", "transfer_checked"],
    "1_1_2": ["burn_checked", "mint_to_checked", "set_authority", "transfer_checked"],
}

CONTROLS = []
for version, functions in PROFILES.items():
    corpus = "anchor_spl_token_" + version
    for function in functions:
        for label, change in [("instruction tag", instruction_tag), ("actual cell effect", cell_effect),
                              ("owned Rc release", retained_owner)]:
            CONTROLS.append((f"{version}/{function}/{label}", corpus, on_record(function + "/00/ok", change)))
    function = functions[0]
    for label, record, change in [
        ("custom provider error", "/01/error", error_code),
        ("error storage profile", "/01/error", error_storage),
        ("unwind cleanup order", "/02/unwind", cleanup_order),
        ("unwind retains cell effects", "/02/unwind", cell_effect),
        ("terminal exact prefix", "/terminal/invoke", terminal_call),
        ("terminal has no after state", "/terminal/invoke", terminal_after_state),
    ]:
        CONTROLS.append((f"{version}/{label}", corpus, on_record(function + record, change)))

C32 = "anchor_spl_token_0_32_1"
C27 = "anchor_spl_token_0_27_0"
for label, corpus, record, change in [
    ("027 cloned count", C27, "burn/00/ok", alias_count),
    ("027 source account order", C27, "mint_to/00/ok", account_order),
    ("027 inline String identity", C27, "burn/07/error", copied_string),
    ("032 boxed String identity", C32, "burn/07/error", copied_string),
    ("032 boxed allocation retained", C32, "burn/01/error", leaked_heap),
    ("032 metadata flags", C32, "transfer_checked/00/ok", meta_flag),
    ("032 source account order", C32, "mint_to/00/ok", account_order),
    ("032 signed seed identity", C32, "transfer_checked/00/ok", seed_identity),
    ("032 signed group multiplicity", C32, "transfer_checked/00/ok", seed_groups),
    ("032 unsigned seed identity", C32, "initialize_account3/00/ok", seed_identity),
    ("032 unsigned seeds empty", C32, "initialize_mint2/00/ok", seed_groups),
    ("size scalar value", C32, "get_account_data_size/00/ok", size_value),
    ("size array released before getter", C32, "get_account_data_size/00/ok", size_mint_still_owned),
    ("size metas live at getter", C32, "get_account_data_size/00/ok", size_instruction_freed),
    ("size data live at getter", C32, "get_account_data_size/00/ok", size_data_freed),
    ("size successful Vec conversion releases", C32, "get_account_data_size/00/ok", returned_vector_leaked),
    ("size key checked before length", C32, "get_account_data_size/08/ok", length_before_key),
    ("size wrong-key Vec releases", C32, "get_account_data_size/08/ok", returned_vector_leaked),
    ("size conversion follows returned Vec release", C32, "get_account_data_size/08/ok", conversion_before_free),
    ("size absent result fails", C32, "get_account_data_size/07/ok", size_accepted),
    ("size short result fails", C32, "get_account_data_size/09/ok", size_accepted),
    ("size long result fails", C32, "get_account_data_size/10/ok", size_accepted),
    ("getter unwind cleanup", C32, "get_account_data_size/11/ok", cleanup_order),
    ("getter terminal observes earlier release", C32, "get_account_data_size/terminal/getter", getter_terminal_array),
    ("invoke and getter terminals differ", C32, "get_account_data_size/terminal/invoke", terminal_kind),
]:
    CONTROLS.append((label, corpus, on_record(record, change)))


# Register controls only for the retained authenticated corpus files.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('anchor_spl_token_0_27_0', 'anchor_spl_token_0_29_0', 'anchor_spl_token_0_32_1', 'anchor_spl_token_1_0_2', 'anchor_spl_token_1_1_2')]

# The registered subset contains transfer_checked. The first helper in PROFILES
# is transfer, so its error/unwind/terminal controls are omitted by that subset.
for label, record, change in [
    ("source account order", "transfer_checked/00/ok", account_order),
    ("aliased owner count", "transfer_checked/04/ok", alias_count),
    ("custom provider error", "transfer_checked/01/error", error_code),
    ("error storage profile", "transfer_checked/01/error", error_storage),
    ("error retains cell effects", "transfer_checked/01/error", cell_effect),
    ("boxed String identity", "transfer_checked/07/error", copied_string),
    ("boxed allocation retained", "transfer_checked/01/error", leaked_heap),
    ("unwind cleanup order", "transfer_checked/02/unwind", cleanup_order),
    ("unwind retains cell effects", "transfer_checked/02/unwind", cell_effect),
    ("terminal exact prefix", "transfer_checked/terminal/invoke", terminal_call),
    ("terminal has no after state", "transfer_checked/terminal/invoke", terminal_after_state),
    ("constructor program error", "transfer_checked/08/ok", constructor_error),
    ("constructor has no CPI effects", "transfer_checked/08/ok", cell_effect),
    ("constructor has no instruction allocation", "transfer_checked/08/ok", constructor_allocation),
    ("constructor releases context owners", "transfer_checked/08/ok", retained_owner),
]:
    CONTROLS.append(("registered checked transfer " + label, C32, on_record(record, change)))
