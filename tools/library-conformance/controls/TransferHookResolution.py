"""Semantic corruptions of the exact transfer-hook 0.9.0 observations.

Every mutation must be rejected by the registered complete reference checker.
The syscall provider is scripted; these are SDK behavior and ABI controls,
not assertions about the PDA implementation of a validator.
"""

from common import on_record, hex_bytes, hex_text


def after(r):
    return r["outcome"]["state"]


def metas(r):
    return after(r)["instruction"]["accounts"]


def wrong_result(r):
    r["outcome"]["result"] = {"ok": None}


def clear_new_signer(r):
    metas(r)[1]["is_signer"] = False


def escalate_alias(r):
    metas(r)[1]["is_writable"] = True


def remove_validation_alias(r):
    metas(r).pop(1)
    after(r)["caller_infos"].pop(2)


def later_equal_key(r):
    after(r)["caller_infos"][2]["cells"] = 6


def swap_validation_program(r):
    values = metas(r)
    values[-2], values[-1] = values[-1], values[-2]
    values = after(r)["caller_infos"]
    values[-2], values[-1] = values[-1], values[-2]


def change_caller_data(r):
    value = bytearray(hex_bytes(after(r)["instruction"]["data"]))
    value[0] ^= 1
    after(r)["instruction"]["data"] = hex_text(bytes(value))


def change_caller_program(r):
    after(r)["instruction"]["program_id"] = "ff" * 32


def wrong_rc_cleanup(r):
    after(r)["counts"][0] += 1


def borrow_leaked(r):
    after(r)["borrows"].append({"account": 5, "cell": "data", "mode": "shared"})


def panic_as_error(r):
    r["outcome"] = {"exit": "returned", "result": {"err": {"variant": "Custom", "fields": [1]}},
                    "state": after(r)}


def failure_keeps_partial_extra(r):
    after(r)["caller_infos"].append(dict(after(r)["caller_infos"][0]))


def pda_seed_order(r):
    after(r)["syscalls"]["log"][0]["seeds"].reverse()


def pda_initial_bump(r):
    after(r)["syscalls"]["log"][0]["bump"] = 253


def empty_pda_wrong_program(r):
    after(r)["syscalls"]["log"][1]["program_id"] = "ff" * 32


def partial_output_without_validation(r):
    metas(r).pop(1)
    after(r)["caller_infos"].pop(2)


def terminal_request_removed(r):
    r["outcome"]["syscalls"]["log"].clear()


def terminal_wrong_detail(r):
    r["outcome"]["detail"] += "!"


def source_pubkey_data_changed(r):
    after(r)["caller_infos"][2]["key"] = "ee" * 32


CORPUS = "spl_transfer_hook_interface_0_9_0"
CONTROLS = [
    ("new-key signer remains requested", CORPUS, on_record("fresh_signer_preserved", clear_new_signer)),
    ("existing alias writable request is clamped", CORPUS, on_record("existing_role_privileges_reduced", escalate_alias)),
    ("validation and program aliases are both appended", CORPUS, on_record("program_is_validation", remove_validation_alias)),
    ("first equal key retains its own Rc cells", CORPUS, on_record("first_match_duplicate_cells", later_equal_key)),
    ("validation precedes program", CORPUS, on_record("validation_empty", swap_validation_program)),
    ("fixed-key resolution still borrows unrelated data", CORPUS, on_record("fixed_extra_unrelated_borrow_conflict", wrong_result)),
    ("POD overflow panics after unpack", CORPUS, on_record("pod_count_over_capacity_panics", panic_as_error)),
    ("the caller instruction bytes are preserved", CORPUS, on_record("fresh_signer_preserved", change_caller_data)),
    ("the caller program is preserved", CORPUS, on_record("fresh_signer_preserved", change_caller_program)),
    ("all temporary owners drop on resolver error", CORPUS, on_record("error_after_first_extra", wrong_rc_cleanup)),
    ("all temporary Ref guards drop on success", CORPUS, on_record("fresh_signer_preserved", borrow_leaked)),
    ("resolver errors precede caller copyback", CORPUS, on_record("error_after_first_extra", failure_keeps_partial_extra)),
    ("validation seeds retain source order", CORPUS, on_record("no_validation", pda_seed_order)),
    ("the PDA bump starts at 255", CORPUS, on_record("no_validation", pda_initial_bump)),
    ("extra PDA uses the current program", CORPUS, on_record("empty_seed_pda", empty_pda_wrong_program)),
    ("partial PDA writes retain the zero suffix", CORPUS, on_record("pda_partial_output", partial_output_without_validation)),
    ("a terminal PDA retains its actual request", CORPUS, on_record("pda_terminal", terminal_request_removed)),
    ("a terminal PDA retains its actual reason", CORPUS, on_record("pda_terminal", terminal_wrong_detail)),
    ("key-data resolution reads current account bytes", CORPUS, on_record("account_data_pubkey", source_pubkey_data_changed)),
]
