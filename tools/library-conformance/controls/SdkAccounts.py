"""Reject altered native results, aliases, guards, backing bytes and admission.

Every exact source-version checker has a semantic corruption. Each nontrivial
registered precondition is exercised separately before fixture validation.
"""

from common import hex_bytes, hex_text, on_record, outside_precondition


CORPORA = {
    "sdk_accounts_2_3_0": ["as_ref", "assign", "data_is_empty", "realloc", "resize",
                           "try_borrow_lamports", "try_data_len"],
    "sdk_accounts_3_1_1": ["as_ref", "assign", "data_is_empty", "resize",
                           "try_borrow_lamports", "try_borrow_mut_lamports", "try_data_len"],
    "sdk_accounts_1_15_2": ["assign", "clone", "data_len", "lamports", "realloc",
                            "try_borrow_data", "try_borrow_mut_data", "try_borrow_mut_lamports",
                            "try_data_len"],
    "sdk_accounts_1_18_26": ["assign", "clone", "data_is_empty", "data_len", "lamports", "realloc",
                             "try_borrow_data", "try_borrow_lamports", "try_borrow_mut_data", "try_data_len"],
}


def after(record):
    return record["outcome"]["state"]


def wrong_kind(cell):
    def change(record):
        original = record["state"]["cells"][cell]
        value = {"data": ""} if "lamports" in original else {"lamports": 40}
        record["state"]["cells"][cell] = {**value, "lease": original["lease"]}
    return change


def absent_owner(record):
    record["state"]["owners"] = []


def insufficient_backing(record):
    record["state"]["buffers"][0]["spare"] = {"prefix": "", "zeros": 0}
    record["args"]["new_len"] = 6


def wrong_reference(record):
    # Equal AccountInfo pointees are different existing reference identities.
    record["outcome"]["result"]["reference"] = 0


def stale_owner_alias(record):
    # The shared owner store changes, so every retained AccountInfo observes it.
    after(record)["infos"][0]["owner"] = record["state"]["infos"][0]["owner"]


def incomplete_clone(record):
    after(record)["rc"][0] -= 1


def wrong_scalar(record):
    record["outcome"]["result"] += 1


def wrong_empty(record):
    record["outcome"]["result"] = True


def wrong_length(record):
    record["outcome"]["result"]["ok"] += 1


def wrong_guard(record):
    record["outcome"]["result"]["ok"]["guard"] += 1


def erased_hidden_byte(record):
    spare = after(record)["buffers"][0]["spare"]
    prefix = bytearray(hex_bytes(spare["prefix"]))
    prefix[0] = 0
    spare["prefix"] = hex_text(prefix)


def stale_growth(record):
    data = bytearray(hex_bytes(after(record)["cells"][1]["data"]))
    data[-1] = 9
    after(record)["cells"][1]["data"] = hex_text(data)


def zeroed_nonzeroing_regrow(record):
    after(record)["cells"][1]["data"] = "0a0000"


def incorrect_serialized_length(record):
    after(record)["buffers"][0]["serialized_len"] += 1


def reset_original_length(record):
    after(record)["buffers"][0]["original_len"] = 5


def invented_memset(record):
    after(record)["memsets"] = [{"cell": 1, "offset": 0, "byte": 0, "length": 1}]


def wrong_memset_range(record):
    after(record)["memsets"][0]["offset"] = 0


def wrong_error_order(record):
    record["outcome"]["result"] = {"err": "InvalidRealloc"}


def wrong_terminal_count(record):
    record["outcome"]["detail"]["length"] += 1


def invent_terminal(record):
    record["outcome"] = {"exit": "terminated", "reason": "zeroing",
                         "detail": {"status": 91, "byte": 0, "length": 2}}


def drop_live_guard(record):
    after(record)["guards"] = []


def twice_exclusive(record):
    state = record["state"]
    state["guards"].append({"id": 1, "cell": 1, "mode": "exclusive", "view": "whole"})
    state["ghost"] = {"slots": 2, "generations": [0, 0]}


def change_frame(record):
    frame = bytearray(hex_bytes(after(record)["frame"]))
    frame[-1] ^= 1
    after(record)["frame"] = hex_text(frame)


CONTROLS = []
for corpus, methods in CORPORA.items():
    for method in methods:
        record_id = f"{method}/aliases-0"
        if method in ("resize", "realloc"):
            record_id = f"{method}/shrink"
        semantic = {
            "as_ref": wrong_reference, "assign": stale_owner_alias, "clone": incomplete_clone,
            "data_len": wrong_scalar, "lamports": wrong_scalar, "data_is_empty": wrong_empty,
            "try_data_len": wrong_length, "resize": erased_hidden_byte, "realloc": erased_hidden_byte,
        }.get(method, wrong_guard)
        CONTROLS.append((f"{corpus} {method} native result", corpus, on_record(record_id, semantic)))
        if method not in ("as_ref", "clone"):
            admission = absent_owner if method == "assign" else insufficient_backing if method in ("resize", "realloc") \
                else wrong_kind(0 if "lamports" in method else 1)
            CONTROLS.append((f"{corpus} {method} admission", corpus,
                             outside_precondition(record_id, admission),
                             f"FAIL {corpus}/{record_id}: the input is outside the registered precondition"))
    for method in ("resize", "realloc"):
        if method not in methods:
            continue
        for label, case, mutate in [
            ("zero tail", "grow-zero", stale_growth),
            ("shared serialized length", "grow-zero", incorrect_serialized_length),
            ("original length", "grow-zero", reset_original_length),
            ("memset range", "grow-zero", wrong_memset_range),
            ("no memset on shrink", "shrink", invented_memset),
            ("borrow error order", "busy-past-limit", wrong_error_order),
            ("terminal call arguments", "zeroing-terminates", wrong_terminal_count),
            ("same length cannot terminate at zeroing", "same", invent_terminal),
        ]:
            # The driver records the terminal child for resize when both APIs exist.
            if case == "zeroing-terminates" and method == "realloc" and "resize" in methods:
                continue
            CONTROLS.append((f"{corpus} {method} {label}", corpus,
                             on_record(f"{method}/{case}", mutate)))
        if method == "realloc":
            CONTROLS.append((f"{corpus} realloc preserves stale regrowth", corpus,
                             on_record("realloc/regrow-stale", zeroed_nonzeroing_regrow)))

CONTROLS += [
    ("assign keeps an existing exclusive data guard", "sdk_accounts_3_1_1",
     on_record("assign/aliases-2", drop_live_guard)),
    ("try_data_len preserves the unrelated exclusive lamports guard", "sdk_accounts_3_1_1",
     on_record("try_data_len/aliases-4", drop_live_guard)),
    ("lamports borrow requires a valid shared protocol", "sdk_accounts_3_1_1",
     outside_precondition("try_borrow_lamports/aliases-2", twice_exclusive),
     "FAIL sdk_accounts_3_1_1/try_borrow_lamports/aliases-2: the input is outside the registered precondition"),
    ("AccountInfo leaves every unmodeled frame byte intact", "sdk_accounts_3_1_1",
     on_record("as_ref/aliases-0", change_frame),
     "FAIL sdk_accounts_3_1_1/as_ref/aliases-0: region bytes no model represents changed: frame"),
]


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('sdk_accounts_1_15_2', 'sdk_accounts_1_18_26', 'sdk_accounts_2_3_0', 'sdk_accounts_3_1_1')]
