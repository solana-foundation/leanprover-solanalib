"""Corrupt actual projected-wrapper observations; the registered relation rejects them."""

from common import on_record


def call(record):
    return record["outcome"]["state"]["calls"][0]


def wrong_tag(record):
    data = call(record)["instruction"]["data"]
    call(record)["instruction"]["data"] = "ff" + data[2:]


def swapped_accounts(record):
    call(record)["accounts"].reverse()


def swapped_metas(record):
    call(record)["instruction"]["metas"].reverse()


def duplicate_removed(record):
    call(record)["accounts"].pop()


def seed_removed(record):
    call(record)["signers"][0].pop()


def wrong_program(record):
    call(record)["instruction"]["program"] = "99" * 32


def wrong_flag(record):
    call(record)["instruction"]["metas"][1]["signer"] = True


def wrong_counts(record):
    record["outcome"]["state"]["counts"][0][0] += 1


def lost_effect(record):
    record["outcome"]["state"]["cells"][0]["lamports"] -= 101


def wrong_drop_order(record):
    record["outcome"]["state"]["freed"][:2] = ["data", "metas"]


def missing_box(record):
    record["outcome"]["state"]["fresh_boxes"] = 0


def copied_string(record):
    record["outcome"]["state"]["same_string"] = False


def wrong_error(record):
    record["outcome"]["result"]["err"]["program_error"]["custom"] += 1


def invented_origin(record):
    record["outcome"]["result"]["err"]["origin"] = "invented source"


def wrong_terminal_request(record):
    record["outcome"]["request"]["accounts"] = []


def wrong_unwind(record):
    record["outcome"]["reason"] = "ordinary error"


def cloned_call_owner(record):
    call(record)["counts"][0][0] += 1


def dropped_call_owner(record):
    call(record)["counts"][0][0] -= 1


def wrong_terminal_counts(record):
    record["outcome"]["request"]["counts"][0][0] += 1


def wrong_terminal_bytes(record):
    instruction = record["outcome"]["request"]["instruction"]
    instruction["data"] = "ff" + instruction["data"][2:]


def wrong_terminal_reason(record):
    record["outcome"]["reason"] = 193


def wrong_unwind_code(record):
    record["outcome"]["reason"] = 191


def terminal_after_state(record):
    record["outcome"]["state"] = record["state"]


CONTROLS = []
for version in ["0_27_0", "0_29_0", "0_32_1", "1_0_2", "1_1_2"]:
    for operation in ["allocate", "assign", "create_account", "transfer"]:
        CONTROLS.append((f"{version} {operation} exact constructor tag",
                         "anchor_system_" + version,
                         on_record(operation + "/ok/aliasfalse/amount37/borshfalse", wrong_tag)))

for label, mutate in [
    ("account order", swapped_accounts), ("metadata order", swapped_metas),
    ("nested seed duplicates", seed_removed), ("fixed System ID", wrong_program),
    ("constructor signer flags", wrong_flag), ("Rc cleanup", wrong_counts),
    ("provider mutation", lost_effect), ("instruction cleanup order", wrong_drop_order),
]:
    CONTROLS.append((label, "anchor_system_1_0_2",
                     on_record("transfer/ok/aliasfalse/amount37/borshfalse", mutate)))

CONTROLS += [
    ("aliased owner occurrence", "anchor_system_1_1_2",
     on_record("transfer/ok/aliastrue/amount37/borshfalse", duplicate_removed)),
    ("actual fresh error Box", "anchor_system_0_29_0",
     on_record("allocate/error/aliasfalse/amount37/borshfalse", missing_box)),
    ("legacy String moved", "anchor_system_0_27_0",
     on_record("allocate/error/aliasfalse/amount37/borshtrue", copied_string)),
    ("actual custom error", "anchor_system_1_1_2",
     on_record("assign/error/aliasfalse/amount37/borshfalse", wrong_error)),
    ("absent error diagnostics", "anchor_system_0_32_1",
     on_record("assign/error/aliasfalse/amount37/borshfalse", invented_origin)),
    ("terminal reached request", "anchor_system_1_0_2",
     on_record("allocate/terminal", wrong_terminal_request)),
    ("unwind outcome", "anchor_system_0_29_0",
     on_record("create_account/unwind/aliasfalse/amount37/borshfalse", wrong_unwind)),
    ("unwind still drops resources", "anchor_system_0_32_1",
     on_record("transfer/unwind/aliasfalse/amount37/borshfalse", wrong_drop_order)),
    ("System Id return bytes", "anchor_system_0_32_1",
     on_record("System/id", lambda r: r["outcome"].update(result="01" * 32))),
]


# Register controls only for the retained authenticated corpus files.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('anchor_system_0_27_0', 'anchor_system_0_29_0', 'anchor_system_0_32_1', 'anchor_system_1_0_2', 'anchor_system_1_1_2')]

# These controls target the four registered wrappers at their reviewed release.
# Controls attached to the other release corpora above cannot exercise this replay.
for label, record, mutate in [
    ("account order", "transfer/ok/aliasfalse/amount37/borshfalse", swapped_accounts),
    ("metadata order", "transfer/ok/aliasfalse/amount37/borshfalse", swapped_metas),
    ("nested seed duplicates", "transfer/ok/aliasfalse/amount37/borshfalse", seed_removed),
    ("fixed System ID", "transfer/ok/aliasfalse/amount37/borshfalse", wrong_program),
    ("constructor signer flags", "transfer/ok/aliasfalse/amount37/borshfalse", wrong_flag),
    ("Rc cleanup", "transfer/ok/aliasfalse/amount37/borshfalse", wrong_counts),
    ("provider mutation", "transfer/ok/aliasfalse/amount37/borshfalse", lost_effect),
    ("instruction cleanup order", "transfer/ok/aliasfalse/amount37/borshfalse", wrong_drop_order),
    ("aliased owner occurrence", "transfer/ok/aliastrue/amount37/borshfalse", duplicate_removed),
    ("fresh error Box", "allocate/error/aliasfalse/amount37/borshfalse", missing_box),
    ("legacy String moved", "allocate/error/aliasfalse/amount37/borshtrue", copied_string),
    ("custom error", "assign/error/aliasfalse/amount37/borshfalse", wrong_error),
    ("error retains provider mutation", "assign/error/aliasfalse/amount37/borshfalse", lost_effect),
    ("terminal reached request", "allocate/terminal", wrong_terminal_request),
    ("terminal has no after state", "allocate/terminal", terminal_after_state),
    ("unwind outcome", "create_account/unwind/aliasfalse/amount37/borshfalse", wrong_unwind),
    ("unwind retains provider mutation", "create_account/unwind/aliasfalse/amount37/borshfalse", lost_effect),
    ("call-time clone", "transfer/ok/aliasfalse/amount37/borshfalse", cloned_call_owner),
    ("call-time drop", "transfer/ok/aliasfalse/amount37/borshfalse", dropped_call_owner),
    ("terminal call-time count", "allocate/terminal", wrong_terminal_counts),
    ("terminal received bytes", "allocate/terminal", wrong_terminal_bytes),
    ("terminal reason code", "allocate/terminal", wrong_terminal_reason),
    ("unwind reason code", "create_account/unwind/aliasfalse/amount37/borshfalse", wrong_unwind_code),
]:
    CONTROLS.append(("registered System " + label, "anchor_system_0_32_1", on_record(record, mutate)))
