"""Corrupt actual value calls and whole-signature projected-wrapper records.

These controls alter outcomes while keeping each recorded input fixed. The
checkers decide the selected primary model/reference, including complete
payloads, source identity, ordered requests and the final resource observations.
Native fixtures have proved admission at their parsed indices; arbitrary
missing-current and premature literal-finish controls are kernel theorems.
"""

from common import on_record


def flip_hex(value, offset=0):
    data = bytearray.fromhex(value)
    data[offset] ^= 1
    return data.hex()


def field_changed(record):
    result = record["outcome"]["result"]
    result["value"] = flip_hex(result["value"], -1)


def parent_changed(record):
    record["outcome"]["result"]["same_parent"] = False


def ids_reordered(record):
    record["outcome"]["result"]["value"].reverse()


def call(record):
    return record["outcome"]["state"]["calls"][0]


def instruction_changed(record):
    instruction = call(record)["instruction"]
    instruction["data"] = flip_hex(instruction["data"])


def infos_reordered(record):
    infos = call(record)["accounts"]
    infos[0], infos[-1] = infos[-1], infos[0]


def signer_changed(record):
    entry = call(record)["instruction"]["metas"][0]
    entry["signer"] = not entry["signer"]


def empty_seed_group_removed(record):
    call(record)["signers"].pop(0)


def remaining_alias_changed(record):
    call(record)["accounts"][-3]["data_alias"] += 1


def clone_missing(record):
    call(record)["accounts"][0]["lamports_count"] -= 1


def duplicate_drop_skipped(record):
    record["outcome"]["state"]["counts"][7]["data"] += 1


def error_string_changed(record):
    record["outcome"]["result"]["program"]["value"] += " changed"


def custom_error_changed(record):
    record["outcome"]["result"]["program"]["value"] += 1


def effect_lost(record):
    record["outcome"]["state"]["effect"] = 0


def unwind_as_return(record):
    outcome = record["outcome"]
    outcome["exit"] = "returned"
    outcome["result"] = {"tag": "ok"}
    del outcome["reason"]


def supplied_ata_replaced(record):
    request = call(record)
    request["accounts"][1]["key"] = request["instruction"]["metas"][1]["key"]


def abi_word_changed(record):
    call(record)["accounts"][0]["abi_word"] = 1


def metadata_payload_changed(record):
    instruction = call(record)["instruction"]
    instruction["data"] = flip_hex(instruction["data"], -1)


CONTROLS = []

# Exercise every selected value/ID/deref registration and version profile.
for profile, prefix in [
    ("v027", "token"), ("v029", "interface"),
    ("v0321_pubkey221", "token"), ("v0321_pubkey221", "interface"),
    ("v0321_pubkey240", "token"), ("v0321_pubkey240", "interface"),
    ("v0321_interface", "interface"), ("v102", "token"),
    ("v102", "interface"), ("v112", "interface"),
]:
    corpus = "anchor_spl_support_" + profile
    CONTROLS.append((f"{profile} {prefix} complete close-authority payload", corpus,
                     on_record(f"{prefix}/true/true", field_changed)))
    CONTROLS.append((f"{profile} {prefix} original parent", corpus,
                     on_record(f"{prefix}/false/false", parent_changed)))

CONTROLS += [
    ("legacy stake credits-observed payload", "anchor_spl_support_v027",
     on_record("stake/2", field_changed)),
    ("legacy stake original parent", "anchor_spl_support_v027",
     on_record("stake/0", parent_changed)),
    ("static interface IDs source order", "anchor_spl_support_v029",
     on_record("interface-ids", ids_reordered)),
    ("static interface IDs repeated pointer", "anchor_spl_support_v029",
     on_record("interface-ids", parent_changed)),
]
for profile, identity in [
    ("v0321_pubkey221", "token-id"), ("v0321_pubkey240", "token-id"),
    ("v102", "token-id"), ("v102", "token2022-id"),
]:
    CONTROLS.append((f"{profile} {identity} fixed ID", "anchor_spl_support_" + profile,
                     on_record(identity, field_changed)))

# A request corruption for every exact selected wrapper/profile.
for profile, operation in [
    ("v027", "deactivate"), ("v027", "withdraw"),
    ("v0321_pubkey221", "associated_create"), ("v0321_pubkey240", "associated_create"),
    ("v0321_pubkey221", "memo"), ("v0321_pubkey221", "metadata"),
    ("v0321_pubkey240", "metadata"), ("v102", "associated_idempotent"),
    ("v112", "associated_create"), ("v112", "associated_idempotent"),
]:
    CONTROLS.append((f"{profile} {operation} instruction discriminator",
                     "anchor_spl_support_" + profile,
                     on_record(f"{operation}/ok/custodian-true", instruction_changed)))

for label, record_id, mutation in [
    ("metadata info order differs from metas", "metadata/ok/custodian-true", infos_reordered),
    ("metadata full collection details", "metadata/ok/custodian-true", metadata_payload_changed),
    ("metadata clone before invocation", "metadata/ok/custodian-true", clone_missing),
    ("metadata remaining aliases", "metadata/ok/custodian-true", remaining_alias_changed),
    ("legacy owned Borsh String", "metadata/borsh/custodian-true", error_string_changed),
    ("custom CPI error payload", "metadata/custom/custodian-true", custom_error_changed),
    ("opaque state effect on error", "metadata/custom/custodian-true", effect_lost),
    ("memo duplicate cleanup", "memo/ok/custodian-true", duplicate_drop_skipped),
    ("memo signer flags", "memo/ok/custodian-true", signer_changed),
    ("nested empty signer group", "associated_create/ok/custodian-true", empty_seed_group_removed),
    ("supplied associated info is not derived meta", "associated_create/ok/custodian-true", supplied_ata_replaced),
    ("legacy AccountInfo rent word", "associated_create/ok/custodian-true", abi_word_changed),
    ("actual unwind retained", "memo/unwind/custodian-true", unwind_as_return),
    ("cleanup after unwind", "memo/unwind/custodian-true", duplicate_drop_skipped),
]:
    CONTROLS.append((label, "anchor_spl_support_v0321_pubkey221", on_record(record_id, mutation)))

CONTROLS += [
    ("modern AccountInfo unused word", "anchor_spl_support_v112",
     on_record("associated_create/ok/custodian-true", abi_word_changed)),
    ("withdraw without custodian order", "anchor_spl_support_v027",
     on_record("withdraw/ok/custodian-false", infos_reordered)),
    ("legacy inline error String", "anchor_spl_support_v027",
     on_record("withdraw/borsh/custodian-true", error_string_changed)),
]


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('anchor_spl_support_v027', 'anchor_spl_support_v029', 'anchor_spl_support_v0321_interface', 'anchor_spl_support_v0321_pubkey221', 'anchor_spl_support_v0321_pubkey240', 'anchor_spl_support_v102', 'anchor_spl_support_v112')]
