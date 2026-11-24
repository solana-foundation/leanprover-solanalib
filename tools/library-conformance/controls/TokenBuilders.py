"""Semantic corruptions of each newly bound instruction or ID reference.

The model checks the actual constructor relation, including allocation and
retirement observations. These mutations do not edit the recorded inputs or
manufacture a successful SDK execution.
"""

from common import hex_bytes, hex_text, on_record

LEGACY = "spl_token_8_0_0_instructions"
TOKEN = "spl_token_2022_8_0_1_instructions"
METADATA = "spl_token_metadata_interface_0_7_0_initialize"
MEMO = "spl_memo_6_0_0_id"


def ok(record):
    return record["outcome"]["result"]["ok"]


def data_byte(record):
    data = bytearray(hex_bytes(ok(record)["data"]))
    data[0] ^= 1
    ok(record)["data"] = hex_text(data)


def id_byte(record):
    data = bytearray(hex_bytes(record["outcome"]["result"]))
    data[-1] ^= 1
    record["outcome"]["result"] = hex_text(data)


def check_flip(record):
    record["outcome"]["result"] = not record["outcome"]["result"]


def extra_allocation(record):
    record["outcome"]["state"]["allocations"] += 1


def lost_drop(record):
    record["outcome"]["state"]["deallocations"] -= 1


def unexpected_drop(record):
    record["outcome"]["state"]["deallocations"] += 1


def wrong_error(record):
    error = record["outcome"]["result"]["err"]
    error["variant"] = ("InvalidArgument" if error["variant"] == "IncorrectProgramId"
                        else "IncorrectProgramId")


def drop_duplicate(record):
    ok(record)["accounts"].pop()


def authority_flag(record):
    account = ok(record)["accounts"][2]
    account["is_signer"] = not account["is_signer"]


def mint_writable(record):
    account = ok(record)["accounts"][1]
    account["is_writable"] = not account["is_writable"]


def utf8_codepoint_length(record):
    data = bytearray(hex_bytes(ok(record)["data"]))
    # The string contains two Unicode scalars but six UTF-8 bytes.
    data[8:12] = len(record["args"]["name"]).to_bytes(4, "little")
    ok(record)["data"] = hex_text(data)


def metadata_alias_removed(record):
    ok(record)["accounts"][1]["pubkey"] = record["args"]["mint"]


def pointer_fields_swapped(record):
    data = bytearray(hex_bytes(ok(record)["data"]))
    data[2:34], data[34:66] = data[34:66], data[2:34]
    ok(record)["data"] = hex_text(data)


CONTROLS = []
for corpus, prefix, builders in (
    (LEGACY, "0", ("mint_to", "burn_checked", "close_account", "set_authority")),
    (TOKEN, "1", ("mint_to", "burn_checked", "close_account", "set_authority",
                   "freeze_account", "thaw_account", "transfer_checked")),
):
    for builder in builders:
        suffix = "/0/0" if builder == "set_authority" else "/0"
        record_id = builder + "/" + prefix + suffix
        CONTROLS.append((f"{corpus}: {builder} tag", corpus, on_record(record_id, data_byte)))
    CONTROLS += [
        (f"{corpus}: native mint constant", corpus, on_record("native_id", id_byte)),
        (f"{corpus}: native mint equality", corpus, on_record("native_check/1", check_flip)),
        (f"{corpus}: retained duplicate signer", corpus,
         on_record(f"close_account/{prefix}/2", drop_duplicate)),
        (f"{corpus}: empty signer authority", corpus,
         on_record(f"close_account/{prefix}/0", authority_flag)),
        (f"{corpus}: allocated data owner", corpus,
         on_record(f"mint_to/{prefix}/0", extra_allocation)),
        (f"{corpus}: successful owners stay live", corpus,
         on_record(f"mint_to/{prefix}/0", unexpected_drop)),
        (f"{corpus}: invalid program has no allocation", corpus,
         on_record("mint_to/2/0", extra_allocation)),
    ]

for builder in ("initialize_account3", "initialize_immutable_owner", "initialize_mint2",
                "initialize_mint_close_authority", "initialize_non_transferable_mint"):
    suffix = "/1/0" if builder in ("initialize_mint2", "initialize_mint_close_authority") else "/1"
    CONTROLS.append((f"{builder}: bytes", TOKEN, on_record(builder + suffix, data_byte)))

CONTROLS += [
    ("Token-2022 program ID", TOKEN, on_record("id", id_byte)),
    ("freeze mint is readonly", TOKEN, on_record("freeze_account/1/0", mint_writable)),
    ("checked burn mint is writable", TOKEN, on_record("burn_checked/1/0", mint_writable)),
    ("nontransferable rejects legacy", TOKEN,
     on_record("initialize_non_transferable_mint/0", wrong_error)),
    ("metadata pointer tag", TOKEN, on_record("metadata_pointer/1/0/0", data_byte)),
    ("metadata pointer field order", TOKEN,
     on_record("metadata_pointer/1/2/0", pointer_fields_swapped)),
    ("metadata pointer field failure destroys metas", TOKEN,
     on_record("metadata_pointer/1/1/0", lost_drop)),
    ("metadata pointer field failure follows allocation", TOKEN,
     on_record("metadata_pointer/1/1/0", extra_allocation)),
    ("metadata pointer program check precedes fields", TOKEN,
     on_record("metadata_pointer/0/1/0", wrong_error)),
    ("metadata discriminator", METADATA, on_record("initialize/0", data_byte)),
    ("metadata UTF-8 byte length", METADATA, on_record("initialize/2", utf8_codepoint_length)),
    ("metadata alias preserved", METADATA, on_record("initialize/2", metadata_alias_removed)),
    ("metadata temporary vector cleanup", METADATA, on_record("initialize/0", lost_drop)),
    ("metadata input string cleanup", METADATA, on_record("initialize/1", lost_drop)),
    ("metadata constructed owners remain allocated", METADATA,
     on_record("initialize/2", extra_allocation)),
    ("memo ID", MEMO, on_record("id", id_byte)),
]
