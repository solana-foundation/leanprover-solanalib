"""Alter source-visible address outputs, guard order, callbacks and preserved state."""
from common import on_record


def set_result(value):
    def change(record):
        record["outcome"]["result"] = value
    return change


def partial_reply(record):
    record["state"]["syscalls"]["replies"][0]["data"] = "0102030405"


def flip_result_byte(record):
    result = record["outcome"]["result"]
    key = "ok" if "ok" in result else "address"
    raw = bytearray.fromhex(result[key])
    raw[-1] ^= 1
    result[key] = raw.hex()


def bump_changed(record):
    record["outcome"]["result"]["bump"] = 255


def initial_bump(record):
    record["outcome"]["state"]["syscalls"]["log"][0]["bump"] = 254


def seed_order(record):
    log = record["outcome"]["state"]["syscalls"]["log"][0]
    log["seeds"] = list(reversed(log["seeds"]))


def program_changed(record):
    record["outcome"]["state"]["syscalls"]["log"][0]["program_id"] = "00" * 32


def callback_on_guard(record):
    record["outcome"]["state"]["syscalls"]["replies"].pop(0)


def drop_hash_field(record):
    record["outcome"]["state"]["syscalls"]["log"][0]["fields"].pop()


def io_kind(kind):
    def change(record):
        record["outcome"]["result"]["err"]["kind"] = kind
    return change


def io_message(record):
    record["outcome"]["result"]["err"]["message"] = "reader stopped"


def reader_position(record):
    record["outcome"]["state"]["position"] = record["state"]["position"]


def reader_default_loop(record):
    record["outcome"]["state"]["read_calls"] = 1


def reader_initial(record):
    record["outcome"]["state"]["initial"] = "01" + "00" * 31


def writer_rollback(record):
    record["outcome"]["state"]["written"] = record["state"]["written"]


def writer_byte_calls(record):
    chunk = record["outcome"]["state"]["calls"].pop()
    record["outcome"]["state"]["calls"] = [chunk[i:i + 2] for i in range(0, len(chunk), 2)]


def legacy_cursor(record):
    record["outcome"]["result"][1] = ""


def terminal_detail(record):
    record["outcome"]["detail"] = "different terminal callback"


def panic_to_error(record):
    record["outcome"] = {"exit": "returned", "result": {"err": "IllegalOwner"},
                         "state": record["outcome"]["state"]}


def find_panic_to_return(record):
    record["outcome"] = {"exit": "returned",
                         "result": {"address": "00" * 32, "bump": 255},
                         "state": record["outcome"]["state"]}


_CASES = []
for corpus in ["address_profiles_260", "address_profiles_261"]:
    _CASES += [
        ("unsigned ordering", corpus, "cmp/1/1", set_result("Less")),
        ("lexicographic last byte", corpus, "cmp/2/1", set_result("Equal")),
        ("create initialized success", corpus, "create/empty/ok", partial_reply, "outside the precondition"),
        ("loader initialized success", corpus, "solana_loader_v3_interface::get_program_data_address/ok",
         partial_reply, "outside the precondition"),
        ("ATA initialized success", corpus,
         "spl_associated_token_account_interface::address::get_associated_token_address_with_program_id/ok",
         partial_reply, "outside the precondition"),
        ("create guard callback", corpus, "create/count17/ok", callback_on_guard),
        ("create terminal detail", corpus, "create/empty/terminal", terminal_detail),
        ("loader program id", corpus, "solana_loader_v3_interface::get_program_data_address/ok", program_changed),
        ("ATA seed order", corpus,
         "spl_associated_token_account_interface::address::get_associated_token_address_with_program_id/ok", seed_order),
    ]
for corpus in ["pubkey_profiles_221", "pubkey_profiles_240", "program_pubkey_115", "program_pubkey_118"]:
    _CASES += [
        ("zeroed create untouched bytes", corpus, "create/empty/partial", flip_result_byte),
        ("zeroed find untouched bytes", corpus, "find/empty/partial", flip_result_byte),
        ("returned zero bump", corpus, "find/empty/bump0", bump_changed),
        ("initial bump255", corpus, "find/count17/ok", initial_bump),
        ("seed UTF8 guard order", corpus, "seed/both_guards/false", set_result({"err": "IllegalOwner"})),
        ("hash vector boundaries", corpus, "seed/length32/false", drop_hash_field),
        ("partial writer retained", corpus, "serialize/error", writer_rollback),
        ("writer unwind retained", corpus, "serialize/unwind", writer_rollback),
        ("whole slice writer override", corpus, "serialize/ok", writer_byte_calls),
    ]
for corpus in ["pubkey_profiles_221", "pubkey_profiles_240", "program_pubkey_118", "address_profiles_261"]:
    kind = "InvalidInput" if corpus == "address_profiles_261" else "InvalidData"
    _CASES += [
        ("selected Borsh EOF kind", corpus, "deserialize_reader/eof", io_kind(kind)),
        ("EOF message remapped", corpus, "deserialize_reader/eof", io_message),
        ("reader partial error retained", corpus, "deserialize_reader/eof", reader_position),
        ("reader unwind retained", corpus, "deserialize_reader/unwind", reader_position),
        ("read_exact override", corpus, "deserialize_reader/ok", reader_default_loop),
        ("zero initial read buffer", corpus, "deserialize_reader/ok", reader_initial),
        ("short successful override", corpus, "deserialize_reader/short_ok", flip_result_byte),
    ]
for corpus in ["program_pubkey_115", "program_pubkey_118"]:
    _CASES.append(("legacy status2 panic", corpus, "create/empty/status2", panic_to_error))
_CASES.append(("legacy short slice retained", "program_pubkey_115", "deserialize/31", legacy_cursor))

# The registered Pubkey profile keeps its own guards and modern status decode.
_CASES += [
    ("Pubkey count guard keeps provider untouched", "pubkey_profiles_240",
     "create/count17/ok", callback_on_guard),
    ("Pubkey length guard keeps provider untouched", "pubkey_profiles_240",
     "create/length33/ok", callback_on_guard),
    ("Pubkey create ordered seeds", "pubkey_profiles_240", "create/ordered/ok", seed_order),
    ("Pubkey create exact program", "pubkey_profiles_240", "create/ordered/ok", program_changed),
    ("Pubkey status one is InvalidSeeds", "pubkey_profiles_240",
     "create/empty/status1", set_result({"err": "IllegalOwner"})),
    ("Pubkey status two is IllegalOwner", "pubkey_profiles_240",
     "create/empty/status2", set_result({"err": "InvalidSeeds"})),
    ("Pubkey unknown create status panics", "pubkey_profiles_240",
     "create/empty/status3", panic_to_error),
    ("Pubkey find failure panics", "pubkey_profiles_240", "find/empty/status1", find_panic_to_return),
    ("Pubkey create terminal detail", "pubkey_profiles_240", "create/empty/terminal", terminal_detail),
    ("Pubkey find terminal detail", "pubkey_profiles_240", "find/empty/terminal", terminal_detail),
    ("Pubkey hash terminal detail", "pubkey_profiles_240", "seed/empty/true", terminal_detail),
]


def _control(label, corpus, record_id, change, expected=None):
    mutation = on_record(record_id, change)
    if expected is None:
        return label, corpus, mutation
    return label, corpus, mutation, f"FAIL {corpus}/{record_id}: {expected}"


def eof_payload_drops(count):
    def change(record):
        record["outcome"]["state"]["drops"] = count
    return change


def eof_payload_unwind_to_return(record):
    record["outcome"] = {
        "exit": "returned",
        "result": {"err": {"kind": "InvalidInput", "message": "Unexpected length of input"}},
        "state": record["outcome"]["state"],
    }


def eof_payload_reason(record):
    record["outcome"]["reason"] = "chosen read unwind"


_CASES += [
    ("EOF payload destruction mutates shared state", "pubkey_profiles_240",
     "deserialize_reader/eof_drop", eof_payload_drops(0)),
    ("EOF payload is destroyed exactly once", "pubkey_profiles_240",
     "deserialize_reader/eof_drop", eof_payload_drops(2)),
    ("EOF payload unwind retains destruction state", "pubkey_profiles_240",
     "deserialize_reader/eof_drop_unwind", eof_payload_drops(0)),
    ("EOF payload unwind is not an ordinary error", "pubkey_profiles_240",
     "deserialize_reader/eof_drop_unwind", eof_payload_unwind_to_return),
    ("EOF payload unwind retains its own reason", "pubkey_profiles_240",
     "deserialize_reader/eof_drop_unwind", eof_payload_reason),
]


CONTROLS = [_control(*case) for case in _CASES]
