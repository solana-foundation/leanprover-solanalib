"""Controls for exact old-version references and their observable outcomes.

Most allocator/accessor counters are native assertions. The owning-error
fixture additionally records them as state and checks the registered cleanup
relation. Other mutations check the result, source range and retained receiver.
"""

from common import hex_bytes, hex_text, on_record

TOKEN = "token_state_8_0_1"
OLDER = "token_state_interface_2_1_0"
INTERFACE = "token_state_interface_3_0_1"


def result(value):
    def mutate(record): record["outcome"]["result"] = value
    return mutate


def ok_field(name, value):
    def mutate(record): record["outcome"]["result"]["ok"][name] = value
    return mutate


def metadata_field(name, value):
    def mutate(record): record["outcome"]["result"][name] = value
    return mutate


def accept_empty_tail(record):
    record["outcome"]["result"] = {"ok": {
        "base": hex_text(hex_bytes(record["state"])[:82]),
        "tlv": "", "origin": "input", "offset": 166,
    }}


def retain_changed_fee(record):
    record["outcome"]["state"]["epoch"] = 7


def change_epoch_receiver(record):
    state = bytearray(hex_bytes(record["outcome"]["state"]))
    state[0] ^= 1
    record["outcome"]["state"] = hex_text(state)


def cleanup_state(name, value):
    def mutate(record): record["outcome"]["state"][name] = value
    return mutate


INVALID_DATA = {"err": {"variant": "InvalidAccountData", "fields": []}}
CASES = [
    ("8.0.1 rejects the marker-only tail", TOKEN, "unpack/true/length_166", accept_empty_tail),
    ("2.1.0 admits the marker-only tail", OLDER, "unpack/true/length_166", result(INVALID_DATA)),
    ("3.0.1 admits the marker-only tail", INTERFACE, "unpack/true/length_166", result(INVALID_DATA)),
    ("unpack preserves borrowed origin", TOKEN, "unpack/true/length_167", ok_field("origin", "static")),
    ("unpack preserves tail offset", TOKEN, "unpack/true/length_167", ok_field("offset", 165)),
    ("TLV list retains duplicates", TOKEN, "types/duplicates", result({"ok": [7]})),
    ("TLV list rejects missing payload", TOKEN, "types/past_end", result({"ok": [7]})),
    ("older TLV list retains duplicates", OLDER, "types/duplicates", result({"ok": [7]})),
    ("typed extension keeps the source offset", TOKEN, "get_fee/fee", ok_field("offset", 3)),
    ("delegate zero becomes None", TOKEN, "delegate/delegate_zero", result({"some": "01" * 32})),
    ("hook uses its program key", TOKEN, "hook/hook_some", result(None)),
    ("delegate consumes its owning error", TOKEN, "delegate/owning_error", cleanup_state("deallocations", 0)),
    ("hook consumes its owning error", TOKEN, "hook/owning_error", cleanup_state("deallocations", 0)),
    ("owning-error getter is called once", TOKEN, "delegate/owning_error", cleanup_state("getter_calls", 0)),
    ("owning error preserves its allocation", TOKEN, "hook/owning_error", cleanup_state("allocations", 0)),
    ("variable length excludes unused backing", TOKEN, "new_length/sentinel_trailing/80/false", result({"ok": 254})),
    ("measurement error precedes malformed TLV", TOKEN, "new_length/past_end/80/true", result(INVALID_DATA)),
    ("fixed lengths deduplicate", TOKEN, "size/1", result({"ok": 174})),
    ("fixed lengths reject variable metadata", OLDER, "size/2", result({"ok": 174})),
    ("required-init retains duplicates and order", OLDER, "required/4", result([13, 7, 2, 15, 27])),
    ("required-init nontransferable push order", OLDER, "required/4", result([7, 13, 2, 13, 7, 15, 27])),
    ("narrowing precedes zero maximum cap", TOKEN, "fee/false/65535/0/18446744073709551615", result({"some": 0})),
    ("inverse zero amount precedes invalid-rate subtraction", TOKEN, "fee/true/65535/0/0", result(None)),
    ("fee retains its receiver", TOKEN, "fee/true/65535/0/0", retain_changed_fee),
    ("epoch equality selects newer reference", TOKEN, "select/10/10", metadata_field("field", "older")),
    ("epoch fee equality applies newer value", TOKEN, "epoch/false/10/10", result({"some": 3})),
    ("inverse epoch equality applies newer value", TOKEN, "epoch/true/10/10", result({"some": 3})),
    ("epoch fee retains unrelated receiver fields", TOKEN, "epoch/false/10/10", change_epoch_receiver),
    ("inverse epoch excess rate is not zero fee", TOKEN,
     "epoch_boundary/positive_excess_rate/true/10", result({"some": 0})),
    ("inverse epoch checked addition does not wrap", TOKEN,
     "epoch_boundary/full_rate_overflow/true/10", result({"some": 0})),
    ("epoch fee narrowing precedes zero cap", TOKEN,
     "epoch_boundary/raw_fee_overflow/false/10", result({"some": 0})),
    ("inverse epoch zero input precedes invalid rate", TOKEN,
     "epoch_boundary/zero_excess_rate/true/10", result(None)),
    ("uninitialized account is not frozen", TOKEN, "is_frozen/0", result(True)),
    ("metadata default clears its mint", TOKEN, "metadata/default", metadata_field("mint", "01" * 32)),
    ("metadata default empties its string", TOKEN, "metadata/default", metadata_field("name", "x")),
    ("metadata default empties additional entries", TOKEN, "metadata/default", metadata_field("additional", [["a", "b"]])),
    ("metadata empty constructors retain zero capacities", TOKEN, "metadata/default", metadata_field("capacities", [1, 0, 0, 0])),
]

CONTROLS = [(label, corpus, on_record(record, mutate)) for label, corpus, record, mutate in CASES]


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('token_state_8_0_1', 'token_state_interface_2_1_0', 'token_state_interface_3_0_1')]
