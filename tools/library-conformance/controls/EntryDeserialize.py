"""Corrupt byte layout, alias identities, allocation order and initialized prefixes.

Malformed input controls exercise the decided unsafe precondition without invoking Rust
on that input. Native failure records use real allocator failure in an isolated child.
"""

from common import hex_bytes, hex_text, on_record, outside_precondition

SDK = "solana_program_entrypoint_2_3_0_deserialize"
PIN = "pinocchio_0_9_2_deserialize"


def account(field, value, index=0):
    def change(record):
        record["outcome"]["result"]["accounts"][index][field] = value
    return change


def view(field, value):
    def change(record):
        record["outcome"]["result"]["views"][field] = value
    return change


def byte(offset, value, before=False):
    def change(record):
        state = record["state"] if before else record["outcome"]["state"]
        raw = bytearray(hex_bytes(state["bytes"]))
        raw[offset] = value
        state["bytes"] = hex_text(bytes(raw))
    return change


def output(index, value):
    def change(record):
        record["outcome"]["state"]["outputs"][index] = value
    return change


def allocation(index, field, value):
    def change(record):
        record["outcome"]["result"]["allocations"][index][field] = value
    return change


def wrong_terminal(record):
    record["outcome"]["reason"] = "control"


def incomplete(record):
    record["state"]["bytes"] = "00"


def fail(corpus, identifier):
    return f"FAIL {corpus}/{identifier}"


def outside(corpus, identifier):
    return f"{fail(corpus, identifier)}: the input is outside the registered precondition"


CONTROLS = [
    ("SDK rejects an incomplete input", SDK,
     outside_precondition("empty", incomplete), outside(SDK, "empty")),
    *[(f"Pinocchio capacity {capacity} rejects an incomplete input", PIN,
       outside_precondition(identifier, incomplete), outside(PIN, identifier))
      for capacity, identifier in [(0, "empty/capacity_0"), (1, "one_3/capacity_1"),
                                   (2, "one_3/capacity_2"), (5, "one_3/capacity_5"),
                                   (64, "one_3/capacity_64"), (254, "maximum/capacity_254")]],
    ("SDK rejects a first-slot duplicate", SDK,
     outside_precondition("aliases", byte(8, 0, before=True)), outside(SDK, "aliases")),
    ("SDK duplicate Rc identity", SDK,
     on_record("aliases", account("lamports_cell", 2, 1)), fail(SDK, "aliases")),
    ("SDK duplicate owner identity", SDK,
     on_record("aliases", account("owner_ref", 1, 1)), fail(SDK, "aliases")),
    ("SDK duplicate Rc count", SDK,
     on_record("aliases", account("data_strong", 2, 0)), fail(SDK, "aliases")),
    ("SDK normalized nonzero flag", SDK,
     on_record("one_3", account("signer", False)), "MISMATCH " + SDK + "/one_3"),
    ("SDK data pointer identity", SDK,
     on_record("one_3", account("data_offset", 97)), fail(SDK, "one_3")),
    ("SDK original-length recording", SDK,
     on_record("one_3", byte(12, 0)), fail(SDK, "one_3")),
    ("SDK hidden reserve preserved", SDK,
     on_record("one_3", byte(99, 0)), fail(SDK, "one_3")),
    ("SDK alignment padding preserved", SDK,
     on_record("one_3", byte(10339, 0)), fail(SDK, "one_3")),
    ("SDK lamports allocation precedes recording", SDK,
     on_record("one_3", allocation(1, "first_original_length", 3)), "MISMATCH " + SDK + "/one_3"),
    ("SDK data allocation follows recording", SDK,
     on_record("one_3", allocation(2, "first_original_length", 0)), "MISMATCH " + SDK + "/one_3"),
    ("SDK actual allocation layout", SDK,
     on_record("one_3", allocation(2, "size", 32)), "MISMATCH " + SDK + "/one_3"),
    ("SDK terminal reason", SDK,
     on_record("allocation_failure/2", wrong_terminal), "MISMATCH " + SDK + "/allocation_failure/2"),
    ("Pinocchio duplicate pointer", PIN,
     on_record("aliases/capacity_64", output(1, 10360)), fail(PIN, "aliases/capacity_64")),
    ("Pinocchio retained output suffix", PIN,
     on_record("one_3/capacity_64", output(63, 8)), "MISMATCH " + PIN + "/one_3/capacity_64"),
    ("Pinocchio does not record original length", PIN,
     on_record("one_3/capacity_64", byte(12, 3)), fail(PIN, "one_3/capacity_64")),
    ("Pinocchio instruction after skipped accounts", PIN,
     on_record("aliases/capacity_1", view("instruction_offset", 10360)),
     "MISMATCH " + PIN + "/aliases/capacity_1"),
    ("Pinocchio raw nonzero flag", PIN,
     on_record("one_3/capacity_2", account("signer", False)), fail(PIN, "one_3/capacity_2")),
]

# The generic first-leaf mutation changes a redundant capacity/count or a getter
# field, which the typed reader rejects before deciding the relation. These
# offsets remain well-formed source values and exercise the registered reference.
SEMANTIC = [
    (SDK, on_record("empty", view("instruction_offset", 15)),
     "Change the returned slice identity while keeping the recorded vector shape well-formed."),
    *[(PIN, on_record(identifier, view("instruction_offset", 15)),
       "Change the returned slice identity while keeping the initialized prefix and getter readback well-formed.")
      for identifier in ["empty/capacity_0", "empty/capacity_64", "one_empty/capacity_1",
                         "one_empty/capacity_2", "one_empty/capacity_5", "maximum/capacity_254"]],
]
