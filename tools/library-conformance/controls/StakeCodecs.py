"""Reject changed alias offsets, imposed lookup limits, counters and cleanup."""
from common import on_record


def alias_offset(record):
    record["outcome"]["result"]["ok"]["addresses"]["address"] += 1


def impose_limit(record):
    record["outcome"]["result"] = {"err": "InvalidAccountData"}


def wrong_enum_order(record):
    record["outcome"]["result"] = {"err": "InvalidAccountData"}


def counter(record):
    record["outcome"]["result"]["ok"] += 1


def omit_cleanup(record):
    record["outcome"]["state"].pop()


def manufacture_error_allocation(record):
    record["outcome"]["state"] += ["alloc:24:8:0", "dealloc:24:8:0"]


def reverse_error_cleanup(record):
    record["outcome"]["state"].reverse()


def wrong_panic(record):
    record["outcome"]["reason"] += " changed"


def wrong_flag(record):
    record["outcome"]["result"]["accounts"][-1]["is_signer"] = False


def reverse_merge_accounts(record):
    metas = record["outcome"]["result"][0]["accounts"]
    metas[0], metas[1] = metas[1], metas[0]


def reorder_split(record):
    instructions = record["outcome"]["result"]
    instructions[0], instructions[1] = instructions[1], instructions[0]


def shorten_split(record):
    record["outcome"]["result"].pop(0)


def change_bytes(record):
    data = record["outcome"]["result"]["data"]
    record["outcome"]["result"]["data"] = data[:-2] + ("00" if data[-2:] != "00" else "01")


CONTROLS = []
for corpus in ["stake_codecs_program", "stake_codecs_interface"]:
    CONTROLS += [
        ("borrowed suffix keeps offset 56", corpus, on_record("lookup-addresses-true-1-1", alias_offset)),
        ("deserialize does not enforce 256 addresses", corpus, on_record("lookup-addresses-false-257-0", impose_limit)),
        ("enum decoding precedes suffix size", corpus, on_record("lookup-enum-3", wrong_enum_order)),
        ("bincode error box is destroyed before return", corpus, on_record("lookup-enum-0", omit_cleanup)),
        ("Uninitialized does not allocate a decoder error", corpus, on_record("lookup-enum-3", manufacture_error_allocation)),
        ("owned diagnostic cleanup follows decoding", corpus, on_record("lookup-enum-5", reverse_error_cleanup)),
        ("count every write and write_all byte", corpus, on_record("packed-len-4", counter)),
        ("serializer cleanup survives error", corpus, on_record("packed-len-6", omit_cleanup)),
        ("serializer cleanup survives unwind", corpus, on_record("packed-len-8", omit_cleanup)),
        ("unwind retains selected panic", corpus, on_record("packed-len-7", wrong_panic)),
    ]
CONTROLS += [
    ("Pack drops after false initialization", "stake_codecs_legacy", on_record("pack-1-false", omit_cleanup)),
    ("Pack query unwind drops decoded value", "stake_codecs_legacy", on_record("pack-4-false", omit_cleanup)),
    ("Pack forwards destructor unwind", "stake_codecs_legacy", on_record("pack-5-false", wrong_panic)),
    ("initialize retains exact lockup bytes", "stake_codecs_legacy", on_record("initialize-0", change_bytes)),
    ("authorize optional custodian is a signer", "stake_codecs_legacy", on_record("authorize-0-staker-true", wrong_flag)),
    ("delegate authority is a signer", "stake_codecs_legacy", on_record("delegate-0", wrong_flag)),
    ("set_lockup encodes all optional fields", "stake_codecs_legacy", on_record("set-lockup-0-7", change_bytes)),
    ("merge preserves destination/source order", "stake_codecs_legacy", on_record("merge-0", reverse_merge_accounts)),
    ("split allocates before assigning", "stake_codecs_legacy", on_record("split-0-0", reorder_split)),
    ("split returns all three instructions", "stake_codecs_legacy", on_record("split-0-0", shorten_split)),
]
