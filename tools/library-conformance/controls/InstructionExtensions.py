"""Corrupt exact metadata, owned results, retained borrows and allocation exits."""

from common import hex_bytes, hex_text, on_record


def flag(r):
    r["outcome"]["result"]["is_writable"] = not r["outcome"]["result"]["is_writable"]


def source_flag(r):
    r["outcome"]["state"]["is_signer"] = not r["outcome"]["state"]["is_signer"]


def change_data(r):
    value = bytearray(hex_bytes(r["outcome"]["result"]["data"]))
    value[-1] ^= 1
    r["outcome"]["result"]["data"] = hex_text(value)


def change_source(r):
    r["outcome"]["state"]["data"] = "ff"


def drop_meta(r):
    r["outcome"]["result"]["accounts"].pop()


def reorder_meta(r):
    r["outcome"]["result"]["accounts"].reverse()


def wrong_seed_length(r):
    value = bytearray(hex_bytes(r["outcome"]["result"]["data"]))
    value[36] = 3  # Three characters, but four UTF-8 bytes in a\0é.
    r["outcome"]["result"]["data"] = hex_text(value)


def readonly_base(r):
    r["outcome"]["result"]["accounts"][2]["is_writable"] = True


def abort_to_unwind(r):
    r["outcome"] = {"exit": "unwound", "reason": "allocation", "state": None}


def terminal_reason(r):
    r["outcome"]["reason"] = "serialization"


CONTROLS = [
    ("instruction clone retained source bytes", "instruction_extensions_legacy_15",
     on_record("clone/duplicates", change_source)),
    ("instruction clone allocator abort is not unwind", "instruction_extensions_legacy_15",
     on_record("clone/oom/2", abort_to_unwind)),
    ("seeded long input remains encoded", "instruction_extensions_legacy_15",
     on_record("seed/33/max/alias", change_data)),
    ("metadata clone retained source", "instruction_extensions_legacy_18",
     on_record("meta-clone/pattern/true/false", source_flag)),
    ("seeded base stays readonly", "instruction_extensions_legacy_18",
     on_record("seed/nul-utf8/pattern/alias", readonly_base)),
    ("metadata constructor writable bit", "instruction_extensions_bincode",
     on_record("meta/pattern/true/true", flag)),
    ("metadata clone readonly bit", "instruction_extensions_v2",
     on_record("meta-clone/pattern/true/false", flag)),
    ("seeded alias keeps third account", "instruction_extensions_v2",
     on_record("seed/nul-utf8/pattern/alias", drop_meta)),
    ("seeded UTF-8 byte length", "instruction_extensions_v2_2",
     on_record("seed/nul-utf8/pattern/alias", wrong_seed_length)),
    ("seeded temporary allocation abort", "instruction_extensions_v2",
     on_record("system/oom/2", terminal_reason)),
    ("prefund wincode amount and owner", "instruction_extensions_wincode",
     on_record("prefund/max/max", change_data)),
]

# Check the remaining branches of the retained 2.3.3 / 1.0.0 profile.
CONTROLS += [
    ("selected metadata constructor writable bit", "instruction_extensions_v2",
     on_record("meta/pattern/true/true", flag)),
    ("selected metadata clone retained source", "instruction_extensions_v2",
     on_record("meta-clone/pattern/true/false", source_flag)),
    ("selected seeded UTF-8 byte length", "instruction_extensions_v2",
     on_record("seed/nul-utf8/pattern/alias", wrong_seed_length)),
    ("selected seeded base stays readonly", "instruction_extensions_v2",
     on_record("seed/nul-utf8/pattern/alias", readonly_base)),
    ("selected seeded long input remains encoded", "instruction_extensions_v2",
     on_record("seed/33/max/alias", change_data)),
    ("selected seeded allocation abort is not unwind", "instruction_extensions_v2",
     on_record("system/oom/2", abort_to_unwind)),
    ("selected seeded distinct account order", "instruction_extensions_v2",
     on_record("seed/distinct", reorder_meta)),
]
