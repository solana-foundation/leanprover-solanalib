"""Mutations of the decided result of the concrete Mint clone, receiver and layout.

Pack82 is a field recording format. Heap counters are auxiliary native
assertions; these Lean controls do not claim to decide allocator observations.
"""

from common import on_record

CORPUS = "token_state_interface_3_1_1"


def byte_changed(where, offset, value):
    def mutate(record):
        raw = bytearray.fromhex(record["outcome"][where])
        raw[offset] = value
        record["outcome"][where] = raw.hex()
    return mutate


def layout_size(record): record["layout"]["size"] = 82
def layout_alignment(record): record["layout"]["alignment"] = 4
def layout_offset(record): record["layout"]["offsets"][-1] = 50


CASES = [
    ("clone mint authority", "clone/1/3", byte_changed("result", 4, 9)),
    ("clone supply", "clone/1/3", byte_changed("result", 36, 2)),
    ("clone decimals", "clone/1/3", byte_changed("result", 44, 9)),
    ("clone initialized flag", "clone/1/3", byte_changed("result", 45, 0)),
    ("clone freeze authority", "clone/1/3", byte_changed("result", 50, 9)),
    ("clone changes receiver", "clone/1/3", byte_changed("state", 36, 2)),
    ("clone None becomes Some zero", "clone/0/0", byte_changed("result", 0, 1)),
    ("clone source size confused with Pack82", "clone/1/3", layout_size),
    ("clone source alignment", "clone/1/3", layout_alignment),
    ("clone source field offset", "clone/1/3", layout_offset),
]

CONTROLS = [(label, CORPUS, on_record(record, mutate)) for label, record, mutate in CASES]
