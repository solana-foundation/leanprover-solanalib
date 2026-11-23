"""Family AccountsV2: semantic corruptions of `solana_account_view_2_0_0` records.

Each change must be rejected as a MISMATCH of its record.
"""

from common import hex_bytes, hex_text, on_record

CORPUS = "solana_account_view_2_0_0"


def acct(state, c):
    return [a for a in state["input"]["accounts"] if "duplicate_of" not in a][c]


def set_after_lamports(r): acct(r["outcome"]["state"], 0)["lamports"] += 1
def marker_off(r): acct(r["outcome"]["state"], 0)["marker"] -= 1
def guard_offset(r): r["outcome"]["state"]["guards"][-1][3] += 1
def obs_bytes(r): r["outcome"]["result"]["ok"]["bytes"] = "00" + r["outcome"]["result"]["ok"]["bytes"][2:]
def zero_backing(r): r["outcome"]["state"]["backing"][0] = "00" * 8
def rent_epoch(r): acct(r["outcome"]["state"], 0)["rent_epoch"] = 1
def err_to_ok(r): r["outcome"]["result"] = {"ok": None}


def unwind_released(r):
    s = r["outcome"]["state"]
    s["guards"][-1] = None
    acct(s, 0)["marker"] = 255


def unwind_reason(r): r["outcome"]["reason"] += "!"


def rollback(r):
    s = r["outcome"]["state"]
    s["backing"][0] = r["state"]["backing"][0]
    acct(s, 0)["data"] = r["state"]["backing"][0]


def deref_offset(r): r["outcome"]["result"]["offset"] += 1


def drop_keeps_marker(r):
    s = r["outcome"]["state"]
    s["guards"][-1] = r["state"]["guards"][-1]
    acct(s, 0)["marker"] = 0


def address_cell(r): r["outcome"]["result"]["cell"] = 1
def epoch_stays(r): r["outcome"]["state"]["owner_epochs"][0] = 0
def generation_stays(r): r["outcome"]["state"]["guards"][-1][2] -= 1
def map_view_len(r): r["outcome"]["state"]["guards"][-1][4] += 1
def obs_data_len(r): r["outcome"]["result"] += 1
def is_signer_flip(r): r["outcome"]["result"] = not r["outcome"]["result"]
def owned_flip(r): r["outcome"]["result"] = not r["outcome"]["result"]
def unwound_exit(r): r["outcome"] = {"exit": "unwound", "reason": "x", "state": r["outcome"]["state"]}


def flip_spare(account, index):
    """Flip one byte of the read-back `spare` of an account (its data area after `data_len`)."""
    spare = bytearray(hex_bytes(account["spare"]))
    spare[index] ^= 0x01
    account["spare"] = hex_text(bytes(spare))
    return account


def entry_len(account):
    """The serialized data length: the data area minus the 10 KiB realloc reserve."""
    return account["data_len"] + len(hex_bytes(account["spare"])) - 10 * 1024


def hidden_byte_after_close(r):
    """`close` changes a data byte it hides (spare byte 2, inside the backing), recorded consistently:
    the read-back spare bytes, their first nonzero byte (still 0) and the recorded backing all agree."""
    s = r["outcome"]["state"]
    flip_spare(acct(s, 0), 2)
    backing = bytearray(hex_bytes(s["backing"][0]))
    backing[2] ^= 0x01
    s["backing"][0] = hex_text(bytes(backing))


def reserve_byte_3000(r):
    """Byte 3000 of the realloc reserve after `close` (the first nonzero byte of the area remains in the backing)."""
    a = acct(r["outcome"]["state"], 0)
    flip_spare(a, entry_len(a) - a["data_len"] + 3000)


def last_spare_byte(r):
    a = acct(r["outcome"]["state"], 0)
    flip_spare(a, len(hex_bytes(a["spare"])) - 1)


def last_spare_byte_consistent(r):
    """The last reserve byte of an open account, with `spare_nonzero_at` updated to match."""
    a = acct(r["outcome"]["state"], 0)
    n = len(hex_bytes(a["spare"]))
    flip_spare(a, n - 1)
    if a["spare_nonzero_at"] is None:
        a["spare_nonzero_at"] = a["data_len"] + n - 1


def alignment_padding(r):
    a = acct(r["outcome"]["state"], 0)
    padding = bytearray(hex_bytes(a["alignment_padding"]))
    padding[0] ^= 0x01
    a["alignment_padding"] = hex_text(bytes(padding))


def duplicate_padding(r):
    d = [a for a in r["outcome"]["state"]["input"]["accounts"] if "duplicate_of" in a][0]
    padding = bytearray(hex_bytes(d["padding"]))
    padding[6] ^= 0x01
    d["padding"] = hex_text(bytes(padding))


def account_count(r): r["outcome"]["state"]["input"]["count"] += 1


# Registered preconditions (`requires`): each mutation keeps the state before the call denoted and
# breaks exactly one decided precondition, which the checker must report as a FAIL.

def dead_guard(r): r["args"]["guard"][1] += 1


def set_mode(mode, marker):
    def change(r):
        s = r["state"]
        s["guards"][r["args"]["guard"][0]][1] = mode
        acct(s, 0)["marker"] = marker
    return change


def shift_view(offset):
    """The view of the guard in the state before starts at `offset` (its length stays): the target or
    write of the script stays inside the slice of the closure but leaves the data of the account."""
    def change(r):
        r["state"]["guards"][r["args"]["guard"][0]][3] = offset
    return change


target_beyond_data = shift_view(4)
write_beyond_backing = shift_view(6)


def lamports_at_2_64(r):
    for s in (r["state"], r["outcome"]["state"]):
        acct(s, 0)["lamports"] = 2 ** 64


# Scripted closures index the slice they receive: a target or a write outside it panics natively.

def shrink_view(r):
    """The view of the guard in the state before shrinks to one byte; the recorded success no longer follows."""
    r["state"]["guards"][r["args"]["guard"][0]][4] = 1


def shared_write(r): r["args"]["callback"]["effects"].append({"write": [0, "00"]})
def reason_changed(r): r["outcome"]["reason"] = r["outcome"]["reason"].replace("10", "9")


def earlier_effect_lost(r): acct(r["outcome"]["state"], 1)["lamports"] = 0


_CASES = [
    ("lamports after set_lamports", "set_lamports/ab/0/free/1", set_after_lamports),
    ("borrow marker after try_borrow", "try_borrow/ab/0/free", marker_off),
    ("guard view offset", "try_borrow/ab/0/free", guard_offset),
    ("observed borrowed bytes", "try_borrow/ab/0/free", obs_bytes),
    ("backing zeroed on close", "close/ab/0/free", zero_backing),
    ("close error turned into success", "close/ab/0/shared1", err_to_ok),
    ("owner epoch not advanced by close", "close/ab/0/free", epoch_stays),
    ("hidden data byte changed by close", "close/ab/0/free", hidden_byte_after_close),
    ("lease released on try_map unwind", "ref_try_map/ab/panic", unwind_released),
    ("try_map unwind reason", "ref_try_map/ab/panic", unwind_reason),
    ("RefMut::try_map writes rolled back", "refmut_try_map/ab/write_err", rollback),
    ("guard generation not advanced by try_map", "ref_try_map/ab/middle", generation_stays),
    ("mapped view length", "ref_try_map/ab/middle", map_view_len),
    ("deref offset of a mapped Ref", "ref_deref/ab/mapped", deref_offset),
    ("RefMut drop keeps the marker", "refmut_drop/ab/whole", drop_keeps_marker),
    ("address cell", "address/ab/2/free", address_cell),
    ("observed data_len", "data_len/ab/0/free", obs_data_len),
    ("is_signer result", "is_signer/c/0/free", is_signer_flip),
    ("owned_by result", "owned_by/ab/0/free/51", owned_flip),
    ("lamports exit turned into an unwind", "lamports/ab/0/free", unwound_exit),
    # `close` is declared in `spare_writes`, so its spare bytes reach the projection of the family.
    ("realloc reserve byte 3000 after close", "close/ab/0/free", reserve_byte_3000),
    ("last spare byte after close", "close/ab/0/free", last_spare_byte),
]

# The runner itself rejects changed region bytes that no family models (FAIL, before any model), and
# spare bytes changed by a function not declared in `spare_writes`; the AccountsV2 projection compares
# them too.
_RUNNER_CASES = [
    ("rent epoch after close", "close/ab/0/free", rent_epoch),
    ("realloc reserve byte 3000 of a closed account (lamports)", "lamports/ab/0/closed", reserve_byte_3000),
    ("last spare byte of a closed account (lamports)", "lamports/ab/0/closed", last_spare_byte),
    ("last spare byte of an open account (set_lamports)", "set_lamports/ab/0/free/1", last_spare_byte_consistent),
    ("alignment padding", "lamports/c/0/free", alignment_padding),
    ("duplicate entry padding", "lamports/ab/0/free", duplicate_padding),
    ("account count", "lamports/ab/0/free", account_count),
]

_CASES += [
    ("Ref::try_map target outside a one-byte guard view", "ref_try_map/ab/middle", shrink_view),
    ("RefMut::try_map write outside a one-byte guard view", "refmut_try_map/ab/write", shrink_view),
    ("Ref::try_map u8 target outside a one-byte guard view", "ref_try_map/ab/byte_last", shrink_view),
    ("Ref::try_map closure writing through a shared slice", "ref_try_map/ab/middle", shared_write),
    ("slice-index panic message of an out-of-range target", "ref_try_map/ab/target_beyond", reason_changed),
    ("effects before an out-of-range write undone", "refmut_try_map/ab/write_beyond", earlier_effect_lost),
]

_PRE = "outside the registered precondition"
# Expected messages below are exact diagnostics from the Lean checker.
_PRECONDITION_CASES = [
    ("Ref::release of a dead guard", "ref_drop/ab/whole", dead_guard, "the guard is not live"),
    ("RefMut::release of a dead guard", "refmut_drop/ab/whole", dead_guard, "the guard is not live"),
    ("Ref::try_map on a dead guard", "ref_try_map/ab/whole", dead_guard, "the guard is not live"),
    ("RefMut::try_map on a dead guard", "refmut_try_map/ab/whole", dead_guard, "the guard is not live"),
    ("Ref::try_map on an exclusive guard", "ref_try_map/ab/whole", set_mode("exclusive", 0),
     "the guard mode does not match the family mode"),
    ("RefMut::try_map on a shared guard", "refmut_try_map/ab/whole", set_mode("shared", 254),
     "the guard mode does not match the family mode"),
    ("Ref::try_map callback target beyond the data (CallbackSafe)", "ref_try_map/ab/whole", target_beyond_data,
     "the scripted callback is not CallbackSafe"),
    ("RefMut::try_map callback write beyond the backing (CallbackSafe)", "refmut_try_map/ab/write",
     write_beyond_backing, "the scripted callback is not CallbackSafe"),
    ("try_borrow observation at lamports 2^64 (Valid)", "try_borrow/ab/0/free", lamports_at_2_64,
     "the observed account is not Valid"),
    ("try_borrow_mut observation at lamports 2^64 (Valid)", "try_borrow_mut/ab/0/free", lamports_at_2_64,
     "the observed account is not Valid"),
]

CONTROLS = [(label, CORPUS, on_record(rid, change)) for label, rid, change in _CASES] + [
    (label, CORPUS, on_record(rid, change), f"FAIL {CORPUS}/{rid}: {_PRE}: {says}")
    for label, rid, change, says in _PRECONDITION_CASES] + [
    (label, CORPUS, on_record(rid, change), f"FAIL {CORPUS}/{rid}") for label, rid, change in _RUNNER_CASES]
