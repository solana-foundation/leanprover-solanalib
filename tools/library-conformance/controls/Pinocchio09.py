"""Semantic controls of exact Pinocchio 0.9.2 and pinocchio-log 0.5.1 calls."""

from common import flip_spare, hex_bytes, hex_text, on_record, outside_precondition

A = "pinocchio_0_9_2_accounts"
V = "pinocchio_0_9_2_values"
L = "pinocchio_log_0_5_1"


def set_at(path, value):
    def change(record):
        target = record
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
    return change


def flip_result(record):
    record["outcome"]["result"] = not record["outcome"]["result"]


def after_account(record):
    return record["outcome"]["state"]["input"]["accounts"][0]


def account(key, value):
    return lambda record: after_account(record).__setitem__(key, value)


def flip_data(record):
    a = after_account(record)
    data = bytearray(hex_bytes(a["data"]))
    data[-1] ^= 1
    a["data"] = hex_text(data)


def changed_spare(record):
    flip_spare(after_account(record), 100)


def borrowed_map(record):
    # The callback mutates the held data. A shared lease forbids that change.
    record["state"]["guards"][0]["mode"] = "shared"
    record["state"]["input"]["accounts"][0]["marker"] = 254


def uninitialized_clock(record):
    record["state"]["syscalls"]["replies"][0]["data"] = ""


PRE = "registered requires does not hold"

CONTROLS = [
    ("key keeps its field pointer", A, on_record("key/ordinary", set_at(["outcome", "result", "offset"], 40))),
    ("owner keeps its current bytes", A, on_record("owner/ordinary", set_at(["outcome", "result", "bytes"], "00" * 32))),
    *[(f"{name} Boolean", A, on_record(f"{name}/ordinary", flip_result))
      for name in ["is_signer", "is_writable", "is_owned_by"]],
    ("lamports value", A, on_record("lamports/ordinary", set_at(["outcome", "result"], 41))),
    ("data length value", A, on_record("data_len/ordinary", set_at(["outcome", "result"], 4))),
    *[(f"{name} lease byte", A, on_record(f"{name}/free", account("marker", 255)))
      for name in ["try_borrow_data", "try_borrow_mut_data", "try_borrow_mut_lamports"]],
    ("new guard identity", A, on_record("try_borrow_data/free", set_at(["outcome", "result", "ok", "guard"], 9))),
    ("seventh shared credit is exhausted", A, on_record("try_borrow_data/shared7", set_at(["outcome", "result"], {"ok": {"guard": 7, "generation": 0}}))),
    ("borrow error precedes size conversion", A, on_record("resize/borrow_before_conversion", set_at(["outcome", "result", "err"], "InvalidRealloc"))),
    ("resize clears growth", A, on_record("resize/grow", flip_data)),
    ("resize keeps unrelated spare bytes", A, on_record("resize/shrink", changed_spare)),
    ("resize commits its signed counter", A, on_record("resize/grow", account("padding", 0))),
    ("resize reaches exact zero length", A, on_record("resize/grow", set_at(["outcome", "state", "syscalls", "log", 0, "n"], 3))),
    *[(f"{case} target", A, on_record(f"guard/{case}", set_at(["outcome", "result", "len"], 2)))
      for case in ["shared", "exclusive_shared_view", "exclusive_mutable_view"]],
    *[(f"{case} releases lease", A, on_record(f"guard/{case}", account("marker", 247)))
      for case in ["drop_shared", "drop_exclusive"]],
    ("mapped guard generation", A, on_record("map/subslice", set_at(["outcome", "result", "generation"], 0))),
    ("mapped target range", A, on_record("map/subslice", set_at(["outcome", "state", "guards", 0, "offset"], 0))),
    ("unwinding map retains its lease", A, on_record("map/unwind_leaks_lease", account("marker", 255))),
    ("unwinding map retains callback mutation", A, on_record("map/unwind_leaks_lease", account("data", "0a141e"))),
    ("duplicate aliases remain identical", A, on_record("key/alias_exclusive_noncanonical_flags", set_at(["outcome", "state", "input", "accounts", 1, "duplicate_of"], 1))),
    *[(f"meta {i} flags", V, on_record(f"meta/{i}/0", set_at(["outcome", "result", "is_writable"], i < 2)))
      for i in range(4)],
    ("meta address identity", V, on_record("meta/0/0", set_at(["outcome", "result", "reference"], 14))),
    ("seed keeps the array size", V, on_record("seed/64", set_at(["outcome", "result", "length"], 32))),
    ("zero seed keeps pointer identity", V, on_record("seed/0", set_at(["outcome", "result", "reference"], 20))),
    ("pubkey word boundary equality", V, on_record("pubkey_eq/Some(8)", flip_result)),
    ("Clock value", V, on_record("clock_get/ok/values", set_at(["outcome", "result", "ok", "slot"], 0))),
    ("Clock terminal detail", V, on_record("clock_get/terminated", set_at(["outcome", "detail"], "altered"))),
    ("default empty prefix", L, on_record("default/3", set_at(["outcome", "result", "len"], 1))),
    ("append keeps receiver identity", L, on_record("append/str/3/exact", set_at(["outcome", "result"], 18))),
    ("append truncation marker", L, on_record("append/str/1/truncates", set_at(["outcome", "state", "bytes"], "61"))),
    ("append splits UTF8 by bytes", L, on_record("append/str/2/utf8_split", set_at(["outcome", "state", "bytes"], "4040"))),
    ("u64 keeps decimal prefix", L, on_record("append/u64/5/18446744073709551615", set_at(["outcome", "state", "bytes"], "3531363140"))),
    ("full append drops operand", L, on_record("append/probe/3/full_drops", set_at(["outcome", "state", "events"], []))),
    ("formatter unwind keeps old length", L, on_record("append/probe/3/write_unwind", set_at(["outcome", "state", "len"], 1))),
    ("formatter unwind drops operand", L, on_record("append/probe/3/write_unwind", set_at(["outcome", "state", "events"], ["write"]))),
    ("drop unwind reason", L, on_record("append/probe/3/drop_unwind", set_at(["outcome", "reason"], "formatter panic"))),
    ("terminal callback detail", L, on_record("append/probe/3/write_terminal", set_at(["outcome", "detail", "column"], 4))),
    ("log request retained", L, on_record("log/200/ascii", set_at(["outcome", "state", "syscalls", "log"], []))),
    *[(f"{name} requires an account", A,
       outside_precondition(f"{name}/ordinary", set_at(["args", "account"], 99)), PRE)
      for name in ["is_signer", "is_writable", "is_owned_by", "data_len"]],
    *[(f"{name} requires its field", A,
       outside_precondition(f"{name}/free", set_at(["args", "account"], 99)), PRE)
      for name in ["try_borrow_data", "try_borrow_mut_data", "try_borrow_mut_lamports"]],
    ("resize requires data", A, outside_precondition("resize/grow", set_at(["args", "account"], 99)), PRE),
    *[(f"{case} requires live guard", A,
       outside_precondition(f"guard/{case}", set_at(["args", "guard"], 99)), PRE)
      for case in ["drop_shared", "drop_exclusive"]],
    ("map requires callback frame", A, outside_precondition("map/mutated", borrowed_map), PRE),
    ("Clock requires initialized success", V, outside_precondition("clock_get/ok/values", uninitialized_clock), "GetterReady does not hold"),
    ("append requires valid prefix", L, outside_precondition("append/str/3/exact", set_at(["state", "len"], 4)), PRE),
    ("log requires valid prefix", L, outside_precondition("log/2/non_utf8_prefix", set_at(["state", "len"], 3)), PRE),
]
