"""Family Runtime: semantic corruptions of the records of the runtime family.

Each mutation changes one observable the decided reference fixes (a value, an error, a panic
reason, a request in the syscall log, a consumed reply, a deref count, a pointer, a guard, a
borrow marker or a backing byte); the checker must reject it as a MISMATCH of its record.
"""

from common import hex_bytes, hex_text, keep_reply, on_record, outside_precondition, setter


def log0(r):
    return r["outcome"]["state"]["syscalls"]["log"][0]


def acct(state, c):
    return [a for a in state["input"]["accounts"] if "duplicate_of" not in a][c]


def tlog0(r):
    return r["outcome"]["syscalls"]["log"][0]


def drop_request(r):
    r["outcome"]["state"]["syscalls"]["log"].clear()


def drop_field(r):
    log0(r)["fields"].pop()


def offset_plus_one(r):
    log0(r)["offset"] += 1


def typed_name(r):
    log0(r)["syscall"] = "sol_get_rent_sysvar"


def log_bytes(r):
    log0(r)["bytes"] = "68"


def marker_free(r):
    acct(r["outcome"]["state"], 0)["marker"] = 255


def guard_length(r):
    r["outcome"]["state"]["guards"][-1][4] += 1


def drop_newline(r):
    r["outcome"]["state"]["stdout"] = r["outcome"]["state"]["stdout"][:-2]


def drop_target(r):
    r["outcome"]["state"]["stubs"]["log"][0].pop("target")


def both_states(r, change):
    """Apply `change` to the state before and after the call."""
    change(r["state"])
    change(r["outcome"]["state"])


def truncate_memory(n):
    def change(st):
        st["memory"][0] = hex_text(hex_bytes(st["memory"][0])[:n])
    return lambda r: both_states(r, change)


def exclusive_guard(r):
    """The guard of the receiver becomes exclusive (marker 0): its reads are unchanged, but
    `Instructions.Ready` requires a shared guard."""
    def change(st):
        st["guards"][-1][1] = "exclusive"
        acct(st, 0)["marker"] = 0
    both_states(r, change)


def short_rent_data(r):
    """Four of the eight bytes of the rate, the rest zero: the raw read gives the same rate, but
    `Rent111ReadReady` requires eight bytes."""
    def change(st):
        a = acct(st, 0)
        a["data_len"] = 4
        a["data"] = a["data"][:8]
        st["backing"][0] = st["backing"][0][:8]
    both_states(r, change)


def uninitialized_reply(r):
    """The status-0 reply writes no bytes: the destination stays uninitialized."""
    r["state"]["syscalls"]["replies"][0]["data"] = ""


def short_hash_reply(r):
    """The reply writes 16 of the 32 output bytes."""
    reply = r["state"]["syscalls"]["replies"][0]
    reply["data"] = hex_text(hex_bytes(reply["data"])[:16])


def slice_length(k, n):
    def change(r):
        r["args"]["receiver"][k]["slice"]["length"] = n
    return change


def backing_byte(r):
    b = r["outcome"]["state"]["backing"][0]
    r["outcome"]["state"]["backing"][0] = ("01" if b[:2] != "01" else "02") + b[2:]


def written_under_error(r):
    """The buffer after an error status holds the bytes the reply of a status-0 case would have
    written: no answer of the hash shape."""
    r["outcome"]["result"]["hash_result"] = hex_text(bytes(range(32)))


def returned_panic(r):
    """A call that returns `!` returns."""
    r["outcome"] = {"exit": "returned", "result": None, "state": {"syscalls": r["outcome"]["syscalls"]}}


def flip(path, offset=0):
    def changed_bytes(original):
        value = bytearray(hex_bytes(original))
        value[offset] ^= 1
        return hex_text(value)
    return setter(path, changed_bytes)


def short_sha512_reply(record):
    reply = record["state"]["syscalls"]["replies"][0]
    reply["data"] = hex_text(hex_bytes(reply["data"])[:32])


def missing_reply(record):
    record["state"]["syscalls"]["replies"].clear()


def mismatched_reply(record):
    record["state"]["syscalls"]["replies"][0]["syscall"] = "sol_sha256"


def change_segments(record):
    fields = record["outcome"]["state"]["syscalls"]["log"][0]["fields"]
    fields[0] = hex_text(hex_bytes(fields[0]) + hex_bytes(fields.pop()))


def change_terminal(record):
    record["outcome"]["detail"] += " changed"


def forbidden_status(record):
    record["state"]["syscalls"]["replies"][0]["return"] = 2
    record["outcome"]["result"]["status"] = 2


def failure_reply_bytes(record):
    record["state"]["syscalls"]["replies"][0]["data"] = "5a" * 32


def invalid_success(record):
    record["state"]["syscalls"]["replies"][0].update({"return": 0, "data": "5a" * 32})
    record["outcome"]["result"].update({"status": 0, "output": "5a" * 32})


def over_limit_returns(record):
    record["outcome"] = {
        "exit": "returned",
        "result": {"status": 1, "output": record["args"]["output"], "guards": record["args"]["guards"]},
        "state": record["state"],
    }


def over_limit_asks(record):
    record["outcome"]["syscalls"]["log"].append({
        "syscall": "sol_curve_multiscalar_mul", "curve_id": record["args"]["curve_id"],
        "count": 513, "scalars": [], "points": [],
    })


def invalid_reads(record):
    record["outcome"]["state"]["syscalls"]["log"][0]["scalars"] = record["args"]["scalars"]


def missing_point(record):
    record["args"]["points"].pop()


def short_scalar(record):
    record["args"]["scalars"][0] = hex_text(hex_bytes(record["args"]["scalars"][0])[:31])


R = "solana_rent_3_0_0"
RW = "solana_rent_3_0_0_wrapping"
P2 = "pinocchio_0_10_2"
P2W = "pinocchio_0_10_2_wrapping"
P1 = "pinocchio_0_11_1"
PA = "pinocchio_0_11_1_accounts"
DS = "solana_define_syscall_5_1_0"
DS52 = "solana_define_syscall_5_2_0"
# The detail of the terminal exit that the raw sol_sha256 reference gives a reply outside the hash
# shape, as the model outcome of the report shows it.
HASH_SHAPE_EXIT = '"detail":"reply outside the hash shape"'

CONTROLS = [
    # Rent arithmetic.
    ("rent: value", R, on_record("minimum_balance/default_165", setter(["outcome", "result"], lambda v: v + 1))),
    ("rent: rounding", R, on_record("minimum_balance/round_tie_up", setter(["outcome", "result"], lambda v: v - 4))),
    ("rent: overflow reason", R, on_record("minimum_balance/add_overflow",
        setter(["outcome", "reason"], lambda _: "attempt to multiply with overflow"))),
    ("rent: NaN threshold", R, on_record("minimum_balance/qnan", setter(["outcome", "result"], lambda _: 1))),
    ("rent wrapping: wrapped value", RW, on_record("minimum_balance/mul_overflow",
        setter(["outcome", "result"], lambda v: v + 1))),
    ("rent wrapping: profile", RW, on_record("minimum_balance/add_overflow",
        setter(["outcome", "state", "overflow_checks"], lambda _: True))),
    ("pinocchio 0.10.2: guard error", P2, on_record("try_minimum_balance/data_over_limit",
        setter(["outcome", "result"], lambda _: {"ok": 0}))),
    ("pinocchio 0.10.2: unreachable rate guard", P2, on_record("try_minimum_balance/one_rate_over_limit_small",
        setter(["outcome", "result"], lambda _: {"err": "InvalidArgument"}))),
    ("pinocchio 0.10.2: overflow is a panic", P2, on_record("try_minimum_balance/one_rate_over_limit_overflow",
        lambda r: r.__setitem__("outcome", {"exit": "returned", "result": {"ok": 0}, "state": r["outcome"]["state"]}))),
    ("pinocchio 0.10.2 wrapping: wrapped value", P2W, on_record("try_minimum_balance/one_rate_max",
        setter(["outcome", "result", "ok"], lambda v: v ^ 1))),
    ("pinocchio 0.11.1: rate guard", P1, on_record("try_minimum_balance/rate_over_limit",
        setter(["outcome", "result"], lambda _: {"ok": 0}))),
    # Getters.
    ("pinocchio 0.10.2 Clock::get: value", P2, on_record("clock_get/ok/values",
        setter(["outcome", "result", "ok", "slot"], lambda _: 1))),
    ("pinocchio 0.10.2 Rent::get: request offset", P2, on_record("rent_get/ok/default", offset_plus_one)),
    ("pinocchio 0.10.2 Clock::get: status 1", P2, on_record("clock_get/status1",
        setter(["outcome", "result", "err"], lambda _: "UnsupportedSysvar"))),
    ("pinocchio 0.10.2 Clock::get: terminal reason", P2, on_record("clock_get/terminated",
        setter(["outcome", "reason"], lambda _: "abort"))),
    ("pinocchio 0.11.1 Clock::get: unconsumed reply", P1, on_record("clock_get/ok/values", keep_reply)),
    ("solana-sysvar Rent::get: default destination", "solana_sysvar_3_1_1", on_record("rent_get/ok/no_bytes",
        setter(["outcome", "result", "ok", "burn_percent"], lambda _: 0))),
    ("solana-sysvar Clock::get: typed syscall", "solana_sysvar_3_1_1", on_record("clock_get/ok/values", typed_name)),
    # Logging, return data, hashing, curve validation.
    ("sol_log: bytes", "solana_msg_3_1_0", on_record("sol_log/ascii", log_bytes)),
    ("sol_log_data: field", "solana_program_4_0_0", on_record("sol_log_data/three", drop_field)),
    ("set_return_data: request", "solana_program_4_0_0", on_record("set_return_data/three", drop_request)),
    ("hashv: output", "solana_sha256_hasher_3_1_0", on_record("hashv/abc/status1",
        setter(["outcome", "result"], lambda _: "00" * 32))),
    ("hashv: slices", "solana_sha256_hasher_3_1_0", on_record("hashv/three/status0", drop_field)),
    ("validate_edwards: status word", "solana_curve25519_3_1_12", on_record("validate_edwards/base/status4294967296",
        setter(["outcome", "result"], lambda _: True))),
    ("validate_edwards: initial result byte", "solana_curve25519_3_1_12", on_record("validate_edwards/pattern/status1",
        lambda r: log0(r).__setitem__("result_initial", 1))),
    ("validate_edwards: null result pointer", "solana_curve25519_3_1_12", on_record("validate_edwards/identity/status0",
        lambda r: (log0(r).__setitem__("result_initial", None), log0(r).__setitem__("result_null", True)))),
    # Terminated records: the terminal carries reason, detail and the shim state, all compared.
    ("terminated Clock::get: request offset", P2, on_record("clock_get/terminated",
        lambda r: tlog0(r).__setitem__("offset", 8))),
    ("terminated Clock::get: sysvar id", P1, on_record("clock_get/terminated",
        lambda r: tlog0(r).__setitem__("sysvar_id", "00" * 32))),
    ("terminated Rent::get: unconsumed reply", P2, on_record("rent_get/terminated",
        lambda r: r["outcome"]["syscalls"].__setitem__("replies", r["state"]["syscalls"]["replies"]))),
    ("terminated Rent::get: detail", P2, on_record("rent_get/terminated",
        setter(["outcome", "detail"], lambda d: d + "!"))),
    ("terminated solana-sysvar Clock::get: log emptied", "solana_sysvar_3_1_1", on_record("clock_get/terminated",
        lambda r: r["outcome"]["syscalls"]["log"].clear())),
    ("terminated hashv: input", "solana_sha256_hasher_3_1_0", on_record("hashv/abc/terminated",
        lambda r: tlog0(r).__setitem__("fields", ["00"]))),
    ("terminated validate_edwards: curve id", "solana_curve25519_3_1_12", on_record("validate_edwards/base/terminated",
        lambda r: tlog0(r).__setitem__("curve_id", 1))),
    ("terminated validate_edwards: point", "solana_curve25519_3_1_12", on_record("validate_edwards/base/terminated",
        lambda r: tlog0(r).__setitem__("point", "00" * 32))),
    # Raw syscalls of solana-define-syscall 5.1.0.
    ("raw sol_sha256: status", DS, on_record("sol_sha256/one/status1",
        setter(["outcome", "result", "status"], lambda _: 2))),
    ("raw sol_sha256: digest", DS, on_record("sol_sha256/several/status0",
        setter(["outcome", "result", "hash_result"], lambda h: hex_text(bytes([hex_bytes(h)[0] ^ 1]) + hex_bytes(h)[1:])))),
    ("raw sol_sha256: buffer written under an error status", DS, on_record("sol_sha256/one/status1", written_under_error)),
    ("raw sol_sha256: slices", DS, on_record("sol_sha256/several/status0", drop_field)),
    ("raw sol_sha256: unconsumed reply", DS, on_record("sol_sha256/none/status0", keep_reply)),
    # The reference ends the run on a reply outside the hash shape (`hashOutcome`), so a record
    # that returns after one is rejected. Both controls expect the terminal detail of the model: a
    # reference that read the reply as an answer would reject them too (the recorded answer
    # differs), but only through a model outcome without that detail.
    ("raw sol_sha256: status-0 reply of 16 bytes", DS, on_record("sol_sha256/one/status0", short_hash_reply),
        HASH_SHAPE_EXIT),
    ("raw sol_sha256: status 2^64", DS,
        on_record("sol_sha256/several/status18446744073709551615",
            setter(["state", "syscalls", "replies", 0, "return"], lambda _: 2 ** 64)), HASH_SHAPE_EXIT),
    ("raw sol_log_: bytes", DS, on_record("sol_log_/non_utf8", log_bytes)),
    ("raw sol_log_: request dropped", DS, on_record("sol_log_/ascii", drop_request)),
    ("raw sol_panic_: line", DS, on_record("sol_panic_/src_lib",
        setter(["outcome", "detail", "line"], lambda v: v + 1))),
    ("raw sol_panic_: file", DS, on_record("sol_panic_/src_lib",
        setter(["outcome", "detail", "file"], lambda _: "7372632f6d61696e2e7273"))),
    ("raw sol_panic_: a return", DS, on_record("sol_panic_/empty_extremes", returned_panic)),
    ("raw abort: detail", DS, on_record("abort/call", setter(["outcome", "detail"], lambda _: "x"))),
    ("terminated raw sol_sha256: input", DS, on_record("sol_sha256/several/terminated",
        lambda r: tlog0(r).__setitem__("fields", ["616263"]))),
    ("terminated raw sol_sha256: detail", DS, on_record("sol_sha256/none/terminated",
        setter(["outcome", "detail"], lambda d: d + "!"))),
    # Value helpers.
    ("COption::is_some", "solana_program_option_3_1_0", on_record("is_some/u64/none",
        setter(["outcome", "result"], lambda v: not v))),
    ("U64 into u64", "solana_zero_copy_1_2_0", on_record("into_u64/byte3", setter(["outcome", "result"], lambda v: v ^ 1))),
    ("Hash::to_bytes", "solana_hash_4_5_0", on_record("to_bytes/zero", setter(["outcome", "result"], lambda _: "11" * 32))),
    ("system_program::id", "solana_sdk_ids_3_1_0", on_record("system_program/id",
        setter(["outcome", "result"], lambda _: "11" * 32))),
    # Instructions sysvar over a generic receiver.
    ("load_current_index: deref count", P1, on_record("load_current_index/three",
        setter(["outcome", "state", "derefs"], lambda _: 1))),
    ("load_current_index: panic payload", P1, on_record("load_current_index/panic_second",
        setter(["outcome", "reason"], lambda _: "x"))),
    ("load_instruction_at: pointer", P1, on_record("load_instruction_at/three/index2",
        setter(["outcome", "result", "ok", "offset"], lambda v: v + 1))),
    ("load_instruction_at: base allocation", P1, on_record("load_instruction_at/base_from_third",
        setter(["outcome", "result", "ok", "allocation"], lambda _: 0))),
    ("get_instruction_data: length", P1, on_record("get_instruction_data/three/entry2",
        setter(["outcome", "result", "length"], lambda _: 2))),
    ("get_program_id: allocation", P1, on_record("get_program_id/odd/entry1",
        setter(["outcome", "result", "allocation"], lambda _: 1))),
    # Host branches.
    ("sol_log hostStd: line", "solana_msg_3_1_0_host", on_record("sol_log/ascii", drop_newline)),
    ("Clock::get host stub: unwind", "solana_sysvar_3_1_1_host", on_record("clock_get/panic",
        setter(["outcome", "reason"], lambda _: "x"))),
    ("Rent::get host stub: default destination", "solana_sysvar_3_1_1_host", on_record("rent_get/ok/no_bytes",
        setter(["outcome", "result", "ok", "burn_percent"], lambda _: 0))),
    ("set_return_data host stub: target", "solana_program_4_0_0_host", on_record("set_return_data/three", drop_target)),
    # Preconditions: each mutation keeps the outcome of the reference and breaks the
    # `requires` of the contract, which the checker decides.
    ("requires CurrentReady: first slice beyond its buffer", P1,
        outside_precondition("load_current_index/panic_second", slice_length(0, 10000)), "CurrentReady does not hold"),
    ("requires AtReady: first slice shorter than the count", P1,
        outside_precondition("load_instruction_at/panic_second", slice_length(0, 1)), "AtReady does not hold"),
    ("requires ProgramReady: program id beyond the buffer", P1,
        outside_precondition("get_program_id/three/entry0", truncate_memory(30)), "ProgramReady does not hold"),
    ("requires DataReady: data beyond the buffer", P1,
        outside_precondition("get_instruction_data/three/entry2", truncate_memory(220)), "DataReady does not hold"),
    ("requires currentIndexReady: exclusive guard", PA,
        outside_precondition("load_current_index/three", exclusive_guard), "currentIndexReady does not hold"),
    ("requires instructionAtReady: exclusive guard", PA,
        outside_precondition("load_instruction_at/three/index0", exclusive_guard), "instructionAtReady does not hold"),
    ("requires programIdReady: exclusive guard", PA,
        outside_precondition("get_program_id/three/entry0", exclusive_guard), "programIdReady does not hold"),
    ("requires dataReady: exclusive guard", PA,
        outside_precondition("get_instruction_data/three/entry0", exclusive_guard), "dataReady does not hold"),
    ("requires GetterReady: pinocchio 0.10.2 Clock::get success without bytes", P2,
        outside_precondition("clock_get/ok/values", uninitialized_reply), "GetterReady does not hold"),
    ("requires GetterReady: pinocchio 0.10.2 Rent::get success without bytes", P2,
        outside_precondition("rent_get/ok/default", uninitialized_reply), "GetterReady does not hold"),
    ("requires GetterReady: pinocchio 0.11.1 Clock::get success without bytes", P1,
        outside_precondition("clock_get/ok/values", uninitialized_reply), "GetterReady does not hold"),
    ("requires EveryReturnInitialized: hashv reply of 16 bytes", "solana_sha256_hasher_3_1_0",
        outside_precondition("hashv/abc/status0", short_hash_reply), "EveryReturnInitialized does not hold"),
    # the getters of solana-sysvar (`GetterReady` holds in every recorded state, `typed_getter_ready`) and
    # `try_from` (only a state the parser cannot denote breaks it) are exercised by the
    # kernel-checked theorems listed in requires-theorems.toml.
    ("requires Rent111ReadReady: four data bytes", PA,
        outside_precondition("from_account_view/rate", short_rent_data), "Rent111ReadReady does not hold"),
    # Over loader-serialized accounts.
    ("Rent::from_account_view: value", PA, on_record("from_account_view/sdk_layout",
        setter(["outcome", "result", "ok", "lamports_per_byte"], lambda _: 1))),
    ("Rent::from_account_view: lease before address", PA, on_record("from_account_view/wrong_address_exclusive",
        setter(["outcome", "result", "err"], lambda _: "InvalidArgument"))),
    ("Instructions::try_from: guard id", PA, on_record("try_from/shared",
        setter(["outcome", "result", "ok", "guard"], lambda _: [0, 0]))),
    ("Instructions::try_from: guard view", PA, on_record("try_from/three", guard_length)),
    ("Instructions::try_from: borrow marker", PA, on_record("try_from/three", marker_free)),
    ("Instructions::try_from: address before lease", PA, on_record("try_from/wrong_address_exclusive",
        setter(["outcome", "result", "err"], lambda _: "AccountBorrowFailed"))),
    ("Ref load_current_index: value", PA, on_record("load_current_index/three",
        setter(["outcome", "result"], lambda v: v + 1))),
    ("Ref load_instruction_at: offset", PA, on_record("load_instruction_at/three/index2",
        setter(["outcome", "result", "ok", "offset"], lambda _: 1))),
    ("Ref get_program_id: offset", PA, on_record("get_program_id/three/entry2",
        setter(["outcome", "result", "offset"], lambda _: 1))),
    ("Ref get_instruction_data: backing", PA, on_record("get_instruction_data/three/entry2", backing_byte)),
    # Raw SHA-512 and multiscalar multiplication of solana-define-syscall 5.2.0.
    ("SHA512 writes its last 32 bytes", DS52,
     on_record("sha512/one/success", flip(["outcome", "result", "output"], 63))),
    ("SHA512 rejects a 32-byte reply", DS52, on_record("sha512/one/success", short_sha512_reply)),
    ("SHA512 retains segment boundaries", DS52, on_record("sha512/segmented/success", change_segments)),
    ("SHA512 consumes its reply", DS52, on_record("sha512/empty/success", keep_reply)),
    ("SHA512 cannot return without a reply", DS52,
     on_record("sha512/one/success", missing_reply)),
    ("SHA512 cannot consume the reply of another syscall", DS52,
     on_record("sha512/one/success", mismatched_reply)),
    ("SHA512 failure preserves output", DS52,
     on_record("sha512/one/failure", flip(["outcome", "result", "output"]))),
    ("SHA512 preserves surrounding bytes", DS52,
     on_record("sha512/one/success", flip(["outcome", "result", "guards"]))),
    ("SHA512 keeps terminal details", DS52, on_record("sha512/one/terminal", change_terminal)),
    ("MSM result bytes", DS52, on_record("msm/0/1/success", flip(["outcome", "result", "output"]))),
    ("MSM scalar argument", DS52,
     on_record("msm/0/3/success", flip(["outcome", "state", "syscalls", "log", 0, "scalars", 1]))),
    ("MSM point argument", DS52,
     on_record("msm/1/1/success", flip(["outcome", "state", "syscalls", "log", 0, "points", 0]))),
    ("MSM failure preserves output", DS52,
     on_record("msm/0/1/failure", flip(["outcome", "result", "output"]))),
    ("MSM rejects status two even with matching observed status", DS52,
     on_record("msm/0/1/failure", forbidden_status)),
    ("MSM failure reply has no bytes", DS52, on_record("msm/0/1/failure", failure_reply_bytes)),
    ("MSM invalid curve cannot succeed", DS52, on_record("msm/2/2/invalid", invalid_success)),
    ("MSM invalid curve does not read scalars", DS52, on_record("msm/2/2/invalid", invalid_reads)),
    ("MSM count rejection cannot return", DS52, on_record("msm/0/513/over_limit", over_limit_returns)),
    ("MSM count rejection precedes invalid curve request", DS52,
     on_record("msm/2/513/over_limit", over_limit_asks)),
    ("MSM matching input counts", DS52, on_record("msm/0/1/success", missing_point),
     "multiscalar input counts differ from the ABI count"),
    ("MSM fixed scalar width", DS52, on_record("msm/0/1/success", short_scalar), "expected 32 bytes"),
    ("MSM keeps terminal details", DS52, on_record("msm/1/1/terminal", change_terminal)),
]
