"""Family Address: semantic corruptions of the solana-address 2.6.0 and 2.6.1 records.

Each change must be rejected as a MISMATCH of its record.
Corpora: `solana_address_2_6_{0,1}_api` (value operations and the shim syscall families) and
`solana_address_2_6_{0,1}_host` (pure observations over an explicit Crypto table).
"""

from common import on_record

API0, API1 = "solana_address_2_6_0_api", "solana_address_2_6_1_api"
HOST0, HOST1 = "solana_address_2_6_0_host", "solana_address_2_6_1_host"
PANIC = "Unable to find a viable program address bump seed"


def flip_hex(h, i=0):
    b = bytearray.fromhex(h)
    b[i] ^= 1
    return b.hex()


def after(r):
    return r["outcome"]["state"]["syscalls"]


def result_set(key, value):
    def change(r): r["outcome"]["result"][key] = value
    return change


# Value operations.
def eq_true(r): r["outcome"]["result"] = True
def as_ref_short(r): r["outcome"]["result"] = r["outcome"]["result"][:-2]
def default_flip(r): r["outcome"]["result"] = flip_hex(r["outcome"]["result"])


# Pure observations (host branch).
def bump_minus_one(r): r["outcome"]["result"]["bump"] -= 1
def address_flip31(r): r["outcome"]["result"]["address"] = flip_hex(r["outcome"]["result"]["address"], 31)
def table_curve_off(r): r["args"]["crypto"]["on_curve"][0][1] = False
def table_drop_digest(r): r["args"]["crypto"]["sha256"].pop()
def panic_reason(r): r["outcome"]["reason"] = "other"
def panic_to_return(r):
    r["outcome"] = {"exit": "returned", "result": {"address": "00" * 32, "bump": 255}, "state": None}
def curve_true(r): r["outcome"]["result"] = True
def seed0_to_32(r): r["args"]["seeds"][0] = r["args"]["seeds"][0][:64]
def seed1_to_32(r): r["args"]["seeds"][1] = r["args"]["seeds"][1][:64]
def drop_seed(r): r["args"]["seeds"].pop()
def drop_two_seeds(r): del r["args"]["seeds"][-2:]


# try_find_program_address through the shim.
def some_bump(value):
    def change(r): r["outcome"]["result"]["some"]["bump"] = value
    return change


def some_on_error(r):
    r["outcome"]["result"] = {"some": {"address": r["state"]["syscalls"]["replies"][0]["data"], "bump": 7}}


def some_zero(r): r["outcome"]["result"] = {"some": {"address": "00" * 32, "bump": 255}}
def log_bump(r): after(r)["log"][0]["bump"] = 254
def log_drop_seed(r): after(r)["log"][0]["seeds"].pop()
def log_drop(r): after(r)["log"].pop()
def extra_reply_consumed(r): after(r)["replies"].pop()


def long_data_window(r):
    r["outcome"]["result"]["some"]["address"] = r["state"]["syscalls"]["replies"][0]["data"][2:66]


def terminal_detail(r): r["outcome"]["detail"] = "other"


def partial_address_reply(r):
    """Status zero whose reply writes only 5 address bytes: outside `SuccessInitialized`. The
    recorded outcome is kept, so only the precondition decision can reject it."""
    reply = r["state"]["syscalls"]["replies"][0]
    assert reply["return"] == 0
    reply["data"] = reply["data"][:10]


def terminal_to_return(r):
    r["outcome"] = {"exit": "returned", "result": None, "state": {"syscalls": r["outcome"]["syscalls"]}}


# find_program_address through the shim.
def unwound_log_cleared(r): r["outcome"]["state"]["syscalls"]["log"] = []


def return_on_error(r):
    r["outcome"] = {"exit": "returned", "result": {"address": "00" * 32, "bump": 7}, "state": r["outcome"]["state"]}


def unwind_on_success(r):
    r["outcome"] = {"exit": "unwound", "reason": PANIC, "state": r["outcome"]["state"]}


# is_on_curve through the shim.
def result_not_null(r): after(r)["log"][0]["result_null"] = False
def initial_byte_with_null(r): after(r)["log"][0]["result_initial"] = 0


def scratch_byte(r):
    after(r)["log"][0]["result_null"] = False
    after(r)["log"][0]["result_initial"] = 0
def curve_id_one(r): after(r)["log"][0]["curve_id"] = 1
def point_zero(r): after(r)["log"][0]["point"] = "00" * 32


_CASES = [
    # Value operations.
    ("eq of addresses differing in byte 31", API1, "eq/pattern!=pattern^byte31", eq_true),
    ("as_ref drops a byte", API0, "as_ref/pattern", as_ref_short),
    ("default is not zero", API1, "default", default_flip),
    # Pure observations.
    ("find bump", HOST0, "find_program_address/vault", bump_minus_one),
    ("find address", HOST1, "find_program_address/bump_252", address_flip31),
    ("Crypto table curve answer", HOST0, "find_program_address/bump_253", table_curve_off),
    ("Crypto table misses a digest", HOST0, "find_program_address/bump_253", table_drop_digest,
     "the Crypto table misses a point the model queries"),
    ("find panic message", HOST0, "find_program_address/seeds_16", panic_reason),
    ("find succeeds beyond the seed limit", HOST0, "find_program_address/seeds_16", panic_to_return),
    # A panic record whose inputs become valid must not pass with an empty table.
    ("panic kept after the 33-byte seed is cut to 32", HOST0, "find_program_address/seed_len_33", seed0_to_32,
     "the Crypto table misses a point the model queries"),
    ("panic kept after a seed is dropped from 16", HOST0, "find_program_address/seeds_16", drop_seed,
     "the Crypto table misses a point the model queries"),
    ("panic kept after two seeds are dropped from 17", HOST1, "find_program_address/seeds_17", drop_two_seeds,
     "the Crypto table misses a point the model queries"),
    ("panic kept after the 33-byte second seed is cut to 32", HOST1, "find_program_address/seed_len_32_and_33",
     seed1_to_32, "the Crypto table misses a point the model queries"),
    ("is_on_curve result", HOST0, "is_on_curve/pattern12", curve_true),
    # try_find_program_address through the shim.
    ("try_find bump", API0, "try_find_program_address/ok_bump254/vault", some_bump(253)),
    ("try_find bump left at 255", API1, "try_find_program_address/ok_bump_unwritten/no_seeds", some_bump(0)),
    ("try_find Some on status 1", API0, "try_find_program_address/err1_written/no_seeds", some_on_error),
    ("try_find Some on a status above 32 bits", API1, "try_find_program_address/err_high_bits/no_seeds",
     some_zero),
    ("try_find logged initial bump", API0, "try_find_program_address/ok_bump0/no_seeds", log_bump),
    ("try_find logged seeds", API1, "try_find_program_address/ok_bump254/seeds_17", log_drop_seed),
    ("try_find request not logged", API0, "try_find_program_address/err_max/no_seeds", log_drop),
    ("try_find consumes the extra reply", API1, "try_find_program_address/ok_extra_reply/no_seeds",
     extra_reply_consumed),
    ("try_find address window of long data", API0, "try_find_program_address/ok_long_data/no_seeds",
     long_data_window),
    ("try_find terminal detail", API0, "try_find_program_address/terminate/no_seeds", terminal_detail),
    ("try_find terminal syscall turned into a return", API1, "try_find_program_address/terminate/no_seeds",
     terminal_to_return),
    # Preconditions (`decidesRequires`): a status-zero reply that does not initialize the address.
    ("try_find outside SuccessInitialized (2.6.0)", API0, "try_find_program_address/ok_bump254/vault",
     partial_address_reply, "outside the precondition"),
    ("try_find outside SuccessInitialized (2.6.1)", API1, "try_find_program_address/ok_bump254/mixed",
     partial_address_reply, "outside the precondition"),
    ("find outside SuccessInitialized (2.6.0)", API0, "find_program_address/ok_bump254/vault",
     partial_address_reply, "outside the precondition"),
    ("find outside SuccessInitialized (2.6.1)", API1, "find_program_address/ok_bump254/mixed",
     partial_address_reply, "outside the precondition"),
    # find_program_address through the shim.
    ("find panic message (shim)", API0, "find_program_address/err1_unwritten/no_seeds", panic_reason),
    ("find unwind loses the request log", API1, "find_program_address/err1_written/vault", unwound_log_cleared),
    ("find returns on status 1", API1, "find_program_address/err1_written/mixed", return_on_error),
    ("find panics on status 0", API0, "find_program_address/ok_bump254/mixed", unwind_on_success),
    # is_on_curve through the shim.
    ("is_on_curve true on status 2", API0, "is_on_curve/status2/pattern", curve_true),
    ("is_on_curve result pointer not null", API0, "is_on_curve/on/zero", result_not_null,
     "a non-null curve result pointer without its initial byte"),
    # A null pointer has no initial byte; a scratch byte is not the null destination.
    ("is_on_curve initial byte behind a null pointer", API0, "is_on_curve/off/zero", initial_byte_with_null,
     "a null curve result pointer with an initial byte"),
    ("is_on_curve scratch byte instead of null", API0, "is_on_curve/status2/pattern", scratch_byte),
    ("is_on_curve curve id", API0, "is_on_curve/off/ones", curve_id_one),
    ("is_on_curve logged point", API0, "is_on_curve/on/pattern", point_zero),
]

def _control(label, corpus, record_id, change, expected=None):
    mutate = on_record(record_id, change)
    if expected is None:
        return (label, corpus, mutate)
    return (label, corpus, mutate, f"FAIL {corpus}/{record_id}: {expected}")


CONTROLS = [_control(*case) for case in _CASES]
