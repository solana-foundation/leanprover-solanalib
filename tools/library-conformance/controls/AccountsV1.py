"""Family AccountsV1: semantic corruptions of solana-account-view 1.0.0 and solana-account-info 3.1.1 records.

Each must be rejected as a MISMATCH of its record: a wrong borrow byte, guard, range, byte, field,
error, Rc count, lease, frame or exit.
"""

from common import hex_bytes, hex_text, on_record, outside_precondition

V = "solana_account_view_1_0_0"
F = "solana_account_view_1_0_0_forged"
I = "solana_account_info_3_1_1"


def after(r):
    return r["outcome"]["state"]


def account(field, value, k=0):
    def change(r):
        after(r)["accounts"][k][field] = value
    return change


def result(value):
    def change(r):
        r["outcome"]["result"] = value
    return change


def result_field(field, value):
    def change(r):
        r["outcome"]["result"][field] = value
    return change


def backing(change):
    def mutate(r):
        a = after(r)["accounts"][0]
        b = bytearray(hex_bytes(a["backing"]))
        change(b)
        a["backing"] = hex_text(bytes(b))
    return mutate


def grown_not_zeroed(b):
    # The byte exposed by growing 16 -> 17 is recorded as nonzero.
    b[16] = 7


def hidden_erased(b):
    # Shrinking 16 -> 1 keeps the hidden suffix; here it is erased.
    b[1:16] = bytes(15)


def mapped_offset(r):
    after(r)["guards"][0]["view"]["offset"] = 0


def guard_dropped(r):
    after(r)["guards"] = []


def hidden_as_consumed(gid):
    # Drop the guard object from the state after and list it as consumed.
    def change(r):
        s = after(r)
        s["guards"] = [g for g in s["guards"] if g.get("id") != gid]
        s["consumed"] = [gid]
    return change


def leaked_with_new_range(r):
    # The lease an unwinding map leaks is reported as an object with another range.
    after(r)["guards"] = [{"id": 0, "cell": 0, "mode": "shared", "view": {"offset": 1, "length": 2}}]


def frame_changed(r):
    s = after(r)
    f = bytearray(hex_bytes(s["frame"]))
    f[-1] ^= 1
    s["frame"] = hex_text(bytes(f))


def try_borrow_guard_id(r):
    r["outcome"]["result"]["ok"]["guard"] += 1


def unwound_getter(r):
    r["outcome"] = {"exit": "unwound", "reason": "control", "state": after(r)}


def returned_getter(r):
    r["outcome"] = {"exit": "returned", "result": 16, "state": after(r)}


def lease(k, value):
    def change(r):
        after(r)["cells"][k]["lease"] = value
    return change


def rc(counts):
    def change(r):
        after(r)["rc"] = counts
    return change


def reason(text):
    def change(r):
        r["outcome"]["reason"] = text
    return change


def exit_terminated(r):
    r["outcome"] = {"exit": "terminated", "reason": "abort"}


def exit_returned_as_model(r):
    # The outcome of the model (Err(InvalidRealloc), state unchanged): the listed model then admits it.
    r["outcome"] = {"exit": "returned", "result": {"err": "InvalidRealloc"}, "state": after(r)}


def before_delta(value):
    def change(r):
        r["state"]["accounts"][0]["resize_delta"] = value
        after(r)["accounts"][0]["resize_delta"] = value
    return change


def new_len(value):
    def change(r):
        r["args"]["new_len"] = value
    return change


GROW, SHRINK, CLOSE = ("forged/delta-near-max/resize/grow", "forged/delta-near-min/resize/shrink",
                       "forged/delta-near-min/close")


def forged(record_id):
    return f"FAIL {F}/{record_id}"


PRE = "the input is outside the registered precondition"


def outside(corpus, record_id):
    return f"FAIL {corpus}/{record_id}: {PRE}"


def before_guard_exclusive(r):
    # Ref::map requires the shared mode: the held guard is exclusive (borrow byte 0 to stay consistent).
    r["state"]["guards"][0]["mode"] = "exclusive"
    r["state"]["accounts"][0]["borrow_state"] = 0


def callback_out_of_range(r):
    # CallbackSafe: the closure returns a target beyond the data of the account.
    r["args"]["callback"]["exit"]["return"]["length"] = 100


def handle(value):
    def change(r):
        r["args"]["handle"] = value
    return change


def guard_arg(value):
    def change(r):
        r["args"]["guard"] = value
    return change


def info_handle(field, value):
    def change(r):
        r["args"]["info"][field] = value
    return change


def before_cell(k, content):
    # The precondition reads the type of the cell; the AccountInfo still names the cells of its account.
    def change(r):
        r["state"]["cells"][k] = {**content, "lease": r["state"]["cells"][k]["lease"]}
    return change


def second_exclusive_guard(r):
    # DataBorrowReady needs Borrow.State.Valid: two exclusive guards on one cell break it.
    s = r["state"]
    s["guards"].append({"id": 1, "cell": 1, "mode": "exclusive", "view": "whole"})
    s["ghost"]["slots"] = 2
    s["ghost"]["generations"] = [0, 0]


MAP_MIDDLE = "one/shared1/map/g0/middle"


def shrink_guard_view(r):
    # The closure returns {1, 14} of an input of length 1, which natively panics.
    r["state"]["guards"][0]["view"]["length"] = 1


def rc_after(counts):
    def change(r):
        after(r)["rc"] = counts
    return change


def rc_before(counts):
    def change(r):
        r["state"]["rc"] = counts
    return change


def duplicate_guard(which):
    def change(r):
        s = r["state"] if which == "before" else after(r)
        s["guards"].append(dict(s["guards"][-1]))
    return change


def info_field(field, value):
    def change(r):
        r["args"]["info"][field] = value
    return change


def word_bits(value):
    def change(r):
        r["args"]["profile"]["word_bits"] = value
    return change


def fail(corpus, record_id):
    return f"FAIL {corpus}/{record_id}"

CONTROLS = [
    # Map targets follow the indexing of the driver; Rc counts, duplicate guards and info/frame consistency.
    ("Ref::map target beyond its input", V, on_record(MAP_MIDDLE, shrink_guard_view), fail(V, MAP_MIDDLE)),
    ("Rc counts changed by try_borrow_data", I, on_record("one/free/try_borrow_data/p0", rc_after([6, 0]))),
    ("Rc counts dropped by lamports", I, on_record("one/free/lamports/p0", rc_after([]))),
    ("Rc counts before data_len", I, on_record("one/free/data_len/p0", rc_before([7, 7]))),
    ("duplicate guard after try_borrow", V, on_record("one/shared1/try_borrow/p0", duplicate_guard("after")),
     fail(V, "one/shared1/try_borrow/p0")),
    ("duplicate guard before deref", V, on_record("one/shared1/deref/g0", duplicate_guard("before")),
     fail(V, "one/shared1/deref/g0")),
    ("duplicate AccountInfo guard", I, on_record("one/data-shared2/try_borrow_data/p0", duplicate_guard("after")),
     fail(I, "one/data-shared2/try_borrow_data/p0")),
    ("AccountInfo key differs from the account key", I, on_record("one/free/lamports/p0", info_field("key", "00" * 32)),
     fail(I, "one/free/lamports/p0")),
    ("AccountInfo owner differs from the account owner", I, on_record("one/free/data_len/p0", info_field("owner", "11" * 32)),
     fail(I, "one/free/data_len/p0")),
    ("AccountInfo flag differs from the account flag", I, on_record("one/free/try_borrow_data/p0", info_field("is_writable", False)),
     fail(I, "one/free/try_borrow_data/p0")),
    ("AccountInfo word size 63", I, on_record("one/free/try_borrow_mut_data/p0", word_bits(63)),
     fail(I, "one/free/try_borrow_mut_data/p0")),
    ("AccountInfo word size 65", I, on_record("one/free/clone/p0", word_bits(65)), fail(I, "one/free/clone/p0")),
    # Each non-trivial registered precondition, broken on one record.
    ("Ref::map guard mode", V, outside_precondition(MAP_MIDDLE, before_guard_exclusive), outside(V, MAP_MIDDLE)),
    ("Ref::map CallbackSafe", V, outside_precondition(MAP_MIDDLE, callback_out_of_range), outside(V, MAP_MIDDLE)),
    ("Ref::release live guard", V, outside_precondition("one/shared1/release/g0", guard_arg(3)),
     outside(V, "one/shared1/release/g0")),
    ("RefMut::release live guard", V, outside_precondition("one/exclusive/release/g0", guard_arg(3)),
     outside(V, "one/exclusive/release/g0")),
    # HasAccount of the observation and update members: a handle naming no cell.
    *[(f"{member} HasAccount", V, outside_precondition(f"one/exclusive/{member}/p0", handle(3)),
       outside(V, f"one/exclusive/{member}/p0"))
      for member in ["lamports", "data_len", "is_data_empty", "is_signer", "is_writable"]],
    ("owned_by HasAccount", V, outside_precondition("one/free/owned_by/own", handle(3)),
     outside(V, "one/free/owned_by/own")),
    ("set_lamports HasAccount", V, outside_precondition("one/free/set_lamports/one", handle(3)),
     outside(V, "one/free/set_lamports/one")),
    ("AccountInfo lamports ObservationReady", I,
     outside_precondition("one/free/lamports/p0", before_cell(0, {"data": "00"})), outside(I, "one/free/lamports/p0")),
    ("AccountInfo data_len ObservationReady", I,
     outside_precondition("one/free/data_len/p0", before_cell(1, {"lamports": 5})), outside(I, "one/free/data_len/p0")),
    ("AccountInfo DataBorrowReady data cell", I,
     outside_precondition("one/free/try_borrow_data/p0", before_cell(1, {"lamports": 5})),
     outside(I, "one/free/try_borrow_data/p0")),
    ("AccountInfo handles of two accounts", I, on_record("dups/free/lamports/p1", info_handle("data", 1)),
     fail(I, "dups/free/lamports/p1")),
    ("AccountInfo DataBorrowReady Valid", I,
     outside_precondition("one/data-exclusive/try_borrow_mut_data/p0", second_exclusive_guard),
     outside(I, "one/data-exclusive/try_borrow_mut_data/p0")),
    # The three forged overflow records are outside the resize/close preconditions; the checker
    # asserts their documented native behavior there (FAIL otherwise).
    ("forged: other overflow reason", F, on_record(GROW, reason("attempt to multiply with overflow")), forged(GROW)),
    ("forged: terminated exit", F, on_record(GROW, exit_terminated), forged(GROW)),
    ("forged: returned as the model computes", F, on_record(GROW, exit_returned_as_model), forged(GROW)),
    ("forged: state after the panic", F, on_record(CLOSE, account("lamports", 12345)), forged(CLOSE)),
    ("forged: frame after the panic", F, on_record(SHRINK, frame_changed), forged(SHRINK)),
    ("forged: reason of close", F, on_record(CLOSE, reason("attempt to add with overflow")), forged(CLOSE)),
    # Made non-overflowing, a forged record is inside the precondition, where the model returns.
    ("forged: input without overflow is a precondition mismatch", F, on_record(GROW, new_len(16))),
    ("forged: header without overflow is a precondition mismatch", F, on_record(GROW, before_delta(0))),
    ("forged: close header without overflow is a precondition mismatch", F, on_record(CLOSE, before_delta(0))),
    # A main-corpus header made to overflow is outside the precondition, which the main corpus forbids.
    ("main: resize header overflows", V,
     outside_precondition("one/free/resize/entry+1", before_delta(2**31 - 1)), outside(V, "one/free/resize/entry+1")),
    ("main: close header overflows", V,
     outside_precondition("one/free/close/p0", before_delta(-2**31)), outside(V, "one/free/close/p0")),
    ("borrow byte after try_borrow", V, on_record("one/free/try_borrow/p0", account("borrow_state", 255))),
    ("guard identity of try_borrow", V, on_record("one/free/try_borrow/p0", try_borrow_guard_id)),
    ("growth not zeroed", V, on_record("one/free/resize/entry+1", backing(grown_not_zeroed))),
    ("shrink erases the hidden suffix", V, on_record("one/free/resize/one", backing(hidden_erased))),
    ("close keeps resize_delta", V, on_record("one/free/close/p0", account("resize_delta", 0))),
    ("close succeeds while borrowed", V, on_record("one/shared1/close/p0", result({"ok": None}))),
    ("resize error kind", V, on_record("one/free/resize/limit+1", result({"err": "AccountBorrowFailed"}))),
    ("unwinding map releases the lease", V, on_record("one/shared1/map/g0/panic", account("borrow_state", 255))),
    ("unwinding map: leaked lease with another range", V,
     on_record("one/shared1/map/g0/panic", leaked_with_new_range)),
    ("acquired guard excused as consumed", V, on_record("one/free/try_borrow/p0", hidden_as_consumed(0))),
    ("mapped guard excused as consumed", V, on_record("one/shared1/map/g0/middle", hidden_as_consumed(0))),
    ("AccountInfo guard excused as consumed", I, on_record("one/free/try_borrow_data/p0", hidden_as_consumed(0))),
    ("map closure effects lost", V, on_record("one/shared1/map/g0/effects", account("lamports", 1000))),
    ("mapped range", V, on_record("one/shared1/map/g0/middle", mapped_offset)),
    ("release keeps the lease", V, on_record("one/shared1/release/g0", account("borrow_state", 254))),
    ("deref bytes", V, on_record("one/shared1/deref/g0", result_field("bytes", "00"))),
    ("deref mutability", V, on_record("one/shared1/deref/g0", result_field("writable", True))),
    ("address field", V, on_record("one/exclusive/address/p0", result_field("field", 40))),
    ("owner bytes", V, on_record("one/exclusive/owner/p0", result_field("bytes", "00" * 32))),
    ("alias handle of clone", V, on_record("dups/free/clone/p2", result_field("cell", 2))),
    # The runner itself rejects a changed frame, before the checker.
    ("frame changed", V, on_record("one/exclusive/lamports/p0", frame_changed), fail(V, "one/exclusive/lamports/p0")),
    ("raw flag byte changed", V, on_record("one/exclusive/is_writable/p0", account("is_writable", 2))),
    ("set_lamports value", V, on_record("one/free/set_lamports/one", account("lamports", 2))),
    ("owned_by result", V, on_record("one/free/owned_by/own", result(False))),
    ("acquired guard missing", V, on_record("one/free/try_borrow_mut/p0", guard_dropped)),
    ("getter unwinds", V, on_record("one/exclusive/lamports/p0", unwound_getter)),
    ("AccountInfo lamports value", I, on_record("one/free/lamports/p0", result(1001))),
    ("RefCell panic reason", I, on_record("one/lamports-exclusive/lamports/p0", reason("control"))),
    ("data_len returns while mutably borrowed", I, on_record("one/data-exclusive/data_len/p0", returned_getter)),
    ("lease after try_borrow_data", I, on_record("one/free/try_borrow_data/p0", lease(1, "free"))),
    ("try_borrow_data succeeds while mutably borrowed", I,
     on_record("one/data-exclusive/try_borrow_data/p0", result({"ok": {"guard": 1}}))),
    ("Rc counts not incremented by clone", I, on_record("one/free/clone/p0", rc([1, 1]))),
    ("clone lamports handle", I, on_record("one/free/clone/p0", result_field("lamports", 1))),
    ("clone owner reference", I, on_record("dups/free/clone/p4", result_field("owner_ref", 0))),
    ("AccountInfo frame changed", I, on_record("one/free/data_len/p0", frame_changed), fail(I, "one/free/data_len/p0")),
]
