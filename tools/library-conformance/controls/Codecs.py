"""Family Codecs: corruptions of the heap requests of borsh 0.10.4 `Vec<T>` decoding, of the
`hint::cautious` records derived from them, and of the no-std `Write::write_all` records of borsh 1.6.1.

Each must be rejected as a MISMATCH of its record (the layout controls: as layout mismatches; the
`flush` control: as a call `write_all` does not make). The `write_all` controls other than `flush`
are coherent runs of a defective `write_all` over the same scripted writer, so the model, not the
record reader, rejects them; the `flush` control exercises the record reader, which accepts only
logged `write` calls. The other semantic controls of the family are the built-in Codecs controls of run.py.
"""

from common import on_record

CORPUS = "borsh_0_10_4"
VEC = "deserialize_reader/Vec<{}>/{}"


def heap(r):
    return r["outcome"]["state"]["heap"]


def capacity_plus_one_element(r):
    heap(r)[0]["size"] += 4                       # with_capacity(cautious(len) + 1)


def growth_by_one(r):
    request = next(e for e in heap(r) if e["op"] == "realloc")
    request["new_size"] = request["size"] + 16    # grow to len + 1, not 2 * capacity


def alignment(r):
    heap(r)[0]["align"] *= 2


def not_zeroed(r):
    heap(r)[0]["op"] = "alloc"                    # vec![0u8; n] uses alloc_zeroed


def realloc_after_error(r):
    events = heap(r)
    events.append(events.pop(1))                  # growth moved after the allocations of the error ...
    events[-1], events[-2] = events[-2], events[-1]   # ... and before the drop of the vector


def drop_before_error(r):
    events = heap(r)
    events.insert(1, events.pop())                # the vector freed before the error is built


def missing_drop(r):
    heap(r).pop()                                 # the vector leaks on the error path


def freed_on_ok(r):
    first = heap(r)[0]
    heap(r).append({"op": "dealloc", "block": 0, "size": first["size"], "align": first["align"]})


def error_on_vector_block(r):
    heap(r)[1]["block"] = 0                       # an error allocation on the block of the vector


def extra_resize(r):
    events = heap(r)
    events.insert(2, {"op": "realloc", "block": 0, "size": 2097152, "align": 1, "new_size": 4194304})
    events[-1]["size"] = 4194304


def element_layout(r):
    r["layout"]["align"] = 8


def cautious_uncapped(r):
    r["outcome"]["result"] = r["args"]["hint"]    # min(hint, 4096 / size) without the cap


def cautious_plus_one(r):
    r["outcome"]["result"] += 1


def cautious_zero(r):
    r["outcome"]["result"] = 0                    # without max(.., 1)


def cautious_hint(r):
    r["args"]["hint"] -= 1


def zero_sized(r):
    r["layout"]["size"] = 0                       # a forged zero-sized layout for the u32 instantiation


NOSTD = "borsh_1_6_1_nostd_io"
WRITE_ALL = "write_all/{}"


def calls(r):
    return r["outcome"]["state"]["calls"]


def returns_ok(r):
    r["outcome"] = {"exit": "returned", "result": {"ok": None}, "state": r["outcome"]["state"]}


def empty_buffer_calls_write(r):
    response = r["args"]["writer"]["script"][0]   # a do-while loop: write is called on the empty
    calls(r).append({"op": "write", "bytes": "", "response": response})   # buffer and its error
    r["outcome"]["result"] = {"err": response["err"]}                     # is returned


def zero_count_accepted(r):
    r["outcome"]["result"] = {"ok": None}         # Ok(0) taken as success


def write_zero_message(r):
    r["outcome"]["result"]["err"]["message"] = "failed to write the whole buffer"


def interrupted_returned(r):
    first = calls(r)[0]                           # the Interrupted error returned, not retried
    r["outcome"]["state"]["calls"] = [first]
    r["outcome"]["result"] = {"err": first["response"]["err"]}


def retry_advanced(r):
    c = calls(r)                                  # the retry after Interrupted skips a byte: it
    c[2]["bytes"] = "0304"                        # offers 0304, takes 1, and the writer takes the
    c[3] = {"op": "write", "bytes": "04", "response": {"ok": 1}}   # remaining 04


def rest_not_advanced(r):
    buf = r["args"]["buf"]                        # the second call offers the whole buffer again,
    calls(r)[1] = {"op": "write", "bytes": buf, "response": {"ok": len(buf) // 2}}   # which the
                                                  # writer, its script used up, takes whole


def overrun_original_length(r):
    r["outcome"]["reason"] = r["outcome"]["reason"].replace("length 3", "length 4")


def overrun_index_is_length(r):
    r["outcome"]["reason"] = r["outcome"]["reason"].replace("index 5", "index 4")   # panics at len


def unwind_drops_call(r):
    calls(r).pop()                                # the unwind state loses the panicking call


def own_write_zero_replaced(r):
    r["outcome"]["result"]["err"]["message"] = "failed to write whole buffer"


def flush_called(r):
    calls(r).append({"op": "flush"})


CONTROLS = [
    ("Vec<u32> with_capacity size at the cautious bound", CORPUS,
     on_record(VEC.format("u32", "hint/len1024/short"), capacity_plus_one_element)),
    ("Vec<Option<u64>> push growth size", CORPUS,
     on_record(VEC.format("Option<u64>", "hint/len257/body257"), growth_by_one)),
    ("Vec<Option<u64>> allocation alignment", CORPUS,
     on_record(VEC.format("Option<u64>", "len1"), alignment)),
    ("Vec<u8> initial buffer not zeroed", CORPUS,
     on_record(VEC.format("u8", "len1"), not_zeroed)),
    ("Vec<bool> growth after the allocations of the error (order)", CORPUS,
     on_record(VEC.format("bool", "hint/len5000/body4097"), realloc_after_error)),
    ("Vec<u32> drop before the allocations of the error (order)", CORPUS,
     on_record(VEC.format("u32", "len2/truncated5"), drop_before_error)),
    ("Vec<u8> no drop of the buffer after an error", CORPUS,
     on_record(VEC.format("u8", "len3/truncated5"), missing_drop)),
    ("Vec<u32> buffer freed although returned", CORPUS,
     on_record(VEC.format("u32", "len1"), freed_on_ok)),
    ("Vec<bool> error allocation on the block of the vector", CORPUS,
     on_record(VEC.format("bool", "len3/invalid_middle"), error_on_vector_block)),
    ("Vec<u8> an extra resize", CORPUS,
     on_record(VEC.format("u8", "resize/len3145728/short"), extra_resize)),
    ("Vec<u32> element layout", CORPUS,
     on_record(VEC.format("u32", "len1"), element_layout), "layout mismatch"),
    ("cautious::<u32> above the bound without the cap", CORPUS,
     on_record("cautious/u32/hint1025", cautious_uncapped)),
    ("cautious::<Option<u64>> for u32::MAX", CORPUS,
     on_record("cautious/Option<u64>/hint4294967295", cautious_plus_one)),
    ("cautious::<bool> without the lower bound 1", CORPUS,
     on_record("cautious/bool/hint1", cautious_zero)),
    ("cautious::<bool> argument", CORPUS,
     on_record("cautious/bool/hint4095", cautious_hint)),
    ("cautious::<u32> forged zero-sized layout", CORPUS,
     on_record("cautious/u32/hint1023", zero_sized), "layout mismatch"),
    ("write_all on an empty buffer calls write", NOSTD,
     on_record(WRITE_ALL.format("empty/would_fail"), empty_buffer_calls_write)),
    ("write_all takes Ok(0) as success", NOSTD,
     on_record(WRITE_ALL.format("zero/first"), zero_count_accepted)),
    ("write_all WriteZero message", NOSTD,
     on_record(WRITE_ALL.format("zero/after_partial"), write_zero_message)),
    ("write_all returns Interrupted instead of retrying", NOSTD,
     on_record(WRITE_ALL.format("interrupted/then_rest"), interrupted_returned)),
    ("write_all retries Interrupted on an advanced buffer", NOSTD,
     on_record(WRITE_ALL.format("interrupted/after_partial"), retry_advanced)),
    ("write_all continues on the whole buffer after a partial count", NOSTD,
     on_record(WRITE_ALL.format("partial/one_then_rest"), rest_not_advanced)),
    ("write_all returns after a count above the length", NOSTD,
     on_record(WRITE_ALL.format("overrun/by_one"), returns_ok)),
    ("write_all panic reports the original length", NOSTD,
     on_record(WRITE_ALL.format("overrun/after_partial"), overrun_original_length)),
    ("write_all panic reports the length as its index", NOSTD,
     on_record(WRITE_ALL.format("overrun/by_one"), overrun_index_is_length)),
    ("write_all swallows a writer error", NOSTD,
     on_record(WRITE_ALL.format("error/other"), returns_ok)),
    ("write_all replaces the WriteZero error of the writer", NOSTD,
     on_record(WRITE_ALL.format("error/writers_write_zero"), own_write_zero_replaced)),
    ("write_all returns after a panic of write", NOSTD,
     on_record(WRITE_ALL.format("panic/first"), returns_ok)),
    ("write_all unwinds without the panicking call in the state of the writer", NOSTD,
     on_record(WRITE_ALL.format("panic/after_partial"), unwind_drops_call)),
    ("write_all calls flush (rejected by the record reader)", NOSTD,
     on_record(WRITE_ALL.format("whole/one_byte"), flush_called), "writer received flush"),
]
