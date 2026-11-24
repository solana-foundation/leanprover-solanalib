"""Observation mutations for the exact raw declaration and SDK-wrapper drivers."""
from common import hex_bytes, hex_text, on_record

BASE = "raw_runtime_solana_define_syscall_5_1_0"


def flip(path, offset=0):
    def mutate(record):
        item = record
        for key in path[:-1]:
            item = item[key]
        data = bytearray(hex_bytes(item[path[-1]]))
        data[offset] ^= 1
        item[path[-1]] = hex_text(data)
    return mutate


def set_value(path, value):
    def mutate(record):
        item = record
        for key in path[:-1]:
            item = item[key]
        item[path[-1]] = value
    return mutate


def terminal_returns(record):
    args = record["args"]
    record["outcome"] = {
        "exit": "returned", "state": record["state"], "trace": record["outcome"]["trace"],
        "result": {"status": 1, "output": args["output"], "guards": args["guards"],
                   "program_output": args["program_output"], "program_guards": args["program_guards"],
                   "bump": args["bump"]},
    }


def reverse_find_writes(record):
    trace = record["outcome"]["trace"]
    trace[-2:] = list(reversed(trace[-2:]))


def change_seed_read(record):
    record["outcome"]["trace"][2]["seed"] = "0909"


def stale_input_buffer(record):
    record["outcome"]["state"]["input"] = record["state"]["input"]


def forbidden_typed_input_destination(record):
    record["args"]["input_region"] = True
    guards = hex_bytes(record["args"]["guards"])
    record["state"]["input"] = hex_text(guards[:8] + hex_bytes(record["args"]["output"]) + guards[8:])
    record["outcome"]["state"]["input"] = hex_text(
        guards[:8] + hex_bytes(record["outcome"]["result"]["output"]) + guards[8:])


CONTROLS = [
    ("memcpy copies every source byte", BASE,
     on_record("copy/nonempty", flip(["outcome", "result", "output"], 4))),
    ("memcpy overlap cannot return", BASE, on_record("copy/overlap", terminal_returns)),
    ("zero memcpy leaves guard bytes", BASE,
     on_record("copy/zero-null", flip(["outcome", "result", "guards"])), "output guard bytes changed"),
    ("memset keeps its byte argument", BASE,
     on_record("set/high-byte", set_value(["args", "byte"], 254))),
    ("memset writes zeros", BASE, on_record("set/zero-byte", flip(["outcome", "result", "output"]))),
    ("PDA failure preserves destination", BASE,
     on_record("create/on-curve-null", flip(["outcome", "result", "output"])), "failed derivation wrote an output"),
    ("PDA excessive seed count terminates", BASE, on_record("create/count-17", terminal_returns)),
    ("PDA excessive seed length terminates", BASE, on_record("find/seed-33", terminal_returns)),
    ("PDA seed order and bytes reach the provider", BASE, on_record("create/success", change_seed_read)),
    ("PDA bump excludes zero", BASE, on_record("find/success", set_value(["outcome", "result", "bump"], 0))),
    ("PDA writes bump before address", BASE, on_record("find/success", reverse_find_writes)),
    ("failed PDA search ignores overlap", BASE,
     on_record("find/overlap-failure", set_value(["outcome", "result", "status"], 0))),
    ("SHA256 has a complete 32-byte result", BASE,
     on_record("sha256/segmented", flip(["outcome", "result", "output"], 31))),
    ("SHA256 preserves segment reads", BASE, on_record("sha256/segmented", change_seed_read)),
    ("clock preserves negative signed field bits", BASE,
     on_record("clock", flip(["outcome", "result", "output"], 15))),
    ("rent uses native zero padding", BASE,
     on_record("rent", flip(["outcome", "result", "output"], 23))),
    ("epoch schedule uses native zero padding", BASE,
     on_record("epoch", flip(["outcome", "result", "output"], 17))),
    ("stack height reads shared invocation state", BASE,
     on_record("stack/5", set_value(["outcome", "result", "status"], 1))),
    ("empty return-data setter clears the bytes", BASE,
     on_record("set-return/0", set_value(["outcome", "state", "return_data"], "0203"))),
    ("setter tags data with the current program", BASE,
     on_record("set-return/1", flip(["outcome", "state", "return_program"]))),
    ("oversized return data cannot return", BASE, on_record("set-return/1025", terminal_returns)),
    ("get reports the full untruncated length", BASE,
     on_record("get-return/1", set_value(["outcome", "result", "status"], 1))),
    ("get preserves the destination suffix", BASE,
     on_record("get-return/5", flip(["outcome", "result", "output"], 4)), "return-data suffix changed"),
    ("zero-copy get leaves program identity untouched", BASE,
     on_record("get-return/0", flip(["outcome", "result", "program_output"])), "zero-copy get wrote program identity"),
    ("get returns the setter program identity", BASE,
     on_record("get-return/2", flip(["outcome", "result", "program_output"]))),
    ("get overlap cannot return", BASE, on_record("get-return/overlap", terminal_returns)),
    ("copied program1.15 declaration result", "raw_runtime_solana_program_1_15_2",
     on_record("copy/nonempty", flip(["outcome", "result", "output"]))),
    ("copied program1.18 declaration result", "raw_runtime_solana_program_1_18_26",
     on_record("sha256/segmented", flip(["outcome", "result", "output"]))),
    ("CPI3 setter forwards empty data", "raw_runtime_solana_cpi_3_1_0",
     on_record("set-return/0", set_value(["outcome", "state", "return_data"], "ff"))),
    ("Anchor stack wrapper forwards the observed height", "raw_runtime_anchor_lang_1_0_2",
     on_record("stack/5", set_value(["outcome", "result", "status"], 0))),
    ("private logger copy declaration", "raw_runtime_pinocchio_log_0_5_1",
     on_record("copy/0", flip(["outcome", "result", "output"]))),
    ("private logger set declaration", "raw_runtime_pinocchio_log_0_5_1",
     on_record("set/2", flip(["outcome", "result", "output"]))),
    ("mapped memset cannot return a stale input buffer", BASE,
     on_record("input-region/set/high-byte", stale_input_buffer),
     "actual input buffer differs from ordered output stores"),
    ("mapped memcpy cannot return a stale input buffer", BASE,
     on_record("input-region/copy/nonempty", stale_input_buffer),
     "actual input buffer differs from ordered output stores"),
    ("mapped PDA output updates the live input buffer", BASE,
     on_record("input-region/create/success", stale_input_buffer),
     "actual input buffer differs from ordered output stores"),
    ("mapped return data updates the live input buffer", BASE,
     on_record("input-region/get-return/5", stale_input_buffer),
     "actual input buffer differs from ordered output stores"),
    ("mapped output snapshot is the actual before allocation", BASE,
     on_record("input-region/set/high-byte", flip(["state", "input"], 8)),
     "input snapshot differs from mapped output storage"),
    ("mapped write preserves earlier input bytes", BASE,
     on_record("input-region/set/high-byte", flip(["outcome", "state", "input"], 7)),
     "actual input buffer differs from ordered output stores"),
    ("mapped return prefix preserves the input suffix", BASE,
     on_record("input-region/get-return/5", flip(["outcome", "state", "input"], 12)),
     "actual input buffer differs from ordered output stores"),
    ("empty mapped write leaves the input buffer", BASE,
     on_record("input-region/set/zero-null", flip(["outcome", "state", "input"])),
     "actual input buffer differs from ordered output stores"),
    ("failed mapped search leaves the input buffer", BASE,
     on_record("input-region/find/count-16", flip(["outcome", "state", "input"], 8)),
     "actual input buffer differs from ordered output stores"),
    ("mapped state projection preserves the heap position", BASE,
     on_record("input-region/set/high-byte", set_value(["outcome", "state", "heap_pos"], 18))),
    ("mapped get writes data before the program identity", BASE,
     on_record("input-region/get-return/5", reverse_find_writes)),
    ("typed input destinations retain the selected runtime pointer restriction", BASE,
     on_record("clock", forbidden_typed_input_destination)),
]

# The generic first-leaf mutation changes the synthetic, untouched bump field.
# The observation parser rejects that framing change before reaching the run relation.
# Mutate a modeled result/state field so the semantic control reaches that relation.
def change_status(record):
    record["outcome"]["result"]["status"] += 1


def semantic_change(record_id):
    if record_id.startswith("stack/") or record_id.startswith("get-return/"):
        return change_status
    if record_id.startswith("set-return/"):
        return set_value(["outcome", "state", "return_data"], "ff")
    return flip(["outcome", "result", "output"])


_SEMANTIC_RECORDS = {
    BASE: ["copy/nonempty", "set/high-byte", "create/success", "sha256/segmented",
           "clock", "rent", "epoch", "stack/0", "set-return/0", "get-return/0"],
    "raw_runtime_solana_define_syscall_2_3_0": [
        "copy/nonempty", "set/high-byte", "create/success", "sha256/segmented", "clock", "rent"],
    "raw_runtime_solana_define_syscall_4_0_1": [
        "copy/nonempty", "set/high-byte", "epoch", "set-return/0"],
    "raw_runtime_solana_program_1_15_2": [
        "copy/nonempty", "set/high-byte", "create/success", "sha256/segmented", "rent"],
    "raw_runtime_solana_program_1_18_26": [
        "copy/nonempty", "set/high-byte", "create/success", "sha256/segmented", "rent", "clock"],
    "raw_runtime_pinocchio_0_9_2": ["clock"],
    "raw_runtime_solana_cpi_2_2_1": ["get-return/0"],
    "raw_runtime_solana_cpi_3_1_0": ["set-return/0"],
    "raw_runtime_anchor_lang_1_0_2": ["stack/0"],
    "raw_runtime_pinocchio_log_0_5_1": ["copy/0", "set/2"],
}
SEMANTIC = [
    (corpus, on_record(record_id, semantic_change(record_id)),
     "The generic mutation changes the untouched auxiliary bump field and is rejected by the "
     "observation parser; this mutation changes the modeled return bytes, register or state.")
    for corpus, records in _SEMANTIC_RECORDS.items() for record_id in records
]


# Retain parent declaration controls and the selected exact version observations.
_ORIGINAL_CONTROLS = CONTROLS
CONTROLS = [(entry[0], selected_corpus, *entry[2:])
    for selected_corpus, selected_ids in (('raw_runtime_anchor_lang_1_0_2', ('stack/0', 'stack/1', 'stack/5')), ('raw_runtime_solana_cpi_2_2_1', ('get-return/0', 'get-return/1', 'get-return/2', 'get-return/5', 'get-return/empty', 'get-return/overlap', 'input-region/get-return/0', 'input-region/get-return/5')), ('raw_runtime_solana_cpi_3_1_0', ('set-return/0', 'set-return/1', 'set-return/1024', 'set-return/1025')), ('raw_runtime_solana_define_syscall_2_3_0', ('clock', 'copy/nonempty', 'copy/overlap', 'copy/zero-null', 'create/count-17', 'create/empty-seeds', 'create/on-curve-null', 'create/seed-32', 'create/seed-33', 'create/success', 'find/count-16', 'find/count-17', 'find/empty-seeds', 'find/on-curve-null', 'find/overlap-failure', 'find/overlap-success', 'find/seed-32', 'find/seed-33', 'find/success', 'input-region/copy/nonempty', 'input-region/copy/zero-null', 'input-region/create/success', 'input-region/find/count-16', 'input-region/find/success', 'input-region/set/high-byte', 'input-region/set/zero-null', 'rent', 'set/high-byte', 'set/zero-byte', 'set/zero-null', 'sha256/empty', 'sha256/segmented')), ('raw_runtime_solana_define_syscall_4_0_1', ('copy/nonempty', 'copy/overlap', 'copy/zero-null', 'epoch', 'input-region/copy/nonempty', 'input-region/copy/zero-null', 'input-region/set/high-byte', 'input-region/set/zero-null', 'set-return/0', 'set-return/1', 'set-return/1024', 'set-return/1025', 'set/high-byte', 'set/zero-byte', 'set/zero-null')), ('raw_runtime_solana_define_syscall_5_1_0', ('clock', 'copy/nonempty', 'copy/overlap', 'copy/zero-null', 'create/count-17', 'create/empty-seeds', 'create/on-curve-null', 'create/seed-32', 'create/seed-33', 'create/success', 'epoch', 'find/count-16', 'find/count-17', 'find/empty-seeds', 'find/on-curve-null', 'find/overlap-failure', 'find/overlap-success', 'find/seed-32', 'find/seed-33', 'find/success', 'get-return/0', 'get-return/1', 'get-return/2', 'get-return/5', 'get-return/empty', 'get-return/overlap', 'input-region/copy/nonempty', 'input-region/copy/zero-null', 'input-region/create/success', 'input-region/find/count-16', 'input-region/find/success', 'input-region/get-return/0', 'input-region/get-return/5', 'input-region/set/high-byte', 'input-region/set/zero-null', 'rent', 'set-return/0', 'set-return/1', 'set-return/1024', 'set-return/1025', 'set/high-byte', 'set/zero-byte', 'set/zero-null', 'sha256/empty', 'sha256/segmented', 'stack/0', 'stack/1', 'stack/5')), ('raw_runtime_solana_program_1_15_2', ('copy/nonempty', 'copy/overlap', 'copy/zero-null', 'create/count-17', 'create/empty-seeds', 'create/on-curve-null', 'create/seed-32', 'create/seed-33', 'create/success', 'find/count-16', 'find/count-17', 'find/empty-seeds', 'find/on-curve-null', 'find/overlap-failure', 'find/overlap-success', 'find/seed-32', 'find/seed-33', 'find/success', 'input-region/copy/nonempty', 'input-region/copy/zero-null', 'input-region/create/success', 'input-region/find/count-16', 'input-region/find/success', 'input-region/set/high-byte', 'input-region/set/zero-null', 'rent', 'set/high-byte', 'set/zero-byte', 'set/zero-null', 'sha256/empty', 'sha256/segmented')), ('raw_runtime_solana_program_1_18_26', ('clock', 'copy/nonempty', 'copy/overlap', 'copy/zero-null', 'create/count-17', 'create/empty-seeds', 'create/on-curve-null', 'create/seed-32', 'create/seed-33', 'create/success', 'find/count-16', 'find/count-17', 'find/empty-seeds', 'find/on-curve-null', 'find/overlap-failure', 'find/overlap-success', 'find/seed-32', 'find/seed-33', 'find/success', 'input-region/copy/nonempty', 'input-region/copy/zero-null', 'input-region/create/success', 'input-region/find/count-16', 'input-region/find/success', 'input-region/set/high-byte', 'input-region/set/zero-null', 'rent', 'set/high-byte', 'set/zero-byte', 'set/zero-null', 'sha256/empty', 'sha256/segmented')))
    for entry in _ORIGINAL_CONTROLS if entry[1] == BASE and entry[2].record_id in selected_ids]
CONTROLS += [entry for entry in _ORIGINAL_CONTROLS if entry[1] == "raw_runtime_pinocchio_log_0_5_1"]
CONTROLS += [(entry[0], "raw_runtime_pinocchio_0_9_2", *entry[2:])
    for entry in _ORIGINAL_CONTROLS if entry[1] == BASE and entry[2].record_id == "clock"]
SEMANTIC = [entry for entry in SEMANTIC if entry[0] in ('raw_runtime_anchor_lang_1_0_2', 'raw_runtime_solana_cpi_2_2_1', 'raw_runtime_solana_cpi_3_1_0', 'raw_runtime_solana_define_syscall_2_3_0', 'raw_runtime_solana_define_syscall_4_0_1', 'raw_runtime_solana_define_syscall_5_1_0', 'raw_runtime_solana_program_1_15_2', 'raw_runtime_solana_program_1_18_26', 'raw_runtime_pinocchio_0_9_2', 'raw_runtime_pinocchio_log_0_5_1')]
