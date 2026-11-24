"""Reject changed Anchor ownership, callback, cursor and diagnostic observations."""

from common import on_record


def replace(path, value):
    def change(record):
        target = record
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
    return change


def increment(path):
    def change(record):
        target = record
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] += 1
    return change


def reverse_callbacks(record):
    record["outcome"]["state"]["callbacks"].reverse()


def reverse_logs(record):
    record["outcome"]["state"]["syscalls"]["log"].reverse()


CONTROLS = []


def control(version, label, record_id, change):
    CONTROLS.append((label, "anchor_operations_" + version, on_record(record_id, change)))


for version in ("0_27_0", "0_29_0", "0_32_1", "1_0_2", "1_1_2"):
    control(version, "ErrorCode allocates its name", "code_name/0",
            increment(["outcome", "state", "fresh_live"]))
    control(version, "versioned ErrorCode message", "from_code/0",
            replace(["outcome", "result", "value", "AnchorError", "message"], "another release"))
    control(version, "inline versus boxed conversion allocation", "from_code/0",
            increment(["outcome", "state", "fresh_live"]))
    control(version, "account-name callback cleanup order", "update/false/false/name",
            reverse_callbacks)
    control(version, "name conversion unwind state", "update/true/true/name_panic",
            increment(["outcome", "state", "fresh_live"]))
    control(version, "borrowed Context accounts reference", "context/new",
            replace(["outcome", "result", "accounts_identity"], False))
    control(version, "Context bumps moved intact", "context/new",
            replace(["outcome", "result", "bumps", 0, 1], 4))
    control(version, "CpiContext full program identity", "cpi_context/0",
            replace(["outcome", "result", "program_identity"], False))
    control(version, "CpiContext creates empty remaining vector", "cpi_context/0",
            replace(["outcome", "result", "remaining_length"], 1))
    control(version, "with_signer keeps exact seed descriptor", "cpi_context/2",
            replace(["outcome", "result", "seed_identity"], False))
    control(version, "logging call and compared-key order", "log/true/2/2", reverse_logs)
    control(version, "logging exact rendered bytes", "log/false/0/0",
            replace(["outcome", "state", "syscalls", "log", 0, "bytes"], "00"))

for version in ("0_27_0", "0_29_0", "0_32_1"):
    control(version, "pubkeys replacement destroys old comparison", "update/true/true/pubkeys",
            replace(["outcome", "state", "strings_live", 2], True))
    control(version, "with_values retains original Borsh string", "with_values/true/0",
            replace(["outcome", "state", "strings_live", 0], False))
    control(version, "with_values callback order", "with_values/false/0", reverse_callbacks)
    control(version, "right Display unwind drops held first String", "with_values/false/2",
            increment(["outcome", "state", "fresh_live"]))
    control(version, "double panic remains terminal", "with_values/false/7",
            replace(["outcome", "reason"], "unrelated abort"))
    control(version, "terminal report forbidden outside double-panic script", "with_values/false/7",
            replace(["args", "mode"], 0))

for version in ("0_27_0", "0_29_0", "0_32_1", "1_1_2"):
    control(version, "short write keeps cursor advance", "write_all/4",
            replace(["outcome", "state", "writer", "position"], 1))
    control(version, "short write keeps copied prefix", "write_all/4",
            replace(["outcome", "state", "writer", "bytes"], "2b2b2b2b"))
    control(version, "short write reaches actual memcpy", "write_all/4",
            replace(["outcome", "state", "syscalls", "log"], []))
    control(version, "writer WriteZero diagnostic", "write_all/1",
            replace(["outcome", "result", "err", "kind"], "InvalidInput"))

control("0_27_0", "inline From<AnchorError> preserves owned names", "from_anchor/2",
        replace(["outcome", "result", "strings", 0], None))
control("0_27_0", "inline ProgramError preserves full owned Borsh text", "from_program/3",
        replace(["outcome", "result", "value", "ProgramError", "error", "fields", 0], "changed"))
control("0_27_0", "source origin assignment destroys old account-name String", "update/true/true/source",
        replace(["outcome", "state", "strings_live", 1], True))
control("0_27_0", "IDL short scalar preserves failed field cursor", "idl/10",
        replace(["outcome", "state", "remaining"], ""))
control("0_27_0", "IDL diagnostic allocation retained", "idl/0",
        replace(["outcome", "state", "fresh_live"], 0))
control("0_27_0", "IDL correct no-payload arm", "idl/6",
        replace(["outcome", "result", "ok", "variant"], "CreateBuffer"))
control("0_32_1", "Anchor equality keeps code-only result", "eq/0",
        replace(["outcome", "result"], False))
control("0_32_1", "IO Display panic cleanup", "from_io/1", reverse_callbacks)
control("0_32_1", "IO Drop panic skips Anchor Box", "from_io/2",
        increment(["outcome", "state", "fresh_live"]))
control("0_32_1", "empty input with capacity still calls zero-byte memcpy", "write_all/2",
        replace(["outcome", "state", "syscalls", "log"], []))
control("0_32_1", "exhausted empty write skips memcpy", "write_all/6",
        replace(["outcome", "state", "syscalls", "log"],
                [{"syscall": "sol_memcpy_", "bytes": ""}]))
control("0_32_1", "signer constructor retains program data owner", "cpi_context/1",
        replace(["outcome", "state", "data_count"], 1))
control("0_32_1", "signer replacement preserves vector capacity", "cpi_context/2",
        replace(["outcome", "result", "remaining_capacity"], 1))
control("0_32_1", "pubkeys replacement preserves original Borsh payload", "update/true/true/pubkeys",
        replace(["outcome", "result", "value", "ProgramError", "error", "fields", 0],
                "changed IO diagnostic"))
control("0_32_1", "value conversion preserves receiver Box identity", "with_values/true/0",
        increment(["outcome", "result", "box"]))
control("0_32_1", "name conversion unwind still drops its operand", "update/true/true/name_panic",
        replace(["outcome", "state", "callbacks"], ["display name"]))
control("1_0_2", "remaining assignment drops both old Rc aliases", "cpi_context/3",
        replace(["outcome", "state", "data_count"], 5))
control("1_0_2", "remaining assignment retires old Vec buffer", "cpi_context/3",
        replace(["outcome", "state", "old_remaining_freed"], False))
control("1_1_2", "loader error drops consumed bincode diagnostic", "loader/0",
        replace(["outcome", "state", "fresh_live"], 2))
control("1_1_2", "loader leaves original cursor", "loader/10",
        replace(["outcome", "state", "remaining"], ""))
control("1_1_2", "default decoder preserves unchecked error mutation", "default_decode/1",
        replace(["outcome", "state", "remaining"], "017788"))
control("1_1_2", "default decoder preserves unchecked unwind", "default_decode/2",
        replace(["outcome", "reason"], "different callback"))


# Select original controls for the recorded cumulative library versions.
CONTROLS = [entry for entry in CONTROLS if entry[1] in ('anchor_operations_0_27_0', 'anchor_operations_0_29_0', 'anchor_operations_0_32_1', 'anchor_operations_1_0_2', 'anchor_operations_1_1_2')]
