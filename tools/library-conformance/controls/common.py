"""Helpers for family control files, `controls/<Family>.py`.

A family control file exports

    CONTROLS = [(label, corpus, mutate), ...]          # or (label, corpus, mutate, expected)

where `mutate(records)` changes the record list of the corpus in place. `run.py --model-only` applies each
control to a copy of the corpus and requires the checker to fail with `expected` in its output: by
default `MISMATCH <corpus>/<id>` for a mutation built with `on_record`, else `MISMATCH`. The offline
tests require every control to change its corpus. A precondition control is built with
`outside_precondition` (or names the precondition in `expected`); its `expected` must appear in the report
of its record, and it exercises the preconditions the checker of that record decides.
"""


def on_record(record_id, change):
    """A mutation of the one record with this id, which the checker must then reject."""
    def mutate(records):
        matches = [r for r in records if r["id"] == record_id]
        if len(matches) != 1:
            raise ValueError(f"control target {record_id!r} matches {len(matches)} records")
        change(matches[0])
    mutate.record_id = record_id
    return mutate


def outside_precondition(record_id, change):
    """A precondition control: a mutation of the one record with this id that breaks a precondition its
    checker decides (`decidesRequires`). The `expected` of the control (required) is the message of the checker for
    that precondition, which must appear in the report of that record."""
    mutate = on_record(record_id, change)
    mutate.precondition = True
    return mutate


def setter(path, value):
    """Set `record[path...]` to `value(old)`."""
    def change(record):
        item = record
        for key in path[:-1]:
            item = item[key]
        item[path[-1]] = value(item[path[-1]])
    return change


def keep_reply(record):
    """Restore consumed replies in the observed state to test reply accounting."""
    record["outcome"]["state"]["syscalls"]["replies"] = record["state"]["syscalls"]["replies"]


def _hexform():
    """The hex form of the runner (`hexform.py` beside `run.py`), so controls build canonical hex."""
    import sys
    from pathlib import Path
    root = str(Path(__file__).resolve().parent.parent)
    if root not in sys.path:
        sys.path.insert(0, root)
    import hexform
    return hexform


def hex_bytes(text):
    """Bytes of a recorded hex string (`[N]` stands for N zero bytes)."""
    return _hexform().expand_hex(text)


def hex_text(data):
    """The canonical hex form of the recorder (zero runs of at least `hexform.ZERO_RUN` bytes as `[N]`)."""
    return _hexform().compact_hex(data)


def flip_spare(account, index):
    """Flip one byte of the `spare` of a read-back account (every byte after `data_len` up to the original
    length plus 10 KiB) and keep its summary `spare_nonzero_at` consistent, as a recording would be;
    the region reader rejects a summary that disagrees with the bytes."""
    spare = bytearray(hex_bytes(account["spare"]))
    spare[index] ^= 0x01
    account["spare"] = hex_text(bytes(spare))
    if "spare_nonzero_at" in account:
        first = next((i for i, b in enumerate(spare) if b), None)
        account["spare_nonzero_at"] = None if first is None else len(hex_bytes(account["data"])) + first
    return account
