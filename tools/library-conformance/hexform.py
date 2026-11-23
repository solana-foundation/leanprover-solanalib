"""The hex form of the corpus for byte fields, shared by `run.py` and `controls/common.py`.

Bytes are written as lowercase hex pairs; every maximal run of at least `ZERO_RUN` zero bytes is
written `[N]`, its decimal length. The recorder (`rust/recorder`) and the Lean reader (`parseHex`)
implement the same form.
"""

import re

HEX = re.compile(r"^(?:[0-9a-f]{2})*$")
ZERO_RUN = 64
COMPACT_HEX = re.compile(r"^(?:[0-9a-f]{2}|\[\d+\])*$")


def expand_hex(text: str) -> bytes:
    """Bytes of a recorded hex string, in which `[N]` stands for N zero bytes."""
    if COMPACT_HEX.match(text) is None:
        raise ValueError(f"not a hex string: {text[:40]!r}")
    out = bytearray()
    for part in re.findall(r"\[\d+\]|[0-9a-f]{2}", text):
        out += bytes(int(part[1:-1])) if part.startswith("[") else bytes.fromhex(part)
    return bytes(out)


def compact_hex(data: bytes) -> str:
    """The canonical form of the recorder: every maximal run of at least `ZERO_RUN` zero bytes as `[N]`."""
    parts, i = [], 0
    while i < len(data):
        j = i
        while j < len(data) and data[j] == 0:
            j += 1
        if j - i >= ZERO_RUN:
            parts.append(f"[{j - i}]")
            i = j
        else:
            parts.append(data[i:i + 1].hex())
            i += 1
    return "".join(parts)
