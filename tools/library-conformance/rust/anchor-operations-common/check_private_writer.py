#!/usr/bin/env python3
"""Check the byte-identical private BpfWriter modules against pinned sources.

The older crates do not reexport this type. Only these two whole private
modules are copied for conformance; their real Solana memcpy dependency is
unchanged. Other cases call the linked Anchor crates directly. This script
checks source bytes and performs no Rust build or execution.
"""

import argparse
import hashlib
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("registry", type=Path,
                        help="immutable Cargo registry source directory")
    args = parser.parse_args()
    drivers = Path(__file__).resolve().parent.parent
    expected = "544511c105eb66783551f85ef85f4e60b13c86350de6d9f1441fff94937d8511"
    for version, suffix in [("0.27.0", "027"), ("0.29.0", "029")]:
        source = args.registry / f"anchor-lang-{version}" / "src/bpf_writer.rs"
        copy = drivers / f"anchor-operations-{suffix}" / "src/private_bpf_writer.rs"
        original = source.read_bytes()
        if hashlib.sha256(original).hexdigest() != expected:
            raise SystemExit(f"wrong source hash: {source}")
        if original != copy.read_bytes():
            raise SystemExit(f"private module differs from immutable source: {copy}")
        print(f"anchor-lang {version}: complete private module matches {expected}")


if __name__ == "__main__":
    main()
