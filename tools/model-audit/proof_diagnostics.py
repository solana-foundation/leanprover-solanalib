#!/usr/bin/env python3
"""Recognize proof-placeholder diagnostics in Lean and Lake output."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
PLACEHOLDER = re.compile(r"\bdeclaration uses\s+['`\"‘“]?sorry\b|\bsorryAx\b")


def has_proof_placeholder(text: str) -> bool:
    """Accept both current backticks and older quoted diagnostics, including cache replay."""
    return PLACEHOLDER.search(ANSI.sub("", text)) is not None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", nargs="+", type=Path)
    args = parser.parse_args()
    failed = False
    for name in args.logs:
        for line, text in enumerate(name.read_text().splitlines(), 1):
            if has_proof_placeholder(text):
                print(f"Proof placeholder: {name}:{line}: {text}", file=sys.stderr)
                failed = True
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
