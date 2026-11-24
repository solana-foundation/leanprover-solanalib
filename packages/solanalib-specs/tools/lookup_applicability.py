#!/usr/bin/env python3
"""Select reviewed function models for one resolved package/build description.

Exit status: 0 at least one eligible model; 1 unsupported; 2 malformed input;
3 unresolved build facts. Input and output are JSON. A checkout reads its current
registry; a standalone bundle reads its exported applicability.json. An explicit
--manifest selects an export. Use --model repeatedly to limit the result to named models.
"""

import argparse
import json
from pathlib import Path
import sys

from applicability import load_manifest, lookup, read_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", required=True, help="resolved build JSON path, or - for stdin")
    parser.add_argument("--manifest", type=Path, help="read an exported applicability manifest instead of the registry")
    parser.add_argument("--model", action="append", help="exact registered model ID")
    args = parser.parse_args()
    try:
        contents = sys.stdin.read() if args.build == "-" else Path(args.build).read_text()
        answer = lookup(load_manifest(args.manifest), read_json(contents), args.model)
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "invalid", "error": str(error)}, ensure_ascii=False))
        return 2
    print(json.dumps(answer, indent=2, ensure_ascii=False))
    return {"eligible": 0, "unsupported": 1, "unresolved": 3}[answer["status"]]


if __name__ == "__main__":
    raise SystemExit(main())
