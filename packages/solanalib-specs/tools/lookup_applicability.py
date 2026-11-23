#!/usr/bin/env python3
"""Select reviewed function models for one resolved package/build description.

Exit status: 0 at least one eligible model; 1 unsupported; 2 malformed input;
3 unresolved build facts. Input and output are JSON. The default generated
manifest ships beside the specification package, so repository tools are not
needed. Use --model repeatedly to limit the result to named registry models.
"""

import argparse
import json
from pathlib import Path
import sys

from applicability import load_manifest, lookup, read_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", required=True, help="resolved build JSON path, or - for stdin")
    parser.add_argument("--manifest", type=Path, help="override the installed applicability manifest")
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
