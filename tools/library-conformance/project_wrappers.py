#!/usr/bin/env python3
"""Project hash-pinned wrapper functions for whole-invocation mock conformance.

The selected Rust text is copied byte-for-byte. Imports supplied by the reviewed
manifest resolve account/context/constructor dependencies normally and replace
only an explicit invocation signature. This tool neither parses nor selects an
invocation implementation. The result is a projection, not the original crate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


class ProjectionError(ValueError):
    """A source, selector, or projection no longer matches its sealed input."""


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def code_positions(source: str, start: int = 0):
    """Yield code characters while skipping Rust comments and string literals."""
    index = start
    while index < len(source):
        if source.startswith("//", index):
            end = source.find("\n", index + 2)
            index = len(source) if end < 0 else end + 1
            continue
        if source.startswith("/*", index):
            depth = 1
            index += 2
            while depth and index < len(source):
                if source.startswith("/*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ProjectionError("unterminated Rust block comment")
            continue
        raw = re.match(r'(?:br|cr|r)(#{0,255})"', source[index:])
        if raw:
            delimiter = '"' + raw.group(1)
            end = source.find(delimiter, index + len(raw.group(0)))
            if end < 0:
                raise ProjectionError("unterminated Rust raw string")
            index = end + len(delimiter)
            continue
        char = source[index]
        # A Rust lifetime is not a character literal. Character escapes and
        # single Unicode codepoints cover the pinned wrapper selectors here.
        character = re.match(r"'(?:[^'\\\n]|\\(?:u\{[0-9A-Fa-f_]+\}|x[0-9A-Fa-f]{2}|.))'", source[index:])
        if character:
            index += len(character.group(0))
            continue
        if char == '"':
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ProjectionError("unterminated Rust string")
            continue
        yield index, char
        index += 1


def select_function(source: str, name: str) -> tuple[str, int, int]:
    """Select one complete public free function, including its final newline."""
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
        raise ProjectionError("invalid function selector")
    if name in {"invoke", "invoke_signed", "invoke_unchecked", "invoke_signed_unchecked"}:
        raise ProjectionError("invocation implementations are outside wrapper projection")
    candidates = list(re.finditer(r"(?m)^pub (?:unsafe )?fn " + re.escape(name) + r"\b", source))
    candidate_starts = {match.start() for match in candidates}
    free_starts = set()
    scope = 0
    for position, char in code_positions(source):
        if position in candidate_starts and scope == 0:
            free_starts.add(position)
        if char == "{":
            scope += 1
        elif char == "}":
            scope -= 1
    matches = [match for match in candidates if match.start() in free_starts]
    if len(matches) != 1:
        raise ProjectionError(f"expected one public free function {name}, got {len(matches)}")
    start = matches[0].start()
    depth = 0
    entered = False
    for position, brace in code_positions(source, matches[0].end()):
        if brace not in "{}":
            continue
        depth += 1 if brace == "{" else -1
        if depth < 0:
            raise ProjectionError(f"unbalanced function {name}")
        entered = True
        if entered and depth == 0:
            end = position + 1
            if source[end:end + 1] == "\n":
                end += 1
            return source[start:end], source.count("\n", 0, start) + 1, source.count("\n", 0, position) + 1
    raise ProjectionError(f"unterminated function {name}")


def project(manifest: dict, source_root: Path) -> tuple[bytes, dict]:
    """Check full inputs and every selected body before emitting any output."""
    if manifest.get("schema_version") != 1 or manifest.get("kind") != "projected-wrapper":
        raise ProjectionError("unsupported projection manifest")
    sources = manifest.get("sources")
    selectors = manifest.get("functions")
    if not isinstance(sources, list) or not sources or not isinstance(selectors, list) or not selectors:
        raise ProjectionError("sources and functions must be nonempty lists")
    preamble = manifest.get("preamble")
    if not isinstance(preamble, str):
        raise ProjectionError("missing reviewed import preamble")
    source_root = source_root.resolve(strict=True)
    indexed: dict[str, tuple[str, dict]] = {}
    for entry in sources:
        relative = Path(entry["path"])
        path = (source_root / relative).resolve(strict=True)
        if relative.is_absolute() or not path.is_relative_to(source_root):
            raise ProjectionError("source path leaves the pinned registry root")
        data = path.read_bytes()
        if digest(data) != entry["sha256"]:
            raise ProjectionError(f"stale source {entry['id']}")
        if entry["id"] in indexed:
            raise ProjectionError("duplicate source identity")
        indexed[entry["id"]] = (data.decode("utf-8"), entry)
    seen: set[tuple[str, str]] = set()
    selected = []
    bodies = []
    for selector in selectors:
        key = (selector["source"], selector["name"])
        if key in seen or selector["source"] not in indexed:
            raise ProjectionError("duplicate selector or unknown source")
        seen.add(key)
        source, entry = indexed[selector["source"]]
        body, first, last = select_function(source, selector["name"])
        body_hash = digest(body.encode())
        if body_hash != selector["sha256"]:
            raise ProjectionError(f"stale function {selector['name']}")
        selected.append({"source": entry["id"], "path": entry["path"], "name": selector["name"],
                         "first_line": first, "last_line": last, "sha256": body_hash})
        bodies.append(body)
    used = {item[0] for item in seen}
    if used != set(indexed):
        raise ProjectionError("unselected source in projection manifest")
    result = ("// Generated by project_wrappers.py; exact pinned function text.\n"
              "// Projected-wrapper conformance: invocation is an explicit replacement.\n"
              + preamble.rstrip() + "\n\n" + "\n".join(bodies)).encode()
    receipt = {"schema_version": 1, "kind": "projected-wrapper", "sources": sources,
               "selected_functions": selected, "output_sha256": digest(result),
               "limits": ["not the original linked crate", "no invocation implementation selected",
                          "dependency build/profile and replacement signature need separate validation"]}
    return result, receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    protected = [args.manifest.resolve(), Path(__file__).resolve()]
    destinations = [args.output] + ([args.receipt] if args.receipt else [])
    resolved = [path.resolve() for path in destinations]
    if len(set(resolved)) != len(resolved) or any(
        path in protected or path.is_relative_to(args.source_root.resolve()) for path in resolved
    ):
        raise ProjectionError("projection destinations must be distinct from pinned inputs")
    manifest_bytes = args.manifest.read_bytes()
    result, receipt = project(json.loads(manifest_bytes), args.source_root)
    receipt["manifest_sha256"] = digest(manifest_bytes)
    receipt["generator_sha256"] = digest(Path(__file__).read_bytes())
    if args.check:
        if not args.output.is_file() or args.output.read_bytes() != result:
            raise ProjectionError("generated wrapper projection is stale")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(result)
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
