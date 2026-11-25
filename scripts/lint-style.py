#!/usr/bin/env python3
"""Textual Lean conventions across all root-owned libraries."""
from pathlib import Path
import re
import sys

from lean_source import code_only

ROOT = Path(__file__).resolve().parent.parent
# Packages whose axiom audit walks their tests. An `example` leaves no declaration,
# so the audit cannot see its axioms; these packages name every test instead. The
# check is here rather than in the audit because Lake replays a cached audit when
# only an `example` changed: the module it imports compiles to the same bytes.
NAMED_ONLY = (ROOT / 'packages' / 'solanalib-sbpf',)


def lean_files(root=ROOT):
    packages = [root, root / 'examples', *sorted((root / 'packages').glob('*'))]
    packages += sorted((root / 'tools').glob('*conformance'))
    for package in packages:
        for name in ('Solanalib', 'SolanalibTest'):
            aggregate = package / (name + '.lean')
            if aggregate.is_file():
                yield aggregate
            yield from sorted((package / name).rglob('*.lean'))


def violations(text, named_only=False):
    header = '\n'.join(text.splitlines()[:6])
    for pattern, message in (
        (r'^Copyright \(c\) [0-9]{4} .* All rights reserved\.$', 'missing copyright owner'),
        (r'^Authors: .* Contributors$', 'missing Authors: <Project> Contributors'),
        (r'^Released under Apache 2\.0 license', 'missing Apache 2.0 license line'),
    ):
        if not re.search(pattern, header, re.M):
            yield 1, message
    for line, original in enumerate(text.splitlines(), 1):
        if len(original) > 100 and not re.search(r'https?://', original):
            yield line, f'line exceeds 100 chars ({len(original)})'
    code = code_only(text)
    for line, body in enumerate(code.splitlines(), 1):
        if re.search(r'(?<![\w])λ(?![\w])', body):
            yield line, "bare 'λ': use 'fun'"
        if re.search(r'(?<!\S)\$(?!\S)', body):
            yield line, "'$' application: use '<|' or '|>'"
        if named_only and re.match(r'\s*example\b', body):
            yield line, "'example' hides its axioms from the audit: name the theorem"
    # A module doc command is executable syntax; imports must precede it.
    docs = re.search(r'^/-!', text, re.M)
    imports = list(re.finditer(r'^(?:public )?(?:meta )?import(?: all)?\s', code, re.M))
    if docs and imports and docs.start() < imports[-1].start():
        yield text.count('\n', 0, docs.start()) + 1, 'module docstring precedes imports'


def main():
    errors = 0
    paths = list(lean_files())
    for path in paths:
        named_only = any(path.is_relative_to(package) for package in NAMED_ONLY)
        for line, message in violations(path.read_text(), named_only):
            print(f'{path.relative_to(ROOT)}:{line}: {message}', file=sys.stderr)
            errors += 1
    if not errors:
        print(f'lint-style: {len(paths)} files OK')
    return int(bool(errors))


if __name__ == '__main__':
    raise SystemExit(main())
