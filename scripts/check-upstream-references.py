#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Check that external URLs and Rust source paths refer to upstream source locations."""
import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
EXTENSIONS = {'.md', '.json', '.toml', '.py'}
NAMESPACE = re.compile(r'\bSolanalib[/.](?:Specs|Runtime)\b', re.IGNORECASE)
URL = re.compile(r'''(?<![a-z0-9+.-])(?:[a-z][a-z0-9+.-]*://|git@[\w.-]+:)[^\s`"'<>()[\]{},;|]+''', re.IGNORECASE)
TOKEN = re.compile(r'''[^\s`"'<>()[\]{},;|=]+''')
SOURCE_DIRECTORY = re.compile(r'(?:^|/)(?:src|crates|programs|target_chains)(?:/|$)')
SOURCE_FILE = re.compile(r'(?:\.rs|(?:^|/)Cargo\.(?:toml|lock))(?=$|[#:])')
LEAN_FILE = re.compile(r'\.lean(?=$|[#:])')
SOURCE_CONTEXT = re.compile(
    r'''\b(?:upstream(?:[_ -](?:source|path|file))?|rust[_ -](?:source|path|file)|'''
    r'''source[_ -](?:path|file)|path_in_vcs)["']?\s*[:=]''', re.IGNORECASE)


@dataclass(frozen=True)
class Finding:
    line: int
    kind: str
    reference: str


def project_url(url):
    """Links to this repository and its API site legitimately use its modules."""
    if url.startswith('git@github.com:'):
        url = 'https://github.com/' + url.split(':', 1)[1]
    parsed = urlsplit(url)
    path = parsed.path.lower().strip('/').split('/')
    if parsed.hostname in {'github.com', 'raw.githubusercontent.com'}:
        return path[:2] == ['solana-foundation', 'leanprover-solanalib']
    return (parsed.hostname == 'solana-foundation.github.io'
            and path[:1] == ['leanprover-solanalib'])


def check_text(text):
    findings = []
    for number, original in enumerate(text.splitlines(), 1):
        # JSON permits escaped slashes; URL paths can also be percent-encoded.
        line = original.replace('\\/', '/')
        if not NAMESPACE.search(unquote(line)):
            continue
        urls = list(URL.finditer(line))
        for match in urls:
            reference = unquote(match.group())
            if NAMESPACE.search(reference) and not project_url(reference):
                findings.append(Finding(number, 'external URL', match.group()))
        for match in TOKEN.finditer(line):
            if any(start.start() < match.end() and match.start() < start.end() for start in urls):
                continue
            reference = unquote(match.group()).replace('\\\\', '/')
            if not NAMESPACE.search(reference) or LEAN_FILE.search(reference):
                continue
            if (SOURCE_DIRECTORY.search(reference) or SOURCE_FILE.search(reference)
                    or SOURCE_CONTEXT.search(line[:match.start()])):
                findings.append(Finding(number, 'upstream source path', match.group()))
    return findings


def source_files(root):
    # Include new files under development; ignore build caches and other ignored files.
    names = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=root)
    return sorted({root / name for name in names.decode().split('\0')
                   if name and Path(name).suffix.lower() in EXTENSIONS
                   and (root / name).is_file()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.root.resolve()
    paths = source_files(root)
    failures = 0
    for path in paths:
        for finding in check_text(path.read_text()):
            print(f'{path.relative_to(root)}:{finding.line}: Lean namespace in '
                  f'{finding.kind}: {finding.reference}', file=sys.stderr)
            failures += 1
    if failures:
        print(f'Upstream references: {failures} invalid references in {len(paths)} files checked',
              file=sys.stderr)
        return 1
    print(f'Upstream references: {len(paths)} files checked; valid upstream source paths')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
