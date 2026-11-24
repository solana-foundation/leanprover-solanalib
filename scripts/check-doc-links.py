#!/usr/bin/env python3
"""Check local file links in maintained package and conformance documentation.

Native oracle sources and fixtures retain their authenticated upstream bytes.
"""
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
EXCLUDED = {'.lake', '.git', '__pycache__', 'rust', 'corpus'}


def main():
    checked = 0
    errors = []
    for base in [ROOT / 'README.md', ROOT / 'CONTRIBUTING.md', ROOT / 'docs', ROOT / 'packages',
                 ROOT / 'tools/runtime-conformance', ROOT / 'tools/library-conformance']:
        files = [base] if base.is_file() else sorted(base.rglob('*.md'))
        for source in files:
            if EXCLUDED.intersection(source.relative_to(ROOT).parts):
                continue
            content = re.sub(r'^```[^\n]*\n.*?^```\s*$', '', source.read_text(), flags=re.M | re.S)
            for link in re.finditer(r'\[[^\]\n]*\]\(([^\s)]+)(?:\s+"[^"\n]*")?\)', content):
                target = urlsplit(link[1])
                if target.scheme or target.netloc or not target.path:
                    continue
                path = unquote(target.path)
                resolved = (ROOT / path.lstrip('/') if path.startswith('/') else source.parent / path).resolve()
                checked += 1
                if not resolved.is_relative_to(ROOT) or not resolved.exists():
                    errors.append(f'{source.relative_to(ROOT)}: missing local target {link[1]}')
    for error in errors:
        print(error)
    print(f'Documentation file links: {checked} checked; {len(errors)} missing')
    return int(bool(errors))


if __name__ == '__main__':
    raise SystemExit(main())
