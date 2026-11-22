#!/usr/bin/env python3
"""Render one documentation site for every owned production module.

The root library deliberately has empty Lake roots to avoid claiming other selectable libraries.
Select actual modules, rather than the library-root facet of doc-gen4, and render all roots
in one invocation so multiple writers cannot overwrite the site index independently.
"""
from pathlib import Path
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / '.lake/build'


def public_modules():
    modules = set()
    for package in [ROOT, *sorted((ROOT / 'packages').glob('*'))]:
        paths = sorted((package / 'Solanalib').rglob('*.lean'))
        if (package / 'Solanalib.lean').is_file():
            paths.append(package / 'Solanalib.lean')
        for path in paths:
            modules.add('.'.join(path.relative_to(package).with_suffix('').parts))
    return sorted(modules)


def main():
    modules = public_modules()
    subprocess.run(['lake', '-R', '-Kenv=dev', 'build', 'doc-gen4/coreDocs',
                    'doc-gen4/bibPrepass', *(f'+{name}:docInfo' for name in modules)],
                   cwd=ROOT, check=True)
    # Clear only generated project HTML. A stale cached page must not satisfy coverage.
    shutil.rmtree(BUILD / 'doc/Solanalib', ignore_errors=True)
    (BUILD / 'doc/Solanalib.html').unlink(missing_ok=True)
    manifest = BUILD / 'doc-manifest.json'
    subprocess.run(['lake', '-Kenv=dev', 'exe', 'doc-gen4', 'fromDb',
                    '--build', '.lake/build', '--manifest', str(manifest),
                    '.lake/build/api-docs.db', *modules, 'Init', 'Std', 'Lake', 'Lean'],
                   cwd=ROOT, check=True)
    generated = set(json.loads(manifest.read_text()))
    expected = {'doc/' + name.replace('.', '/') + '.html' for name in modules}
    missing = sorted(name for name in expected if name not in generated or not (BUILD / name).is_file())
    if missing:
        raise SystemExit('Missing generated module documentation: ' + ', '.join(missing))
    subprocess.run([sys.executable, 'scripts/postprocess-docs.py'], cwd=ROOT, check=True)
    print(f'Documentation coverage: {len(expected)} production modules generated in one site')


if __name__ == '__main__':
    main()
