#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Check public module roots and ask Lake for the unique owner of every module."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PUBLIC_ROOTS = {'Solanalib', 'SolanalibTest'}


def source_inventory(root, names):
    """Check all source directories, including files outside the declared globs."""
    source_roots = [root, root / 'examples', *sorted((root / 'packages').glob('*')),
                    root / 'tools/runtime-conformance', root / 'tools/library-conformance']
    source_roots.sort(key=lambda path: len(path.parts), reverse=True)
    modules = {}
    for name in names:
        if not name.endswith('.lean') or name in {'lakefile.lean', 'scripts/CheckModuleOwners.lean'}:
            continue
        source = root / name
        if not source.is_file():
            continue
        package = next(path for path in source_roots if source.is_relative_to(path))
        relative = source.relative_to(package)
        module = '.'.join(relative.with_suffix('').parts)
        if module.split('.')[0] not in PUBLIC_ROOTS:
            raise ValueError(f'Module outside the public roots: {name}')
        if module in modules:
            raise ValueError(f'Duplicate module {module}: {modules[module]}, {source}')
        modules[module] = source
    if not modules:
        raise ValueError('Empty module inventory')
    return modules


def validate_libraries(rows, modules):
    """Every configured library and module must agree with the source inventory."""
    seen = set()
    for row in rows:
        if row['package'] != 'solanalib' or row['name'].split('.')[0] not in PUBLIC_ROOTS:
            raise ValueError(f'Library outside the public roots: {row["name"]}')
        for name, source in zip(row['modules'], row['files'], strict=True):
            if name.split('.')[0] not in PUBLIC_ROOTS:
                raise ValueError('Configured module outside the public roots: ' + name)
            if name not in modules or Path(source).resolve() != modules[name].resolve():
                raise ValueError('Configured module source differs: ' + name)
            if name in seen:
                raise ValueError('Multiple library owners: ' + name)
            seen.add(name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path, default=ROOT)
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    names = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=ROOT)
    modules = source_inventory(ROOT, sorted(set(names.decode().split('\0'))))
    rows = json.loads(subprocess.check_output(
        ['lake', '--quiet', 'run', 'libraryInventory'], cwd=ROOT, text=True))
    validate_libraries(rows, modules)
    if workspace == ROOT:
        command = ['lake', 'run', 'checkModuleOwners']
    else:
        modules.pop('Oracle', None)
        command = ['lake', '--quiet', 'env', 'lean', '-DwarningAsError=true', '--run',
                   str(ROOT / 'scripts/CheckModuleOwners.lean'), str(workspace)]
    return subprocess.call([*command, *sorted(modules)], cwd=workspace)


if __name__ == '__main__':
    raise SystemExit(main())
