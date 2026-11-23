#!/usr/bin/env python3
"""Validate or build the SDK CI partition from the actual Lake library inventory.

Each production root and its scenarios belong to one group. Lake builds the
complete import closure, including shared core and cross-crate dependencies.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'tools/model-audit'))
from solana_specs_config import package_roots, test_root


def groups():
    data = json.loads((ROOT / 'scripts/ci-sdk-groups.json').read_text())
    production, tests = package_roots(ROOT / 'packages/solanalib-specs')
    selected = [f'Solanalib.Specs.{member}' for members in data.values() for member in members]
    if Counter(selected) != Counter(production):
        raise ValueError('CI groups must partition the complete SDK production inventory exactly once')
    if Counter(test_root(name) for name in selected) != Counter(tests):
        raise ValueError('CI groups must partition the complete SDK test inventory exactly once')
    return {name: [target for member in members
                   for target in (f'Solanalib.Specs.{member}', f'SolanalibTest.Specs.{member}')]
            for name, members in data.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', metavar='GROUP')
    args = parser.parse_args()
    matrix = groups()
    if args.build:
        if args.build != 'all' and args.build not in matrix:
            parser.error('unknown SDK group: ' + args.build)
        targets = [target for group in matrix.values() for target in group] if args.build == 'all' else matrix[args.build]
        return subprocess.call(['lake', '--wfail', 'build', *targets], cwd=ROOT)
    print(json.dumps({'groups': list(matrix), 'libraries': sum(map(len, matrix.values()))}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
