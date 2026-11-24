#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Refresh the source hashes of one reviewed SDK abstraction in its crate record."""
import argparse
from pathlib import Path

from review_seals import module_digest, write_json
from registry_data import record_file
from solana_source_map import read_json

ROOT = Path(__file__).resolve().parents[2] / 'packages/solanalib-specs'


def refresh(identifier, root=ROOT):
    path, data = record_file(root, 'abstractions', identifier, read_json)
    row = data['abstractions'][identifier]
    modules = row['modules']
    if not isinstance(modules, dict) or not modules:
        raise ValueError('Reviewed modules must be a nonempty name-to-hash map')
    hashes = {}
    for name in modules:
        if path.stem == 'core' and isinstance(name, str) and (
                name == 'Solanalib.Contracts' or name.startswith('Solanalib.Contracts.')):
            hashes[name] = module_digest(root.parent / 'solanalib-contracts', name, 'Solanalib.Contracts')
        else:
            hashes[name] = module_digest(root, name, 'Solanalib.Specs')
    row['modules'] = hashes
    write_json(path, data, compact=True)
    return len(modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('abstraction_id')
    args = parser.parse_args()
    count = refresh(args.abstraction_id)
    print(f'Refreshed {count} module hashes in SDK abstraction {args.abstraction_id}; source review is separate')


if __name__ == '__main__':
    main()
