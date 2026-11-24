#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Refresh the Lean hashes of one runtime row after reviewing its source correspondence."""
import argparse
import json
from pathlib import Path

from review_seals import module_digest, write_json

ROOT = Path(__file__).resolve().parents[2] / 'packages/solanalib-runtime'


def refresh(identifier, root=ROOT):
    path = root / 'source-map/sources.json'
    data = json.loads(path.read_text())
    matches = [row for row in data['correspondence'] if row['id'] == identifier]
    if len(matches) != 1:
        raise ValueError(f'Expected exactly one runtime correspondence row: {identifier}')
    row = matches[0]
    modules = row['modules']
    if not isinstance(modules, list) or not modules or len(set(modules)) != len(modules):
        raise ValueError('Reviewed modules must be a nonempty list without duplicates')
    row['model_sha256'] = {name: module_digest(root, name, 'Solanalib.Runtime') for name in modules}
    write_json(path, data)
    return len(modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('correspondence_id')
    args = parser.parse_args()
    count = refresh(args.correspondence_id)
    print(f'Refreshed {count} module hashes in runtime row {args.correspondence_id}; source review is separate')


if __name__ == '__main__':
    main()
