#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Refresh the hashes of one reviewed SDK abstraction in its library or foundation layer."""
import argparse
import json
from pathlib import Path

from review_seals import module_digest, write_json

ROOT = Path(__file__).resolve().parents[2] / 'packages/solanalib-specs'


def refresh(identifier, root=ROOT, layer='libraries'):
    if layer not in {'libraries', 'foundation'}:
        raise ValueError(f'Unknown SDK review layer: {layer}')
    path = root / 'source-map' / (layer + '.json')
    data = json.loads(path.read_text())
    if identifier not in data['abstractions']:
        raise ValueError(f'Unknown SDK {layer} abstraction: {identifier}')
    row = data['abstractions'][identifier]
    modules = row['modules']
    if not isinstance(modules, dict) or not modules:
        raise ValueError('Reviewed modules must be a nonempty name-to-hash map')
    hashes = {}
    for name in modules:
        if layer == 'foundation' and isinstance(name, str) and (
                name == 'Solanalib.Contracts' or name.startswith('Solanalib.Contracts.')):
            hashes[name] = module_digest(root.parent / 'solanalib-contracts', name, 'Solanalib.Contracts')
        else:
            hashes[name] = module_digest(root, name, 'Solanalib.Specs')
    row['modules'] = hashes
    write_json(path, data)
    return len(modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('abstraction_id')
    parser.add_argument('--layer', choices=['libraries', 'foundation'], default='libraries')
    args = parser.parse_args()
    count = refresh(args.abstraction_id, layer=args.layer)
    print(f'Refreshed {count} module hashes in SDK {args.layer} abstraction {args.abstraction_id}; source review is separate')


if __name__ == '__main__':
    main()
