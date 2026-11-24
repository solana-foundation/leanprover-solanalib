# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""A foundation refresh uses canonical owners and cannot overwrite unrelated review evidence."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import refresh_sdk_abstraction as sdk


class FoundationSealControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.root = self.base / 'solanalib-specs'
        self.contracts = self.base / 'solanalib-contracts'
        self.names = ['Solanalib.Specs.Core', 'Solanalib.Contracts.Family']
        for root, name in zip([self.root, self.contracts], self.names):
            path = root.joinpath(*name.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('def selected : Nat := 7\n')
        self.path = self.root / 'source-map/core.json'
        self.path.parent.mkdir()
        (self.root / 'source-map.json').write_text(json.dumps({'fragments': ['source-map/core.json']}))
        self.data = {'abstractions': {
            'selected': {'modules': dict.fromkeys(self.names, 'old'), 'limitations': ['Open binding']},
            'other': {'modules': {'Solanalib.Specs.Missing': 'unreviewed'}}},
            'source_pin': 'unchanged'}
        self.save()

    def save(self):
        self.path.write_text(json.dumps(self.data, indent=2) + '\n')

    def rejected(self, call):
        before = self.path.read_bytes()
        with self.assertRaises(ValueError):
            call()
        self.assertEqual(self.path.read_bytes(), before)

    def test_foundation_hashes_only_selected_modules_at_their_owners(self):
        # A same-name file in the SDK directory cannot shadow the contract owner.
        shadow = self.root / 'Solanalib/Contracts/Family.lean'
        shadow.parent.mkdir(parents=True)
        shadow.write_text('def wrong : Nat := 8\n')
        self.assertEqual(sdk.refresh('selected', self.root), 2)
        expected = copy.deepcopy(self.data)
        digest = hashlib.sha256(b'def selected : Nat := 7\n').hexdigest()
        expected['abstractions']['selected']['modules'] = dict.fromkeys(self.names, digest)
        self.assertEqual(json.loads(self.path.read_text()), expected)

    def test_unknown_record_cannot_write(self):
        self.rejected(lambda: sdk.refresh('../core', self.root))
        self.rejected(lambda: sdk.refresh('absent', self.root))

    def test_missing_contract_does_not_refresh_the_other_module(self):
        (self.contracts / 'Solanalib/Contracts/Family.lean').unlink()
        self.rejected(lambda: sdk.refresh('selected', self.root))

    def test_outside_module_and_empty_map_are_rejected(self):
        for modules in [{}, {'Solanalib.Runtime.AccountState': 'old'}, {'../escape': 'old'}]:
            with self.subTest(modules=modules):
                self.data['abstractions']['selected']['modules'] = modules
                self.save()
                self.rejected(lambda: sdk.refresh('selected', self.root))

    def test_symlink_cannot_substitute_a_contract_source(self):
        source = self.contracts / 'Solanalib/Contracts/Family.lean'
        source.unlink()
        outside = self.base / 'outside.lean'
        outside.write_text('def selected : Nat := 7\n')
        source.symlink_to(outside)
        self.rejected(lambda: sdk.refresh('selected', self.root))

    def test_crate_record_rejects_contract_modules(self):
        target = self.path.with_name('example.json')
        target.write_bytes(self.path.read_bytes())
        (self.root / 'source-map.json').write_text(json.dumps({'fragments': ['source-map/example.json']}))
        before = target.read_bytes()
        with self.assertRaises(ValueError):
            sdk.refresh('selected', self.root)
        self.assertEqual(target.read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
