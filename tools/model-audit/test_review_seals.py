# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Keep explicit seal refreshes scoped and reject incomplete inputs before writing."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import generate_gap_index as gaps
import refresh_gap_review
import refresh_runtime_correspondence as runtime
import refresh_sdk_abstraction as sdk


class ModelSealControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.runtime = self.root / 'runtime'
        self.sdk = self.root / 'sdk'
        self.runtime_name = 'Solanalib.Runtime.Borrowed'
        self.sdk_name = 'Solanalib.Specs.SolanaSystemInterface.Operational'
        for root, name in [(self.runtime, self.runtime_name), (self.sdk, self.sdk_name)]:
            source = root.joinpath(*name.split('.')).with_suffix('.lean')
            source.parent.mkdir(parents=True)
            source.write_text('def changed : Nat := 7\n')
        self.runtime_path = self.runtime / 'source-map/sources.json'
        self.sdk_path = self.sdk / 'source-map/libraries.json'
        self.runtime_data = {'reference_runtime': 'unchanged pin', 'correspondence': [
            {'id': 'selected', 'modules': [self.runtime_name],
             'model_sha256': {self.runtime_name: 'old'}, 'limitations': ['Still open']},
            {'id': 'other', 'modules': ['Solanalib.Runtime.Other'], 'model_sha256': {'unreviewed': 'old'}}]}
        self.sdk_data = {'models': {'retained': {'role': 'observation'}}, 'abstractions': {
            'selected': {'modules': {self.sdk_name: 'old'}, 'argument': 'Reviewed argument'},
            'other': {'modules': {'unreviewed': 'old'}, 'limitations': ['Still open']}}}
        self.write(self.runtime_path, self.runtime_data)
        self.write(self.sdk_path, self.sdk_data)

    def write(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(data, indent=2) + '\n')

    def rejected_without_write(self, path, call, error=ValueError):
        before = path.read_bytes()
        with self.assertRaises(error):
            call()
        self.assertEqual(path.read_bytes(), before)

    def test_runtime_refresh_changes_only_the_selected_hashes(self):
        self.assertEqual(runtime.refresh('selected', self.runtime), 1)
        expected = copy.deepcopy(self.runtime_data)
        expected['correspondence'][0]['model_sha256'][self.runtime_name] = hashlib.sha256(
            b'def changed : Nat := 7\n').hexdigest()
        self.assertEqual(json.loads(self.runtime_path.read_text()), expected)

    def test_sdk_refresh_changes_only_the_selected_hashes(self):
        self.assertEqual(sdk.refresh('selected', self.sdk), 1)
        expected = copy.deepcopy(self.sdk_data)
        expected['abstractions']['selected']['modules'][self.sdk_name] = hashlib.sha256(
            b'def changed : Nat := 7\n').hexdigest()
        self.assertEqual(json.loads(self.sdk_path.read_text()), expected)

    def test_unknown_record_is_not_created(self):
        for module, root, path in [(runtime, self.runtime, self.runtime_path), (sdk, self.sdk, self.sdk_path)]:
            with self.subTest(module=module.__name__):
                self.rejected_without_write(path, lambda: module.refresh('unknown', root))

    def test_duplicate_runtime_identity_is_rejected(self):
        self.runtime_data['correspondence'].append(copy.deepcopy(self.runtime_data['correspondence'][0]))
        self.write(self.runtime_path, self.runtime_data)
        self.rejected_without_write(self.runtime_path, lambda: runtime.refresh('selected', self.runtime))

    def test_missing_second_module_does_not_partially_refresh(self):
        self.runtime_data['correspondence'][0]['modules'].append('Solanalib.Runtime.Missing')
        self.write(self.runtime_path, self.runtime_data)
        self.rejected_without_write(self.runtime_path, lambda: runtime.refresh('selected', self.runtime))
        self.sdk_data['abstractions']['selected']['modules']['Solanalib.Specs.Missing'] = 'old'
        self.write(self.sdk_path, self.sdk_data)
        self.rejected_without_write(self.sdk_path, lambda: sdk.refresh('selected', self.sdk))

    def test_empty_duplicate_and_foreign_modules_are_rejected(self):
        for modules in [[], [self.runtime_name, self.runtime_name], ['Solanalib.Specs.Core'], ['../outside']]:
            with self.subTest(modules=modules):
                self.runtime_data['correspondence'][0]['modules'] = modules
                self.write(self.runtime_path, self.runtime_data)
                self.rejected_without_write(self.runtime_path, lambda: runtime.refresh('selected', self.runtime))
        for modules in [{}, {'Solanalib.Runtime.Account': 'old'}, {'../outside': 'old'}]:
            with self.subTest(modules=modules):
                self.sdk_data['abstractions']['selected']['modules'] = modules
                self.write(self.sdk_path, self.sdk_data)
                self.rejected_without_write(self.sdk_path, lambda: sdk.refresh('selected', self.sdk))

    def test_symlink_cannot_seal_a_source_outside_the_layer(self):
        source = self.runtime.joinpath(*self.runtime_name.split('.')).with_suffix('.lean')
        outside = self.root / 'outside.lean'
        outside.write_text(source.read_text())
        source.unlink()
        source.symlink_to(outside)
        self.rejected_without_write(self.runtime_path, lambda: runtime.refresh('selected', self.runtime))


class GapSealControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in [*gaps.input_hashes(gaps.ROOT), gaps.REVIEW.as_posix()]:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(gaps.ROOT / name, target)
        self.path = self.root / gaps.REVIEW

    def test_refresh_preserves_the_explicit_review_and_open_policies(self):
        original = json.loads(self.path.read_text())
        source = self.root / gaps.RUNTIME
        source.write_text(source.read_text() + '\n')
        self.assertEqual(refresh_gap_review.refresh(self.root), len(original['inputs']))
        expected = copy.deepcopy(original)
        expected['inputs'] = gaps.input_hashes(self.root)
        self.assertNotEqual(expected['inputs'], original['inputs'])
        self.assertEqual(json.loads(self.path.read_text()), expected)

    def test_invented_coverage_status_cannot_be_sealed(self):
        review = json.loads(self.path.read_text())
        review['policies']['sdk-binding']['status'] = 'closed'
        self.path.write_text(json.dumps(review))
        before = self.path.read_bytes()
        with self.assertRaisesRegex(ValueError, 'coverage status'):
            refresh_gap_review.refresh(self.root)
        self.assertEqual(self.path.read_bytes(), before)

    def test_invalid_date_or_missing_input_leaves_review_unchanged(self):
        review = json.loads(self.path.read_text())
        review['reviewed_on'] = 'not-a-date'
        self.path.write_text(json.dumps(review))
        before = self.path.read_bytes()
        with self.assertRaises(ValueError):
            refresh_gap_review.refresh(self.root)
        self.assertEqual(self.path.read_bytes(), before)
        review['reviewed_on'] = '2026-11-23'
        self.path.write_text(json.dumps(review))
        before = self.path.read_bytes()
        (self.root / gaps.RUNTIME).unlink()
        with self.assertRaises(FileNotFoundError):
            refresh_gap_review.refresh(self.root)
        self.assertEqual(self.path.read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
