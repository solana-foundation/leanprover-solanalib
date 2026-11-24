# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Reject stale committed guides and Lean controls without requiring a machine export."""

from contextlib import redirect_stdout
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from test_solana_applicability import fixture
from applicability import load_manifest
import version_compatibility as generator


class VersionGenerationControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        (self.package / 'SolanalibTest/Specs/Core').mkdir(parents=True)
        self.enterContext(patch.object(generator, 'PACKAGE', self.package))
        self.enterContext(patch.object(generator, 'load_source_map', return_value=fixture()))

    def run_generator(self, *arguments):
        with patch('sys.argv', ['version_compatibility.py', *arguments]), redirect_stdout(io.StringIO()):
            generator.main()

    def test_check_needs_no_export_and_writes_nothing(self):
        self.run_generator()
        exported = load_manifest(self.package / 'applicability.json')
        self.assertEqual({row['model_id'] for row in exported['models']}, {'read', 'shared'})
        (self.package / 'applicability.json').unlink()
        before = {p.relative_to(self.package): p.read_bytes() for p in self.package.rglob('*') if p.is_file()}
        self.run_generator('--check')
        after = {p.relative_to(self.package): p.read_bytes() for p in self.package.rglob('*') if p.is_file()}
        self.assertEqual(before, after)

    def test_stale_lean_or_human_guide_is_rejected_without_rewriting(self):
        self.run_generator()
        for name in ['VERSION_COMPATIBILITY.md', 'SolanalibTest/Specs/Core/VersionCompatibility.lean']:
            with self.subTest(name=name):
                path = self.package / name
                content = path.read_bytes()
                path.write_bytes(content + b'changed\n')
                with self.assertRaisesRegex(SystemExit, 'Stale version compatibility output'):
                    self.run_generator('--check')
                self.assertEqual(path.read_bytes(), content + b'changed\n')
                path.write_bytes(content)

    def test_explicit_export_is_validated_while_checking_committed_outputs(self):
        self.run_generator()
        destination = self.package / 'site/data/applicability.json'
        self.run_generator('--check', '--manifest-output', str(destination))
        self.assertEqual(load_manifest(destination), load_manifest(self.package / 'applicability.json'))


if __name__ == '__main__':
    unittest.main()
