#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Controls for public module roots and library/source ownership."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('module_ownership', Path(__file__).with_name('check-module-ownership.py'))
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class ModuleOwnershipTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def source(self, name):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('-- fixture\n')
        return name

    def test_library_test_and_executable_roots(self):
        names = [self.source(name) for name in (
            'Solanalib.lean', 'packages/runtime/Solanalib/Runtime.lean',
            'examples/SolanalibTest/Example.lean', 'Oracle.lean')]
        self.assertEqual(set(CHECK.source_inventory(self.root, names)),
                         {'Solanalib', 'Solanalib.Runtime', 'SolanalibTest.Example', 'Oracle'})

    def test_stray_module_outside_globs_is_rejected(self):
        for name in ('Unexpected.lean', 'packages/runtime/Unexpected/Basic.lean'):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'outside the public roots'):
                CHECK.source_inventory(self.root, [self.source(name)])

    def test_same_name_in_two_source_directories_is_rejected(self):
        names = [self.source('Solanalib/Example.lean'),
                 self.source('packages/runtime/Solanalib/Example.lean')]
        with self.assertRaisesRegex(ValueError, 'Duplicate module'):
            CHECK.source_inventory(self.root, names)

    def test_lake_must_report_the_actual_module_source(self):
        name = self.source('Solanalib/Example.lean')
        modules = CHECK.source_inventory(self.root, [name])
        row = {'name': 'Solanalib', 'package': 'solanalib',
               'modules': ['Solanalib.Example'], 'files': [str(self.root / name)]}
        CHECK.validate_libraries([row], modules)
        with self.assertRaisesRegex(ValueError, 'Multiple library owners'):
            CHECK.validate_libraries([row, row], modules)
        row['files'] = [str(self.root / 'Solanalib/Other.lean')]
        with self.assertRaisesRegex(ValueError, 'source differs'):
            CHECK.validate_libraries([row], modules)

    def test_foreign_library_and_module_roots_are_rejected(self):
        for row in (
            {'name': 'Unexpected', 'package': 'solanalib', 'modules': [], 'files': []},
            {'name': 'Solanalib', 'package': 'solanalib', 'modules': ['Unexpected'], 'files': ['Unexpected.lean']},
        ):
            with self.subTest(row=row), self.assertRaisesRegex(ValueError, 'outside the public roots'):
                CHECK.validate_libraries([row], {})


if __name__ == '__main__':
    unittest.main()
