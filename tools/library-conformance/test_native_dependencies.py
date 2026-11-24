# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Controls for exact pins, selected compiler packages, origins and fresh resolution."""

from copy import deepcopy
import io
import json
from pathlib import Path
import tempfile
import tomllib
import unittest
from unittest.mock import patch

import native_dependencies as deps


class NativeDependencyControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.driver = self.root / 'rust/driver'
        self.workspace = self.root / 'rust/workspaces/profile-00'
        self.driver.mkdir(parents=True)
        self.workspace.mkdir(parents=True)
        self.cargo = '''[package]
name = "driver"
workspace = "../workspaces/profile-00"
[dependencies]
borsh = "=1.6.1"
pin-borsh-0-10-4 = { package = "borsh", version = "=0.10.4", optional = true, default-features = false }
'''
        (self.driver / 'Cargo.toml').write_text(self.cargo)
        (self.workspace / 'Cargo.toml').write_text('''[workspace]
members = ["../../driver"]
[profile.dev]
panic = "unwind"
[profile.abort]
inherits = "dev"
panic = "abort"
''')
        self.new = {'version': '1.6.1', 'source': deps.CRATES_IO, 'checksum': 'a' * 64}
        self.old = {'version': '0.10.4', 'source': deps.CRATES_IO, 'checksum': 'b' * 64}
        self.receipt = {'modeled': {'borsh': [self.new]}, 'unused_pins': ['pin-borsh-0-10-4']}

    def test_exact_selection_and_unused_optional_constraint(self):
        self.assertEqual(deps.validate_resolution(self.driver, self.receipt), {'borsh': [self.new]})
        self.assertEqual(deps.selected_version(self.driver, self.receipt, 'borsh'), '1.6.1')

    def test_direct_version_wins_over_other_compiled_transitive_version(self):
        self.receipt['modeled']['borsh'].append(self.old)
        self.receipt['unused_pins'] = []
        self.assertEqual(deps.selected_version(self.driver, self.receipt, 'borsh'), '1.6.1')
        cargo = self.cargo.replace('borsh = "=1.6.1"',
            'pin-borsh-1-6-1 = { package = "borsh", version = "=1.6.1", optional = true, default-features = false }')
        (self.driver / 'Cargo.toml').write_text(cargo)
        self.assertIsNone(deps.selected_version(self.driver, self.receipt, 'borsh'))

    def test_unpinned_or_feature_enabling_constraint_is_rejected(self):
        for old, new in [('"=1.6.1"', '"1.6.1"'), ('optional = true', 'optional = false'),
                         ('default-features = false', 'default-features = true')]:
            with self.subTest(new=new):
                (self.driver / 'Cargo.toml').write_text(self.cargo.replace(old, new))
                with self.assertRaisesRegex(ValueError, 'exact|constraint'):
                    deps.pins(self.driver)

    def test_changed_versions_origins_checksums_and_missing_packages_are_rejected(self):
        for key, value, message in [('version', '1.8.1', 'exact version/origin pin'),
                                    ('source', 'registry+https://example.invalid/index', 'registry checksum'),
                                    ('checksum', '', 'archive checksum')]:
            with self.subTest(key=key):
                receipt = deepcopy(self.receipt)
                receipt['modeled']['borsh'][0][key] = value
                with self.assertRaisesRegex(ValueError, message):
                    deps.validate_resolution(self.driver, receipt)
        with self.assertRaisesRegex(ValueError, 'reviewed archive checksum differs'):
            deps.validate_resolution(self.driver, self.receipt, {('borsh', '1.6.1'): 'c' * 64})
        for receipt in [{'modeled': {}, 'unused_pins': ['pin-borsh-0-10-4']},
                        {'modeled': {}, 'unused_pins': ['borsh', 'pin-borsh-0-10-4']}]:
            with self.assertRaisesRegex(ValueError, 'inventory|not compiled'):
                deps.validate_resolution(self.driver, receipt)

    def test_removed_transitive_pin_cannot_authenticate_a_selected_provider(self):
        self.receipt['modeled']['borsh'].append(self.old)
        self.receipt['unused_pins'] = []
        (self.driver / 'Cargo.toml').write_text(self.cargo.split('pin-borsh-', 1)[0])
        with self.assertRaisesRegex(ValueError, 'exact version/origin pin'):
            deps.validate_resolution(self.driver, self.receipt)

    def test_repeated_selected_package_is_rejected(self):
        self.receipt['modeled']['borsh'].append(deepcopy(self.new))
        with self.assertRaisesRegex(ValueError, 'repeated resolved package'):
            deps.validate_resolution(self.driver, self.receipt)

    def test_git_requires_exact_revision_and_origin(self):
        revision = 'c' * 40
        cargo = self.cargo.replace('borsh = "=1.6.1"',
            f'borsh = {{ git = "https://github.com/example/borsh", rev = "{revision}" }}')
        (self.driver / 'Cargo.toml').write_text(cargo)
        self.receipt['modeled']['borsh'] = [{'version': '1.6.1',
            'source': f'git+https://github.com/example/borsh?rev={revision}#{revision}'}]
        deps.validate_resolution(self.driver, self.receipt)
        self.receipt['modeled']['borsh'][0]['source'] = self.receipt['modeled']['borsh'][0]['source'].replace('#' + revision, '#' + 'd' * 40)
        with self.assertRaisesRegex(ValueError, 'exact version/origin pin'):
            deps.validate_resolution(self.driver, self.receipt)
        (self.driver / 'Cargo.toml').write_text(cargo.replace(revision, 'main'))
        with self.assertRaisesRegex(ValueError, 'exact revision'):
            deps.pins(self.driver)

    def test_workspace_membership_and_custom_panic_profile(self):
        self.assertEqual(deps.workspace(self.driver), self.workspace)
        self.assertEqual(deps.profile(self.driver, 'abort'), {
            'profile': 'abort', 'panic': 'abort', 'opt_level': '0',
            'debug_assertions': True, 'overflow_checks': True})
        path = self.workspace / 'Cargo.toml'
        path.write_text(path.read_text().replace('"../../driver"', '"../../another"'))
        with self.assertRaisesRegex(ValueError, 'does not list'):
            deps.workspace(self.driver)

    def graph(self):
        metadata = {'packages': [
            {'id': 'driver', 'name': 'driver', 'version': '0.1.0', 'source': None,
             'manifest_path': str(self.driver / 'Cargo.toml')},
            {'id': 'borsh', 'name': 'borsh', **{k: v for k, v in self.new.items() if k != 'checksum'}},
            {'id': 'other-member-dependency', 'name': 'unrelated', 'version': '9.0.0', 'source': deps.CRATES_IO}]}
        settings = {'name': 'dev', 'panic': 'unwind', 'opt_level': '0', 'debug_assertions': True, 'overflow_checks': True}
        units = {'roots': [0], 'units': [{'pkg_id': 'driver', 'profile': settings}, {'pkg_id': 'borsh', 'profile': settings}]}
        (self.workspace / 'Cargo.lock').write_text(deps.seed_contents([{'name': 'borsh', **self.new}]))
        return metadata, units

    def test_compiler_graph_excludes_other_workspace_members(self):
        metadata, units = self.graph()
        receipt, settings = deps.compiled_resolution(self.driver, metadata, units, {'borsh', 'unrelated'})
        self.assertEqual(receipt, self.receipt)
        self.assertEqual(settings, deps.profile(self.driver, 'dev'))
        units['units'].append({'pkg_id': 'other-member-dependency', 'profile': units['units'][0]['profile']})
        with self.assertRaisesRegex(ValueError, 'archive checksum|exact version/origin pin'):
            deps.compiled_resolution(self.driver, metadata, units, {'borsh', 'unrelated'})

    def test_compiler_graph_cannot_select_a_different_driver(self):
        metadata, units = self.graph()
        metadata['packages'][0]['manifest_path'] = str(self.driver.parent / 'another/Cargo.toml')
        with self.assertRaisesRegex(ValueError, 'different driver'):
            deps.compiled_resolution(self.driver, metadata, units, {'borsh'})

    def test_broad_range_uses_the_unique_explicit_pin_without_changing_incidental_selection(self):
        (self.driver / 'Cargo.toml').write_text(self.cargo.split('pin-borsh-', 1)[0])
        unexpected = {'id': 'borsh@2.0.0', 'name': 'borsh', 'version': '2.0.0', 'source': deps.CRATES_IO}
        incidental = {'id': 'libc@0.2.170', 'name': 'libc', 'version': '0.2.170', 'source': deps.CRATES_IO}
        final = {'packages': [{**unexpected, 'id': 'borsh@1.6.1', 'version': '1.6.1'}, incidental]}
        commands = []
        class Runner:
            def run(self, name, command, cwd, **flags):
                commands.append(command)
                return 0, json.dumps(final)
        result = deps.constrain_modeled(self.workspace, Runner(), {'packages': [unexpected, incidental]}, {'borsh'})
        self.assertEqual(result, final)
        self.assertEqual(commands[0], ['cargo', 'update', '-p', 'borsh@2.0.0', '--precise', '1.6.1'])
        self.assertEqual(len(commands), 2)

    def test_broad_range_never_guesses_between_multiple_model_pins(self):
        metadata = {'packages': [{'id': 'borsh@2.0.0', 'name': 'borsh', 'version': '2.0.0', 'source': deps.CRATES_IO}]}
        with self.assertRaisesRegex(ValueError, 'no unique exact modeled dependency selection'):
            deps.constrain_modeled(self.workspace, None, metadata, {'borsh'})


class FreshResolutionControls(unittest.TestCase):
    def test_public_index_entry_must_match_the_exact_yanked_release(self):
        valid = {'name': 'example', 'vers': '1.2.0', 'cksum': 'a' * 64, 'yanked': True}
        for row in [valid, {**valid, 'yanked': False}, {**valid, 'vers': '1.2.1'}, {**valid, 'cksum': 'bad'}]:
            with self.subTest(row=row), patch.object(deps, 'urlopen', return_value=io.BytesIO(json.dumps(row).encode())):
                if row == valid:
                    self.assertEqual(deps.yanked_entry('example', '1.2.0')['checksum'], 'a' * 64)
                else:
                    with self.assertRaisesRegex(ValueError, 'yanked public release'):
                        deps.yanked_entry('example', '1.2.0')

    def test_fresh_resolution_discards_prior_graph_and_seeds_only_the_exact_yanked_release(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            workspace = root / 'profile-00'
            workspace.mkdir()
            lock = workspace / 'Cargo.lock'
            lock.write_text('an incidental prior dependency graph')
            seed = {'name': 'example', 'version': '1.2.0', 'source': deps.CRATES_IO, 'checksum': 'a' * 64}
            snapshots = []
            class Runner:
                evidence = root

                def run(self, name, command, cwd, **flags):
                    snapshots.append(lock.read_text() if lock.exists() else None)
                    if len(snapshots) == 1:
                        (root / ('run-' + name + '.log')).write_text(
                            'error: failed to select a version for the requirement `example = "=1.2.0"`\n'
                            '  version 1.2.0 is yanked\n')
                        return 101, ''
                    return 0, '{"packages": []}'

            with patch.object(deps, 'yanked_entry', return_value=seed) as fetch:
                self.assertEqual(deps.fresh_resolution(workspace, Runner()), {'packages': []})
                fetch.assert_called_once_with('example', '1.2.0', offline=False)
            self.assertIsNone(snapshots[0])
            self.assertEqual(tomllib.loads(snapshots[1]), {'version': 4, 'package': [seed]})

    def test_other_resolution_failures_are_not_bypassed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            class Runner:
                evidence = root

                def run(self, name, command, cwd, **flags):
                    (root / ('run-' + name + '.log')).write_text('conflicting exact dependencies')
                    return 101, ''

            with patch.object(deps, 'yanked_entry') as fetch:
                with self.assertRaisesRegex(ValueError, 'failed; see'):
                    deps.fresh_resolution(root, Runner())
                fetch.assert_not_called()


if __name__ == '__main__':
    unittest.main()
