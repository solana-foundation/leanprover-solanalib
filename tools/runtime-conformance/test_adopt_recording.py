# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Reject incomplete or mismatched native seals without replacing either recording file."""
import gzip
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import adopt_recording as adoption
import run


class AdoptionControls(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.suite, self.evidence = root / 'suite', root / 'evidence'
        self.suite.mkdir()
        self.evidence.mkdir()
        for name in [*run.NATIVE_INPUT_FILES, 'expected-native.json', 'expected-native.tsv.gz']:
            shutil.copy2(run.ROOT / name, self.suite / name)
        record = json.loads((self.suite / 'expected-native.json').read_text())
        self.native = gzip.decompress((self.suite / 'expected-native.tsv.gz').read_bytes())
        self.write('native.tsv', self.native)
        self.write('run-status.json', {'status': 'passed', 'case_count': record['native_output']['cases'],
                                      'finished_utc': '2026-11-23T00:00:00+00:00'})
        build = {name: record[name] for name in ['revision', 'target', 'source_archive_url',
                 'cargo_lock_sha256', 'native_cpi_profile']}
        build['native_binary_sha256'] = 'b' * 64
        build['harness_files'] = record['native_inputs_sha256']
        self.write('native-build.json', build)
        self.write('source-before.json', {'archive_sha256': record['source_archive_sha256']})
        self.write('tool-identities.json', {'rustc': {'version': 'rustc ' + record['rust'] + ' (fixture)'}})
        self.write('extra.log', b'Every listed artifact must be checked.\n')
        self.manifest = {'schema_version': 1, 'revision': record['revision'],
                         'case_count': record['native_output']['cases'], 'files': {}}
        self.seal()

    def write(self, name, data):
        content = data if isinstance(data, bytes) else (json.dumps(data, sort_keys=True) + '\n').encode()
        (self.evidence / name).write_bytes(content)

    def seal(self):
        self.manifest['files'] = {name: run.sha256(self.evidence / name)
                                  for name in [*sorted(adoption.REQUIRED), 'extra.log']}
        self.write('MANIFEST.json', self.manifest)

    def mutate(self, name, field, value):
        data = json.loads((self.evidence / name).read_text())
        data[field] = value
        self.write(name, data)
        self.seal()

    def rejected(self, message):
        names = ('expected-native.tsv.gz', 'expected-native.json')
        before = {name: (self.suite / name).read_bytes() for name in names}
        with self.assertRaisesRegex(ValueError, message):
            adoption.adopt(self.evidence, self.suite)
        self.assertEqual({name: (self.suite / name).read_bytes() for name in names}, before)
        self.assertFalse(list(self.suite.glob('.adopt-recording-*')))

    def test_passed_evidence_produces_deterministic_authenticated_pair(self):
        self.assertEqual(adoption.adopt(self.evidence, self.suite), self.manifest['case_count'])
        native, record = run.expected_native(self.suite)
        self.assertEqual(native.encode(), self.native)
        self.assertEqual(record['native_binary_sha256'], 'b' * 64)
        self.assertEqual(record['evidence_manifest_sha256'], run.sha256(self.evidence / 'MANIFEST.json'))
        first = {name: (self.suite / name).read_bytes() for name in ['expected-native.tsv.gz', 'expected-native.json']}
        adoption.adopt(self.evidence, self.suite)
        self.assertEqual({name: (self.suite / name).read_bytes() for name in first}, first)

    def test_digest_mismatch_in_any_listed_file_is_rejected(self):
        self.write('extra.log', b'Modified after sealing.\n')
        self.rejected('Evidence digest differs: extra.log')

    def test_missing_required_artifact_cannot_be_hidden_by_omitting_its_hash(self):
        del self.manifest['files']['native-build.json']
        self.write('MANIFEST.json', self.manifest)
        self.rejected('Incomplete native evidence manifest')

    def test_unsafe_manifest_path_is_rejected(self):
        self.manifest['files']['../outside'] = '0' * 64
        self.write('MANIFEST.json', self.manifest)
        self.rejected('Unsafe evidence path')

    def test_failed_run_is_rejected(self):
        self.mutate('run-status.json', 'status', 'failed')
        self.rejected('did not pass')

    def test_revision_mismatch_is_rejected(self):
        self.mutate('native-build.json', 'revision', '0' * 40)
        self.rejected('revision differs')

    def test_manifest_revision_mismatch_is_rejected(self):
        self.manifest['revision'] = '0' * 40
        self.write('MANIFEST.json', self.manifest)
        self.rejected('revision differs')

    def test_target_mismatch_is_rejected(self):
        self.mutate('native-build.json', 'target', 'different-target')
        self.rejected('target differs')

    def test_archive_mismatch_is_rejected(self):
        self.mutate('source-before.json', 'archive_sha256', '0' * 64)
        self.rejected('archive differs')

    def test_archive_url_mismatch_is_rejected(self):
        self.mutate('native-build.json', 'source_archive_url', 'https://invalid.example/archive')
        self.rejected('archive differs')

    def test_rust_pin_mismatch_is_rejected(self):
        self.mutate('tool-identities.json', 'rustc', {'version': 'rustc wrong (fixture)'})
        self.rejected('Rust compiler pin differs')

    def test_case_count_mismatch_is_rejected(self):
        self.mutate('run-status.json', 'case_count', self.manifest['case_count'] + 1)
        self.rejected('case counts differ')

    def test_changed_local_fixture_is_rejected(self):
        path = self.suite / 'accounts.tsv'
        path.write_text(path.read_text() + '\n')
        self.rejected('Native input changed: accounts.tsv')

    def test_missing_native_input_identity_is_rejected(self):
        self.mutate('native-build.json', 'harness_files', {})
        self.rejected('Native input changed')

    def test_invalid_build_identity_is_rejected(self):
        self.mutate('native-build.json', 'cargo_lock_sha256', '')
        self.rejected('Invalid native build identity')

    def test_malformed_native_case_set_is_rejected_before_replacement(self):
        self.write('native.tsv', self.native.split(b'\n', 1)[1])
        self.seal()
        self.rejected('recorded native case set differs')


if __name__ == '__main__':
    unittest.main()
