#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Adopt a passed, sealed Agave run into the authenticated replay recording."""
import argparse
from datetime import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile

import run

REQUIRED = {'run-status.json', 'native-build.json', 'source-before.json',
            'tool-identities.json', 'native.tsv'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked_evidence(evidence):
    evidence = evidence.resolve()
    manifest_bytes = (evidence / 'MANIFEST.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    files = manifest.get('files')
    run.require(manifest.get('schema_version') == 1 and isinstance(files, dict)
                and REQUIRED <= files.keys(), 'Incomplete native evidence manifest')
    checked = {}
    for name, expected in files.items():
        relative = Path(name)
        path = evidence / relative
        run.require(not relative.is_absolute() and '..' not in relative.parts
                    and path.is_file() and not path.is_symlink()
                    and path.resolve().is_relative_to(evidence), f'Unsafe evidence path: {name}')
        content = path.read_bytes()
        run.require(digest(content) == expected, f'Evidence digest differs: {name}')
        if name in REQUIRED:
            checked[name] = content
    return manifest_bytes, manifest, checked


def adopt(evidence, suite=run.ROOT):
    manifest_bytes, manifest, checked = checked_evidence(evidence)
    read = lambda name: json.loads(checked[name])
    status, build = read('run-status.json'), read('native-build.json')
    run.require(status.get('status') == 'passed', 'Native run did not pass')
    record = json.loads((suite / 'expected-native.json').read_text())
    run.require(build.get('revision') == manifest.get('revision') == record['revision'],
                'Native revision differs from the recording pin')
    run.require(build.get('target') == record['target'], 'Native target differs from the recording pin')
    run.require(build.get('source_archive_url') == record['source_archive_url']
                and read('source-before.json').get('archive_sha256') == record['source_archive_sha256'],
                'Native source archive differs from the recording pin')
    rust = read('tool-identities.json').get('rustc', {}).get('version', '')
    run.require(rust.startswith('rustc ' + record['rust'] + ' '), 'Native Rust compiler pin differs')
    run.require(type(status.get('case_count')) is int and status['case_count'] > 0
                and status['case_count'] == manifest.get('case_count'), 'Native case counts differ')
    datetime.fromisoformat(status['finished_utc'])
    run.require(set(record['native_inputs_sha256']) == set(run.NATIVE_INPUT_FILES),
                'Recorded native input set is incomplete')
    for name in run.NATIVE_INPUT_FILES:
        path = suite / name
        run.require(path.is_file() and not path.is_symlink(), f'Missing regular native input: {name}')
        actual = run.sha256(path)
        run.require(actual == build.get('harness_files', {}).get(name), f'Native input changed: {name}')
        record['native_inputs_sha256'][name] = actual
    for field in ('cargo_lock_sha256', 'native_binary_sha256'):
        value = build.get(field)
        run.require(isinstance(value, str) and len(value) == 64
                    and all(character in '0123456789abcdef' for character in value),
                    f'Invalid native build identity: {field}')
        record[field] = value
    run.require(isinstance(build.get('native_cpi_profile'), dict), 'Missing native CPI profile')
    record['native_cpi_profile'] = build['native_cpi_profile']
    native = checked['native.tsv']
    packed = gzip.compress(native, mtime=0)
    record['native_output'] = {'bytes': len(native), 'cases': status['case_count'],
        'file': 'expected-native.tsv.gz', 'gzip_sha256': digest(packed), 'sha256': digest(native)}
    record['evidence_manifest_sha256'] = digest(manifest_bytes)
    record['recorded_utc'] = status['finished_utc']
    metadata = (json.dumps(record, indent=2, sort_keys=True) + '\n').encode()

    # Validate the complete candidate with the replay loader before replacing either file.
    with tempfile.TemporaryDirectory(prefix='.adopt-recording-', dir=suite) as temporary:
        staging = Path(temporary)
        for name in run.NATIVE_INPUT_FILES:
            shutil.copyfile(suite / name, staging / name)
        (staging / 'expected-native.tsv.gz').write_bytes(packed)
        (staging / 'expected-native.json').write_bytes(metadata)
        run.expected_native(staging)
        for name in ('expected-native.tsv.gz', 'expected-native.json'):
            os.chmod(staging / name, (suite / name).stat().st_mode & 0o777)
            os.replace(staging / name, suite / name)
    return status['case_count']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('evidence', type=Path)
    args = parser.parse_args()
    count = adopt(args.evidence)
    print(f'Adopted {count} authenticated native cases; replay the current model next')


if __name__ == '__main__':
    main()
