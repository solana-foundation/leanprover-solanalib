#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Controls for upstream references and legitimate local module names."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from urllib.parse import quote

SCRIPT = Path(__file__).with_name('check-upstream-references.py')
SPEC = importlib.util.spec_from_file_location('check_upstream_references', SCRIPT)
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)
REMOTE = 'https://github.com/example/upstream/blob/main/'
NAMESPACES = ['Solanalib/Specs', 'Solanalib.Runtime', 'Solanalib.Specs', 'Solanalib/Runtime']


class UpstreamReferenceTests(unittest.TestCase):
    def test_external_repository_and_file_paths(self):
        for namespace in NAMESPACES:
            for url in [f'https://github.com/example/{namespace}/Codec/blob/main/src/lib.rs',
                        f'{REMOTE}crates/{namespace}/Codec/src/lib.rs']:
                with self.subTest(url=url):
                    findings = CHECK.check_text(f'[source]({url}#L12)')
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(findings[0].kind, 'external URL')

    def test_namespace_in_external_url_fragment(self):
        url = f'{REMOTE}src/lib.rs#{NAMESPACES[1]}.Account'
        self.assertEqual(len(CHECK.check_text(url)), 1)

    def test_namespace_at_url_end_or_before_query_and_fragment(self):
        for suffix in ['', '?raw=1', '#L1']:
            with self.subTest(suffix=suffix):
                url = REMOTE + NAMESPACES[1] + suffix
                self.assertEqual(len(CHECK.check_text(f'[source]({url})')), 1)

    def test_encoded_and_json_escaped_urls(self):
        urls = [REMOTE + quote(NAMESPACES[0], safe='') + '/Codec/src/lib.rs',
                REMOTE + NAMESPACES[1] + '/src/lib.rs']
        for url in urls:
            with self.subTest(url=url):
                self.assertEqual(len(CHECK.check_text(json.dumps({'source': url}))), 1)
                escaped = json.dumps({'source': url}).replace('/', '\\/')
                self.assertEqual(len(CHECK.check_text(escaped)), 1)

    def test_git_and_ssh_urls(self):
        for scheme in ['git+https://github.com/', 'ssh://git@github.com/', 'git@github.com:']:
            with self.subTest(scheme=scheme):
                self.assertEqual(len(CHECK.check_text(scheme + 'example/' + NAMESPACES[0] + '/repo')), 1)

    def test_upstream_paths_without_urls(self):
        for namespace in NAMESPACES:
            for path in [f'{namespace}/Codec/src/de/mod.rs', f'src/{namespace}/value',
                         f'crates/{namespace}/Codec/Cargo.toml', f'upstream/{namespace}/value.rs:12']:
                with self.subTest(path=path):
                    findings = CHECK.check_text(f'| Source | `{path}` |')
                    self.assertEqual(len(findings), 1)
                    self.assertEqual(findings[0].kind, 'upstream source path')

    def test_explicit_upstream_path_fields(self):
        path = NAMESPACES[0] + '/Codec/README.md'
        for field in ['upstream_path', 'source_file', 'path_in_vcs']:
            with self.subTest(field=field):
                self.assertEqual(len(CHECK.check_text(json.dumps({field: path}))), 1)
                self.assertEqual(len(CHECK.check_text(f'{field} = "{path}"')), 1)

    def test_local_module_paths_and_declarations_are_allowed(self):
        text = '\n'.join([
            '`Solanalib.Runtime.Account` and `Solanalib.Specs.Codec.decode`',
            '`packages/solanalib-specs/' + NAMESPACES[0] + '/Codec/Basic.lean`',
            'source_file = "' + NAMESPACES[0] + '/Codec/Basic.lean"',
            '`' + NAMESPACES[0] + '/Codec`',
            '[API](./' + NAMESPACES[0] + '/Codec.html)',
        ])
        self.assertEqual(CHECK.check_text(text), [])

    def test_project_source_and_api_urls_are_allowed(self):
        prefix = 'solana-foundation/leanprover-solanalib/'
        for url in [f'https://github.com/{prefix}blob/main/{NAMESPACES[0]}/Codec/Basic.lean',
                    f'https://raw.githubusercontent.com/{prefix}main/{NAMESPACES[0]}/Codec/Basic.lean',
                    f'https://solana-foundation.github.io/leanprover-solanalib/{NAMESPACES[0]}/Codec.html']:
            with self.subTest(url=url):
                self.assertEqual(CHECK.check_text(url), [])

    def test_similarly_named_projects_are_external(self):
        for prefix in ['https://github.com/solana-foundation/leanprover-solanalib-other/',
                       'https://github.com.example/solana-foundation/leanprover-solanalib/']:
            with self.subTest(prefix=prefix):
                self.assertEqual(len(CHECK.check_text(prefix + NAMESPACES[0] + '/Codec')), 1)

    def test_module_near_valid_upstream_reference_is_allowed(self):
        self.assertEqual(CHECK.check_text(
            f'| `{NAMESPACES[1]}.Account` | [source]({REMOTE}src/lib.rs) |'), [])

    def test_line_numbers_and_link_labels(self):
        path = NAMESPACES[0] + '/Codec/src/lib.rs'
        findings = CHECK.check_text('\nTitle\n[' + path + '](' + REMOTE + path + ')')
        self.assertEqual(len(findings), 2)
        self.assertEqual({finding.line for finding in findings}, {3})

    def test_cli_scans_all_formats_and_new_files_but_not_ignored_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            bad = REMOTE + NAMESPACES[0] + '/Codec/src/lib.rs'
            paths = [root / ('reference' + suffix) for suffix in ['.md', '.json', '.toml', '.py']]
            contents = [f'[source]({bad})', json.dumps({'source': bad}),
                        f'source = "{bad}"', f'source = "{bad}"']
            for path, content in zip(paths, contents):
                path.write_text(content)
            subprocess.run(['git', 'add', 'reference.md'], cwd=root, check=True)
            (root / '.gitignore').write_text('ignored.md\n')
            (root / 'ignored.md').write_text(bad)
            result = subprocess.run([sys.executable, '-B', str(SCRIPT), '--root', str(root)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn('4 invalid references in 4 files checked', result.stderr)
            self.assertNotIn('ignored.md:', result.stderr)
            for path in paths:
                path.write_text(REMOTE + 'src/lib.rs')
            result = subprocess.run([sys.executable, '-B', str(SCRIPT), '--root', str(root)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('4 files checked', result.stdout)


if __name__ == '__main__':
    unittest.main()
