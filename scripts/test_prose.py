#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Controls for prose selection, possessive diagnostics and upstream exemptions."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('check-prose.py')
SPEC = importlib.util.spec_from_file_location('check_prose', SCRIPT)
CHECK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECK
SPEC.loader.exec_module(CHECK)


class ProseTests(unittest.TestCase):
    def words(self, path, text, inherited=()):
        return [f.word for f in CHECK.check_text(path, text, inherited)]

    def test_inanimate_nouns_and_inline_identifiers(self):
        text = "The runtime's setters use Anchor’s types and `Account`'s fields."
        self.assertEqual(self.words('README.md', text), ["runtime's", 'Anchor’s', "`Account`'s"])

    def test_plural_possessives_and_repeated_occurrences(self):
        text = "The models' laws retain the model's state and the model's exit."
        self.assertEqual(self.words('README.md', text), ["models'", "model's", "model's"])

    def test_plural_possessor_before_an_inline_identifier(self):
        text = "The APIs' `rust_names` are recorded. `sources'` is an identifier."
        self.assertEqual(self.words('README.md', text), ["APIs'"])

    def test_people_contractions_and_pronouns(self):
        text = ("It's the author's proof; that's Euler's result. Let’s check its type. "
                "He's ready; she’s reviewing it.")
        self.assertEqual(self.words('README.md', text), [])

    def test_reader_can_be_an_inanimate_io_type(self):
        self.assertEqual(self.words('notes.md', "The reader's remaining slice."), ["reader's"])

    def test_markdown_fenced_comments_and_explicit_source_quotations(self):
        text = """A `name's` identifier.
```rust
// The crate's original source comment.
let value = "source's data";
```
> The quoted source's prose.

The crate's model.
"""
        findings = CHECK.check_text('notes.md', text)
        self.assertEqual([(f.line, f.word) for f in findings], [(3, "crate's"), (8, "crate's")])

    def test_multiline_code_span_does_not_hide_following_prose(self):
        text = "receiver (`{projection,\nreceiver}`) whose projection the checker's code uses. `decides.json` lists it."
        self.assertEqual(self.words('REFERENCE.md', text), ["checker's"])

    def test_toml_fenced_comment_is_prose(self):
        text = '''```toml
model = "Some.model"  # one of the deciding checker's `decides`
reason_contains = "the source's literal observation"
```
'''
        self.assertEqual(self.words('REFERENCE.md', text), ["checker's"])

    def test_exact_backtick_delimiters_and_unmatched_ticks(self):
        text = "``a `nested` model's identifier``; the model's result.\nUnmatched ` leaves the runtime's result visible."
        self.assertEqual(self.words('notes.md', text), ["model's", "runtime's"])

    def test_lean_nested_comments_and_message_strings(self):
        text = '''def value := "the runtime's value -- no comment"
def «model's» := 1
/- Outer /- the model's state -/ and the runtime's exit. -/
/-- The α value and the provider's result. -/
'''
        findings = CHECK.check_text('Model.lean', text)
        self.assertEqual([(f.line, f.word) for f in findings],
                         [(1, "runtime's"), (3, "model's"), (3, "runtime's"), (4, "provider's")])

    def test_lean_identifier_apostrophes_are_not_prose(self):
        self.assertEqual(self.words('Model.lean', "def xs' := [1]\ndef s' := xs'\n"), [])

    def test_python_docstrings_comments_help_and_message_strings(self):
        text = '''"""The package's interface."""
VALUE = "the record's exact data"
# Keep the driver's pin.
def run():
    """Read the archive's manifest."""
    parser.add_argument('--input', help="The recorder's output.")
'''
        self.assertEqual(self.words('run.py', text),
                         ["driver's", "package's", "record's", "archive's", "recorder's"])

    def test_python_emitted_documentation_and_control_labels(self):
        text = '''CONTROL = {"label": "The model's malformed input."}
SOURCE = """
open Lean
/-- The checker's decision. -/
def value := "the record's literal"
"""
def report(count):
    return f"""# Evidence
The runtime's results: {count}.
"""
'''
        self.assertEqual(self.words('run.py', text),
                         ["model's", "checker's", "record's", "runtime's"])
        self.assertEqual(self.words('test_run.py', text), [])

    def test_python_additional_docstring(self):
        text = '''def run():
    """Describe the input."""
    """Retain the model's result."""
    return "the record's literal"
'''
        self.assertEqual(self.words('run.py', text), ["model's", "record's"])

    def test_python_quoted_source_and_test_fixtures_are_literal(self):
        text = '''ROW = {"contains": "// the source's exact comment"}
raise ValueError("The driver's recording is invalid")
'''
        self.assertEqual(self.words('run.py', text), ["driver's"])
        self.assertEqual(self.words('test_run.py', text), [])

    def test_rust_nested_comments_raw_strings_and_lifetimes(self):
        text = '''// The driver's observation.
let plain = "// the record's data";
let raw = br##"/* the record's bytes */"##;
let character = '\\'';
/* Outer /* the model's state */ and the provider's error. */
fn borrow<'s>(s: &'s str) { /* The borrow's owner. */ }
'''
        self.assertEqual(self.words('main.rs', text),
                         ["driver's", "model's", "provider's", "borrow's"])

    def test_requirements_comments(self):
        self.assertEqual(self.words('tools/requirements.txt', "# Python's dependencies\n"), ["Python's"])

    def test_registry_prose_and_literal_source_anchors(self):
        text = json.dumps({'description': "The model's contract.",
                           'contains': "// the source's exact comment",
                           'function': "name's", 'reason': "The provider's version."})
        self.assertEqual(self.words('registry.json', text), ["model's", "provider's"])
        toml = 'reason = "The driver\'s observation."\nfunction = "name\'s"\n'
        self.assertEqual(self.words('registry.toml', toml), ["driver's"])

    def test_registry_escaped_punctuation_retains_source_lines(self):
        text = '{\n  "description": "The runtime\\u0027s and model\\u2019s state."\n}\n'
        findings = CHECK.check_text('registry.json', text)
        self.assertEqual([(f.line, f.word) for f in findings], [(2, "runtime's"), (2, 'model’s')])

    def test_baseline_exempts_only_the_exact_inherited_line(self):
        original = "The upstream model's result."
        baseline = [CHECK.line_hash(original)]
        self.assertEqual(self.words('README.md', original, baseline), [])
        self.assertEqual(self.words('README.md', original + ' New claim.', baseline), ["model's"])

    def test_cli_counts_owned_files_and_excludes_recorded_data(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            (root / 'README.md').write_text("The runtime's contract.\n")
            corpus = root / 'tools/conformance/corpus'
            corpus.mkdir(parents=True)
            (corpus / 'record.json').write_text(json.dumps({'description': "source's observation"}))
            (root / '.gitignore').write_text('ignored.md\n')
            (root / 'ignored.md').write_text("The source's text.")
            command = [sys.executable, '-B', str(SCRIPT), '--root', str(root), '--json']
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 1, result.stderr)
            report = json.loads(result.stdout)
            self.assertEqual((report['files'], report['findings']), (1, 1))
            (root / 'README.md').write_text('The contract of the runtime.\n')
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['findings'], 0)


if __name__ == '__main__':
    unittest.main()
