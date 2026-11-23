"""Controls for exact, non-destructive generation of library capability catalogs."""

from contextlib import redirect_stdout
from copy import deepcopy
import importlib.util
import io
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "generate_capabilities", ROOT / "packages/solanalib-specs/tools/generate_capabilities.py")
generator = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(generator)


def ungap(source):
    return re.sub(r"\\\n[ \t]*", "", source)


def compact_lean(source):
    return "".join(re.findall(r'"(?:\\.|[^"\\])*"|[^\s]', ungap(source)))


class CapabilityGenerationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        self.module = self.package / "Solanalib/Specs/ExampleSdk" / "Contract.lean"
        self.module.parent.mkdir(parents=True)
        self.module.write_text("\n".join([
            "namespace Solanalib.Specs.ExampleSdk", "namespace Example",
            "def call_contract := ()", "def call_family := ()",
            "def reference := ()", "theorem reference_correct := True.intro",
            "theorem satisfiable := True.intro", "theorem has_execution := True.intro",
            "def sample := ()", "end Example", "end Solanalib.Specs.ExampleSdk", "",
        ]))
        self.model = {
            "id": "example.call", "kind": "partial",
            "contract": "Solanalib.Specs.ExampleSdk.Example.call_contract",
            "family": "Solanalib.Specs.ExampleSdk.Example.call_family",
            "reference": "Solanalib.Specs.ExampleSdk.Example.reference",
            "sample": "Solanalib.Specs.ExampleSdk.Example.sample",
            "witness_kind": "FamilyReference",
            "witnesses": ["Solanalib.Specs.ExampleSdk.Example." + suffix for suffix in
                          ("reference_correct", "satisfiable", "has_execution")],
        }
        self.source_map = {
            "models": [self.model],
            "interfaces": [{"id": "example-source", "crate": "example-crate-1.0.0"}],
            "api": [{"id": "example.call", "source_id": "example-source", "models": ["example.call"],
                     "rust_names": ["<example::Value<'a, [u8; N]> as example::Call<&'a [u8]>>::call",
                                    "example::Value::<'a>::call_inherent"]}],
        }
        self.enterContext(patch.object(generator, "PACKAGE", self.package))
        self.enterContext(patch.object(generator, "load_source_map",
                                       return_value=self.source_map))

    def test_full_family_and_role_are_preserved(self):
        [(path, text)] = generator.generated_files()
        self.assertEqual(path, self.package / "Solanalib/Specs/ExampleSdk/Capabilities.lean")
        self.assertIn("Example.call_family", text)
        self.assertIn("=> .partialModel", text)
        self.assertIn("Example.reference_correct index", text)
        self.assertNotIn("Example.sample", text)
        self.assertNotIn("Capabilities.single", text)

    def test_rust_identities_come_from_the_api_source_and_names(self):
        [(_, text)] = generator.generated_files()
        self.assertIn(compact_lean(
            "    | .Example_call => [⟨\"example-crate\", \"1.0.0\", \"example::Call::call\", "
            "\"<example::Value<'a, [u8; N]> as example::Call<&'a [u8]>>::call\"⟩, "
            "⟨\"example-crate\", \"1.0.0\", \"example::Value::<'a>::call_inherent\", "
            "\"example::Value::<'a>::call_inherent\"⟩]"), compact_lean(text))
        self.source_map["api"] = []
        [(_, text)] = generator.generated_files()
        self.assertIn("    | .Example_call => []", text)

    def add_applicability(self):
        source = {"kind": "registry", "url": "https://github.com/rust-lang/crates.io-index", "revision": ""}
        self.source_map["applicability_sources"] = {"example": {
            "package": "example-crate", "source": source, "reviewed_on": "2026-11-09",
            "releases": {"1.1.0": {
                "archive_url": "https://static.crates.io/crates/example-crate/example-crate-1.1.0.crate",
                "sha256": "a" * 64}}, "evidence": ["Exact published archive."]}}
        self.source_map["applicability"] = {"example.call": {"profiles": [{
            "id": "reviewed", "source": "example", "releases": ["1.1.0"],
            "items": [{"releases": ["1.1.0"], "implementation": "example::Old::call"}],
            "argument": "The predecessor has the same complete contract.",
            "evidence": ["Immutable source closure."],
            "conditions": ["Use the original indexed callback interpretation."]}]}}
        return self.source_map["applicability"]["example.call"]["profiles"][0]

    def test_applicability_extends_catalog_views_without_replacing_registered_models(self):
        self.add_applicability()
        [(_, text)] = generator.generated_files()
        self.assertIn("Example.call_family", text)
        self.assertIn("=> .partialModel", text)
        self.assertIn("  applicability := fun key => match key with", text)
        self.assertIn('releases := ["1.1.0"]', text)
        self.assertIn('implementation := "example::Old::call"', text)
        self.assertIn('⟨"example-crate", "1.0.0",', text)
        self.assertNotIn('⟨"example-crate", "1.1.0",', text)
        self.source_map["api"] = []
        [(_, text)] = generator.generated_files()
        self.assertIn("  identities := fun key => match key with\n    | .Example_call => []", text)
        self.assertIn('implementation := "example::Old::call"', text)

    def test_profiles_use_the_same_multiline_layout_for_every_library(self):
        self.add_applicability()
        [(_, text)] = generator.generated_files()
        expected = (
            '{ id := "reviewed", package := "example-crate", '
            'source := { kind := "registry", url := "https://github.com/rust-lang/crates.io-index", '
            'revision := "" }, releases := ["1.1.0"], item := "example::Old::call", '
            'implementation := "example::Old::call", '
            'conditions := ["Use the original indexed callback interpretation."], '
            'evidence := ["Immutable source closure."], '
            'argument := "The predecessor has the same complete contract." }')
        tokens = r'"(?:\\.|[^"\\])*"|[^\s]'
        compact = f"    | .Example_call => [{expected}]"
        clause = text.split("  applicability := fun key => match key with\n", 1)[1].split(
            "\n  applicabilityConsumers", 1)[0]
        self.assertEqual(re.findall(tokens, clause), re.findall(tokens, compact))
        self.assertIn("    | .Example_call => [\n      {\n", clause)

    def test_multiline_profiles_preserve_all_tokens_and_string_escapes(self):
        profile = self.add_applicability()
        quoted = ('Keep "quoted, [fields] {together}" and \\paths; preserve λ.'
                  ' Preserve separators: \u0085 \u2028 \u2029.')
        profile.update({
            "identity_dependency": "provider",
            "target": [{"field": "arch", "include": ["x86_64"], "exclude": ["bpf"],
                        "reason": quoted}],
            "features": {"all": ["decode"], "any": ["std", "alloc"], "none": ["alternate"],
                         "reason": quoted},
            "target_features": {"none": ["static-syscalls"], "reason": quoted},
            "dependencies": [{"package": "provider", "releases": ["2.0.0"],
                              "source": {"kind": "git", "url": "https://example.invalid/provider",
                                         "revision": "a" * 40}, "reason": quoted}],
            "conditions": [quoted], "argument": quoted, "evidence": [quoted],
        })
        other = deepcopy(profile)
        other["id"] = "alternative"
        self.source_map["applicability"]["example.call"]["profiles"].append(other)
        [(_, multiline)] = generator.generated_files()
        render_profile = generator.lean_profile
        with patch.object(generator, "lean_profile",
                          side_effect=lambda profile, **_: render_profile(profile, multiline=False)):
            [(_, compact)] = generator.generated_files()
        # Compare every non-whitespace character, preserving complete string literals.
        tokens = r'"(?:\\.|[^"\\])*"|[^\s]'
        self.assertEqual(re.findall(tokens, ungap(compact)), re.findall(tokens, ungap(multiline)))
        self.assertIn(json.dumps(quoted, ensure_ascii=False), ungap(multiline))
        self.assertIn("    | .Example_call => [\n      {\n", multiline)
        self.assertIn('      },\n      {\n        id := "alternative",\n', multiline)
        self.assertIn('        source := {\n          kind := "registry",\n', multiline)
        self.assertIn('        dependencies := [{\n          package := "provider",\n', multiline)

    def test_profiles_reject_control_characters_in_strings(self):
        profile = self.add_applicability()
        for character in ("\0", "\n", "\t", "\x7f"):
            with self.subTest(character=repr(character)):
                profile["argument"] = "Invalid" + character + "argument"
                with self.assertRaisesRegex(ValueError, "Invalid profile argument"):
                    generator.generated_files()

    def test_multiple_exact_releases_do_not_duplicate_the_member(self):
        self.source_map["interfaces"].append({"id": "next-source", "crate": "example-crate-2.0.0"})
        self.source_map["api"].append({**deepcopy(self.source_map["api"][0]),
                                      "id": "next-api", "source_id": "next-source"})
        [(_, text)] = generator.generated_files()
        self.assertIn('⟨"example-crate", "1.0.0",', text)
        self.assertIn('⟨"example-crate", "2.0.0",', text)
        self.assertEqual(text.count("  | Example_call\n"), 1)
        self.assertEqual(text.count('=> "example.call"'), 1)
        self.assertIn("Example.call_family", text)

    def test_unsupported_rust_name_is_rejected(self):
        self.source_map["api"][0]["rust_names"] = ["<example::Value as example::Call>::call::{closure#0}"]
        with self.assertRaisesRegex(ValueError, "Unsupported Rust name form"):
            generator.generated_files()

    def test_check_rejects_changed_binding_without_rewriting(self):
        self.add_applicability()
        [(path, text)] = generator.generated_files()
        for old, new in (("=> .partialModel", "=> .full"),
                         ('implementation := "example::Old::call"',
                          'implementation := "example::Other::call"')):
            path.write_text(text.replace(old, new))
            before = path.read_bytes()
            with patch("sys.argv", ["generate_capabilities.py", "--check"]):
                with self.assertRaisesRegex(SystemExit, "Stale capability catalogs"):
                    generator.main()
            self.assertEqual(path.read_bytes(), before)
        path.write_text(text)
        with patch("sys.argv", ["generate_capabilities.py", "--check"]):
            with redirect_stdout(io.StringIO()):
                generator.main()
        self.assertEqual(path.read_text(), text)

    def test_missing_or_ambiguous_declaration_is_rejected(self):
        self.model["reference"] = "Solanalib.Specs.ExampleSdk.Example.missing"
        with self.assertRaisesRegex(ValueError, "Expected one source module"):
            generator.generated_files()
        self.model["reference"] = "Solanalib.Specs.ExampleSdk.Example.reference"
        (self.module.parent / "Duplicate.lean").write_text(self.module.read_text())
        with self.assertRaisesRegex(ValueError, "Expected one source module"):
            generator.generated_files()


if __name__ == "__main__":
    unittest.main()
