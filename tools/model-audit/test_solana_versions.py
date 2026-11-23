"""Reject unsupported version widening independently of the catalog generator."""

from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from solana_source_map import rust_identities
from solana_versions import compatibility_groups, version_ranges, verify_release_windows

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "packages/solanalib-specs/tools"))
from version_compatibility import equality_controls, markdown  # noqa: E402


def fixture():
    document = {"interfaces": [], "models": [], "api": [], "compatibility": []}
    for version in ("1.0.0", "1.1.0", "1.2.0"):
        document["interfaces"].append({"id": version, "crate": "example-sdk-" + version})
        document["models"].append({"id": version, "kind": "full"})
        document["api"].append({"id": version, "source_id": version, "models": [version],
                                "rust_names": ["example_sdk::read"]})
    document["compatibility"] = [{"id": "read", "models": ["1.0.0", "1.2.0"],
                                    "releases": ["1.0.0", "1.1.0", "1.2.0"],
                                    "reviewed_on": "2026-11-09", "argument": "Same source behavior."}]
    return document


def shared_fixture():
    """Two exact source releases share one named contract; the gap stays open."""
    document = fixture()
    document["models"] = [{"id": "read", "kind": "full", "contract": "Solanalib.Specs.ExampleSdk.read_contract"},
                          {"id": "1.1.0", "kind": "full", "contract": "Solanalib.Specs.ExampleSdk.other_contract"}]
    for api in (document["api"][0], document["api"][2]):
        api["models"] = ["read"]
    document["compatibility"][0]["models"] = ["read"]
    return document


class VersionCompatibilityTests(unittest.TestCase):
    def test_gap_in_review_does_not_become_a_supported_interval(self):
        group = compatibility_groups(fixture())[0]
        self.assertEqual(version_ranges(group["versions"], group["releases"]), "1.0.0; 1.2.0")
        self.assertEqual(version_ranges({"1.0.0", "1.1.0", "1.2.0"}, group["releases"]), "1.0.0–1.2.0")

    def test_ranges_do_not_change_exact_source_identities(self):
        document = fixture()
        before = rust_identities(document)
        compatibility_groups(document)
        self.assertEqual(rust_identities(document), before)
        self.assertEqual({row["crate_version"] for row in before["1.0.0"]}, {"1.0.0"})

    def test_one_model_can_keep_several_exact_bindings_without_filling_the_gap(self):
        document = shared_fixture()
        before = deepcopy(document)
        group = compatibility_groups(document)[0]
        self.assertEqual(group["versions"], {"1.0.0": "read", "1.2.0": "read"})
        self.assertEqual(version_ranges(group["versions"], group["releases"]), "1.0.0; 1.2.0")
        self.assertEqual({row["crate_version"] for row in rust_identities(document)["read"]},
                         {"1.0.0", "1.2.0"})
        self.assertEqual(document, before)

    def test_shared_model_must_have_the_same_complete_identity_set_at_each_release(self):
        for names in (["example_sdk::write"], ["example_sdk::read", "example_sdk::other"]):
            with self.subTest(names=names):
                document = shared_fixture()
                document["api"][2]["rust_names"] = names
                with self.assertRaisesRegex(ValueError, "mixes functions or model roles"):
                    compatibility_groups(document)

    def test_shared_model_cannot_mix_source_crates(self):
        document = shared_fixture()
        document["interfaces"][2]["crate"] = "different-sdk-1.2.0"
        with self.assertRaisesRegex(ValueError, "mixes source crates"):
            compatibility_groups(document)

    def test_two_models_cannot_claim_the_same_release_in_one_review(self):
        document = fixture()
        document["api"][2]["source_id"] = "1.0.0"
        with self.assertRaisesRegex(ValueError, "Repeated compatibility version"):
            compatibility_groups(document)

    def test_shared_model_keeps_release_window_and_difference_guards(self):
        document = shared_fixture()
        document["compatibility"][0]["releases"] = ["1.0.0", "1.1.0"]
        with self.assertRaisesRegex(ValueError, "Invalid release window"):
            compatibility_groups(document)
        document = shared_fixture()
        document["compatibility"][0]["differences"] = [{
            "source_id": "1.2.0", "line": 1, "anchor_text": "pub fn read()",
            "reason": "Different error."}]
        with self.assertRaisesRegex(ValueError, "Conflicting or unrelated"):
            compatibility_groups(document)

    def test_rejects_mixing_different_functions_and_model_roles(self):
        for change in ("name", "role"):
            with self.subTest(change=change):
                document = fixture()
                if change == "name":
                    document["api"][2]["rust_names"] = ["example_sdk::write"]
                else:
                    document["models"][2]["kind"] = "observation"
                with self.assertRaisesRegex(ValueError, "mixes functions or model roles"):
                    compatibility_groups(document)

    def test_rejects_unknown_duplicate_and_unbound_models(self):
        for selected in (["unknown"], ["1.0.0", "1.0.0"]):
            document = fixture()
            document["compatibility"][0]["models"] = selected
            with self.assertRaisesRegex(ValueError, "Unknown or repeated compatibility model"):
                compatibility_groups(document)
        document = fixture()
        document["api"][0]["rust_names"] = []
        with self.assertRaisesRegex(ValueError, "no registered Rust identity"):
            compatibility_groups(document)

    def test_cannot_claim_both_compatibility_and_a_behavior_difference(self):
        document = fixture()
        document["compatibility"][0]["differences"] = [{
            "source_id": "1.0.0", "line": 1, "anchor_text": "pub fn read()",
            "reason": "Different error."}]
        with self.assertRaisesRegex(ValueError, "Conflicting or unrelated"):
            compatibility_groups(document)
        document["compatibility"][0]["differences"][0]["source_id"] = "1.1.0"
        group = compatibility_groups(document)[0]
        self.assertNotIn("1.1.0", group["versions"])

    def test_review_requires_explicit_releases_date_and_argument(self):
        for key, value in (("releases", ["1.0.0", "1.0.0", "1.2.0"]),
                           ("releases", ["1.0.0", "1.1.x", "1.2.0"]),
                           ("releases", ["1.0.0", "1.1.0"]),
                           ("argument", ""), ("reviewed_on", "yesterday")):
            with self.subTest(key=key, value=value):
                document = fixture()
                document["compatibility"][0][key] = value
                with self.assertRaises(ValueError):
                    compatibility_groups(document)

    def test_published_intermediate_release_cannot_be_omitted(self):
        document = fixture()
        document["compatibility"][0]["releases"] = ["1.0.0", "1.2.0"]
        group = compatibility_groups(document)[0]
        published = "\n".join(json.dumps({"name": "example-sdk", "vers": v})
                               for v in ("1.0.0", "1.1.0", "1.2.0"))
        with self.assertRaisesRegex(ValueError, "Release window needs review"):
            verify_release_windows([group], lambda crate: published)

    def test_yanked_releases_are_included_and_outside_releases_do_not_extend_support(self):
        group = compatibility_groups(fixture())[0]
        published = "\n".join(json.dumps({"name": "example-sdk", "vers": v, "yanked": v == "1.1.0"})
                               for v in ("0.9.0", "1.0.0", "1.1.0", "1.2.0", "2.0.0", "1.2.0-rc.1"))
        before = deepcopy(group)
        verify_release_windows([group], lambda crate: published)
        self.assertEqual(group, before)
        incomplete = deepcopy(group)
        incomplete["releases"] = ["1.0.0", "1.2.0"]
        with self.assertRaisesRegex(ValueError, "Release window needs review"):
            verify_release_windows([incomplete], lambda crate: published)

    def test_wrong_crate_index_cannot_supply_version_evidence(self):
        with self.assertRaisesRegex(ValueError, "Wrong crate release index"):
            verify_release_windows(compatibility_groups(fixture()),
                                   lambda crate: '{"name":"different-sdk","vers":"1.0.0"}')


class EqualityControlGenerationTests(unittest.TestCase):
    def test_a_shared_contract_has_no_self_equality_control_or_unused_import(self):
        document = shared_fixture()
        with patch("version_compatibility.declaration_modules", return_value={}):
            result = equality_controls(document, compatibility_groups(document))
        self.assertNotIn("example :", result)
        self.assertNotIn("public import", result)

    def test_distinct_contracts_keep_whole_contract_equality_controls(self):
        document = {"models": [
            {"id": "original", "contract": "Solanalib.Specs.ExampleSdk.read_contract"},
            {"id": "same-name", "contract": "Solanalib.Specs.ExampleSdk.read_contract"},
            {"id": "other", "contract": "Solanalib.Specs.ExampleSdk.alternate.read_contract"}]}
        groups = [{"models": ["original", "same-name", "other"]}]
        declarations = {"Solanalib.Specs.ExampleSdk.read_contract": {"Solanalib.Specs.ExampleSdk.Read"},
                        "Solanalib.Specs.ExampleSdk.alternate.read_contract": {"Solanalib.Specs.ExampleSdk.Alternate"}}
        with patch("version_compatibility.declaration_modules", return_value=declarations):
            result = equality_controls(document, groups)
        self.assertEqual(result.count("example :"), 1)
        self.assertIn("example : Solanalib.Specs.ExampleSdk.alternate.read_contract =\n"
                      "    Solanalib.Specs.ExampleSdk.read_contract := rfl", result)
        self.assertIn("public import Solanalib.Specs.ExampleSdk.Read", result)
        self.assertIn("public import Solanalib.Specs.ExampleSdk.Alternate", result)

    def test_shared_contract_documentation_links_each_release_to_its_own_source(self):
        document = shared_fixture()
        for source in document["interfaces"]:
            version = source["id"]
            source.update(repository="https://example.invalid/sdk", revision=version,
                          path="src/lib.rs", path_in_repository="src/lib.rs")
        result = markdown(document, compatibility_groups(document))
        for version in ("1.0.0", "1.2.0"):
            row = next(line for line in result.splitlines() if line.startswith(f"| {version} |"))
            self.assertIn(f"/blob/{version}/src/lib.rs", row)
            other = "1.2.0" if version == "1.0.0" else "1.0.0"
            self.assertNotIn(f"/blob/{other}/", row)


if __name__ == "__main__":
    unittest.main()
