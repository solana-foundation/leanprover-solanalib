"""Executable function-version selection, including installed-package controls."""

from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from solana_applicability import (catalog_names, lean_profile, normalized_applicability,
                                 verify_source_census)
from solana_source_map import load_source_map
from solana_versions import compatibility_groups
from applicability import (CRATES_IO, lookup, normalize_build, read_json, validate_manifest,
                           version_matches)


ROOT = Path(__file__).resolve().parents[2]
REGISTRY = {"kind": "registry", "url": CRATES_IO, "revision": ""}


def fixture():
    versions = ["1.0.0", "1.1.0", "1.2.0"]
    profile = {"id": "stable", "source": "example", "releases": ["1.0.0", "1.2.0"],
               "items": [{"releases": ["1.0.0"], "item": "example::Old::read",
                          "implementation": "example::Old::read"},
                         {"releases": ["1.2.0"], "item": "example::Current::read",
                          "implementation": "example::Current::read"}],
               "conditions": ["Supply the existing indexed reader interpretation."],
               "argument": "The same operation was renamed; the intermediate error path differs.",
               "evidence": ["https://example.invalid/source/" + "a" * 40]}
    document = {"models": [
        {"id": "read", "contract": "example.Value.read_contract", "kind": "full"},
        {"id": "shared", "contract": "Solanalib.Specs.Core.Buffer.construction_contract", "kind": "supporting"}],
        "interfaces": [{"id": "current", "crate": "example-1.2.0"}],
        "api": [{"source_id": "current", "models": ["read"], "rust_names": ["example::Current::read"]}],
        "applicability_scope": ["Existing mathematical models; no Rust implementation proof."],
        "applicability_sources": {"example": {
            "package": "example", "source": deepcopy(REGISTRY), "reviewed_on": "2026-11-09",
            "releases": {version: {"archive_url": f"https://static.crates.io/crates/example/example-{version}.crate",
                                   "sha256": "a" * 64} for version in versions},
            "evidence": ["Published archives with exact checksums."]}},
        "applicability": {"read": {"profiles": [profile]},
                          "shared": {"consumers": ["read"], "conditions": ["Use the caller's resource interpretation."]}}}
    return document


def build(version="1.2.0", **extra):
    return {"package": "example", "version": version, "source": deepcopy(REGISTRY), **extra}


def decision(document, actual=None, model="read"):
    return lookup(normalized_applicability(document), actual or build(), [model])["models"][0]


class SourceApplicabilityTests(unittest.TestCase):
    def test_declared_range_is_distinct_from_reference_releases(self):
        document = fixture()
        mapping = document["applicability"]["read"]["profiles"][0]["items"][1]
        mapping["compatible_ranges"] = [{"lower": "1.2.0", "upper": "2.0.0"}]
        for version in ("1.2.0", "1.2.1", "1.10.0", "1.10.0+build.7"):
            answer = decision(document, build(version))
            self.assertEqual(answer["status"], "eligible", version)
            self.assertEqual(answer["identities"][0]["implementation"], "example::Current::read")
            self.assertEqual(answer["identities"][0]["version"], version)
        for version in ("1.1.0", "2.0.0", "1.3.0-rc.1"):
            self.assertEqual(decision(document, build(version))["status"], "unsupported", version)
        profiles = normalized_applicability(document)["models"][0]["profiles"]
        self.assertEqual(profiles[1]["releases"], ["1.2.0"])
        self.assertNotIn("compatible_ranges", profiles[0])
        self.assertIn('lower := "1.2.0", upper := "2.0.0"', lean_profile(profiles[1]))

    def test_dependency_ranges_preserve_origins_and_unknown_fact_handling(self):
        document = fixture()
        document["applicability"]["read"]["profiles"][0]["dependencies"] = [
            {"package": "codec", "releases": ["1.6.1"],
             "compatible_ranges": [{"lower": "1.5.3", "upper": "2.0.0"}],
             "reason": "Assume the selected slice reader preserves the reference error and value contract."}]
        self.assertEqual(decision(document)["status"], "unresolved")
        for version, status in (("1.5.2", "unsupported"), ("1.5.3", "eligible"),
                                ("1.8.1", "eligible"), ("2.0.0", "unsupported")):
            actual = {"package": "codec", "version": version, "source": REGISTRY}
            self.assertEqual(decision(document, build(dependencies=[actual]))["status"], status)
        fork = {"kind": "git", "url": "https://example.invalid/fork", "revision": "b" * 40}
        self.assertEqual(decision(document, build(dependencies=[
            {"package": "codec", "version": "1.8.1", "source": fork}]))["status"], "unsupported")

    def test_cargo_pre_one_ranges_and_explicit_behavioral_holes(self):
        document = fixture()
        profile = document["applicability"]["read"]["profiles"][0]
        profile["dependencies"] = [{"package": "codec", "releases": ["0.10.1", "0.10.4", "0.0.3"],
            "compatible_ranges": [{"lower": "0.10.1", "upper": "0.10.2"},
                                  {"lower": "0.10.3", "upper": "0.11.0"},
                                  {"lower": "0.0.3", "upper": "0.0.4"}],
            "reason": "0.10.2 differs; 0.0.3 is a separate reference."}]
        for version, status in (("0.10.0", "unsupported"), ("0.10.1", "eligible"),
                ("0.10.2", "unsupported"), ("0.10.3", "eligible"), ("0.10.99", "eligible"),
                ("0.11.0", "unsupported"), ("0.0.3", "eligible"), ("0.0.4", "unsupported")):
            actual = {"package": "codec", "version": version, "source": REGISTRY}
            self.assertEqual(decision(document, build(dependencies=[actual]))["status"], status, version)

    def test_invalid_unbacked_and_cross_line_ranges_are_rejected(self):
        intervals = [{"lower": "1.2.0", "upper": "3.0.0"},
                     {"lower": "0.2.0", "upper": "0.4.0"},
                     {"lower": "0.0.2", "upper": "0.0.4"},
                     {"lower": "1.2.0", "upper": "1.2.0"},
                     {"lower": "1.3.0", "upper": "2.0.0"},
                     {"lower": "1.2.0-rc.1", "upper": "2.0.0"},
                     {"lower": "1.2.0+build", "upper": "2.0.0"},
                     {"lower": "01.2.0", "upper": "2.0.0"}]
        for interval in intervals:
            document = fixture()
            document["applicability"]["read"]["profiles"][0]["items"][1]["compatible_ranges"] = [interval]
            with self.subTest(interval=interval), self.assertRaises(ValueError):
                normalized_applicability(document)
        for value in ({}, "1.2.0", None):
            document = fixture()
            document["applicability"]["read"]["profiles"][0]["items"][1]["compatible_ranges"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                normalized_applicability(document)

    def test_ranges_do_not_generalize_git_revisions(self):
        document = fixture()
        document["applicability_sources"]["example"]["source"] = {
            "kind": "git", "url": "https://example.invalid/fork", "revision": "b" * 40}
        document["applicability"]["read"]["profiles"][0]["items"][1]["compatible_ranges"] = [
            {"lower": "1.2.0", "upper": "2.0.0"}]
        with self.assertRaisesRegex(ValueError, "registry source"):
            normalized_applicability(document)

    def test_source_sets_preserve_holes_future_releases_and_predecessor_names(self):
        document = fixture()
        for version, implementation in (("1.0.0", "example::Old::read"),
                                         ("1.2.0", "example::Current::read")):
            answer = decision(document, build(version))
            self.assertEqual(answer["status"], "eligible")
            self.assertEqual(answer["identities"][0]["implementation"], implementation)
            self.assertEqual(answer["identities"][0]["version"], version)
        for version in ("0.9.0", "1.1.0", "1.3.0", "2.0.0", "1.2.0-rc.1"):
            with self.subTest(version=version):
                answer = decision(document, build(version))
                self.assertEqual(answer["status"], "unsupported")
                self.assertEqual(answer["identities"], [])
                self.assertEqual(answer["profiles"][0]["reasons"][0]["code"], "release_excluded")

    def test_missing_irrelevant_build_facts_do_not_become_obligations(self):
        answer = decision(fixture())
        self.assertEqual(answer["status"], "eligible")
        self.assertTrue(all(not profile["reasons"] for profile in answer["profiles"]
                            if profile["status"] == "eligible"))
        self.assertEqual(answer["profiles"][1]["conditions"],
                         ["Supply the existing indexed reader interpretation."])

    def test_target_unknown_mismatch_and_actual_selected_path_are_distinct(self):
        document = fixture()
        document["applicability"]["read"]["profiles"][0]["target"] = [
            {"field": "os", "include": ["solana"], "reason": "Only that branch invokes the syscall."}]
        self.assertEqual(decision(document)["status"], "unresolved")
        self.assertEqual(decision(document, build(target=[{"field": "os", "value": "linux"}]))["status"],
                         "unsupported")
        self.assertEqual(decision(document, build(target=[{"field": "os", "value": "solana"}]))["status"],
                         "eligible")
        # A different package or release does not acquire spurious missing-OS obligations.
        self.assertEqual(decision(document, build("9.0.0"))["status"], "unsupported")

    def test_feature_sets_are_explicit_but_unrelated_features_are_allowed(self):
        document = fixture()
        document["applicability"]["read"]["profiles"][0]["features"] = {
            "all": ["borsh"], "any": ["std", "alloc"], "none": ["alternate-errors"],
            "reason": "These features select the reviewed decoder and error branch."}
        self.assertEqual(decision(document)["status"], "unresolved")
        for enabled in ([], ["borsh"], ["borsh", "std", "alternate-errors"]):
            self.assertEqual(decision(document, build(features=enabled))["status"], "unsupported")
        self.assertEqual(decision(document, build(features=["borsh", "alloc", "unrelated"]))["status"],
                         "eligible")

    def test_target_features_are_not_cargo_features(self):
        document = fixture()
        document["applicability"]["read"]["profiles"][0]["target_features"] = {
            "none": ["static-syscalls"], "reason": "Static dispatch uses a different calling convention."}
        self.assertEqual(decision(document, build(features=[]))["status"], "unresolved")
        self.assertEqual(decision(document, build(target_features=[]))["status"], "eligible")
        self.assertEqual(decision(document, build(target_features=["static-syscalls"]))["status"], "unsupported")

    def test_exact_git_origin_and_commit_cannot_be_replaced_by_a_version_string(self):
        document = fixture()
        fork = {"kind": "git", "url": "https://example.invalid/fork", "revision": "b" * 40}
        document["applicability_sources"]["example"]["source"] = fork
        self.assertEqual(decision(document)["status"], "unsupported")
        self.assertEqual(decision(document, build(source=fork))["status"], "eligible")
        for key, value in (("revision", "c" * 40), ("url", "https://example.invalid/other")):
            changed = {**fork, key: value}
            self.assertEqual(decision(document, build(source=changed))["status"], "unsupported")

    def test_exact_git_origin_accepts_compatible_registry_dependencies(self):
        document = fixture()
        source = {"kind": "git", "url": "https://example.invalid/source", "revision": "b" * 40}
        document["applicability_sources"]["example"]["source"] = source
        document["applicability"]["read"]["profiles"][0]["dependencies"] = [
            {"package": package, "source": deepcopy(REGISTRY), "releases": ["1.6.1"],
             "compatible_ranges": [{"lower": "1.5.3", "upper": "2.0.0"}],
             "reason": "Assume preservation of the reviewed reader and derive behavior."}
            for package in ("codec", "codec-derive")]
        dependencies = [{"package": package, "version": "1.8.1", "source": deepcopy(REGISTRY)}
                        for package in ("codec", "codec-derive")]
        actual = build(source=deepcopy(source), dependencies=dependencies)
        self.assertEqual(decision(document, actual)["status"], "eligible")
        actual["source"]["revision"] = "0" * 40
        self.assertEqual(decision(document, actual)["status"], "unsupported")

    def test_only_behavior_relevant_dependencies_are_required(self):
        document = fixture()
        document["applicability"]["read"]["profiles"][0]["dependencies"] = [
            {"package": "resolver", "releases": ["0.11.1"],
             "reason": "Later versions retain a different borrow set."}]
        self.assertEqual(decision(document)["status"], "unresolved")
        dependency = {"package": "resolver", "version": "0.11.1", "source": deepcopy(REGISTRY)}
        unrelated = {"package": "unrelated", "version": "99.0.0", "source": deepcopy(REGISTRY)}
        self.assertEqual(decision(document, build(dependencies=[dependency, unrelated]))["status"], "eligible")
        for changed in ({**dependency, "version": "0.11.4"},
                        {**dependency, "source": {"kind": "git", "url": "https://example.invalid/fork",
                                                   "revision": "b" * 40}}):
            self.assertEqual(decision(document, build(dependencies=[changed]))["status"], "unsupported")

    def test_reexport_identity_uses_the_actual_defining_package(self):
        document = fixture()
        profile = document["applicability"]["read"]["profiles"][0]
        profile["identity_dependency"] = "example-v2"
        with self.assertRaisesRegex(ValueError, "constrained dependency"):
            normalized_applicability(document)
        profile["dependencies"] = [{"package": "example-v2", "source": deepcopy(REGISTRY),
                                    "releases": ["2.0.0", "2.1.0"],
                                    "reason": "The facade reexports the selected definition."}]
        self.assertEqual(decision(document)["status"], "unresolved")
        dependency = {"package": "example-v2", "version": "2.1.0", "source": deepcopy(REGISTRY)}
        answer = decision(document, build(dependencies=[dependency]))
        self.assertEqual(answer["status"], "eligible")
        self.assertEqual(answer["identities"][0]["package"], "example-v2")
        self.assertEqual(answer["identities"][0]["version"], "2.1.0")
        self.assertEqual(answer["identities"][0]["source"], REGISTRY)

    def test_ambiguous_dependencies_or_target_facts_never_choose_an_arbitrary_instance(self):
        dependency = {"package": "resolver", "version": "1.0.0", "source": deepcopy(REGISTRY)}
        with self.assertRaisesRegex(ValueError, "Ambiguous dependency"):
            normalize_build(build(dependencies=[dependency, {**dependency, "version": "2.0.0"}]))
        with self.assertRaisesRegex(ValueError, "Duplicate target"):
            normalize_build(build(target=[{"field": "os", "value": "solana"},
                                          {"field": "os", "value": "linux"}]))

    def test_alternative_profiles_are_disjunctive(self):
        document = fixture()
        original = document["applicability"]["read"]["profiles"][0]
        other = deepcopy(original)
        original["features"] = {"all": ["first"], "reason": "First equivalent branch."}
        other.update(id="alternative", features={"all": ["second"], "reason": "Second equivalent branch."})
        document["applicability"]["read"]["profiles"].append(other)
        self.assertEqual(decision(document, build(features=["second"]))["status"], "eligible")
        self.assertEqual(decision(document, build(features=[]))["status"], "unsupported")

    def test_shared_eligibility_preserves_its_own_family_without_caller_identity(self):
        answer = decision(fixture(), model="shared")
        self.assertEqual(answer["status"], "eligible")
        self.assertEqual(answer["contract"], "Solanalib.Specs.Core.Buffer.construction_contract")
        self.assertEqual(answer["identities"], [])
        self.assertFalse(answer["source_call"])
        self.assertEqual(answer["consumers"][0]["model_id"], "read")
        self.assertEqual(answer["catalog"], "Solanalib.Specs.Core.SupportingCapabilities.catalog")
        self.assertEqual(decision(fixture(), build("1.1.0"), "shared")["status"], "unsupported")

    def test_source_review_without_registered_call_does_not_manufacture_identity(self):
        document = fixture()
        document["api"] = []
        answer = decision(document)
        self.assertEqual(answer["status"], "eligible")
        self.assertFalse(answer["source_call"])
        self.assertEqual(answer["identities"], [])
        self.assertTrue(any(profile["status"] == "eligible" for profile in answer["profiles"]))

    def test_complete_accounting_unknown_sources_and_unreviewed_releases_are_checked(self):
        document = fixture()
        document["applicability"].pop("shared")
        with self.assertRaisesRegex(ValueError, "Incomplete function applicability"):
            normalized_applicability(document)
        for change in ("source", "release", "mapping"):
            document = fixture()
            profile = document["applicability"]["read"]["profiles"][0]
            if change == "source":
                profile["source"] = "unknown"
            elif change == "release":
                profile["releases"].append("1.3.0")
            else:
                profile["items"].pop()
            with self.subTest(change=change), self.assertRaises(ValueError):
                normalized_applicability(document)

    def test_shared_cycles_and_unknown_consumers_are_rejected(self):
        for consumer in ("shared", "unknown"):
            document = fixture()
            document["applicability"]["shared"]["consumers"] = [consumer]
            with self.assertRaises(ValueError):
                normalized_applicability(document)

    def test_called_item_uses_trait_path_and_does_not_silently_rename_implementation(self):
        document = fixture()
        mapping = document["applicability"]["read"]["profiles"][0]["items"][0]
        mapping.update(implementation="<example::Value as example::Read>::read", item="example::Read::read")
        self.assertEqual(decision(document, build("1.0.0"))["identities"][0]["item"], "example::Read::read")
        mapping["item"] = "example::Other::read"
        with self.assertRaisesRegex(ValueError, "Called item disagrees"):
            normalized_applicability(document)

    def test_source_history_requires_immutable_release_evidence(self):
        for change in ("url", "digest", "revision"):
            document = fixture()
            source = document["applicability_sources"]["example"]
            if change == "url":
                source["releases"]["1.0.0"]["archive_url"] = "https://example.invalid/latest"
            elif change == "digest":
                source["releases"]["1.0.0"]["sha256"] = "missing"
            else:
                source["source"] = {"kind": "git", "url": "https://example.invalid/repo", "revision": "main"}
            with self.subTest(change=change), self.assertRaises(ValueError):
                normalized_applicability(document)

    def test_census_detects_new_releases_and_missing_intermediate_history(self):
        document = fixture()
        releases = document["applicability_sources"]["example"]["releases"]

        def fetch(package, source):
            self.assertEqual(package, "example")
            self.assertEqual(source, REGISTRY)
            return "\n".join(json.dumps({"name": package, "vers": version, "cksum": digest})
                             for version, digest in published.items())

        published = {version: row["sha256"] for version, row in releases.items()}
        verify_source_census(document, fetch)
        published["1.2.1-rc.1"] = "b" * 64
        verify_source_census(document, fetch)
        published["1.3.0"] = "b" * 64
        with self.assertRaisesRegex(ValueError, "unrecorded.*1.3.0"):
            verify_source_census(document, fetch)
        del published["1.3.0"]
        del releases["1.1.0"]
        with self.assertRaisesRegex(ValueError, "unrecorded.*1.1.0"):
            verify_source_census(document, fetch)

    def test_census_verifies_checksums_without_fetching_git_forks(self):
        document = fixture()
        rows = [{"name": "example", "vers": version, "cksum": "a" * 64}
                for version in document["applicability_sources"]["example"]["releases"]]
        rows[0]["cksum"] = "b" * 64
        with self.assertRaisesRegex(ValueError, "archive digest differs"):
            verify_source_census(document, lambda *_: "\n".join(json.dumps(row) for row in rows))
        document["applicability_sources"]["example"]["source"] = {
            "kind": "git", "url": "https://example.invalid/fork", "revision": "b" * 40}
        verify_source_census(document, lambda *_: self.fail("Git sources must not use a registry census"))

    def test_typoed_filters_and_contradictory_profiles_are_rejected(self):
        for feature_filter in ({"al": ["std"]}, {"all": ["std"], "none": ["std"], "reason": "Conflict."},
                               {"all": ["std"]}):
            document = fixture()
            document["applicability"]["read"]["profiles"][0]["features"] = feature_filter
            with self.subTest(rule=feature_filter), self.assertRaises(ValueError):
                normalized_applicability(document)

    def test_duplicate_json_facts_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            read_json('{"version":"1.0.0", "version":"2.0.0"}')
        with self.assertRaisesRegex(ValueError, "Non-JSON"):
            read_json('{"version":NaN}')

    def test_lean_emission_uses_normalized_fields_and_preserves_family_names(self):
        document = fixture()
        document["applicability"]["read"]["profiles"][0]["target"] = [
            {"field": "os", "include": ["solana"], "exclude": ["linux"], "reason": "Branch difference."}]
        document["applicability"]["read"]["profiles"][0]["target_features"] = {
            "none": ["static-syscalls"], "reason": "Dynamic declaration."}
        manifest = normalized_applicability(document)
        emitted = lean_profile(manifest["models"][0]["profiles"][0])
        self.assertIn('«include» := ["solana"]', emitted)
        self.assertIn('«exclude» := ["linux"]', emitted)
        self.assertIn('targetFeatures :=', emitted)
        self.assertIn('implementation := "example::Old::read"', emitted)
        self.assertEqual(catalog_names(document["models"][0]),
                         ("example.Capabilities.catalog", "example.Capabilities.Key.Value_read"))


class RegisteredApplicabilityTests(unittest.TestCase):
    def test_pubkey_release_unions_preserve_exact_membership_without_duplicates(self):
        expected_items = {
            "as_ref": ("core::convert::AsRef::as_ref", "<solana_pubkey::Pubkey as core::convert::AsRef<[u8]>>::as_ref"),
            "cmp": ("core::cmp::Ord::cmp", "<solana_pubkey::Pubkey as core::cmp::Ord>::cmp"),
            "create_program_address_solana": ("solana_pubkey::Pubkey::create_program_address", "solana_pubkey::Pubkey::create_program_address"),
            "create_with_seed": ("solana_pubkey::Pubkey::create_with_seed", "solana_pubkey::Pubkey::create_with_seed"),
            "default": ("core::default::Default::default", "<solana_pubkey::Pubkey as core::default::Default>::default"),
            "deserialize_reader": ("borsh::de::BorshDeserialize::deserialize_reader", "<solana_pubkey::Pubkey as borsh::de::BorshDeserialize>::deserialize_reader"),
            "eq": ("core::cmp::PartialEq::eq", "<solana_pubkey::Pubkey as core::cmp::PartialEq>::eq"),
            "find_program_address_solana": ("solana_pubkey::Pubkey::find_program_address", "solana_pubkey::Pubkey::find_program_address"),
            "from": ("core::convert::From::from", "<solana_pubkey::Pubkey as core::convert::From<[u8; 32]>>::from"),
            "new_from_array": ("solana_pubkey::Pubkey::new_from_array", "solana_pubkey::Pubkey::new_from_array"),
            "serialize": ("borsh::ser::BorshSerialize::serialize", "<solana_pubkey::Pubkey as borsh::ser::BorshSerialize>::serialize"),
            "clone": ("core::clone::Clone::clone", "<solana_pubkey::Pubkey as core::clone::Clone>::clone"),
            "to_bytes": ("solana_pubkey::Pubkey::to_bytes", "solana_pubkey::Pubkey::to_bytes"),
        }
        compatible = {"2.4.0", "2.4.1", "2.9.99+fixture"}
        for version in ("2.2.0", "2.2.1", "2.2.2", "2.3.0", "2.4.0", "2.4.1",
                        "2.9.99+fixture", "3.0.0", "2.4.1-rc.1"):
            actual = {"package": "solana-pubkey", "version": version, "source": REGISTRY,
                      "target": [{"field": "pointer_width", "value": "64"},
                                 {"field": "os", "value": "solana"}],
                      "features": ["borsh"],
                      "dependencies": [{"package": "borsh", "version": "0.10.4", "source": REGISTRY}]}
            for method, (item, implementation) in expected_items.items():
                with self.subTest(version=version, method=method):
                    model = "solana-pubkey::Pubkey::" + method
                    answer = lookup(self.manifest, actual, [model])["models"][0]
                    admitted = version in compatible
                    if method in {"cmp", "from", "new_from_array", "to_bytes"}:
                        admitted |= version in {"2.2.1", "2.2.2", "2.3.0"}
                    elif method != "clone":
                        admitted |= version == "2.2.1"
                    self.assertEqual(answer["status"], "eligible" if admitted else "unsupported")
                    expected = [{"package": "solana-pubkey", "version": version, "source": REGISTRY,
                                 "item": item, "implementation": implementation}] if admitted else []
                    self.assertEqual(answer["identities"], expected)
                    self.assertEqual(sum(profile["status"] == "eligible" for profile in answer["profiles"]),
                                     int(admitted))

    def test_pubkey_borsh_requires_legacy_generation_and_rejects_mixed_closure(self):
        legacy = {"package": "borsh", "version": "0.10.4", "source": REGISTRY}
        current = {**legacy, "version": "1.6.0"}
        for version in ("2.2.1", "2.4.0", "2.4.1"):
            actual = {"package": "solana-pubkey", "version": version, "source": REGISTRY,
                      "features": ["borsh"], "dependencies": [legacy]}
            for method in ("serialize", "deserialize_reader"):
                model = "solana-pubkey::Pubkey::" + method
                for dependencies, expected in (([legacy], "eligible"), ([{**legacy, "version": "0.10.5"}], "eligible"),
                                               ([], "unresolved"),
                                               ([current], "unsupported")):
                    with self.subTest(version=version, method=method, dependencies=dependencies):
                        answer = lookup(self.manifest, {**actual, "dependencies": dependencies}, [model])
                        self.assertEqual(answer["models"][0]["status"], expected)
                answer = lookup(self.manifest, {**actual, "features": []}, [model])
                self.assertEqual(answer["models"][0]["status"], "unsupported")
                with self.subTest(version=version, method=method), self.assertRaisesRegex(
                        ValueError, "Ambiguous dependency"):
                    lookup(self.manifest, {**actual, "dependencies": [legacy, current]}, [model])

    def test_rent_release_union_keeps_width_and_exact_release_guards(self):
        model = "solana-rent::Rent::is_exempt"
        admitted_versions = {"2.2.1", "2.2.2", "3.0.0", "3.1.0", "3.9.99+fixture"}
        for version in ("2.2.0", "2.2.1", "2.2.2", "3.0.0", "3.1.0", "3.9.99+fixture",
                        "4.0.0", "3.1.1-rc.1"):
            for width in (None, "32", "64"):
                with self.subTest(version=version, width=width):
                    actual = {"package": "solana-rent", "version": version, "source": REGISTRY,
                              "target": [] if width is None else [{"field": "pointer_width", "value": width}]}
                    answer = lookup(self.manifest, actual, [model])["models"][0]
                    admitted = version in admitted_versions and width == "64"
                    status = "eligible" if admitted else "unsupported"
                    if width is None and version in admitted_versions:
                        status = "unresolved"
                    self.assertEqual(answer["status"], status)
                    expected = [{"package": "solana-rent", "version": version, "source": REGISTRY,
                                 "item": "solana_rent::Rent::is_exempt",
                                 "implementation": "solana_rent::Rent::is_exempt"}] if admitted else []
                    self.assertEqual(answer["identities"], expected)
                    self.assertEqual(sum(profile["status"] == "eligible" for profile in answer["profiles"]),
                                     int(admitted))

    def test_anchor_system_wrappers_keep_exact_constructor_and_error_dependencies(self):
        operations = ("allocate", "assign", "create_account", "transfer")
        items = {"anchor-lang::system_program::" + operation:
                 "anchor_lang::system_program::" + operation for operation in operations}
        # Package, baseline, inspected references, extra patch, below lower, upper.
        # Extra patches exercise declared lookup ranges, not additional source review.
        gates = (
            ("solana-system-interface", "1.0.0", ("1.0.0",), "1.0.1", "0.999.0", "2.0.0"),
            ("solana-account-info", "2.3.0", ("2.3.0",), "2.3.1", "2.2.999", "3.0.0"),
            ("solana-program-error", "2.2.2", ("2.2.0", "2.2.1", "2.2.2"),
             "2.2.3", "2.1.999", "3.0.0"),
            ("solana-pubkey", "2.2.1", ("2.2.1", "2.4.0"), "2.4.1", "2.2.0", "3.0.0"),
            ("bincode", "1.3.3", ("1.3.3",), "1.3.4", "1.3.2", "2.0.0"),
        )
        dependencies = [{"package": gate[0], "version": gate[1], "source": REGISTRY}
                        for gate in gates]
        actual = {"package": "anchor-lang", "version": "0.32.1", "source": REGISTRY,
                  "dependencies": dependencies}
        other_sources = (
            {**REGISTRY, "url": "https://example.invalid/registry-index"},
            {"kind": "git", "url": "https://example.invalid/fork", "revision": "a" * 40},
        )

        def check(candidate, status="eligible", reason=None):
            answers = lookup(self.manifest, candidate, list(items))["models"]
            self.assertEqual(len(answers), len(items))
            self.assertEqual({answer["model_id"] for answer in answers}, set(items))
            for answer in answers:
                self.assertEqual(answer["status"], status)
                item = items[answer["model_id"]]
                expected = [{"package": "anchor-lang", "version": candidate["version"],
                             "source": REGISTRY, "item": item, "implementation": item}]
                self.assertEqual(answer["identities"], expected if status == "eligible" else [])
                if reason is not None:
                    self.assertIn(reason, {row["code"] for profile in answer["profiles"]
                                           for row in profile["reasons"]})

        for version in ("0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"):
            with self.subTest(source_version=version):
                # 0.32.4 is a hypothetical compatibility lookup, not an inspected release.
                check({**actual, "version": version})
        for version in ("0.31.999", "0.33.0", "1.0.0", "0.32.2-rc.1"):
            with self.subTest(excluded_source_version=version):
                check({**actual, "version": version}, "unsupported", "release_excluded")
        for source in other_sources:
            with self.subTest(source=source):
                check({**actual, "source": source}, "unsupported", "source_mismatch")

        # These wrappers have no source-feature or target gate. CPI remains opaque.
        for features in ([], ["event-cpi"]):
            with self.subTest(features=features):
                check({**actual, "features": features})
        for os, target_features in (("linux", []), ("solana", ["static-syscalls"])):
            with self.subTest(os=os, target_features=target_features):
                check({**actual, "target": [{"field": "os", "value": os}],
                       "target_features": target_features})
        check({key: value for key, value in actual.items() if key != "dependencies"},
              "unresolved", "dependency_unknown")

        for index, (package, baseline, references, patch, below, upper) in enumerate(gates):
            for version in references + (patch,):
                with self.subTest(dependency=package, admitted_version=version):
                    changed = deepcopy(actual)
                    changed["dependencies"][index]["version"] = version
                    check(changed)
            for version in (below, upper, patch + "-rc.1", "99.0.0"):
                with self.subTest(dependency=package, excluded_version=version):
                    changed = deepcopy(actual)
                    changed["dependencies"][index]["version"] = version
                    check(changed, "unsupported", "dependency_mismatch")
            with self.subTest(dependency=package, missing=True):
                check({**actual, "dependencies": dependencies[:index] + dependencies[index + 1:]},
                      "unresolved", "dependency_unknown")
            for source in other_sources:
                with self.subTest(dependency=package, source=source):
                    changed = deepcopy(actual)
                    changed["dependencies"][index]["source"] = source
                    check(changed, "unsupported", "dependency_mismatch")
            # Both candidates satisfy the range; lookup must still demand one actual edge.
            # For Pubkey this retains the original 2.2.1/2.4.0 ambiguity control.
            second = next(version for version in references + (patch,) if version != baseline)
            ambiguous = {**actual, "dependencies": dependencies + [
                {"package": package, "version": second, "source": REGISTRY}]}
            with self.subTest(dependency=package, ambiguous=True):
                with self.assertRaisesRegex(ValueError, "Ambiguous dependency"):
                    lookup(self.manifest, ambiguous, list(items))

    def test_anchor_checked_transfer_keeps_its_feature_and_constructor_release(self):
        model = "anchor-spl::token_2022::transfer_checked"
        item = "anchor_spl::token_2022::transfer_checked"
        # Package, baseline, inspected references, extra patch, below lower, upper.
        # Extra patches exercise declared lookup ranges, not additional source review.
        gates = (
            ("anchor-lang", "0.32.1", ("0.32.0", "0.32.1", "0.32.2", "0.32.3"),
             "0.32.4", "0.31.999", "0.33.0"),
            ("spl-token-2022", "8.0.1", ("8.0.0", "8.0.1"), "8.0.2", "7.999.0", "9.0.0"),
            ("solana-account-info", "2.3.0", ("2.3.0",), "2.3.1", "2.2.999", "3.0.0"),
            ("solana-program-error", "2.2.2", ("2.2.0", "2.2.1", "2.2.2"),
             "2.2.3", "2.1.999", "3.0.0"),
        )
        dependencies = [{"package": gate[0], "version": gate[1], "source": REGISTRY}
                        for gate in gates]
        actual = {"package": "anchor-spl", "version": "0.32.1", "source": REGISTRY,
                  "features": ["token_2022"], "dependencies": dependencies}
        other_sources = (
            {**REGISTRY, "url": "https://example.invalid/registry-index"},
            {"kind": "git", "url": "https://example.invalid/fork", "revision": "a" * 40},
        )

        def check(candidate, status="eligible", reason=None):
            answers = lookup(self.manifest, candidate, [model])["models"]
            self.assertEqual(len(answers), 1)
            answer = answers[0]
            self.assertEqual(answer["model_id"], model)
            self.assertEqual(answer["status"], status)
            expected = [{"package": "anchor-spl", "version": candidate["version"],
                         "source": REGISTRY, "item": item, "implementation": item}]
            self.assertEqual(answer["identities"], expected if status == "eligible" else [])
            if reason is not None:
                self.assertIn(reason, {row["code"] for profile in answer["profiles"]
                                       for row in profile["reasons"]})

        for version in ("0.32.0", "0.32.1", "0.32.2", "0.32.3", "0.32.4"):
            with self.subTest(source_version=version):
                # 0.32.4 is a hypothetical compatibility lookup, not an inspected release.
                check({**actual, "version": version})
        for version in ("0.31.999", "0.33.0", "1.0.0", "0.32.2-rc.1"):
            with self.subTest(excluded_source_version=version):
                check({**actual, "version": version}, "unsupported", "release_excluded")
        for source in other_sources:
            with self.subTest(source=source):
                check({**actual, "source": source}, "unsupported", "source_mismatch")

        missing_feature = {key: value for key, value in actual.items() if key != "features"}
        check(missing_feature, "unresolved", "features_unknown")
        for features in ([], ["token"]):
            with self.subTest(features=features):
                check({**actual, "features": features}, "unsupported", "features_mismatch")
        check({**actual, "features": ["token_2022", "token"]})
        # Target metadata does not supply a callee or physical-layout proof.
        for os, target_features in (("linux", []), ("solana", ["static-syscalls"])):
            with self.subTest(os=os, target_features=target_features):
                check({**actual, "target": [{"field": "os", "value": os}],
                       "target_features": target_features})
        check({key: value for key, value in actual.items() if key != "dependencies"},
              "unresolved", "dependency_unknown")

        for index, (package, baseline, references, patch, below, upper) in enumerate(gates):
            for version in references + (patch,):
                with self.subTest(dependency=package, admitted_version=version):
                    changed = deepcopy(actual)
                    changed["dependencies"][index]["version"] = version
                    check(changed)
            for version in (below, upper, patch + "-rc.1", "99.0.0"):
                with self.subTest(dependency=package, excluded_version=version):
                    changed = deepcopy(actual)
                    changed["dependencies"][index]["version"] = version
                    check(changed, "unsupported", "dependency_mismatch")
            with self.subTest(dependency=package, missing=True):
                check({**actual, "dependencies": dependencies[:index] + dependencies[index + 1:]},
                      "unresolved", "dependency_unknown")
            for source in other_sources:
                with self.subTest(dependency=package, source=source):
                    changed = deepcopy(actual)
                    changed["dependencies"][index]["source"] = source
                    check(changed, "unsupported", "dependency_mismatch")
            second = next(version for version in references + (patch,) if version != baseline)
            ambiguous = {**actual, "dependencies": dependencies + [
                {"package": package, "version": second, "source": REGISTRY}]}
            with self.subTest(dependency=package, ambiguous=True):
                with self.assertRaisesRegex(ValueError, "Ambiguous dependency"):
                    lookup(self.manifest, ambiguous, [model])
        # Retain the original ambiguous constructor-edge control as well.
        ambiguous = {**actual, "dependencies": dependencies + [
            {"package": "spl-token-2022", "version": "11.0.0", "source": REGISTRY}]}
        with self.assertRaisesRegex(ValueError, "Ambiguous dependency"):
            lookup(self.manifest, ambiguous, [model])

    @classmethod
    def setUpClass(cls):
        cls.document = load_source_map(ROOT / "packages/solanalib-specs")
        cls.manifest = normalized_applicability(cls.document)

    def test_switchboard_parser_accepts_its_reviewed_git_source(self):
        model = "switchboard-on-demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse"
        item = "switchboard_on_demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse"
        source = {"kind": "git", "url": "https://github.com/switchboard-xyz/switchboard-sdk",
                  "revision": "f75b1ef63e10eda35d046b1838810ec2935d7f39"}
        for origin, version, status in (
                (REGISTRY, "0.12.1", "eligible"),
                (source, "0.12.1", "eligible"),
                (REGISTRY, "0.12.2", "eligible"),
                (REGISTRY, "0.12.1+probe", "eligible"),
                (source, "0.12.0", "unsupported"),
                (source, "0.12.2", "unsupported"),
                (source, "0.13.0", "unsupported"),
                (source, "0.12.1-rc.1", "unsupported"),
                (source, "0.12.1+probe", "unsupported"),
                ({**source, "revision": "0" * 40}, "0.12.1", "unsupported"),
                ({**source, "url": "https://example.invalid/switchboard-sdk"}, "0.12.1", "unsupported")):
            with self.subTest(source=origin, version=version):
                actual = {"package": "switchboard-on-demand", "version": version, "source": origin}
                answer = lookup(self.manifest, actual, [model])["models"][0]
                self.assertEqual(answer["status"], status)
                if status == "eligible":
                    self.assertEqual(answer["identities"], [
                        {**actual, "item": item, "implementation": item}])
                    self.assertEqual(answer["contract"],
                                     "Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed."
                                     "PullFeedAccountData.parse_contract")
                else:
                    self.assertEqual(answer["identities"], [])

    def test_switchboard_parser_requires_one_exact_source(self):
        model = "switchboard-on-demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse"
        source = {"kind": "git", "url": "https://github.com/switchboard-xyz/switchboard-sdk",
                  "revision": "f75b1ef63e10eda35d046b1838810ec2935d7f39"}
        for invalid in (None, [REGISTRY, source],
                        {"kind": "git", "url": source["url"]},
                        {**source, "revision": "f75b1ef"}):
            with self.subTest(source=invalid), self.assertRaises(ValueError):
                actual = {"package": "switchboard-on-demand", "version": "0.12.1"}
                if invalid is not None:
                    actual["source"] = invalid
                lookup(self.manifest, actual, [model])

    def test_inspected_references_keep_their_source_and_admission(self):
        sources = self.document["applicability_sources"].values()
        for model in self.manifest["models"]:
            for profile in model["profiles"]:
                if profile["source"]["kind"] == "git":
                    self.assertNotIn("compatible_ranges", profile)
                source = next(row for row in sources if row["package"] == profile["package"]
                              and row["source"] == profile["source"])
                # A package census also contains releases admitted only by a
                # declared range. It does not turn them into inspected references.
                for release in profile["releases"]:
                    with self.subTest(model=model["model_id"], profile=profile["id"], release=release):
                        self.assertIn(release, source["releases"])
                        self.assertTrue(version_matches(profile, release))

    def test_published_compatible_release_is_not_an_inspected_reference(self):
        model = "solana-program-option::COption::as_ref"
        profiles = next(row for row in self.manifest["models"] if row["model_id"] == model)["profiles"]
        profile = next(row for row in profiles if not row.get("dependencies"))
        source = self.document["applicability_sources"]["solana-program-option"]
        self.assertEqual(profile["releases"], ["2.1.0", "2.2.0", "2.2.1"])
        self.assertIn("2.1.20", source["releases"])
        self.assertNotIn("2.1.20", profile["releases"])
        for version, eligible in (("2.1.20", True), ("2.1.20-rc.1", False), ("3.0.0", False)):
            with self.subTest(version=version):
                build = {"package": "solana-program-option", "version": version,
                         "source": REGISTRY, "dependencies": []}
                answer = lookup(self.manifest, build, [model])["models"][0]
                self.assertEqual(answer["status"], "eligible" if eligible else "unsupported")
                self.assertEqual([row["version"] for row in answer["identities"]],
                                 [version] if eligible else [])
        build = {"package": "solana-program-option", "version": "2.1.20", "dependencies": [],
                 "source": {"kind": "git", "url": "https://example.invalid/fork", "revision": "f" * 40}}
        self.assertEqual(lookup(self.manifest, build, [model])["models"][0]["status"], "unsupported")

    def test_sysvar_and_anchor_same_major_behavior_changes_remain_excluded(self):
        cases = [
            ("solana-sysvar::clock::Clock::get", "solana-sysvar",
             {"3.0.99": True, "3.1.0": False, "3.1.1": True, "3.1.99": True, "4.0.0": False}),
            ("anchor-lang::accounts::account_loader::AccountLoader::load", "anchor-lang",
             {"1.1.2": True, "1.1.99": True, "1.2.0": False, "1.3.0": False}),
        ]
        for model, package, versions in cases:
            for version, eligible in versions.items():
                with self.subTest(model=model, version=version):
                    actual = {"package": package, "version": version, "source": REGISTRY}
                    answer = lookup(self.manifest, actual, [model])["models"][0]
                    self.assertEqual(answer["status"], "eligible" if eligible else "unsupported")

    def test_facade_range_uses_the_actual_defining_version(self):
        model = "solana-hash::Hash::to_bytes"
        actual = {"package": "solana-hash", "version": "3.1.9", "source": REGISTRY,
                  "dependencies": [{"package": "solana-hash", "version": "4.8.0", "source": REGISTRY}]}
        answer = lookup(self.manifest, actual, [model])["models"][0]
        self.assertEqual(answer["status"], "eligible")
        self.assertEqual([row["version"] for row in answer["identities"]], ["4.8.0"])
        actual["dependencies"][0]["version"] = "5.0.0"
        self.assertEqual(lookup(self.manifest, actual, [model])["models"][0]["status"], "unsupported")

    def test_hook_dependency_ranges_preserve_signer_borrow_and_allocation_boundaries(self):
        model = "spl-token-2022::onchain::invoke_transfer_checked"
        profile = next(row for row in self.manifest["models"] if row["model_id"] == model)["profiles"][1]
        dependencies = [{"package": row["package"], "version": row["releases"][0], "source": row["source"]}
                        for row in profile["dependencies"]]
        actual = {"package": "spl-token-2022", "version": "11.0.1", "source": REGISTRY,
                  "dependencies": dependencies}
        resolver = next(row for row in dependencies if row["package"] == "spl-tlv-account-resolution")
        for version, eligible in (("0.11.0", False), ("0.11.1", True), ("0.11.3", True),
                                  ("0.11.4", False), ("0.12.0", False)):
            with self.subTest(resolver=version):
                resolver["version"] = version
                answer = lookup(self.manifest, actual, [model])["models"][0]
                self.assertEqual(answer["status"], "eligible" if eligible else "unsupported")
        resolver["version"] = "0.11.1"
        interface = next(row for row in dependencies if row["package"] == "spl-token-2022-interface")
        interface["version"] = "3.1.0"
        self.assertEqual(lookup(self.manifest, actual, [model])["models"][0]["status"], "unsupported")
        observation = model + "_value"
        self.assertEqual(lookup(self.manifest, actual, [observation])["models"][0]["status"], "eligible")

    def test_pyth_borsh_resolution_uses_a_range_without_new_caller_obligations(self):
        model = "pyth-solana-receiver-sdk::price_update::PriceUpdateV2::deserialize_reader"
        profile = next(row for row in self.manifest["models"] if row["model_id"] == model)["profiles"][0]
        dependencies = [{"package": row["package"], "version": row["releases"][0], "source": row["source"]}
                        for row in profile["dependencies"]]
        actual = {"package": "pyth-solana-receiver-sdk", "version": "2.0.0", "source": REGISTRY,
                  "dependencies": dependencies}
        for version in ("1.6.1", "1.8.1"):
            for dependency in dependencies:
                if dependency["package"] in ("borsh", "borsh-derive"):
                    dependency["version"] = version
            answer = lookup(self.manifest, actual, [model])["models"][0]
            self.assertEqual(answer["status"], "eligible", version)
            self.assertEqual(answer["profiles"][0]["conditions"], profile["conditions"])
        git_source = {"kind": "git", "url": "https://example.invalid/source", "revision": "b" * 40}
        self.assertEqual(lookup(self.manifest, {**actual, "source": git_source}, [model])
                         ["models"][0]["status"], "unsupported")
        dependencies[:] = [row for row in dependencies if row["package"] != "borsh"]
        self.assertEqual(lookup(self.manifest, actual, [model])["models"][0]["status"], "unresolved")

    def test_borsh_behavior_variants_and_pre_one_boundary_stay_distinct(self):
        invalid_input = "borsh::u64::invalid_input::deserialize_reader"
        invalid_data = "borsh::u64::invalid_data::deserialize_reader"
        for version, eligible in (("0.10.99", invalid_input), ("1.8.1", invalid_data),
                                  ("0.11.1", None), ("2.0.0", None)):
            actual = {"package": "borsh", "version": version, "source": REGISTRY, "features": ["std"]}
            answers = lookup(self.manifest, actual, [invalid_input, invalid_data])["models"]
            self.assertEqual([row["model_id"] for row in answers if row["status"] == "eligible"],
                             [] if eligible is None else [eligible], version)

    def test_default_borsh_vector_reader_uses_the_actual_predecessor_name(self):
        model = "borsh::de::BorshDeserialize::vec_from_reader"
        for version, method in (("0.9.1", "vec_from_bytes"), ("0.9.2", "vec_from_bytes"),
                                ("0.9.3", "vec_from_bytes"), ("0.10.0", "vec_from_reader"),
                                ("0.10.4", "vec_from_reader"), ("1.8.1", "vec_from_reader")):
            with self.subTest(version=version):
                actual = {"package": "borsh", "version": version, "source": REGISTRY}
                answer = lookup(self.manifest, actual, [model])["models"][0]
                self.assertEqual(answer["status"], "eligible")
                self.assertEqual(len(answer["identities"]), 1)
                identity = answer["identities"][0]
                self.assertEqual(identity["item"], "borsh::de::BorshDeserialize::" + method)
                self.assertEqual(identity["implementation"], identity["item"])

    def test_operational_token_type_list_preserves_the_allocation_order_boundary(self):
        model = "spl-token-2022-interface::extension::BaseStateWithExtensions::get_extension_types_operational"
        group = next(group for group in compatibility_groups(self.document)
                     if group["id"] == "token-extension-type-list")
        admitted = {"3.1.0", "3.1.1", "3.1.2", "4.0.0"}
        self.assertTrue(admitted <= set(group["releases"]))
        self.assertEqual(set(group["versions"]), {"3.1.1"})
        for version in group["releases"]:
            with self.subTest(version=version):
                actual = {"package": "spl-token-2022-interface", "version": version, "source": REGISTRY}
                answer = lookup(self.manifest, actual, [model])["models"][0]
                self.assertEqual(answer["status"], "eligible" if version in admitted else "unsupported")


class InstalledLookupTests(unittest.TestCase):
    def test_lookup_runs_from_a_standalone_package_without_repository_scripts(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary) / "installed/packages/solanalib-specs"
            tools = package / "tools"
            tools.mkdir(parents=True)
            for name in ("applicability.py", "lookup_applicability.py"):
                shutil.copyfile(ROOT / "packages/solanalib-specs/tools" / name, tools / name)
            document = fixture()
            document["applicability"]["read"]["profiles"][0]["features"] = {
                "all": ["borsh"], "reason": "Enables this API."}
            document["applicability"]["read"]["profiles"][0]["items"][1]["compatible_ranges"] = [
                {"lower": "1.2.0", "upper": "2.0.0"}]
            (package / "applicability.json").write_text(json.dumps(normalized_applicability(document)))
            env = {**os.environ, "PYTHONPATH": "", "PYTHONDONTWRITEBYTECODE": "1"}
            for value, status, code in ((build(features=["borsh"]), "eligible", 0),
                                        (build("1.8.1", features=["borsh"]), "eligible", 0),
                                        (build("9.0.0", features=["borsh"]), "unsupported", 1),
                                        (build(), "unresolved", 3),
                                        (build(version="^1.0"), "invalid", 2),
                                        (build(source={**REGISTRY, "kind": []}), "invalid", 2),
                                        (build(source={**REGISTRY, "kind": {}}), "invalid", 2)):
                run = subprocess.run([sys.executable, str(tools / "lookup_applicability.py"),
                                      "--build", "-", "--model", "read"], input=json.dumps(value),
                                     text=True, capture_output=True, env=env, cwd=temporary)
                self.assertEqual(run.returncode, code, run.stdout + run.stderr)
                self.assertEqual(json.loads(run.stdout)["status"], status)


if __name__ == "__main__":
    unittest.main()
