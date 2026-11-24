"""Source receipts distinguish checked Git and Cargo identities from unchecked anchors."""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
SPEC = importlib.util.spec_from_file_location(
    "model_source_map", TOOLS / "runtime_source_map.py")
SOURCE_MAP = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE_MAP)


class SourceMapTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.agave = root / "agave"
        self.registry = root / "registry"
        self.manifest = root / "sources.json"
        self.body = "// immutable source\npub fn example() {}\n"
        self.rows = []
        for kind, repository, package, repo_path in (
            ("git", "https://github.com/anza-xyz/agave", "solana-svm-4.3.2", "svm/src/lib.rs"),
            ("cargo", "https://github.com/anza-xyz/solana-sdk", "solana-account-3.2.0", "account/src/lib.rs"),
        ):
            revision = "a" * 40
            row = {"id": kind, "source_kind": kind, "crate": package,
                   "path": "src/lib.rs", "repository": repository, "revision": revision,
                   "path_in_repository": repo_path, "line": 2,
                   "anchor_text": "pub fn example() {}",
                   "sha256": hashlib.sha256(self.body.encode()).hexdigest(),
                   "url": f"{repository}/blob/{revision}/{repo_path}#L2"}
            self.rows.append(row)
            source = (self.agave / repo_path if kind == "git"
                      else self.registry / package / row["path"])
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(self.body)
            if kind == "cargo":
                (self.registry / package / ".cargo_vcs_info.json").write_text(json.dumps(
                    {"git": {"sha1": revision}, "path_in_vcs": "account"}))
        self.write_manifest()

    def write_manifest(self):
        self.manifest.write_text(json.dumps({"entries": self.rows}))

    def test_no_local_copy_is_not_reported_as_checked(self):
        result = SOURCE_MAP.verify_source_map(self.manifest)
        self.assertEqual(result["checked_source_anchors"], 0)
        self.assertFalse(result["local_source_hashes_checked"])

    def test_each_source_set_is_checked_independently(self):
        for supplied in ({"registry": self.registry}, {"agave_source": self.agave}):
            with self.subTest(supplied=list(supplied)):
                result = SOURCE_MAP.verify_source_map(self.manifest, **supplied)
                self.assertEqual(result["checked_source_anchors"], 1)
                self.assertFalse(result["local_source_hashes_checked"])
        result = SOURCE_MAP.verify_source_map(
            self.manifest, registry=self.registry, agave_source=self.agave)
        self.assertEqual(result["checked_source_anchors"], 2)
        self.assertTrue(result["local_source_hashes_checked"])

    def test_changed_git_content_is_rejected(self):
        (self.agave / self.rows[0]["path_in_repository"]).write_text(self.body + "// changed\n")
        with self.assertRaisesRegex(ValueError, "Source content differs: git"):
            SOURCE_MAP.verify_source_map(self.manifest, agave_source=self.agave)

    def test_git_repository_entry_needs_no_cargo_version_suffix(self):
        self.rows[0]["crate"] = "agave"
        self.write_manifest()
        result = SOURCE_MAP.verify_source_map(
            self.manifest, registry=self.registry, agave_source=self.agave, require_sources=True)
        self.assertEqual(result["checked_source_anchors"], 2)

    def test_wrong_line_anchor_is_rejected_even_with_matching_hash(self):
        self.rows[0]["anchor_text"] = "pub fn different() {}"
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Source anchor differs: git"):
            SOURCE_MAP.verify_source_map(self.manifest, agave_source=self.agave)

    def test_cargo_revision_is_checked(self):
        package = self.registry / self.rows[1]["crate"]
        (package / ".cargo_vcs_info.json").write_text(json.dumps(
            {"git": {"sha1": "b" * 40}, "path_in_vcs": "account"}))
        with self.assertRaisesRegex(ValueError, "Cargo source revision differs: cargo"):
            SOURCE_MAP.verify_source_map(self.manifest, registry=self.registry)

    def test_url_must_use_the_declared_revision_and_anchor(self):
        self.rows[0]["url"] = self.rows[0]["url"].replace("#L2", "#L3")
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Source URL does not match"):
            SOURCE_MAP.verify_source_map(self.manifest)

    def test_complete_source_check_rejects_partial_or_missing_copies(self):
        for supplied in ({}, {"registry": self.registry}, {"agave_source": self.agave}):
            with self.subTest(supplied=list(supplied)):
                with self.assertRaisesRegex(ValueError, "Complete source verification required"):
                    SOURCE_MAP.verify_source_map(self.manifest, require_sources=True, **supplied)
        result = SOURCE_MAP.verify_source_map(
            self.manifest, registry=self.registry, agave_source=self.agave, require_sources=True)
        self.assertTrue(result["local_source_hashes_checked"])

    def test_duplicate_source_ids_are_rejected(self):
        self.rows.append(self.rows[0].copy())
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Duplicate source id"):
            SOURCE_MAP.verify_source_map(self.manifest)

    def test_package_source_fallback_must_keep_the_pinned_version(self):
        self.rows[1]["package_source_url"] = "https://docs.rs/crate/solana-account/latest/source/src/lib.rs"
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Package source URL differs"):
            SOURCE_MAP.verify_source_map(self.manifest)

    def test_one_source_file_cannot_have_conflicting_hashes(self):
        duplicate = {**self.rows[0], "id": "another-anchor", "sha256": "b" * 64}
        self.rows.append(duplicate)
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Conflicting source hashes"):
            SOURCE_MAP.verify_source_map(self.manifest)

    def archive_pin(self):
        row = self.rows[1]
        del row["revision"], row["path_in_repository"]
        row.update(archive_url="https://static.crates.io/crates/solana-account/solana-account-3.2.0.crate",
                   archive_sha256="a" * 64,
                   url="https://docs.rs/crate/solana-account/3.2.0/source/src/lib.rs#2")
        self.write_manifest()
        return row

    def test_archive_source_keeps_file_hash_and_line_checks(self):
        self.archive_pin()
        result = SOURCE_MAP.verify_source_map(self.manifest, registry=self.registry)
        self.assertEqual(result["checked_source_anchors"], 1)
        (self.registry / self.rows[1]["crate"] / "src/lib.rs").write_text(self.body + "// changed\n")
        with self.assertRaisesRegex(ValueError, "Source content differs"):
            SOURCE_MAP.verify_source_map(self.manifest, registry=self.registry)

    def test_archive_source_requires_an_exact_version_and_digest(self):
        row = self.archive_pin()
        for field, value in (("archive_sha256", "invalid"), ("archive_url", "https://example.com/source"),
                             ("revision", "b" * 40)):
            before = dict(row)
            row[field] = value
            self.write_manifest()
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "Invalid source archive pin"):
                SOURCE_MAP.verify_source_map(self.manifest)
            row.clear()
            row.update(before)


class CorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.manifest = Path(self.temporary.name) / "sources.json"
        self.sources = {"Solanalib/Runtime.lean": "public import Solanalib.Runtime.Example\n",
                        "Solanalib/Runtime/Example.lean": "def example := 0\n"}
        self.declarations = [{"name": "Solanalib.Runtime.example", "module": "Solanalib.Runtime.Example"}]
        self.row = {"id": "example", "modules": ["Solanalib.Runtime.Example"],
                    "model_sha256": {"Solanalib.Runtime.Example": hashlib.sha256(
                        self.sources["Solanalib/Runtime/Example.lean"].encode()).hexdigest()},
                    "source_ids": ["runtime"], "declarations": ["Solanalib.Runtime.example"],
                    "treatment": "source-read", "section": "example",
                    "argument": "The source returns zero.",
                    "assumptions": [], "limitations": ["No full implementation refinement."]}
        self.write_manifest()

    def write_manifest(self):
        self.manifest.write_text(json.dumps({"entries": [{"id": "runtime"}],
                                             "correspondence": [self.row]}))

    def verify(self):
        return SOURCE_MAP.verify_correspondence(self.manifest, self.sources, self.declarations)

    def test_matching_argument_records_checked_identity(self):
        result = self.verify()
        self.assertTrue(result["reviewed_model_hashes_checked"])
        self.assertEqual(result["modules"], 1)

    def test_changed_model_requires_a_new_reviewed_identity(self):
        self.sources["Solanalib/Runtime/Example.lean"] = "def example := 1\n"
        with self.assertRaisesRegex(ValueError, "Reviewed model content differs"):
            self.verify()

    def test_an_added_module_cannot_escape_the_source_argument(self):
        self.sources["Solanalib/Runtime/New.lean"] = "def another := 1\n"
        with self.assertRaisesRegex(ValueError, "Incomplete correspondence coverage"):
            self.verify()

    def test_removed_declaration_cannot_keep_a_stale_reference(self):
        self.declarations = [{"name": "Solanalib.Runtime.renamed", "module": "Solanalib.Runtime.Example"}]
        with self.assertRaisesRegex(ValueError, "Unknown or misplaced correspondence declaration"):
            self.verify()

    def test_source_reference_must_exist(self):
        self.row["source_ids"] = ["missing"]
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "Unknown correspondence source"):
            self.verify()


if __name__ == "__main__":
    unittest.main()
