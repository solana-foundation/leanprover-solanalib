"""Declared line-ending pairs never admit an unreviewed source-byte change."""

import copy
import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_solana_specs as checker
from solana_source_bytes import from_repository, check_published


class SourceBytes(unittest.TestCase):
    def setUp(self):
        self.git = b"// reviewed\npub fn value() -> u8 { 7 }\n"
        self.published = self.git.replace(b"\n", b"\r\n")
        self.interface = {
            "id": "source", "crate": "example-1.0.0", "path": "src/lib.rs",
            "repository": "https://github.com/example/sdk", "revision": "a" * 40,
            "path_in_repository": "src/lib.rs", "sha256": self.digest(self.published),
            "repository_bytes": {"sha256": self.digest(self.git), "transform": "lf-to-crlf"},
        }

    @staticmethod
    def digest(content):
        return hashlib.sha256(content).hexdigest()

    def test_exact_pair_is_verified_in_both_directions(self):
        self.assertEqual(from_repository(self.interface, self.git), self.published)
        self.assertIsNone(check_published(self.interface, self.published))

    def test_fetch_stages_the_exact_compiled_bytes_and_checks_anchors(self):
        document = {"interfaces": [self.interface], "api": [
            {"id": "value", "source_id": "source", "line": 2,
             "anchor_text": "pub fn value() -> u8 { 7 }"}]}
        with tempfile.TemporaryDirectory() as temporary:
            registry = Path(temporary)
            with patch("check_solana_specs.urllib.request.urlopen", return_value=io.BytesIO(self.git)):
                checker.fetch_sdk(document, registry)
            self.assertEqual((registry / "example-1.0.0/src/lib.rs").read_bytes(), self.published)
            self.assertEqual(checker.verify_sources(document, registry), (1, 1))

    def test_undeclared_conversion_is_rejected(self):
        row = copy.deepcopy(self.interface)
        del row["repository_bytes"]
        with self.assertRaises(ValueError):
            from_repository(row, self.git)

    def test_existing_byte_equal_sources_stay_byte_equal(self):
        row = copy.deepcopy(self.interface)
        del row["repository_bytes"]
        row["sha256"] = self.digest(self.git)
        self.assertEqual(from_repository(row, self.git), self.git)
        self.assertIsNone(check_published(row, self.git))

    def test_git_bytes_and_git_digest_are_both_sealed(self):
        with self.assertRaises(ValueError):
            from_repository(self.interface, self.git.replace(b"7", b"8"))
        row = copy.deepcopy(self.interface)
        row["repository_bytes"]["sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            from_repository(row, self.git)
        with self.assertRaises(ValueError):
            check_published(row, self.published)

    def test_published_bytes_and_published_digest_are_both_sealed(self):
        with self.assertRaises(ValueError):
            check_published(self.interface, self.published.replace(b"7", b"8"))
        row = copy.deepcopy(self.interface)
        row["sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            from_repository(row, self.git)

    def test_resealing_only_one_form_does_not_allow_a_code_change(self):
        row = copy.deepcopy(self.interface)
        changed = self.git.replace(b"7", b"8")
        row["repository_bytes"]["sha256"] = self.digest(changed)
        with self.assertRaises(ValueError):
            from_repository(row, changed)
        changed = self.published.replace(b"7", b"8")
        row = copy.deepcopy(self.interface)
        row["sha256"] = self.digest(changed)
        with self.assertRaises(ValueError):
            check_published(row, changed)

    def test_unknown_transform_and_extra_command_are_rejected(self):
        for declared in [{"sha256": self.digest(self.git), "transform": "normalize"},
                         {"sha256": self.digest(self.git), "transform": "lf-to-crlf", "command": "anything"},
                         None, {}, {"sha256": 7, "transform": "lf-to-crlf"}]:
            row = copy.deepcopy(self.interface)
            row["repository_bytes"] = declared
            with self.assertRaises(ValueError):
                checker.source_interfaces({"interfaces": [row]})

    def test_mixed_or_bare_carriage_returns_are_not_normalized(self):
        for content in [self.git, self.published.replace(b"\r\n", b"\n", 1),
                        self.published + b"\r"]:
            row = copy.deepcopy(self.interface)
            row["sha256"] = self.digest(content)
            with self.assertRaises(ValueError):
                check_published(row, content)
        row = copy.deepcopy(self.interface)
        row["repository_bytes"]["sha256"] = self.digest(self.published)
        with self.assertRaises(ValueError):
            from_repository(row, self.published)


if __name__ == "__main__":
    unittest.main()
