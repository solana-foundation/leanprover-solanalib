"""Published archive transport preserves exact source identity and provenance."""

import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

import check_solana_specs as checker
import solana_source_archives as archives
from solana_source_map import load_source_map


CRATE = "example-sdk-1.0.0"
URL = "https://static.crates.io/crates/example-sdk/example-sdk-1.0.0.crate"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def packed(entries):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w") as archive:
        for name, data in entries:
            member = copy.copy(name) if isinstance(name, tarfile.TarInfo) else tarfile.TarInfo(name)
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
    return gzip.compress(buffer.getvalue(), mtime=0)


class SourceArchives(unittest.TestCase):
    def setUp(self):
        self.contents = [b"// reviewed\npub fn value() -> u8 { 7 }\n", b"// second source\n"]
        self.paths = ["src/lib.rs", "src/view.rs"]
        self.content = packed([(CRATE + "/" + path, content)
                               for path, content in zip(self.paths, self.contents)])
        self.pin = {"kind": "crates-io", "package": "example-sdk", "version": "1.0.0",
                    "sha256": digest(self.content)}
        self.interfaces = [
            {"id": f"source-{index}", "crate": CRATE, "path": path,
             "repository": "https://github.com/example/sdk", "revision": "a" * 40,
             "path_in_repository": "sdk/" + path, "sha256": digest(content),
             "source_archive": {**self.pin, "member": CRATE + "/" + path}}
            for index, (path, content) in enumerate(zip(self.paths, self.contents))]
        self.document = {"interfaces": self.interfaces, "api": [
            {"id": "value", "source_id": "source-0", "line": 2,
             "anchor_text": "pub fn value() -> u8 { 7 }"}]}

    def reseal(self, content):
        rows = copy.deepcopy(self.interfaces)
        for row in rows:
            row["source_archive"]["sha256"] = digest(content)
        return rows

    def reject_archive(self, content, pattern=None):
        with self.assertRaisesRegex(ValueError, pattern or "."):
            archives.archive_sources(content, self.reseal(content))

    def test_fetches_one_archive_and_checks_both_sources_and_anchor(self):
        document = copy.deepcopy(self.document)
        with tempfile.TemporaryDirectory() as temporary:
            registry = Path(temporary)
            with patch("check_solana_specs.urllib.request.urlopen", return_value=io.BytesIO(self.content)) as request:
                checker.fetch_sdk(document, registry)
            request.assert_called_once_with(URL, timeout=60)
            for path, contents in zip(self.paths, self.contents):
                self.assertEqual((registry / CRATE / path).read_bytes(), contents)
            self.assertEqual(checker.verify_sources(document, registry), (2, 1))
            self.assertEqual(document, self.document)

    def test_no_tar_extraction_api_is_called(self):
        with patch.object(tarfile.TarFile, "extractall", side_effect=AssertionError("extractall")), \
                patch.object(tarfile.TarFile, "extract", side_effect=AssertionError("extract")):
            self.assertEqual(archives.archive_sources(self.content, self.interfaces),
                             {"source-0": self.contents[0], "source-1": self.contents[1]})

    def test_wrong_archive_hash_fails_before_decompression(self):
        with patch.object(gzip, "GzipFile", side_effect=AssertionError("unverified gzip")) as decoder:
            with self.assertRaisesRegex(ValueError, "archive checksum"):
                archives.archive_sources(self.content + b"different", self.interfaces)
            decoder.assert_not_called()

    def test_wrong_file_hash_stages_no_member_of_the_archive(self):
        document = copy.deepcopy(self.document)
        document["interfaces"][1]["sha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as temporary:
            registry = Path(temporary)
            with patch("check_solana_specs.urllib.request.urlopen", return_value=io.BytesIO(self.content)):
                with self.assertRaisesRegex(ValueError, "Reviewed SDK source differs"):
                    checker.fetch_sdk(document, registry)
            self.assertEqual(list(registry.rglob("*")), [])

    def test_resealed_archive_cannot_change_reviewed_source_bytes(self):
        changed = packed([(CRATE + "/" + self.paths[0], self.contents[0].replace(b"7", b"8")),
                          (CRATE + "/" + self.paths[1], self.contents[1])])
        self.reject_archive(changed, "Reviewed SDK source differs")

    def test_missing_member_is_rejected(self):
        self.reject_archive(packed([(CRATE + "/" + self.paths[0], self.contents[0])]),
                            "Missing source archive members")

    def test_duplicate_member_is_rejected(self):
        content = packed([(CRATE + "/" + self.paths[0], self.contents[0]),
                          (CRATE + "/" + self.paths[0], self.contents[0]),
                          (CRATE + "/" + self.paths[1], self.contents[1])])
        self.reject_archive(content, "duplicate source archive path")

    def test_wrong_package_and_noncanonical_tar_paths_are_rejected(self):
        paths = ["different-sdk-1.0.0/src/lib.rs", "/" + CRATE + "/src/lib.rs",
                 CRATE + "/../lib.rs", CRATE + "/src/./lib.rs",
                 CRATE + "/src//lib.rs", CRATE + "/src\\lib.rs", CRATE + "/src/\nlib.rs"]
        for path in paths:
            with self.subTest(path=path):
                self.reject_archive(packed([(path, self.contents[0])]), "archive path")

    def test_links_special_and_sparse_members_are_rejected(self):
        for kind in [tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.CHRTYPE,
                     tarfile.BLKTYPE, tarfile.FIFOTYPE, tarfile.GNUTYPE_SPARSE]:
            for name in [CRATE + "/src/lib.rs", CRATE + "/unselected"]:
                with self.subTest(kind=kind, name=name):
                    member = tarfile.TarInfo(name)
                    member.type, member.linkname = kind, "../outside"
                    self.reject_archive(packed([(member, b"")]))

    def test_directories_are_allowed_but_selected_files_must_be_regular(self):
        directory = tarfile.TarInfo(CRATE)
        directory.type = tarfile.DIRTYPE
        content = packed([(directory, b""), *[(CRATE + "/" + path, content)
                          for path, content in zip(self.paths, self.contents)]])
        self.assertEqual(archives.archive_sources(content, self.reseal(content))["source-0"], self.contents[0])
        directory.name = CRATE + "/src/lib.rs"
        self.reject_archive(packed([(directory, b"")]), "not a regular file")

    def test_malformed_gzip_crc_and_truncation_are_rejected(self):
        for content in [b"not gzip", self.content[:-5],
                        self.content[:-8] + bytes([self.content[-8] ^ 1]) + self.content[-7:],
                        b"\x1f\x8b\x08\x00" + b"\x00" * 6 + b"\xff" * 20]:
            with self.subTest(content=content[:10]):
                self.reject_archive(content, "Malformed source archive gzip")

    def test_malformed_tar_header_and_missing_trailer_are_rejected(self):
        for data in [b"\0" * 512, b"x" * 512 + b"\0" * 1024,
                     gzip.decompress(self.content)[:1024]]:
            with self.subTest(size=len(data)):
                self.reject_archive(gzip.compress(data, mtime=0), "Malformed source archive tar")

    def test_truncated_member_is_rejected(self):
        member = tarfile.TarInfo(CRATE + "/src/lib.rs")
        member.size = 4096
        content = gzip.compress(member.tobuf() + b"x" * 512 + b"\0" * 1024, mtime=0)
        self.reject_archive(content, "Truncated source archive member")

    def test_nonzero_content_after_tar_end_is_rejected(self):
        data = gzip.decompress(self.content) + b"hidden".ljust(512, b"\0") + b"\0" * 1024
        self.reject_archive(gzip.compress(data, mtime=0), "nonzero tar trailer")

    def test_limits_bound_compressed_expanded_member_and_count_inputs(self):
        for constant, bound, pattern in [
                ("MAX_ARCHIVE_BYTES", len(self.content) - 1, "compressed byte limit"),
                ("MAX_TAR_BYTES", 512, "uncompressed byte limit"),
                ("MAX_MEMBER_BYTES", 4, "member byte limit"),
                ("MAX_MEMBERS", 1, "member limit")]:
            with self.subTest(constant=constant), patch.object(archives, constant, bound):
                self.reject_archive(self.content, pattern)

    def test_oversized_header_is_rejected_without_reading_its_declared_payload(self):
        member = tarfile.TarInfo(CRATE + "/src/lib.rs")
        member.size = archives.MAX_MEMBER_BYTES + 1
        self.reject_archive(gzip.compress(member.tobuf() + b"\0" * 1024, mtime=0), "member byte limit")

    def test_network_read_is_bounded(self):
        sizes = []

        class Response(io.BytesIO):
            def read(self, size=-1):
                sizes.append(size)
                return super().read(size)

        with patch("check_solana_specs.urllib.request.urlopen", return_value=Response(self.content)):
            with tempfile.TemporaryDirectory() as temporary:
                checker.fetch_sdk(self.document, Path(temporary))
        self.assertEqual(sizes, [archives.MAX_ARCHIVE_BYTES + 1])

    def test_http_failure_has_no_git_or_other_release_fallback(self):
        failure = HTTPError(URL, 404, "Not Found", {}, None)
        with patch("check_solana_specs.urllib.request.urlopen", side_effect=failure) as request:
            with tempfile.TemporaryDirectory() as temporary:
                with self.assertRaises(HTTPError):
                    checker.fetch_sdk(self.document, Path(temporary))
                self.assertEqual(list(Path(temporary).rglob("*")), [])
        request.assert_called_once_with(URL, timeout=60)

    def test_undeclared_source_keeps_exact_repository_route(self):
        legacy = copy.deepcopy(self.interfaces[0])
        del legacy["source_archive"]
        expected = "https://raw.githubusercontent.com/example/sdk/" + "a" * 40 + "/sdk/src/lib.rs"
        with patch("check_solana_specs.urllib.request.urlopen", return_value=io.BytesIO(self.contents[0])) as request:
            with tempfile.TemporaryDirectory() as temporary:
                checker.fetch_sdk({"interfaces": [legacy]}, Path(temporary))
                self.assertEqual((Path(temporary) / CRATE / "src/lib.rs").read_bytes(), self.contents[0])
        request.assert_called_once_with(expected, timeout=60)

    def test_declaration_rejects_unknown_kind_fields_and_mismatched_identity(self):
        for key, value in [("kind", "git"), ("package", "different-sdk"), ("version", "1.0.1"),
                           ("sha256", "0" * 63), ("sha256", 7), ("url", URL),
                           ("member", "other-1.0.0/src/lib.rs"), ("member", CRATE + "/src/view.rs")]:
            row = copy.deepcopy(self.interfaces[0])
            row["source_archive"][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                checker.source_interfaces({"interfaces": [row]})
        for value in [None, [], {}, {"kind": "crates-io"}]:
            row = copy.deepcopy(self.interfaces[0])
            row["source_archive"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                checker.source_interfaces({"interfaces": [row]})

    def test_source_path_cannot_be_relabelled_or_normalized(self):
        for path in ["", "../lib.rs", "/src/lib.rs", "src/./lib.rs", "src//lib.rs", "src\\lib.rs"]:
            row = copy.deepcopy(self.interfaces[0])
            row["path"] = path
            row["source_archive"]["member"] = CRATE + "/" + path
            with self.subTest(path=path), self.assertRaises(ValueError):
                checker.source_interfaces({"interfaces": [row]})

    def test_same_crate_must_use_one_declared_archive(self):
        for mixed in (False, True):
            rows = copy.deepcopy(self.interfaces)
            if mixed:
                del rows[1]["source_archive"]
            else:
                rows[1]["source_archive"]["sha256"] = "0" * 64
            with self.subTest(mixed=mixed), self.assertRaisesRegex(ValueError, "Inconsistent source archive"):
                checker.source_interfaces({"interfaces": rows})

    def test_archive_bytes_keep_crlf_without_a_conversion(self):
        content = packed([(CRATE + "/" + path, data.replace(b"\n", b"\r\n"))
                          for path, data in zip(self.paths, self.contents)])
        rows = self.reseal(content)
        for row, data in zip(rows, self.contents):
            row["sha256"] = digest(data.replace(b"\n", b"\r\n"))
        result = archives.archive_sources(content, rows)
        self.assertEqual(result["source-0"], self.contents[0].replace(b"\n", b"\r\n"))
        self.reject_archive(content, "Reviewed SDK source differs")

    def compact(self, package):
        (package / "source-map").mkdir()
        (package / "source-map.json").write_text(json.dumps({
            "schema_version": 3, "fragments": ["source-map/control.json"]}))
        fragment = {"packages": {CRATE: {
            "repository": "https://github.com/example/sdk", "revision": "a" * 40,
            "path_prefix": "sdk/", "source_archive": self.pin}},
            "interfaces": {row["id"]: {key: row[key] for key in ("crate", "path", "sha256")}
                           for row in self.interfaces}}
        (package / "source-map/control.json").write_text(json.dumps(fragment))
        return fragment

    def test_compact_pin_expands_exact_members_and_preserves_git_provenance(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary)
            fragment = self.compact(package)
            actual = load_source_map(package)
            self.assertEqual(actual["interfaces"], self.interfaces)
            del fragment["packages"][CRATE]["source_archive"]
            (package / "source-map/control.json").write_text(json.dumps(fragment))
            legacy = load_source_map(package)
            for row in actual["interfaces"]:
                del row["source_archive"]
            self.assertEqual(actual, legacy)

    def test_compact_interface_cannot_override_transport_or_member(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary)
            fragment = self.compact(package)
            fragment["interfaces"]["source-0"]["source_archive"] = self.interfaces[0]["source_archive"]
            (package / "source-map/control.json").write_text(json.dumps(fragment))
            with self.assertRaisesRegex(ValueError, "repeats its identity or crate pin"):
                load_source_map(package)

    def test_archive_pin_without_git_metadata_checks_the_same_source_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary)
            fragment = self.compact(package)
            for key in ("revision", "path_prefix"):
                del fragment["packages"][CRATE][key]
            (package / "source-map/control.json").write_text(json.dumps(fragment))
            document = load_source_map(package)
            rows = list(checker.source_interfaces(document).values())
            self.assertTrue(all("revision" not in row and "path_in_repository" not in row
                                for row in rows))
            self.assertEqual(archives.archive_sources(self.content, rows),
                             {row["id"]: content for row, content in zip(rows, self.contents)})
            rows[0]["sha256"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "Reviewed SDK source differs"):
                archives.archive_sources(self.content, rows)

    def test_archive_only_route_does_not_allow_incomplete_repository_pins(self):
        for field, value in (("revision", "a" * 40), ("path_in_repository", "src/lib.rs"),
                             ("repository_bytes", {"sha256": "a" * 64, "transform": "lf-to-crlf"})):
            row = {key: value for key, value in self.interfaces[0].items()
                   if key not in {"revision", "path_in_repository"}}
            row[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                checker.source_interfaces({"interfaces": [row]})

    def test_source_pin_requires_a_git_revision_or_an_archive_digest(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary)
            fragment = self.compact(package)
            for key in ("revision", "path_prefix", "source_archive"):
                del fragment["packages"][CRATE][key]
            (package / "source-map/control.json").write_text(json.dumps(fragment))
            with self.assertRaisesRegex(ValueError, "Invalid immutable crate pin"):
                load_source_map(package)

    def test_compact_pin_rejects_member_url_and_wrong_package(self):
        for key, value in [("member", CRATE + "/src/lib.rs"), ("url", URL), ("package", "other")]:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as temporary:
                package = Path(temporary)
                fragment = self.compact(package)
                fragment["packages"][CRATE]["source_archive"] = {**self.pin, key: value}
                (package / "source-map/control.json").write_text(json.dumps(fragment))
                with self.assertRaisesRegex(ValueError, "Invalid source archive declaration"):
                    load_source_map(package)

    def test_ci_triggers_and_runs_archive_controls(self):
        root = Path(__file__).resolve().parents[2]
        workflow = (root / ".github/workflows/ci.yml").read_text()
        triggers = workflow.split("jobs:", 1)[0]
        self.assertIn("  pull_request:", triggers)
        self.assertNotIn("paths:", triggers)
        self.assertNotIn("paths-ignore:", triggers)
        # This discovery pattern includes these archive-corruption controls.
        self.assertIn("-s tools/model-audit -p 'test_solana_*.py'", workflow)
        self.assertIn("check_solana_specs.py --fetch-sdk", workflow)


if __name__ == "__main__":
    unittest.main()
