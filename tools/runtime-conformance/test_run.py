"""Negative controls for evidence comparison, especially erased error states."""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import run


ACCOUNT = "1000000," + "00" * 32 + ",01,0,7"


class ComparisonControls(unittest.TestCase):
    def setUp(self):
        self.fixtures = {
            "serialized": {"kind": "serialization", "fields": []},
            "cpi_error": {"kind": "cpi", "fields": []},
        }
        self.model = [
            ["serialized", "serialization", "ok", ACCOUNT, "0", "ok", "0102", "0103", "-"],
            ["cpi_error", "cpi", "InvalidAccountData", "-", "-", "-", "00", "-", "-"],
        ]
        self.native = [
            self.model[0].copy(),
            ["cpi_error", "cpi", "InvalidAccountData", ACCOUNT, "2", "ok", "00", "01", "observed"],
        ]

    def compare(self):
        def render(rows):
            return "\n".join("\t".join(row) for row in rows) + "\n"
        return run.compare_outputs(render(self.model), render(self.native), self.fixtures)

    def test_error_partial_state_is_preserved_but_not_compared(self):
        result = self.compare()
        case = result["cases"][1]
        self.assertIsNone(case["model_accounts"])
        self.assertEqual(case["native_resize_delta"], 2)
        self.assertNotIn("accounts", case["compared_fields"])
        self.assertNotIn("serialized_after", case["compared_fields"])

    def test_success_byte_change_is_rejected(self):
        self.native[0][7] = "0104"
        with self.assertRaisesRegex(ValueError, "serialized_after"):
            self.compare()

    def test_success_account_change_is_rejected(self):
        self.native[0][3] = ACCOUNT.replace("1000000", "1000001")
        with self.assertRaisesRegex(ValueError, "accounts"):
            self.compare()

    def test_missing_account_data_is_rejected(self):
        self.model[0][3] = self.native[0][3] = ACCOUNT.replace(",01,", ",-,")
        with self.assertRaisesRegex(ValueError, "missing account data bytes"):
            self.compare()

    def test_empty_account_data_is_represented(self):
        self.model[0][3] = self.native[0][3] = ACCOUNT.replace(",01,", ",,")
        case = self.compare()["cases"][0]
        self.assertEqual(case["model_accounts"][0]["data_hex"], "")
        self.assertEqual(case["native_accounts"][0]["data_hex"], "")

    def test_error_code_change_is_rejected(self):
        self.native[1][2] = "InvalidArgument"
        with self.assertRaisesRegex(ValueError, "outcome"):
            self.compare()

    def test_missing_success_state_is_rejected(self):
        self.model[0][3] = self.native[0][3] = "-"
        with self.assertRaisesRegex(ValueError, "missing successful model state"):
            self.compare()

    def test_invented_model_error_state_is_rejected(self):
        self.model[1][3] = ACCOUNT
        with self.assertRaisesRegex(ValueError, "unexpected model error state"):
            self.compare()

    def test_missing_case_is_rejected(self):
        self.native.pop()
        with self.assertRaisesRegex(ValueError, "case set"):
            self.compare()

    def test_duplicate_case_is_rejected(self):
        self.native.append(self.native[0])
        with self.assertRaisesRegex(ValueError, "duplicate native output"):
            self.compare()

    def test_wrong_case_kind_is_rejected(self):
        self.native[0][1] = "account"
        with self.assertRaisesRegex(ValueError, "wrong kind"):
            self.compare()

    def test_noncanonical_byte_encoding_is_rejected(self):
        self.model[0][7] = self.native[0][7] = "0A"
        with self.assertRaisesRegex(ValueError, "noncanonical hex"):
            self.compare()

    def test_missing_successful_serialization_buffers_are_rejected(self):
        self.model[0][6:8] = self.native[0][6:8] = ["-", "-"]
        with self.assertRaisesRegex(ValueError, "missing successful buffer"):
            self.compare()

    def test_empty_successful_serialization_buffers_are_rejected(self):
        self.model[0][6:8] = self.native[0][6:8] = ["", ""]
        with self.assertRaisesRegex(ValueError, "missing successful buffer"):
            self.compare()

    def test_missing_successful_cpi_auxiliary_is_rejected(self):
        self.fixtures["serialized"]["kind"] = "cpi"
        self.model[0][1] = self.native[0][1] = "cpi"
        with self.assertRaisesRegex(ValueError, "CPI auxiliary"):
            self.compare()

    def test_malformed_cpi_return_bytes_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "odd-length"):
            run.check_cpi_auxiliary(
                "info_len=1;return_program=" + "00" * 32 + ";return=0;cpi_count=1;stack=1")

    def test_unbounded_cpi_auxiliary_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unbounded"):
            run.check_cpi_auxiliary(
                f"info_len={2**64};return_program=" + "00" * 32 + ";return=;cpi_count=1;stack=1")

    def test_unrecognized_error_is_rejected(self):
        self.model[1][2] = self.native[1][2] = "UNRECOGNIZED_ERROR"
        with self.assertRaisesRegex(ValueError, "unrecognized outcome"):
            self.compare()

    def test_unrecognized_pop_outcome_is_rejected(self):
        self.model[0][5] = self.native[0][5] = "UNKNOWN_POP"
        with self.assertRaisesRegex(ValueError, "unrecognized outcome"):
            self.compare()


class AxiomControls(unittest.TestCase):
    def report(self, names):
        return f"'{run.AXIOM_THEOREM}' depends on axioms: [{names}]\n"

    def test_exact_allowed_axioms_and_empty_proof_are_accepted(self):
        self.assertEqual(run.checked_axioms(self.report("propext, Quot.sound")), ["Quot.sound", "propext"])
        self.assertEqual(run.checked_axioms(f"'{run.AXIOM_THEOREM}' does not depend on any axioms\n"), [])

    def test_custom_placeholder_native_decide_and_unapproved_classical_axioms_are_rejected(self):
        for name in ("Untrusted.claim", "sorryAx", "Lean.ofReduceBool", "Classical.choice",
                     f"{run.AXIOM_THEOREM}._native.native_decide.ax_1_1"):
            with self.subTest(axiom=name), self.assertRaisesRegex(ValueError, "unapproved proof axioms"):
                run.checked_axioms(self.report(f"propext, {name}, Quot.sound"))

    def test_missing_ambiguous_wrong_theorem_and_malformed_reports_are_rejected(self):
        valid = self.report("propext, Quot.sound")
        for report in ("", "no axioms", valid + valid, valid.replace(run.AXIOM_THEOREM, "Other.theorem"),
                       valid + "warning: unexpected diagnostic\n", self.report("propext,, Quot.sound"),
                       self.report("propext, propext"), valid.replace("]", "")):
            with self.subTest(report=report), self.assertRaises(ValueError):
                run.checked_axioms(report)


class NativeExpectations(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        # Synthetic input-integrity controls, not native execution evidence.
        for name, content in {
            "agave_cases.rs": "// synthetic native driver\n",
            "cpi_cases.rs": "// synthetic native CPI driver\n",
            "accounts.tsv": "control\tread_fields\t1\t1\t1\t7\t1,2\t0\t0\t0\t-\n",
            "serialization.tsv": "# no synthetic serialization case\n",
            "cpi.tsv": "# no synthetic CPI case\n",
        }.items():
            (self.root / name).write_text(content)
        self.record = {
            "schema_version": 1, "revision": run.REVISION,
            "source_archive_url": run.ARCHIVE_URL, "source_archive_sha256": run.ARCHIVE_SHA256,
            "rust": run.RUST, "target": run.TARGET,
            "native_inputs_sha256": {name: run.sha256(self.root / name) for name in run.NATIVE_INPUT_FILES},
        }
        self.native = "\t".join(["control", "account", "ok", ACCOUNT, "0", "ok", "-", "-", "-"]) + "\n"
        self.seal(self.native)

    def save(self):
        (self.root / "expected-native.json").write_text(json.dumps(self.record))

    def seal(self, text):
        data = text.encode()
        compressed = gzip.compress(data, mtime=0)
        (self.root / "expected-native.tsv.gz").write_bytes(compressed)
        self.record["native_output"] = {
            "file": "expected-native.tsv.gz", "gzip_sha256": hashlib.sha256(compressed).hexdigest(),
            "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data), "cases": 1,
        }
        self.save()

    def test_recorded_bytes_are_recovered_exactly(self):
        native, record = run.expected_native(self.root)
        self.assertEqual(native, self.native)
        self.assertEqual(record, self.record)

    def test_corrupt_gzip_or_uncompressed_digest_is_rejected(self):
        (self.root / "expected-native.tsv.gz").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "gzip digest differs"):
            run.expected_native(self.root)
        self.seal(self.native)
        self.record["native_output"]["sha256"] = "0" * 64
        self.save()
        with self.assertRaisesRegex(ValueError, "output digest differs"):
            run.expected_native(self.root)

    def test_missing_recorded_output_is_rejected(self):
        (self.root / "expected-native.tsv.gz").unlink()
        with self.assertRaisesRegex(ValueError, "missing regular native expected output"):
            run.expected_native(self.root)

    def test_missing_case_is_rejected_even_when_output_is_resealed(self):
        self.seal("")
        with self.assertRaisesRegex(ValueError, "case set differs"):
            run.expected_native(self.root)

    def test_wrong_native_pin_is_rejected(self):
        for field in ("revision", "source_archive_url", "source_archive_sha256", "rust", "target"):
            original = self.record[field]
            self.record[field] = "changed"
            self.save()
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "pin differs"):
                run.expected_native(self.root)
            self.record[field] = original

    def test_changed_native_fixture_or_missing_input_hash_is_rejected(self):
        (self.root / "cpi_cases.rs").write_text("// changed native driver\n")
        with self.assertRaisesRegex(ValueError, "native fixture differs"):
            run.expected_native(self.root)
        self.record["native_inputs_sha256"].pop("cpi_cases.rs")
        self.save()
        with self.assertRaisesRegex(ValueError, "inputs are incomplete"):
            run.expected_native(self.root)

    def test_unsealed_native_archive_is_rejected_before_extraction_or_compilation(self):
        archive = self.root / "unsealed.tar.gz"
        archive.write_bytes(b"not the pinned archive")
        arguments = argparse.Namespace(source_archive=archive, evidence_dir=self.root / "evidence", timeout=1)
        with patch.object(run, "pristine_source") as extraction, patch.object(run.Runner, "run") as compilation:
            with self.assertRaisesRegex(ValueError, "unexpected Agave archive digest"):
                run.replay(arguments)
        extraction.assert_not_called()
        compilation.assert_not_called()


class ReplayInputs(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.source = root / "original"
        self.source.mkdir()
        self.evidence = root / "evidence"
        for name in run.HARNESS_FILES:
            (self.source / name).parent.mkdir(parents=True, exist_ok=True)
            (self.source / name).write_bytes((run.ROOT / name).read_bytes())

    def test_fixture_edits_cannot_change_snapshot_used_by_both_drivers(self):
        fixtures = run.load_fixtures(self.source)
        snapshot, sealed = run.snapshot_harness(self.evidence, self.source)
        (self.source / "accounts.tsv").write_text("changed after parsing\n")
        (self.source / "agave_cases.rs").write_text("changed before compilation\n")
        self.assertEqual(run.load_fixtures(snapshot), fixtures)
        self.assertEqual(run.harness_inputs(snapshot), sealed)
        self.assertNotEqual(run.harness_inputs(self.source), sealed)

    def test_corrupt_retained_snapshot_cannot_be_reused(self):
        snapshot, _ = run.snapshot_harness(self.evidence, self.source)
        (snapshot / "cpi_cases.rs").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "snapshot differs"):
            run.snapshot_harness(self.evidence, self.source)

    def test_missing_harness_source_is_rejected(self):
        (self.source / "cpi_cases.rs").unlink()
        with self.assertRaisesRegex(ValueError, "missing regular harness input"):
            run.snapshot_harness(self.evidence, self.source)

    def test_unsealed_snapshot_file_is_rejected(self):
        snapshot, _ = run.snapshot_harness(self.evidence, self.source)
        (snapshot / "test_unsealed.py").write_text("raise RuntimeError('unsealed test ran')\n")
        with self.assertRaisesRegex(ValueError, "unsealed harness entries"):
            run.harness_inputs(snapshot)
        with self.assertRaisesRegex(ValueError, "unsealed harness entries"):
            run.snapshot_harness(self.evidence, self.source)

    def test_unsealed_snapshot_directory_is_rejected(self):
        snapshot, _ = run.snapshot_harness(self.evidence, self.source)
        cache = snapshot / "__pycache__"
        cache.mkdir()
        (cache / "run.pyc").write_bytes(b"unsealed cached bytecode")
        with self.assertRaisesRegex(ValueError, "unsealed harness entries"):
            run.harness_inputs(snapshot)
        with self.assertRaisesRegex(ValueError, "unsealed harness entries"):
            run.snapshot_harness(self.evidence, self.source)

    def test_target_environment_overrides_are_removed(self):
        flags = {"CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS": "-Ctarget-cpu=native",
                 "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER": "/unexpected/linker",
                 "CARGO_BUILD_RUSTFLAGS": "--cfg unexpected", "RUSTFLAGS": "--cfg unexpected"}
        with patch.dict(os.environ, flags):
            runner = run.Runner(self.evidence, 1)
        for key in flags:
            self.assertNotIn(key, runner.environment)


if __name__ == "__main__":
    unittest.main()
