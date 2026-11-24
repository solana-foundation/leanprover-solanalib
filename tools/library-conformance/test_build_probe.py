"""Failure controls for executable configuration receipts, without Rust or Lean."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

import build_probe


class BuildProbe(unittest.TestCase):
    def setUp(self):
        self.spec = {"scope": "whole-signature-mock", "build_probe": {
            "argument": "--build-config", "profile": "dev", "panic": "abort"}}
        self.probe = build_probe.configuration(self.spec, Path("driver.toml"))
        self.observed = {"scope": "whole-signature-mock", "panic": "abort",
                         "debug_assertions": True, "solana_cfg": True, "pointer_width": 64,
                         "little_endian": True, "signature_check_enabled": False}
        self.manifest = {"rust": {"profile": "dev", "panic": "unwind"}}
        build_probe.attach(self.manifest, self.probe, self.observed)

    def test_matching_executable_configuration(self):
        build_probe.validate(self.probe, self.observed, False, "fixture")
        build_probe.authenticate(self.manifest, self.probe, False, "fixture")
        self.assertEqual(build_probe.profile_flags(self.probe), ["--profile", "dev"])

    def test_stderr_warning_does_not_corrupt_probe_json(self):
        import run
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            runner = run.Runner(root, 10)
            command = [sys.executable, "-c", "import sys; print(sys.argv[1]); "
                       "print('ordinary compiler warning', file=sys.stderr)", json.dumps(self.observed)]
            _, output = runner.run("probe", command, root, stdout_only=True)
            build_probe.validate(self.probe, json.loads(output), False, "fixture")
            self.assertEqual((root / "run-probe.log").read_text(), "ordinary compiler warning\n")
            _, legacy_output = runner.run("legacy", command, root)
            self.assertIn("ordinary compiler warning", legacy_output)

    def test_legacy_receipt_is_unchanged(self):
        manifest = {"rust": {"profile": "dev", "panic": "unwind"}, "inputs": {"sample": "sealed"}}
        original = copy.deepcopy(manifest)
        self.assertIsNone(build_probe.configuration({}, Path("driver.toml")))
        self.assertEqual(build_probe.profile_flags(None), [])
        build_probe.attach(manifest, None, None)
        build_probe.authenticate(manifest, None, False, "legacy")
        self.assertEqual(manifest, original)

    def test_scope_cannot_be_claimed_without_a_probe(self):
        with self.assertRaisesRegex(ValueError, "explicit scope requires"):
            build_probe.configuration({"scope": "whole-signature-mock"}, Path("driver.toml"))

    def test_compiled_panic_override_is_rejected(self):
        self.observed["panic"] = "unwind"
        with self.assertRaisesRegex(ValueError, "compiled panic strategy differs"):
            build_probe.validate(self.probe, self.observed, False, "workspace override")

    def test_changed_profile_claim_is_rejected(self):
        self.manifest["rust"]["profile"] = "release"
        with self.assertRaisesRegex(ValueError, "claimed profile differs"):
            build_probe.authenticate(self.manifest, self.probe, False, "fixture")

    def test_changed_profile_command_is_rejected(self):
        self.manifest["build_probe"]["profile_flags"] = ["--release"]
        with self.assertRaisesRegex(ValueError, "recorded profile command differs"):
            build_probe.authenticate(self.manifest, self.probe, False, "fixture")

    def test_changed_panic_claim_is_rejected(self):
        self.manifest["rust"]["panic"] = "unwind"
        with self.assertRaisesRegex(ValueError, "claimed panic strategy differs"):
            build_probe.authenticate(self.manifest, self.probe, False, "fixture")

    def test_changed_scope_claim_is_rejected(self):
        self.manifest["scope"] = "linked-source"
        with self.assertRaisesRegex(ValueError, "claimed mock/source scope differs"):
            build_probe.authenticate(self.manifest, self.probe, False, "fixture")

    def test_compiled_scope_mismatch_is_rejected(self):
        self.observed["scope"] = "linked-source"
        with self.assertRaisesRegex(ValueError, "compiled mock/source scope differs"):
            build_probe.validate(self.probe, self.observed, False, "fixture")

    def test_source_signature_feature_is_rejected_during_recording(self):
        self.observed["signature_check_enabled"] = True
        with self.assertRaisesRegex(ValueError, "compile-only signature checking was enabled"):
            build_probe.validate(self.probe, self.observed, False, "fixture")

    def test_host_cfg_override_is_rejected(self):
        self.observed["solana_cfg"] = False
        with self.assertRaisesRegex(ValueError, "compiled Solana cfg differs"):
            build_probe.validate(self.probe, self.observed, False, "fixture")


if __name__ == "__main__":
    unittest.main()
