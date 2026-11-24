"""Offline controls: manifest consistency, schema validation and pins. No Rust, no Lean."""

import copy
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import shutil
import sys
import tempfile
import threading
import tomllib
import unittest
from unittest import mock

import project_anchor_spl_support as anchor_spl_projector
import run


class ConcurrentRunnerEvidence(unittest.TestCase):
    def test_cli_accepts_positive_parallelism_above_four(self):
        with tempfile.TemporaryDirectory() as directory:
            command = ['run.py', '--model-only', '--control-jobs', '8',
                       '--evidence-dir', directory]
            with mock.patch.object(sys, 'argv', command), mock.patch.object(run, 'model_only') as replay:
                self.assertEqual(run.main(), 0)
            self.assertEqual(replay.call_args.args[0].control_jobs, 8)

    def test_cli_rejects_nonpositive_parallelism(self):
        for jobs in ('0', '-1'):
            with self.subTest(jobs=jobs), mock.patch.object(sys, 'argv',
                    ['run.py', '--model-only', '--control-jobs', jobs]), \
                    mock.patch.object(sys, 'stderr'), self.assertRaises(SystemExit) as error:
                run.main()
            self.assertEqual(error.exception.code, 2)

    def test_concurrent_subprocesses_keep_every_result_and_separate_output(self):
        with tempfile.TemporaryDirectory() as directory:
            evidence = Path(directory)
            runner = run.Runner(evidence, 10, control_jobs=4)
            barrier = threading.Barrier(4)

            def execute(number):
                barrier.wait(timeout=10)
                return runner.run(str(number), [sys.executable, '-c',
                    f'import sys; print("result-{number}"); sys.exit({number % 2})'], evidence, check=False)

            with ThreadPoolExecutor(max_workers=4) as pool:
                results = list(pool.map(execute, range(16)))
            records = json.loads((evidence / 'commands.json').read_text())
            self.assertEqual(len(records), 16)
            self.assertEqual({r['name'] for r in records}, {str(n) for n in range(16)})
            for number, (code, output) in enumerate(results):
                self.assertEqual(code, number % 2)
                self.assertEqual(output, f'result-{number}\n')
            for row in records:
                self.assertEqual(row['exit_code'], int(row['name']) % 2)
                self.assertEqual((evidence / row['stdout']).read_text(), f"result-{row['name']}\n")


class CommittedCorpus(unittest.TestCase):
    def test_corpus_matches_manifest_and_driver_inputs(self):
        auth = run.authenticate()
        drivers = run.discover_drivers()
        self.assertEqual(set(auth["summaries"]), {f"{c}.json" for d in drivers.values() for c in d["corpora"]})
        self.assertGreater(sum(s["records"] for s in auth["summaries"].values()), 1000)

    def test_registry_is_generated_from_the_family_modules(self):
        self.assertTrue(run.generate_registry(write=False), "run run.py --generate-registry")
        self.assertIn("Codecs", run.family_modules())

    def test_libraries_under_test_are_pinned_exactly(self):
        for driver in run.discover_drivers():
            pins = run.pinned_requirements(run.RUST / driver / "Cargo.toml")
            for name, requirement in pins.items():
                if name.startswith("conformance-"):
                    continue
                self.assertTrue(requirement.startswith("=") or requirement.startswith("git "),
                                f"{driver}: {name} = {requirement}")

    def test_pyth_drivers_use_reviewed_registry_releases(self):
        sources = run.source_map()["applicability_sources"]
        registry = "registry+https://github.com/rust-lang/crates.io-index"
        for driver in ("pyth", "instructions-3-4-0-bincode"):
            lockfile = run.RUST / driver / "Cargo.lock"
            lock = run.locked_packages(lockfile)
            for crate, version in (("pyth-solana-receiver-sdk", "2.0.0"), ("pythnet-sdk", "3.0.0")):
                with self.subTest(driver=driver, crate=crate):
                    self.assertEqual(lock[crate], [{"version": version, "source": registry,
                        "checksum": sources[crate]["releases"][version]["sha256"]}])
            package = tomllib.loads((lockfile.parent / "Cargo.toml").read_text())["package"]["name"]
            for crate, version in (("anchor-lang", "1.0.2"), ("anchor-derive-serde", "1.0.2"),
                                   ("anchor-attribute-account", "1.0.2"), ("borsh", "1.6.1")):
                with self.subTest(driver=driver, dependency=crate):
                    self.assertEqual(run.linked_version(lockfile, package, crate), version)

    def test_two_bytemuck_versions_live_in_separate_lockfiles(self):
        versions = {d: [p["version"] for p in run.locked_packages(run.RUST / d / "Cargo.lock").get("bytemuck", [])]
                    for d in ("codecs-borsh-0-10-4-bytemuck-1-25-2", "codecs-borsh-1-6-1-stake-3-1-0")}
        self.assertEqual(versions, {"codecs-borsh-0-10-4-bytemuck-1-25-2": ["1.25.2"], "codecs-borsh-1-6-1-stake-3-1-0": ["1.25.0"]})

    def test_drivers_build_with_the_declared_cfg_and_panic_strategy(self):
        drivers = run.discover_drivers()
        for driver in drivers:
            config = tomllib.loads((run.RUST / driver / ".cargo/config.toml").read_text())
            # The recorder passes --target explicitly; a config default is optional.
            self.assertEqual(config.get("build", {}).get("target", run.TARGET), run.TARGET)
            expected = [] if drivers[driver]["host"] else run.SOLANA_RUSTFLAGS
            self.assertEqual(config["target"][run.TARGET]["rustflags"], expected, driver)
            profiles = tomllib.loads((run.RUST / driver / "Cargo.toml").read_text())["profile"]
            probe = drivers[driver]["build_probe"]
            self.assertEqual(profiles["dev"]["panic"], probe["panic"] if probe else "unwind")


class Validation(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        source = json.loads((run.CORPUS / "bytemuck_1_25_2.json").read_text())
        self.data = copy.deepcopy(source)

    def write(self, data) -> Path:
        path = self.tmp / "bytemuck_1_25_2.json"
        path.write_text(json.dumps(data))
        return path

    def test_valid_file_passes(self):
        summary = run.validate_corpus(self.write(self.data))
        self.assertEqual(summary["records"], len(self.data["records"]))

    def test_duplicate_id_is_rejected(self):
        self.data["records"].append(copy.deepcopy(self.data["records"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate id"):
            run.validate_corpus(self.write(self.data))

    def test_unknown_exit_is_rejected(self):
        self.data["records"][0]["outcome"]["exit"] = "aborted"
        with self.assertRaisesRegex(ValueError, "unknown exit"):
            run.validate_corpus(self.write(self.data))

    def test_returned_without_result_is_rejected(self):
        del self.data["records"][0]["outcome"]["result"]
        with self.assertRaisesRegex(ValueError, "without result"):
            run.validate_corpus(self.write(self.data))

    def test_unknown_field_is_rejected(self):
        self.data["records"][0]["note"] = "x"
        with self.assertRaisesRegex(ValueError, "unexpected or missing fields"):
            run.validate_corpus(self.write(self.data))

    def test_wrong_schema_is_rejected(self):
        self.data["schema"] = "v0"
        with self.assertRaisesRegex(ValueError, "unknown schema"):
            run.validate_corpus(self.write(self.data))

    def test_corpus_name_must_match_file(self):
        self.data["corpus"] = "bytemuck_1_25_0"
        with self.assertRaisesRegex(ValueError, "differs from file name"):
            run.validate_corpus(self.write(self.data))


CODECS = {"borsh_0_10_4", "borsh_1_6_1", "bytemuck_1_25_0", "bytemuck_1_25_2", "solana_address_2_6_0",
          "solana_stake_interface_3_1_0", "pythnet_sdk_3_0_0", "pyth_solana_receiver_sdk_2_0_0"}


class Authentication(unittest.TestCase):
    """Manifest authentication controls using the corpora of the Codecs drivers."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        self.corpus = self.tmp / "corpus"
        shutil.copytree(run.CORPUS, self.corpus)

    def test_changed_corpus_byte_is_rejected(self):
        path = self.corpus / "borsh_1_6_1.json"
        text = path.read_text()
        path.write_text(text.replace('"ok":0', '"ok":1', 1))
        with self.assertRaisesRegex(ValueError, "hash differs"):
            run.authenticate(self.corpus, only=CODECS)

    def test_missing_corpus_file_is_rejected(self):
        (self.corpus / "pythnet_sdk_3_0_0.json").unlink()
        with self.assertRaisesRegex(ValueError, "missing corpus file"):
            run.authenticate(self.corpus, only=CODECS)

    def test_corpus_file_without_driver_is_rejected(self):
        shutil.copyfile(self.corpus / "pythnet_sdk_3_0_0.json", self.corpus / "orphan.json")
        with self.assertRaisesRegex(ValueError, "without a driver"):
            run.authenticate(self.corpus)

    def test_missing_driver_is_rejected(self):
        (self.corpus / "manifests" / "codecs-borsh-0-10-4-bytemuck-1-25-2.json").unlink()
        with self.assertRaisesRegex(ValueError, "driver set differs"):
            run.authenticate(self.corpus)

    def test_missing_driver_corpus_assignment_is_rejected(self):
        manifest = self.corpus / "manifests" / "codecs-borsh-0-10-4-bytemuck-1-25-2.json"
        data = json.loads(manifest.read_text())
        data["corpora"] = {}
        manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "corpus assignment differs"):
            run.authenticate(self.corpus, only=CODECS)

    def test_mismatched_driver_corpus_assignment_is_rejected(self):
        manifest = self.corpus / "manifests" / "codecs-borsh-0-10-4-bytemuck-1-25-2.json"
        data = json.loads(manifest.read_text())
        data["corpora"]["borsh_1_6_1.json"] = data["corpora"].pop("borsh_0_10_4.json")
        manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "corpus assignment differs"):
            run.authenticate(self.corpus, only=CODECS)

    def test_driver_without_manifest_is_rejected(self):
        (self.corpus / "manifests" / "pyth.json").unlink()
        with self.assertRaisesRegex(ValueError, "has no manifest"):
            run.authenticate(self.corpus, only=CODECS)

    def test_selected_corpus_checks_only_its_driver(self):
        (self.corpus / "manifests" / "pyth.json").unlink()
        auth = run.authenticate(self.corpus, only={"borsh_0_10_4"})
        self.assertEqual(set(auth["manifests"]), {"codecs-borsh-0-10-4-bytemuck-1-25-2"})

    def test_changed_driver_input_requires_rerecording(self):
        root = self.tmp / "tool"
        shutil.copytree(run.ROOT / "rust", root / "rust", ignore=shutil.ignore_patterns("target"))
        source = root / "rust/codecs-borsh-1-6-1-stake-3-1-0/src/stake.rs"
        source.write_text(source.read_text() + "\n// edited\n")
        with self.assertRaisesRegex(ValueError, "inputs changed"):
            run.authenticate(self.corpus, root, only=CODECS)

    def test_changed_toolchain_requires_rerecording(self):
        manifest = self.corpus / "manifests" / "codecs-borsh-1-6-1-stake-3-1-0.json"
        data = json.loads(manifest.read_text())
        data["rust"]["toolchain"] = "nightly-2000-01-01"
        manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "repository toolchain"):
            run.authenticate(self.corpus, only=CODECS)


class CountReports(unittest.TestCase):
    def test_reference_with_spaces_is_counted(self):
        counts = run.parse_counts(
            "example\n  ok   1/1  example::f []  -> Example.reference (Format.bincode)\n"
            "All 1 records admitted by the registered references.\n")
        self.assertEqual(counts["example"]["example::f []"]["reference"],
                         "Example.reference (Format.bincode)")
        run.check_counts(counts, {"example.json": {"records": 1}})

    def test_missing_reported_records_is_rejected(self):
        counts = run.parse_counts("example\n  ok   1/1  example::f []  -> Example.reference\n")
        with self.assertRaisesRegex(ValueError, "count report has 1 records, expected 2"):
            run.check_counts(counts, {"example.json": {"records": 2}})

    def test_missing_reported_corpus_is_rejected(self):
        counts = run.parse_counts("example\n  ok   1/1  example::f []  -> Example.reference\n")
        with self.assertRaisesRegex(ValueError, "count report corpora differ"):
            run.check_counts(counts, {"example.json": {"records": 1}, "other.json": {"records": 1}})


class ControlEvidence(unittest.TestCase):
    """Small corpus fixtures exercise retention without running Lean or native code."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        self.source, self.evidence = self.tmp / "corpus", self.tmp / "evidence"
        self.source.mkdir()
        self.evidence.mkdir()
        record = {"id": "r", "function": "f", "generics": {},
                  "outcome": {"exit": "returned", "result": 1, "state": None}}
        for name in ("example", "omitted"):
            (self.source / f"{name}.json").write_text(json.dumps({"records": [record]}))
        self.original = self.snapshot(self.source)
        self.runner = run.Runner(self.evidence, 1)
        self.seen = {}

    @staticmethod
    def snapshot(directory):
        return {p.name: p.read_bytes() for p in directory.iterdir() if p.is_file()}

    def restore(self, directory):
        for p in (self.evidence / "control-baseline").glob("*.json"):
            if not (directory / p.name).exists():
                shutil.copyfile(p, directory / p.name)

    def checker(self, reply):
        checker = mock.Mock(spec=run.Checker)
        checker.selection = None
        checker.records.side_effect = lambda _, records: records
        checker.mutate_selected.side_effect = lambda _, mutate: mutate
        def invoke(name, directory, only, **kwargs):
            self.seen[name] = self.snapshot(directory)
            self.assertEqual(set(self.seen[name]), set(self.original))
            self.assertTrue(all(p.is_file() and not p.is_symlink() for p in directory.iterdir()))
            self.assertEqual(self.snapshot(self.source), self.original)
            return reply(name)
        checker.run.side_effect = invoke
        return checker

    def structural(self, checker, family=()):
        with mock.patch.object(run, "KIND_CONTROLS", []), \
             mock.patch.object(run, "unobserved_kinds", return_value={"input"}), \
             mock.patch.object(run, "selected_fixed_controls", return_value=[]), \
             mock.patch.object(run, "_semantic_controls", return_value=[]), \
             mock.patch.object(run, "load_family_controls", return_value=list(family)):
            return run.run_controls(self.runner, checker, self.source, ["example"])

    def test_passed_controls_restore_exact_inputs_and_keep_logs(self):
        logs = {"commands.json": b"[]\n", "run-control-0.out": b"rejected\n",
                "omissions-control-0.json": b"[]\n"}
        for name, data in logs.items():
            (self.evidence / name).write_bytes(data)
        checker = self.checker(lambda _: (1, "no registered checker\nno records for"))
        results = self.structural(checker)
        self.assertEqual(len(results), 2)
        self.assertEqual(len(self.seen), 2)
        for name, full in self.seen.items():
            directory = self.evidence / name
            self.assertEqual(set(self.snapshot(directory)), {"example.json"})
            self.restore(directory)
            self.assertEqual(self.snapshot(directory), full)
        self.assertEqual(self.snapshot(self.evidence / "control-baseline"), self.original)
        self.assertEqual(self.snapshot(self.source), self.original)
        self.assertTrue(all((self.evidence / n).read_bytes() == b for n, b in logs.items()))

    def test_parallel_structural_controls_preserve_serial_results_and_input_bytes(self):
        reply = lambda _: (1, "no registered checker\nno records for")
        serial = self.structural(self.checker(reply))
        serial_inputs = dict(self.seen)
        shutil.rmtree(self.evidence)
        self.evidence.mkdir()
        self.runner = run.Runner(self.evidence, 1, control_jobs=4)
        self.seen = {}
        parallel = self.structural(self.checker(reply))
        self.assertEqual(parallel, serial)
        self.assertEqual(self.seen, serial_inputs)
        self.assertEqual(self.snapshot(self.source), self.original)

    def test_parallel_structural_failure_propagates_and_keeps_failed_inputs(self):
        self.runner.control_jobs = 4
        checker = self.checker(lambda name: (0, "unexpected pass") if name == 'control-0'
                               else (1, "no records for"))
        with self.assertRaisesRegex(ValueError, 'was not rejected'):
            self.structural(checker)
        self.assertEqual(self.snapshot(self.evidence / 'control-0'), self.seen['control-0'])
        self.assertEqual(self.snapshot(self.source), self.original)

    def test_same_size_mutation_extra_file_and_auxiliary_listing_survive(self):
        run._control_baseline(self.runner, self.source)
        directory = self.evidence / "control-example"
        directory.mkdir()
        run.copy_corpus(self.source, directory)
        original = (directory / "example.json").read_bytes()
        changed = original.replace(b'"result": 1', b'"result": 2')
        self.assertEqual(len(changed), len(original))
        self.assertNotEqual(changed, original)
        (directory / "example.json").write_bytes(changed)
        (directory / "unregistered_0_0_0.json").write_text("{}")
        (directory / "divergences-without.json").write_text("[]")
        full = self.snapshot(directory)
        run._compact_control(self.runner, directory)
        self.assertEqual(set(self.snapshot(directory)),
                         {"example.json", "unregistered_0_0_0.json", "divergences-without.json"})
        self.restore(directory)
        self.assertEqual(self.snapshot(directory), full)
        self.assertEqual(self.snapshot(self.source), self.original)

    def test_intentional_missing_corpus_is_not_compacted(self):
        run._control_baseline(self.runner, self.source)
        directory = self.evidence / "control-missing"
        directory.mkdir()
        run.copy_corpus(self.source, directory)
        (directory / "example.json").unlink()
        before = self.snapshot(directory)
        run._compact_control(self.runner, directory)
        self.assertEqual(self.snapshot(directory), before)
        self.assertEqual(self.snapshot(self.source), self.original)

    def test_unexpected_admission_exit_diagnostic_or_timeout_keeps_full_input(self):
        for code, output in ((0, "admitted"), (2, "parser error"),
                             (1, "wrong rejection"), (124, "timeout")):
            with self.subTest(code=code):
                self.evidence = self.tmp / f"failure-{code}"
                self.evidence.mkdir()
                self.runner = run.Runner(self.evidence, 1)
                checker = self.checker(lambda _: (code, output))
                with self.assertRaisesRegex(ValueError, "negative control"):
                    self.structural(checker)
                self.assertEqual(self.snapshot(self.evidence / "control-0"), self.seen["control-0"])
                self.assertEqual(checker.run.call_count, 1)
                self.assertEqual(self.snapshot(self.source), self.original)

    def test_failed_record_specific_assertion_keeps_family_input(self):
        def mutate(records):
            records[0]["outcome"]["result"] = 2
        mutate.record_id = "r"
        control = {"family": "Example", "label": "precondition", "corpus": "example",
                   "mutate": mutate, "expected": "outside precondition"}
        checker = self.checker(lambda name: (1, "FAIL example/other: outside precondition"
                               if name.startswith("control-family") else "no registered checker\nno records for"))
        with self.assertRaisesRegex(ValueError, "report of its record"):
            self.structural(checker, [control])
        self.assertEqual(self.snapshot(self.evidence / "control-family-0"), self.seen["control-family-0"])
        self.assertEqual(self.snapshot(self.source), self.original)

    def test_semantic_admission_keeps_full_input(self):
        run._control_baseline(self.runner, self.source)
        checker = self.checker(lambda _: (0, "admitted"))
        with mock.patch.object(run, "load_semantic_overrides", return_value=[]):
            with self.assertRaisesRegex(ValueError, "semantic controls"):
                run._semantic_controls(self.runner, checker, self.source, {"example"}, {})
        self.assertEqual(self.snapshot(self.evidence / "control-semantic-example"),
                         self.seen["control-semantic-example"])
        self.assertTrue(json.loads((self.evidence / "semantic-admitted.json").read_text()))

    def test_semantic_timeout_after_expected_messages_is_not_compacted(self):
        for code in (124, 1):
            with self.subTest(code=code):
                self.evidence = self.tmp / f"semantic-{code}"
                self.evidence.mkdir()
                self.runner = run.Runner(self.evidence, 1)
                run._control_baseline(self.runner, self.source)
                checker = self.checker(lambda _: (code, "MISMATCH example/r changed"))
                with mock.patch.object(run, "load_semantic_overrides", return_value=[]):
                    results = run._semantic_controls(self.runner, checker, self.source, {"example"}, {})
                self.assertEqual(results[0]["exit_code"], code)
                directory = self.evidence / "control-semantic-example"
                if code == 1:
                    self.assertNotIn("omitted.json", self.snapshot(directory))
                    self.restore(directory)
                self.assertEqual(self.snapshot(directory), self.seen["control-semantic-example"])

    def test_failed_spare_setup_keeps_full_input(self):
        run._control_baseline(self.runner, self.source)
        checker = self.checker(lambda _: (124, "FAIL example/r: timeout"))
        records = json.loads((self.source / "example.json").read_text())["records"]
        with mock.patch.object(run, "_later_spare_account", return_value=None), \
             mock.patch.object(run, "_spare_pair", return_value=0), \
             mock.patch.object(run, "_set_first_spare_both", side_effect=lambda r: r.update(setup=True)):
            result = run._spare_after_nonzero_control(self.runner, checker, self.source, "example", records, [])
        self.assertIsNone(result)
        self.assertEqual(self.snapshot(self.evidence / "control-spare-setup-example"),
                         self.seen["control-spare-setup-example"])

    def test_spare_pair_compacts_only_after_the_later_flip_is_rejected(self):
        records = json.loads((self.source / "example.json").read_text())["records"]
        region = {"input": {"count": 1, "accounts": [{"spare": "0000"}]}}
        records[0]["state"] = copy.deepcopy(region)
        records[0]["outcome"]["state"] = copy.deepcopy(region)
        (self.source / "example.json").write_text(json.dumps({"records": records}))
        self.original = self.snapshot(self.source)
        for setup_code, rejected in ((0, False), (0, True), (124, True)):
            with self.subTest(setup_code=setup_code, rejected=rejected):
                self.evidence = self.tmp / f"pair-{setup_code}-{rejected}"
                self.evidence.mkdir()
                self.runner = run.Runner(self.evidence, 1)
                run._control_baseline(self.runner, self.source)
                checker = self.checker(lambda name: (setup_code, "setup output") if "setup" in name
                                       else (1, "MISMATCH example/r changed") if rejected else (0, "admitted"))
                if rejected:
                    result = run._spare_after_nonzero_control(
                        self.runner, checker, self.source, "example", records, [])
                    self.assertEqual(result["synthetic"], 1)
                else:
                    with self.assertRaisesRegex(ValueError, "spare byte after"):
                        run._spare_after_nonzero_control(
                            self.runner, checker, self.source, "example", records, [])
                for name in ("control-spare-setup-example", "control-spare-later-example"):
                    directory = self.evidence / name
                    if rejected and ("later" in name or setup_code == 0):
                        self.assertNotIn("omitted.json", self.snapshot(directory))
                        self.restore(directory)
                    self.assertEqual(self.snapshot(directory), self.seen[name])
                self.assertEqual(self.snapshot(self.source), self.original)

    def test_checker_exception_keeps_complete_control_input(self):
        def interrupted(_):
            raise OSError("checker interrupted")
        checker = self.checker(interrupted)
        with self.assertRaisesRegex(OSError, "checker interrupted"):
            self.structural(checker)
        self.assertEqual(self.snapshot(self.evidence / "control-0"), self.seen["control-0"])
        self.assertEqual(self.snapshot(self.source), self.original)

    def test_repeated_evidence_use_fails_before_overwriting_saved_files(self):
        run._control_baseline(self.runner, self.source)
        (self.source / "omitted.json").unlink()
        (self.source / "new.json").write_text("{}")
        status = self.evidence / "run-status.json"
        status.write_text('{"status": "passed"}')
        before = self.snapshot(self.evidence / "control-baseline")
        with self.assertRaises(FileExistsError):
            run._control_baseline(self.runner, self.source)
        with mock.patch.object(run.sys, "argv", ["run.py", "--model-only", "--evidence-dir", str(self.evidence)]), \
             mock.patch.object(run.sys, "stderr"), mock.patch.object(run, "model_only") as model:
            with self.assertRaises(SystemExit) as raised:
                run.main()
        self.assertEqual(raised.exception.code, 2)
        model.assert_not_called()
        self.assertEqual(self.snapshot(self.evidence / "control-baseline"), before)
        self.assertEqual(status.read_text(), '{"status": "passed"}')


class Controls(unittest.TestCase):
    def test_every_negative_control_changes_its_corpus(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        for label, corpus_name, mutate, _ in run.CONTROLS:
            work = tmp / label.replace(" ", "_")
            work.mkdir()
            run.apply_control(run.CORPUS, work, corpus_name, mutate)
            before = json.loads((run.CORPUS / f"{corpus_name}.json").read_text())["records"]
            after = json.loads((work / f"{corpus_name}.json").read_text())["records"]
            self.assertNotEqual(before, after, label)

    def test_remaining_slice_control_mutates_an_error_record(self):
        records = json.loads((run.CORPUS / "borsh_1_6_1.json").read_text())["records"]
        mutated = copy.deepcopy(records)
        run._mutate_remaining(mutated)
        changed = [m for r, m in zip(records, mutated) if r != m]
        self.assertEqual(len(changed), 1)
        self.assertIn("err", changed[0]["outcome"]["result"])

    def test_runtime_kind_controls_mutate_their_records(self):
        records = [
            {"id": "a", "function": "f", "generics": {},
             "outcome": {"exit": "returned", "result": None,
                         "state": {"syscalls": {"replies": [], "log": [{"syscall": "sol_log_"}]},
                                   "region": {"accounts": [{"duplicate_of": 0}, {"lamports": 5}]}}}},
            {"id": "b", "function": "f", "generics": {},
             "outcome": {"exit": "terminated", "reason": "sol_panic_", "detail": None,
                         "syscalls": {"replies": [], "log": [{"syscall": "sol_log_"}, {"syscall": "x"}]}}},
            {"id": "c", "function": "g", "generics": {},
             "outcome": {"exit": "returned", "result": 1, "state": {"stubs": {"log": [{"call": "h"}]},
                                                                  "accounts": [{"lamports": 1}]}}},
        ]
        kinds = {}
        for kind, _, present, mutate in run.KIND_CONTROLS:
            kinds.setdefault(kind, (present, mutate))   # the first control of each kind
        # one target per function instantiation, divergences excluded
        self.assertEqual(run.kind_targets(records, kinds["syscalls"][0], []), ["a", "c"])
        self.assertEqual(run.kind_targets(records, kinds["syscalls"][0], ["a"]), ["b", "c"])
        self.assertEqual(run.kind_targets(records, kinds["input"][0], []), ["a", "c"])
        before = copy.deepcopy(records)
        kinds["syscalls"][1](records[1])
        self.assertEqual(records[1]["outcome"]["syscalls"]["log"], [{"syscall": "sol_log_"}])
        kinds["syscalls"][1](records[2])
        self.assertEqual(records[2]["outcome"]["state"]["stubs"]["log"], [])
        kinds["input"][1](records[0])
        self.assertEqual(records[0]["outcome"]["state"]["region"]["accounts"][1]["lamports"], 6)
        kinds["input"][1](records[2])
        self.assertEqual(records[2]["outcome"]["state"]["accounts"][0]["lamports"], 2)
        kinds["terminated"][1](records[1])
        self.assertEqual(records[1]["outcome"]["reason"], "abort")
        self.assertNotEqual(records, before)

    def test_spare_byte_controls_flip_the_deep_and_the_last_spare_byte(self):
        spare = run.compact_hex(bytes(10240 + 7))
        record = {"id": "a", "function": "f", "generics": {},
                  "outcome": {"exit": "returned", "result": None,
                              "state": {"region": {"accounts": [{"duplicate_of": 0},
                                                                {"lamports": 5, "data": "", "spare": "01",
                                                                 "spare_nonzero_at": 0},
                                                                {"lamports": 6, "data": "ab", "spare": spare,
                                                                 "spare_nonzero_at": None}]}}}}
        controls = {label: (present, mutate) for _, label, present, mutate in run.KIND_CONTROLS if "spare" in label}
        self.assertEqual(len(controls), 2)
        deep, last = (controls[label] for label in sorted(controls, key=lambda label: "last" in label))
        self.assertTrue(deep[0](record) and last[0](record))
        mutated = copy.deepcopy(record)
        deep[1](mutated)
        accounts = mutated["outcome"]["state"]["region"]["accounts"]
        self.assertEqual(accounts[1]["spare"], "01")   # too short for the deep byte
        self.assertEqual(run.expand_hex(accounts[2]["spare"])[run.DEEP_SPARE], 1)
        self.assertEqual(sum(run.expand_hex(accounts[2]["spare"])), 1)
        self.assertEqual(accounts[2]["spare_nonzero_at"], 1 + run.DEEP_SPARE)   # kept consistent
        mutated = copy.deepcopy(record)
        last[1](mutated)
        self.assertEqual(mutated["outcome"]["state"]["region"]["accounts"][1]["spare"], "00")
        self.assertIsNone(mutated["outcome"]["state"]["region"]["accounts"][1]["spare_nonzero_at"])
        self.assertFalse(deep[0]({**record, "outcome": {"exit": "terminated", "reason": "abort"}}))

    def test_spare_flip_after_an_earlier_nonzero_byte(self):
        def account(spare):
            return {"lamports": 1, "data": "ab", "spare": run.compact_hex(spare),
                    "spare_nonzero_at": run._spare_summary({"data": "ab"}, spare)}
        record = {"id": "a", "function": "f", "generics": {},
                  "state": {"region": {"count": 1, "accounts": [account(bytes(8))]}},
                  "outcome": {"exit": "returned", "result": None,
                              "state": {"region": {"count": 1, "accounts": [account(bytes(8))]}}}}
        self.assertIsNone(run._later_spare_account(record))
        self.assertEqual(run._spare_pair(record), 0)
        run._set_first_spare_both(record)
        after = record["outcome"]["state"]["region"]["accounts"][0]
        self.assertEqual(record["state"]["region"]["accounts"][0], after)   # the setup is consistent
        self.assertEqual(after["spare_nonzero_at"], 1)
        self.assertIs(run._later_spare_account(record), after)
        run._flip_last_spare(after)
        self.assertEqual(run.expand_hex(after["spare"]), b"\x01" + bytes(6) + b"\x01")
        self.assertEqual(after["spare_nonzero_at"], 1)   # the summary does not change

    def test_semantic_mutation_is_type_preserving(self):
        self.assertEqual(run._perturb({"ok": 5}), {"ok": 4})
        self.assertEqual(run._perturb({"ok": 0}), {"ok": 1})
        self.assertEqual(run._perturb([True, 1]), [False, 1])
        self.assertEqual(run._perturb({"b": "0102", "a": None}), {"b": "0002", "a": None})
        self.assertEqual(run._perturb(run.compact_hex(bytes(70))), "01" + run.compact_hex(bytes(69)))
        self.assertIsNone(run._perturb({"err": "Busy"}))   # no other recorded text
        self.assertEqual(run._perturb({"err": "Busy"}, [{("err",): {"Busy", "Idle"}}]), {"err": "Idle"})
        enum = {"err": {"variant": "A", "fields": []}}
        records = [{"outcome": {"exit": "returned", "result": {"err": {"variant": "Custom", "fields": [48]}}}}]
        self.assertEqual(run._perturb(enum, [run.text_alternatives(records)]),
                         {"err": {"variant": "Custom", "fields": [48]}})
        r = {"id": "x", "outcome": {"exit": "returned", "result": None, "state": {"s": 1}}}
        self.assertEqual(run.semantic_mutation(r), "returned -> unwound")
        self.assertEqual(r["outcome"]["exit"], "unwound")
        t = {"id": "y", "outcome": {"exit": "terminated", "reason": "abort"}}
        run.semantic_mutation(t)
        self.assertEqual(t["outcome"]["reason"], "sol_panic_")

    def test_semantic_plan_takes_the_first_record_or_the_override(self):
        records = [{"id": i, "function": f, "generics": {}, "outcome": {"exit": "returned", "result": 1}}
                   for i, f in (("a1", "f"), ("a2", "f"), ("b1", "g"))]
        plan = run.semantic_plan(records, [], [])
        self.assertEqual([(s["record"], s["override"]) for s in plan], [("a1", None), ("b1", None)])
        override = {"family": "F", "corpus": "c", "record": "a2", "mutate": lambda rs: None, "reason": "r"}
        self.assertEqual([s["record"] for s in run.semantic_plan(records, [], [override])], ["a2", "b1"])
        self.assertEqual([s["record"] for s in run.semantic_plan(records, ["a1"], [])], ["a2", "b1"])
        with self.assertRaisesRegex(ValueError, "no record zz"):
            run.semantic_plan(records, [], [{**override, "record": "zz"}])

    def test_exported_requires_keeps_contract_and_unknown_names_exact(self):
        def output(projection="Solanalib.Contracts.Model.requires", contract="a.f_contract", declared="a.f_run"):
            return PinsAndDeclarations.report(
                ("DECIDES", "F", "c", "a::A::f []", "a::A::f", declared, "true", "true"),
                ("PRECONDITION", "F", "c", "a::A::f []", declared),
                ("REACHES", "F", "c", "a::A::f []", declared),
                ("REACHES", "F", "c", "a::A::f []", projection),
                ("REACHES", "F", "c", "a::A::f []", contract),
                ("REQUIRES", "a.f_contract", "nontrivial", "fun s a => s.Valid"))

        report = run.checked_decides(output(), PinsAndDeclarations.MODELS)
        self.assertEqual(report["models"]["a@1::A::f"]["precondition_decided_by"], ["F c a::A::f []"])
        self.assertEqual(run.REQUIRES_PROJECTIONS, {"Solanalib.Contracts.Model.requires"})
        for projection in run.REQUIRES_PROJECTIONS:
            self.assertEqual(run.checked_decides(output(projection=projection), PinsAndDeclarations.MODELS), report)
        for projection in ("Solanalib.Contracts.Model.unknown.requires", "Solanalib.Contracts.Model.requiresChanged"):
            with self.subTest(projection=projection), self.assertRaisesRegex(ValueError, f"does not use {run.REQUIRES_FIELD}"):
                run.checked_decides(output(projection=projection), PinsAndDeclarations.MODELS)
        with self.assertRaisesRegex(ValueError, "does not use the registered contract a.f_contract"):
            run.checked_decides(output(contract="Solanalib.Contracts.Model.a.f_contract"), PinsAndDeclarations.MODELS)
        with self.assertRaisesRegex(ValueError, "Solanalib.Contracts.Model.a.f_run is not a registered"):
            run.checked_decides(output(declared="Solanalib.Contracts.Model.a.f_run"), PinsAndDeclarations.MODELS)

    def test_precondition_controls_and_theorems_exercise_decided_preconditions(self):
        f = ("DECIDES", "F", "c", "a::A::f []", "a::A::f")
        lines = (f + ("a.f_run", "true", "true"), ("REACHES", "F", "c", "a::A::f []", "a.f_run"),
                 ("PRECONDITION", "F", "c", "a::A::f []", "a.f_run"),
                 ("REACHES", "F", "c", "a::A::f []", run.REQUIRES_FIELD),
                 ("REACHES", "F", "c", "a::A::f []", "a.f_contract"),
                 ("CHECKER", "F", "c", "a::A::f []", "[]"),
                 ("REQUIRES", "a.f_contract", "nontrivial", "fun s a => s.Valid"))
        out = PinsAndDeclarations.report(*lines)
        index = {("c", "a::A::f", frozenset()): ["F: f outside"]}
        report = run.checked_decides(out, PinsAndDeclarations.MODELS, precondition_controls=index)
        self.assertEqual(report["models"]["a@1::A::f"]["precondition_exercised_by"]["controls"], ["F: f outside"])
        with self.assertRaisesRegex(ValueError, "a@1::A::f: its precondition is decided by F c a::A::f \\[\\], but no"):
            run.checked_decides(out, PinsAndDeclarations.MODELS, precondition_controls={})
        theorem = [{"model": "a@1::A::f", "theorem": "T.neg", "detail": "F", "reason": "r", "kind": "negative"}]
        bridge = ("BRIDGE\tF\tc\ta::A::f []\tSolanalibTest.Conformance.Library.Families.F.fDec\t"
                  f"{run.REQUIRES_FIELD},a.f_contract\n")
        def shaped(name, shape, head, target, uses="SolanalibTest.Conformance.Library.Families.F.fDec"):
            return (f"THEOREM\t{name}\ttrue\ttrue\t\nTHEOREMSHAPE\t{name}\t{shape}\t{head}\t{target}\t\t\n"
                    f"THEOREMUSES\t{name}\t{uses}\n")
        negative = shaped("T.neg", "not", run.REQUIRES_FIELD, f"{run.REQUIRES_FIELD},a.f_contract")
        report = run.checked_decides(out + bridge + negative, PinsAndDeclarations.MODELS, precondition_controls={},
                                     requires_theorems=theorem)
        self.assertEqual(report["models"]["a@1::A::f"]["precondition_exercised_by"]["theorems"], ["T.neg"])
        for projection in run.REQUIRES_PROJECTIONS:
            exported = (out + bridge + negative).replace(run.REQUIRES_FIELD, projection)
            exported_report = run.checked_decides(exported, PinsAndDeclarations.MODELS, precondition_controls={},
                                                 requires_theorems=theorem)
            self.assertEqual(exported_report["models"], report["models"])
        for text, listing, message in (
                (shaped("T.neg", "not", run.REQUIRES_FIELD, f"{run.REQUIRES_FIELD},a.f_contract", uses=""), theorem,
                 "does not use a decider of the precondition"),
                (shaped("T.neg", "positive", "True", "True"), theorem, "is not about the precondition"),
                (shaped("T.neg", "iff_true", run.REQUIRES_FIELD, f"{run.REQUIRES_FIELD},a.f_contract"), theorem,
                 "is listed as \\[\\[theorem\\]\\] \\(negative\\) for a@1::A::f but is trivial"),
                (negative.replace("\ttrue\ttrue\t", "\ttrue\tfalse\t"), theorem, "is not a theorem of the checked modules")):
            with self.assertRaisesRegex(ValueError, message):
                run.checked_decides(out + bridge + text, PinsAndDeclarations.MODELS, precondition_controls={},
                                    requires_theorems=listing)
        trivial = [{**theorem[0], "kind": "trivial"}]
        report = run.checked_decides(out + bridge + shaped("T.neg", "iff_true", run.REQUIRES_FIELD,
                                                           f"{run.REQUIRES_FIELD},a.f_contract"),
                                     PinsAndDeclarations.MODELS, precondition_controls={}, requires_theorems=trivial)
        self.assertEqual(report["models"]["a@1::A::f"]["precondition_exercised_by"]["trivial_at_index"], ["T.neg"])

    def test_precondition_theorem_keeps_generic_and_solana_core_predicates_distinct(self):
        theorem = "T.negative"
        where = "F c f []"
        decider = "SolanalibTest.Conformance.Library.Families.F.readyDec"
        models = {"model": {"contract": "a.contract"}}
        for predicate in ("Solanalib.Contracts.Model.Ready", "Solanalib.Specs.Core.Ready"):
            with self.subTest(predicate=predicate):
                audit = {"bridges": {}, "decidables": {where: [(decider, {predicate})]}, "reached": {}}
                data = {"theorems": {theorem: ("true", "true")},
                        "shapes": {theorem: ("not", predicate, {predicate}, set(), set())},
                        "uses": {theorem: {decider}}, "requires_uses": {"a.contract": {predicate}}}
                self.assertEqual(run.theorem_class(theorem, "model", [where], audit, data, models),
                                 ("negative", ""))
                # Using the right decider cannot make a theorem about another predicate count.
                wrong = "Solanalib.Specs.Core.Unrelated"
                data["shapes"][theorem] = ("not", wrong, {wrong}, set(), set())
                self.assertIsNone(run.theorem_class(theorem, "model", [where], audit, data, models)[0])

    def test_record_report_is_the_record_block(self):
        output = ("MISMATCH c/a (m; rejected by [m])\n  state: {}\n  model: \"outside the precondition\"\n"
                  "FAIL c/b: other\n  ok   1/1  f []  -> m\n")
        self.assertIn("outside the precondition", run.record_report(output, "c", "a"))
        self.assertNotIn("outside the precondition", run.record_report(output, "c", "b"))

    def test_toolchain_is_checked_against_the_pinned_nightly(self):
        lines = ["binary: rustc", "commit-hash: " + "f" * 40, "commit-date: 2026-04-30", "release: 1.97.0-nightly"]
        self.assertIsNone(run.toolchain_problem(lines, "nightly-2026-05-01"))
        self.assertIn("does not belong", run.toolchain_problem(lines, "nightly-2026-06-01"))
        self.assertIn("not a nightly", run.toolchain_problem(["release: 1.99.1", *lines[:3]], "nightly-2026-05-01"))
        self.assertIn("not a dated nightly", run.toolchain_problem(lines, "stable"))
        self.assertEqual(run.toolchain_overrides(), [])
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        (tmp / "rust" / "d").mkdir(parents=True)
        (tmp / "rust" / "d" / "rust-toolchain.toml").write_text('[toolchain]\nchannel = "stable"\n')
        self.assertEqual(run.toolchain_overrides(tmp), ["rust/d/rust-toolchain.toml"])

    def test_included_sources_must_be_hashed_inputs(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        d = tmp / "rust" / "d"
        (d / "src").mkdir(parents=True)
        (tmp / "rust" / "common").mkdir()
        (tmp / "rust" / "common" / "x.rs").write_text("")
        (d / "Cargo.toml").write_text('[package]\nname = "d"\n')
        (d / "src" / "main.rs").write_text('#[path = "../../common/x.rs"]\nmod x;\n')
        (d / "driver.toml").write_text('corpora = ["c"]\n')
        with self.assertRaisesRegex(ValueError, "includes ../../common/x.rs .* list it in the `inputs` of the driver"):
            run.driver_inputs("d", tmp)
        (d / "driver.toml").write_text('corpora = ["c"]\ninputs = ["rust/common/x.rs"]\n')
        self.assertIn("rust/common/x.rs", run.driver_inputs("d", tmp))

    def test_divergence_globs_leave_an_unlisted_control_id(self):
        self.assertIsNotNone(run.unlisted_control_id("f/a", ["f/*"]))
        self.assertIsNone(run.unlisted_control_id("f/a", ["*"]))

    def test_cross_function_and_theorem_listings_are_validated_and_their_tables_are_current(self):
        models = run.source_map()
        run.load_cross_function(models=models)
        run.load_requires_theorems(models=models)
        self.assertTrue(run.generate_cross_function_table(write=False), "run run.py --generate-registry")
        self.assertTrue(run.generate_requires_theorems_table(write=False), "run run.py --generate-registry")
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        (tmp / "x.toml").write_text('[[allow]]\nmodel = "a@1::A::f"\nfunction = "a::A::f"\ndetail = "F"\nreason = "r"\n')
        with self.assertRaisesRegex(ValueError, "already binds a::A::f"):
            run.load_cross_function(tmp / "x.toml", PinsAndDeclarations.MODELS)

    def test_axiom_report_rejects_unapproved_axioms(self):
        good = "AXIOMS theorem SolanalibTest.Conformance.Library.x_evaluated [propext]\n"
        self.assertEqual(run.checked_axioms(good)["theorems"], ["SolanalibTest.Conformance.Library.x_evaluated"])
        with self.assertRaisesRegex(ValueError, "unapproved"):
            run.checked_axioms(good + "AXIOMS definition SolanalibTest.Conformance.Library.y [sorryAx]\n")
        with self.assertRaisesRegex(ValueError, "missing axiom report"):
            run.checked_axioms("")


class Discovery(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        for name in ("a", "b"):
            (self.root / "rust" / name / "src").mkdir(parents=True)
            (self.root / "rust" / name / "Cargo.toml").write_text(f'[package]\nname = "{name}"\n')

    def driver(self, name: str, text: str) -> None:
        (self.root / "rust" / name / "driver.toml").write_text(text)

    def test_corpus_written_by_two_drivers_is_rejected(self):
        self.driver("a", 'corpora = ["x"]\n')
        self.driver("b", 'corpora = ["x"]\n')
        with self.assertRaisesRegex(ValueError, "written by both"):
            run.discover_drivers(self.root)

    def test_corpus_name_must_be_lower_snake_case(self):
        self.driver("a", 'corpora = ["Bad-Name"]\n')
        with self.assertRaisesRegex(ValueError, "must match"):
            run.discover_drivers(self.root)

    def test_unobserved_kinds_are_validated(self):
        self.driver("a", 'corpora = ["x"]\nunobserved = ["accounts"]\n')
        with self.assertRaisesRegex(ValueError, "record kinds"):
            run.discover_drivers(self.root)

    def test_directories_without_driver_toml_are_not_drivers(self):
        self.driver("a", 'corpora = ["x"]\n')
        self.assertEqual(list(run.discover_drivers(self.root)), ["a"])

    def test_family_corpora_must_be_in_the_family_namespace(self):
        families = self.root / "Families"
        families.mkdir()
        (families / "Good.lean").write_text("namespace SolanalibTest.Conformance.Library.Families.Good\ndef corpora := []\n")
        (families / "Helper.lean").write_text("namespace SolanalibTest.Conformance.Library.Families.Helper\ndef other := 1\n")
        self.assertEqual(run.family_modules(families), ["Good"])
        (families / "Bad.lean").write_text("namespace Elsewhere\ndef corpora := []\n")
        with self.assertRaisesRegex(ValueError, "must be in namespace"):
            run.family_modules(families)


class CountsAndDivergences(unittest.TestCase):
    OUTPUT = (
        "corpus_a\n"
        "  ok   3/3  f [T = u8]  -> m.f_run\n"
        "  ok   1/2 [1 known divergent]  g []  -> m.g_run (scripted, heap) + m.g_obs_run\n"
        "All 5 records admitted by the registered references, except 1 known divergences rejected as listed.\n"
    )

    def test_references_with_spaces_and_divergent_counts_are_parsed(self):
        counts = run.parse_counts(self.OUTPUT)
        self.assertEqual(counts["corpus_a"]["g []"],
                         {"admitted": 1, "total": 2, "divergent": 1, "reference": "m.g_run (scripted, heap) + m.g_obs_run"})
        self.assertEqual(counts["corpus_a"]["f [T = u8]"]["reference"], "m.f_run")

    def test_an_unparsable_count_line_fails_loudly(self):
        with self.assertRaisesRegex(ValueError, "unparsable count line"):
            run.parse_counts("corpus_a\n  ok   three/3  f  -> r\n")

    def test_divergent_records_count_towards_the_corpus_total(self):
        counts = run.parse_counts(self.OUTPUT)
        run.check_counts(counts, {"corpus_a.json": {"records": 5}})
        with self.assertRaisesRegex(ValueError, "count report has 5 records, expected 6"):
            run.check_counts(counts, {"corpus_a.json": {"records": 6}})

    def test_glob(self):
        self.assertTrue(run.glob_match("with_values/*/left_drop_panics", "with_values/a+b/left_drop_panics"))
        self.assertFalse(run.glob_match("with_values/*/left_drop_panics", "with_values/a/left_drop_panics#control"))
        self.assertTrue(run.glob_match("a.b*", "a.bc"))
        self.assertFalse(run.glob_match("a.b", "axb"))

    def test_divergence_listings_are_validated(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        (tmp / "c.toml").write_text('[[divergence]]\nrecords = "x/*"\nmodel = "m.run"\nreason = "why"\n')
        self.assertEqual(run.load_divergences(None, tmp),
                         [{"corpus": "c", "records": "x/*", "model": "m.run", "reason": "why"}])
        (tmp / "d.toml").write_text('[[divergence]]\nrecords = "x/*"\nmodel = "m.run"\n')
        with self.assertRaisesRegex(ValueError, "string `records`, `model`, `reason`"):
            run.load_divergences(None, tmp)

    def test_divergence_listings_name_existing_corpora_and_the_table_is_current(self):
        corpora = {c for d in run.discover_drivers().values() for c in d["corpora"]}
        for entry in run.load_divergences():
            self.assertIn(entry["corpus"], corpora)
        self.assertTrue(run.generate_divergence_table(write=False), "run run.py --generate-registry")


class AnchorSplProjection(unittest.TestCase):
    def test_profiles_match_retained_drivers(self):
        prefix = "anchor-spl-support-"
        expected = {name.removeprefix(prefix) for name in run.discover_drivers()
                    if name.startswith(prefix)}
        self.assertEqual(set(anchor_spl_projector.PROFILES), expected)

    def test_check_is_read_only_for_current_missing_and_stale_outputs(self):
        profile = "v0321-interface"
        relative = Path("rust") / ("anchor-spl-support-" + profile)
        files = [relative / "src/projected.rs", relative / "projection.json"]
        for state in ("current", "missing", "stale"):
            with self.subTest(state=state), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                for path in files:
                    (root / path).parent.mkdir(parents=True, exist_ok=True)
                    (root / path).write_bytes((run.ROOT / path).read_bytes())
                projected = root / files[0]
                if state == "missing":
                    projected.unlink()
                elif state == "stale":
                    projected.write_bytes(projected.read_bytes() + b"// drift\n")
                argv = ["project_anchor_spl_support.py", "--registry", str(root), "--check"]
                with mock.patch.object(anchor_spl_projector, "ROOT", root), \
                        mock.patch.dict(anchor_spl_projector.PROFILES,
                                        {profile: ("0.32.1", {})}, clear=True), \
                        mock.patch("sys.argv", argv), \
                        mock.patch.object(Path, "mkdir",
                                          side_effect=AssertionError("--check attempted mkdir")), \
                        mock.patch.object(Path, "write_bytes",
                                          side_effect=AssertionError("--check attempted a write")):
                    if state == "current":
                        anchor_spl_projector.main()
                    elif state == "missing":
                        with self.assertRaises(FileNotFoundError):
                            anchor_spl_projector.main()
                    else:
                        with self.assertRaisesRegex(AssertionError, "stale projection"):
                            anchor_spl_projector.main()


class FamilyControls(unittest.TestCase):
    def test_every_family_control_changes_its_corpus(self):
        controls = run.load_family_controls()
        self.assertTrue(controls)
        corpora = {}
        for control in controls:
            name = control["corpus"]
            if name not in corpora:
                path = run.CORPUS / f"{name}.json"
                self.assertTrue(path.exists(), f"{control['family']}: no corpus {name}")
                corpora[name] = json.loads(path.read_text())["records"]
            records = copy.deepcopy(corpora[name])
            control["mutate"](records)
            self.assertNotEqual(records, corpora[name], f"{control['family']}: {control['label']}")

    def test_control_files_are_validated(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        shutil.copyfile(run.CONTROLS_DIR / "common.py", tmp / "common.py")
        (tmp / "Bad.py").write_text("CONTROLS = [('label only',)]\n")
        with self.assertRaisesRegex(ValueError, "each control is"):
            run.load_family_controls(tmp)


class CompactHex(unittest.TestCase):
    def test_round_trip_and_canonical_form(self):
        data = b"\x01" + bytes(70) + b"\xff" + bytes(63) + b"\x02"
        text = run.compact_hex(data)
        self.assertEqual(text, "01[70]ff" + "00" * 63 + "02")
        self.assertEqual(run.expand_hex(text), data)
        self.assertEqual(run.compact_hex(bytes(10240)), "[10240]")

    def test_validation_rejects_uncompacted_and_noncanonical_runs(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        data = json.loads((run.CORPUS / "bytemuck_1_25_2.json").read_text())
        for bad, message in (("00" * 64, "not compacted"), ("[3]", "non-canonical"), ("[64]00", "non-canonical")):
            d = copy.deepcopy(data)
            d["records"][0]["args"]["note"] = bad
            path = tmp / "bytemuck_1_25_2.json"
            path.write_text(json.dumps(d))
            with self.assertRaisesRegex(ValueError, message):
                run.validate_corpus(path)


class PinsAndDeclarations(unittest.TestCase):
    def test_linked_version_prefers_the_direct_dependency(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        lock = tmp / "Cargo.lock"
        lock.write_text(
            'version = 4\n'
            '[[package]]\nname = "borsh"\nversion = "0.10.4"\nsource = "registry"\n'
            '[[package]]\nname = "borsh"\nversion = "1.6.1"\nsource = "registry"\n'
            '[[package]]\nname = "solo"\nversion = "2.0.0"\nsource = "registry"\n'
            '[[package]]\nname = "driver"\nversion = "0.1.0"\ndependencies = ["borsh 1.6.1"]\n')
        self.assertEqual(run.linked_version(lock, "driver", "borsh"), "1.6.1")
        self.assertEqual(run.linked_version(lock, "driver", "solo"), "2.0.0")
        self.assertIsNone(run.linked_version(lock, "other", "borsh"))

    def test_registry_pins_and_registered_names_are_read(self):
        pins = run.registry_pins()
        self.assertIn("1.6.1", pins["borsh"])
        names = run.registered_constants()
        self.assertIn("Solanalib.Specs.Borsh.u8.invalid_data.deserialize_reader_model", names)
        self.assertIn("Solanalib.Specs.Bytemuck.bytes_of_run", names)
        self.assertIn("Solanalib.Specs.SolanaAccountView.AccountView.Observation.reference", names)

    MODELS = {
        "a@1::A::f": {"names": {"a.f_contract", "a.f_run"}, "contract": "a.f_contract", "receiver": None,
                      "projection": None, "rust_names": {"a::A::f"}},
        "a@1::A::g": {"names": {"a.g_contract", "a.g_run"}, "contract": "a.g_contract", "receiver": None,
                      "projection": None, "rust_names": {"a::A::g"}},
        "a@1::Obs::f": {"names": {"a.f_obs_contract", "a.reference"}, "contract": "a.f_obs_contract",
                        "receiver": "a.reference", "projection": "a.Ops.f", "rust_names": set()},
        "a@1::Obs::g": {"names": {"a.g_obs_contract", "a.reference"}, "contract": "a.g_obs_contract",
                        "receiver": "a.reference", "projection": "a.Ops.g", "rust_names": set()},
    }

    @classmethod
    def report(cls, *lines):
        """Audit output; contracts the lines do not classify get a trivial `requires`."""
        classified = {line[1] for line in lines if line[0] == "REQUIRES"}
        lines += tuple(("REQUIRES", m["contract"], "trivial") for m in cls.MODELS.values()
                       if m["contract"] not in classified)
        return "".join("\t".join(line) + "\n" for line in lines)

    def test_declaration_report_is_checked_per_checker(self):
        f = ("DECIDES", "F", "c", "a::A::f []", "a::A::f")
        g = ("DECIDES", "F", "c", "a::A::g []", "a::A::g")
        good = self.report(f + ("a.f_run", "true", "true"), f + ("a.reference", "true", "true"),
                           ("REACHES", "F", "c", "a::A::f []", "a.f_run"),
                           ("REACHES", "F", "c", "a::A::f []", "a.Ops.f"),
                           g + ("a.g_run", "true", "true"), ("REACHES", "F", "c", "a::A::g []", "a.g_run"))
        allow = [{"model": "a@1::Obs::f", "function": "a::A::f", "detail": "F", "reason": "observation"}]
        report = run.checked_decides(good, self.MODELS, cross_function=allow)
        self.assertEqual(report["declared"], {"F": ["a.f_run", "a.g_run", "a.reference"]})
        with self.assertRaisesRegex(ValueError, "declares a@1::Obs::f, whose source-map rust_names \\(none\\) do not "
                                                "include a::A::f; list the pair in cross-function.toml"):
            run.checked_decides(good, self.MODELS)
        with self.assertRaisesRegex(ValueError, "cross-function.toml: no checker of a::A::g declares a@1::Obs::g"):
            run.checked_decides(good, self.MODELS, complete=True, cross_function=allow + [
                {"model": "a@1::Obs::g", "function": "a::A::g", "detail": "F", "reason": "r"}],
                not_tested=[{"id": "a@1::Obs::g", "reason": "r"}])
        self.assertEqual(sorted(report["models"]), ["a@1::A::f", "a@1::A::g", "a@1::Obs::f"])
        self.assertEqual(report["models"]["a@1::A::f"]["requires"], "trivial")
        for bad, message in (
                (self.report(f + ("-", "-", "-")), "declares no decided models"),
                (self.report(f + ("x.run", "true", "true")), "not a registered"),
                (self.report(f + ("a.f_run", "false", "false")), "does not exist"),
                # the checker of f declares g, which its own code does not use, and
                # uses the model of f without declaring it, while another checker of the family uses g
                (self.report(f + ("a.g_run", "true", "false"), ("REACHES", "F", "c", "a::A::f []", "a.f_run"),
                             g + ("a.g_run", "true", "true"), ("REACHES", "F", "c", "a::A::g []", "a.g_run")),
                 "a.g_run is not used by the decision code of this checker"),
                (self.report(f + ("a.g_run", "true", "true"), ("REACHES", "F", "c", "a::A::f []", "a.g_run"),
                             ("REACHES", "F", "c", "a::A::f []", "a.f_run")),
                 "uses a.f_run of the model a@1::A::f .*which it does not declare"),
                # a shared receiver decides an observation only with its projection
                (self.report(f + ("a.f_run", "true", "true"), f + ("a.reference", "true", "true"),
                             ("REACHES", "F", "c", "a::A::f []", "a.f_run")),
                 "a.reference is shared by .* identifies none of them")):
            with self.assertRaisesRegex(ValueError, message):
                run.checked_decides(bad, self.MODELS)

    def test_untested_models_must_be_exactly_the_listed_ones(self):
        f = ("DECIDES", "F", "c", "a::A::f []", "a::A::f")
        out = self.report(f + ("a.f_run", "true", "true"), ("REACHES", "F", "c", "a::A::f []", "a.f_run"))
        listed = [{"id": m, "reason": "r"} for m in ("a@1::A::g", "a@1::Obs::f", "a@1::Obs::g")]
        self.assertEqual(run.checked_decides(out, self.MODELS, listed, complete=True)["decided_models"], 1)
        with self.assertRaisesRegex(ValueError, "a@1::Obs::g is decided by no checker and not listed"):
            run.checked_decides(out, self.MODELS, listed[:2], complete=True)
        run.checked_decides(out, self.MODELS, listed[:2], complete=False)   # a selection of families
        with self.assertRaisesRegex(ValueError, "a@1::A::f is listed in not-tested.toml but decided by"):
            run.checked_decides(out, self.MODELS, listed + [{"id": "a@1::A::f", "reason": "r"}])

    def test_preconditions_are_decided_or_listed(self):
        f = ("DECIDES", "F", "c", "a::A::f []", "a::A::f")
        g = ("DECIDES", "F", "c", "a::A::g []", "a::A::g")
        base = (f + ("a.f_run", "true", "true"), ("REACHES", "F", "c", "a::A::f []", "a.f_run"),
                g + ("a.g_run", "true", "true"), ("REACHES", "F", "c", "a::A::g []", "a.g_run"),
                ("REQUIRES", "a.f_contract", "nontrivial", "fun s a => s.Valid"),
                ("REQUIRES", "a.g_contract", "trivial"))
        claim = (("PRECONDITION", "F", "c", "a::A::f []", "a.f_run"),
                 ("REACHES", "F", "c", "a::A::f []", run.REQUIRES_FIELD),
                 ("REACHES", "F", "c", "a::A::f []", "a.f_contract"))
        decided = run.checked_decides(self.report(*base, *claim), self.MODELS)
        self.assertEqual(decided["models"]["a@1::A::f"]["precondition_decided_by"], ["F c a::A::f []"])
        listed = [{"id": "a@1::A::f", "reason": "holds by the parser"}]
        report = run.checked_decides(self.report(*base), self.MODELS, requires_open=listed)
        self.assertEqual(report["requires_open"], ["a@1::A::f"])
        self.assertEqual(len(report["controls"]), 1)   # dropping the listing is rejected
        for lines, listing, message in (
                (base, None, "a@1::A::f has a non-trivial requires that F c a::A::f \\[\\] does not decide"),
                (base + claim, listed, "each of its checkers decides its precondition; remove the listing"),
                (base, listed + [{"id": "a@1::A::g", "reason": "r"}], "a@1::A::g is listed .* reduces to True"),
                (base + claim[:1], None, f"does not use {run.REQUIRES_FIELD}"),
                (base + claim[:2], None, "does not use the registered contract a.f_contract"),
                (base + (("PRECONDITION", "F", "c", "a::A::f []", "a.g_run"),), listed,
                 "decidesRequires names a.g_run, which it does not declare"),
                (base + (("PRECONDITION", "F", "c", "a::A::g []", "a.g_run"),), listed,
                 "it decides the precondition of a@1::A::g, but its decision code does not use")):
            with self.assertRaisesRegex(ValueError, message):
                run.checked_decides(self.report(*lines), self.MODELS, requires_open=listing)
        with self.assertRaisesRegex(ValueError, "a@1::Obs::f is listed in requires-open.toml but decided by no"):
            run.checked_decides(self.report(*base), self.MODELS, complete=True,
                                not_tested=[{"id": m, "reason": "r"} for m in ("a@1::Obs::f", "a@1::Obs::g")],
                                requires_open=listed + [{"id": "a@1::Obs::f", "reason": "r"}])

    def test_corpus_selection_keeps_selected_checker_and_precondition_obligations(self):
        # One family contains two corpora, both with non-trivial preconditions. A selective
        # run executes only the controls of the chosen corpus, so the other corpus must not demand one.
        rows = []
        for corpus, name in (("chosen", "f"), ("other", "g")):
            key = f"a::A::{name} []"
            rows.extend([
                ("DECIDES", "F", corpus, key, f"a::A::{name}", f"a.{name}_run", "true", "true"),
                ("REACHES", "F", corpus, key, f"a.{name}_run"),
                ("PRECONDITION", "F", corpus, key, f"a.{name}_run"),
                ("REACHES", "F", corpus, key, run.REQUIRES_FIELD),
                ("REACHES", "F", corpus, key, f"a.{name}_contract"),
                ("CHECKER", "F", corpus, key, "[]"),
                ("REQUIRES", f"a.{name}_contract", "nontrivial", "fun s a => s.Valid"),
            ])
        output = self.report(*rows)
        controls = {("chosen", "a::A::f", frozenset()): ["chosen control"]}
        with self.assertRaisesRegex(ValueError, "a@1::A::g:.*no family control"):
            run.checked_decides(output, self.MODELS, precondition_controls=controls)
        selected = run.checked_decides(output, self.MODELS, precondition_controls=controls, corpora={"chosen"})
        self.assertEqual(set(selected["models"]), {"a@1::A::f"})
        self.assertEqual(selected["models"]["a@1::A::f"]["precondition_exercised_by"]["controls"], ["chosen control"])
        with self.assertRaisesRegex(ValueError, "a@1::A::f:.*no family control"):
            run.checked_decides(output, self.MODELS, precondition_controls={}, corpora={"chosen"})
        omitted = [row for row in rows if not (row[0] == "PRECONDITION" and row[2] == "chosen")]
        with self.assertRaisesRegex(ValueError, "a@1::A::f has a non-trivial requires"):
            run.checked_decides(self.report(*omitted), self.MODELS,
                                precondition_controls=controls, corpora={"chosen"})
        wrong_model = output.replace("a.f_run\ttrue\ttrue", "a.unknown_run\ttrue\ttrue", 1)
        with self.assertRaisesRegex(ValueError, "a.unknown_run is not a registered"):
            run.checked_decides(wrong_model, self.MODELS, precondition_controls=controls, corpora={"chosen"})
        controls[("other", "a::A::g", frozenset())] = ["other control"]
        self.assertEqual(run.checked_decides(output, self.MODELS, precondition_controls=controls),
                         run.checked_decides(output, self.MODELS, precondition_controls=controls,
                                             corpora={"chosen", "other"}))

    def test_decides_control_must_be_rejected(self):
        control = ("DECIDES", "control:0", "audit", "a::A::f []", "a::A::f")
        f = ("DECIDES", "F", "c", "a::A::f []", "a::A::f")
        good = (f + ("a.f_run", "true", "true"), ("REACHES", "F", "c", "a::A::f []", "a.f_run"))
        saved = run.DECIDES_CONTROLS
        self.addCleanup(setattr, run, "DECIDES_CONTROLS", saved)
        run.DECIDES_CONTROLS = [{"family": "F", "label": "f declaring g", "corpora": "[]",
                                 "expected": ["a.g_run is not used by the decision code of this checker"]}]
        rejected = self.report(*good, control + ("a.g_run", "true", "false"))
        for corpora in (None, {"c"}):
            self.assertEqual(len(run.checked_decides(rejected, self.MODELS, corpora=corpora)["controls"]), 1)
            with self.assertRaisesRegex(ValueError, "decides control 'f declaring g' was not rejected"):
                run.checked_decides(self.report(*good, control + ("a.g_run", "true", "true")), self.MODELS,
                                    corpora=corpora)

    def test_not_tested_listing_is_validated_and_its_table_is_current(self):
        models = run.source_map()
        ids = [e["id"] for e in run.load_not_tested(models=models)]
        self.assertEqual(sorted(ids), ["shared-owned-array::construction"])
        self.assertTrue(run.generate_not_tested_table(write=False), "run run.py --generate-registry")
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        for text, message in (('[[model]]\nid = "nope"\nreason = "r"\n', "not a registered model"),
                              ('[[model]]\nid = "a@1::A::f"\n', "string `id`, `reason`"),
                              ('[[model]]\nid = "a@1::A::f"\nreason = "r"\n' * 2, "listed twice")):
            (tmp / "n.toml").write_text(text)
            with self.assertRaisesRegex(ValueError, message):
                run.load_not_tested(tmp / "n.toml", self.MODELS)

    def test_decides_audit_source_carries_the_review_control(self):
        source = run.decides_audit_source(["AccountsV2", "Codecs"])
        self.assertIn('decides := [SolanalibTest.Conformance.Library.Families.AccountsV2.pool "close_header"]', source)
        self.assertIn('("control:0", `DecidesControl.c0, DecidesControl.c0)', source)
        self.assertIn("decidesRequires := c.decides", source)
        self.assertNotIn("DecidesControl.c", run.decides_audit_source(["Address"]))

    def test_requires_open_listing_is_validated_and_its_table_is_current(self):
        models = run.source_map()
        for entry in run.load_requires_open(models=models):
            self.assertTrue(entry.get("detail"), f"{entry['id']}: name the deciding family in `detail`")
        self.assertTrue(run.generate_requires_open_table(write=False), "run run.py --generate-registry")

    def test_spare_writers_come_from_driver_toml(self):
        self.assertIn({"corpus": "solana_account_view_2_0_0", "function": "solana_account_view::AccountView::close"},
                      run.spare_writers())
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        (tmp / "rust" / "d").mkdir(parents=True)
        (tmp / "rust" / "d" / "driver.toml").write_text('corpora = ["c"]\nspare_writes = "f"\n')
        with self.assertRaisesRegex(ValueError, "`spare_writes` lists function globs"):
            run.discover_drivers(tmp)

    def test_divergence_pins_are_validated(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        (tmp / "c.toml").write_text('[[divergence]]\nrecords = "x"\nmodel = "m"\nreason = "r"\nexit = "crashed"\n')
        with self.assertRaisesRegex(ValueError, "`exit` is returned, unwound or terminated"):
            run.load_divergences(None, tmp)


if __name__ == "__main__":
    unittest.main()
