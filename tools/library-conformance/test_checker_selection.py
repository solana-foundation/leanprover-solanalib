"""Authenticated selection controls; optional actual Lean runner checks.

Set SOLANA_CONFORMANCE_SELECTION_LEAN=1 after the existing model-only recipe
builds the complete checker executable and family modules. These checks cover
synthetic harness fixtures and actual registry selection, not new Rust runs.
"""

import copy
from contextlib import ExitStack, redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch

import checker_selection as selection
import run


def record(rid, function="fixture::read", generics=None):
    return {"id": rid, "function": function, "generics": {"T": "u64"} if generics is None else generics,
            "state": None, "args": None, "outcome": {"exit": "returned", "result": 7, "state": None}}


class Selection(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.path = self.root / "selection_fixture.json"
        self.data = {"schema": run.SCHEMA, "corpus": "selection_fixture",
                     "crates": [{"name": "fixture", "version": "1.0.0"}],
                     "records": [record("read-0"), record("read-1"), record("write", "fixture::write"),
                                 record("other-type", generics={"T": "u8"})]}
        self.path.write_text(json.dumps(self.data))
        self.descriptors = [{"corpus": "selection_fixture", "function": "fixture::read",
                             "generics": {"T": "u64"}}]
        self.auth = self.authentication()
        # Synthetic exceptions are local to this fixture, never production policy.
        self.allowed_omissions = {
            ("write", "fixture::write", (("T", "u64"),)),
            ("other-type", "fixture::read", (("T", "u8"),)),
        }
        exceptions = patch.dict(selection.KNOWN_OMISSIONS,
                                {"selection_fixture": self.allowed_omissions}, clear=True)
        exceptions.start()
        self.addCleanup(exceptions.stop)

    def authentication(self):
        return {"manifests": {"fixture": {"corpora": {self.path.name: {
            "sha256": hashlib.sha256(self.path.read_bytes()).hexdigest(), "records": len(self.data["records"])}}}},
                "summaries": {self.path.name: run.validate_corpus(self.path)}}

    def prepare(self):
        return selection.prepare(self.root, self.auth, self.descriptors, {"selection_fixture"})

    def test_exact_keys_separate_another_function_and_another_instantiation(self):
        original = self.path.read_bytes()
        plan = self.prepare()
        self.assertEqual(plan["corpora"]["selection_fixture"]["selected_ids"], ["read-0", "read-1"])
        self.assertEqual(plan["corpora"]["selection_fixture"]["omitted_ids"], ["write", "other-type"])
        self.assertEqual(plan["selected_summaries"][self.path.name]["records"], 2)
        self.assertEqual(self.path.read_bytes(), original)

    def test_checker_removal_before_selection_is_rejected(self):
        self.data["records"].append(record("second", "fixture::second"))
        self.path.write_text(json.dumps(self.data))
        self.auth = self.authentication()
        self.descriptors.append({"corpus": "selection_fixture", "function": "fixture::second",
                                 "generics": {"T": "u64"}})
        self.prepare()
        self.descriptors.pop()
        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
            self.prepare()

    def test_new_authenticated_unknown_records_do_not_become_exceptions(self):
        for extra in [record("new-function", "fixture::unknown"),
                      record("new-instantiation", generics={"T": "u16"}),
                      record("another-write", "fixture::write")]:
            with self.subTest(record=extra):
                self.data["records"].append(extra)
                self.path.write_text(json.dumps(self.data))
                self.auth = self.authentication()
                with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                    self.prepare()
                self.data["records"].pop()

    def test_new_covered_record_is_checked(self):
        self.data["records"].append(record("read-2"))
        self.path.write_text(json.dumps(self.data))
        self.auth = self.authentication()
        self.assertEqual(self.prepare()["corpora"]["selection_fixture"]["selected_records"], 3)

    def test_reauthenticated_omission_identity_change_is_rejected(self):
        for changed in [record("write", "fixture::other"),
                        record("write", "fixture::write", {"T": "u8"})]:
            with self.subTest(record=changed):
                self.data["records"][2] = changed
                self.path.write_text(json.dumps(self.data))
                self.auth = self.authentication()
                with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                    self.prepare()

    def test_missing_expected_omission_is_rejected_after_authentication(self):
        self.data["records"].pop()
        self.path.write_text(json.dumps(self.data))
        self.auth = self.authentication()
        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
            self.prepare()

    def test_new_checker_requires_removing_its_stale_exception(self):
        self.descriptors.append({"corpus": "selection_fixture", "function": "fixture::write",
                                 "generics": {"T": "u64"}})
        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
            self.prepare()
        self.allowed_omissions.remove(("write", "fixture::write", (("T", "u64"),)))
        self.assertEqual(self.prepare()["corpora"]["selection_fixture"]["selected_records"], 3)

    def test_complete_corpus_has_no_implicit_exceptions(self):
        self.data["records"] = self.data["records"][:2]
        self.path.write_text(json.dumps(self.data))
        self.auth = self.authentication()
        with patch.dict(selection.KNOWN_OMISSIONS, {}, clear=True):
            self.assertEqual(self.prepare()["corpora"]["selection_fixture"]["omitted_records"], 0)
            self.data["records"].append(record("new-function", "fixture::unknown"))
            self.path.write_text(json.dumps(self.data))
            self.auth = self.authentication()
            with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                self.prepare()

    def test_duplicate_checker_key_after_generic_reordering_is_rejected(self):
        self.descriptors[0]["generics"] = {"A": "u64", "B": "u8"}
        self.descriptors.append({**self.descriptors[0], "generics": {"B": "u8", "A": "u64"}})
        with self.assertRaisesRegex(ValueError, "duplicate checker selection"):
            self.prepare()

    def test_selected_checker_without_records_is_rejected(self):
        self.descriptors[0]["generics"] = {"T": "u32"}
        with self.assertRaisesRegex(ValueError, "no records for selected checker"):
            self.prepare()

    def test_empty_selection_is_rejected(self):
        self.descriptors.clear()
        with self.assertRaisesRegex(ValueError, "no registered checker keys"):
            self.prepare()

    def test_full_authentication_is_required(self):
        self.auth["manifests"].clear()
        with self.assertRaisesRegex(ValueError, "missing complete corpus authentication"):
            self.prepare()

    def test_changed_omitted_outcome_still_fails_complete_hash_authentication(self):
        self.data["records"][2]["outcome"]["result"] = 99
        self.path.write_text(json.dumps(self.data))
        with self.assertRaisesRegex(ValueError, "changed after complete authentication"):
            self.prepare()

    def test_all_omitted_records_must_be_accounted_for(self):
        plan = self.prepare()
        selection.check_omissions("OMITTED\tselection_fixture\t2\n", plan)
        for report in ["", "OMITTED\tselection_fixture\t1\n", "OMITTED\tunknown\t2\n",
                       "OMITTED\tselection_fixture\t2\nOMITTED\tselection_fixture\t2\n"]:
            with self.subTest(report=report), self.assertRaises(ValueError):
                selection.check_omissions(report, plan)

    def test_report_parser_does_not_count_omissions_as_a_corpus(self):
        output = ("OMITTED\tselection_fixture\t2\nselection_fixture\n"
                  "  ok   2/2  fixture::read [T = u64]  -> synthetic selected checker\n"
                  "All 2 selected records admitted; 2 authenticated records omitted.\n")
        self.assertEqual(set(run.parse_counts(output)), {"selection_fixture"})


class NativeAuthentication(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("SOLANA_CONFORMANCE_SELECTION_LEAN") == "1", "explicit Lean test mode")
    def test_complete_registry_accounts_for_every_authenticated_corpus(self):
        """Use actual compiled keys; synthetic fixture descriptors do not establish prefix coverage."""
        auth = run.authenticate()
        with tempfile.TemporaryDirectory() as directory:
            runner = run.Runner(Path(directory), 60)
            checker = run.Checker(runner, None)
            code, output = checker.run("describe", run.CORPUS, None, describe=True, divergences=False)
            self.assertEqual(code, 0, output)
            listings = [line.removeprefix("CHECKERS\t") for line in output.splitlines()
                        if line.startswith("CHECKERS\t")]
            self.assertEqual(len(listings), 1, output)
            descriptors = json.loads(listings[0])
            names = {row["corpus"] for row in descriptors}
            plan = selection.prepare(run.CORPUS, auth, descriptors, names, complete=True)
            self.assertEqual(set(plan["corpora"]), {Path(name).stem for name in auth["summaries"]})
            selection.check_corpus_files(run.CORPUS, plan)
            for omitted in plan["omitted_corpora"]:
                with self.subTest(omitted=omitted):
                    without = dict(selection.KNOWN_OMISSIONS)
                    del without[omitted]
                    with patch.dict(selection.KNOWN_OMISSIONS, without, clear=True):
                        with self.assertRaisesRegex(ValueError, "wholly omitted corpus has no reviewed exception"):
                            selection.prepare(run.CORPUS, auth, descriptors, names, complete=True)

    def test_existing_native_input_authentication_precedes_selection(self):
        name = "utility_split222"
        auth = run.authenticate(only={name})
        path = run.CORPUS / (name + ".json")
        original = path.read_bytes()
        data = json.loads(original)
        descriptors = [{"corpus": name, "function": function, "generics": {}}
                       for function in ["solana_rent::Rent::is_exempt",
                                        "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get",
                                        "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get",
                                        "solana_sha256_hasher::hashv", "solana_sha256_hasher::hash",
                                        "solana_msg::sol_log"]]
        plan = selection.prepare(run.CORPUS, auth, descriptors, {name})
        self.assertEqual(plan["corpora"][name]["authenticated_records"], len(data["records"]))
        self.assertEqual(plan["corpora"][name]["omitted_records"], 0)
        self.assertEqual(path.read_bytes(), original)
        with tempfile.TemporaryDirectory() as directory:
            changed = Path(directory) / path.name
            selected = next(row for row in data["records"] if row["id"] == "clock/ok/zero")
            selected["outcome"]["reason"] = "changed selected native observation"
            changed.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "changed after complete authentication"):
                selection.prepare(Path(directory), auth, descriptors, {name})

    def test_split222_getters_require_checkers_and_no_stale_exceptions(self):
        name = "utility_split222"
        clock = "solana_sysvar::clock::<impl solana_sysvar::Sysvar for solana_clock::Clock>::get"
        rent = "solana_sysvar::rent::<impl solana_sysvar::Sysvar for solana_rent::Rent>::get"
        auth = run.authenticate(only={name})
        functions = ["solana_rent::Rent::is_exempt", clock, rent,
                     "solana_sha256_hasher::hashv", "solana_sha256_hasher::hash", "solana_msg::sol_log"]
        descriptors = [{"corpus": name, "function": function, "generics": {}} for function in functions]
        plan = selection.prepare(run.CORPUS, auth, descriptors, {name})
        self.assertEqual(plan["corpora"][name]["selected_records"], 196)
        self.assertEqual(plan["corpora"][name]["omitted_records"], 0)
        for getter in [clock, rent]:
            with self.subTest(getter=getter), self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                selection.prepare(run.CORPUS, auth, [d for d in descriptors if d["function"] != getter], {name})
        with patch.dict(selection.KNOWN_OMISSIONS, {name: frozenset({("clock/ok/zero", clock, ())})}):
            with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                selection.prepare(run.CORPUS, auth, descriptors, {name})

    def test_pinocchio_guard_drop_exceptions_preserve_function_and_generic_identity(self):
        name = "pinocchio_0_9_2_accounts"
        auth = run.authenticate(only={name})
        functions = [
            "pinocchio::account_info::AccountInfo::key",
            "pinocchio::account_info::AccountInfo::owner",
            "pinocchio::account_info::AccountInfo::is_signer",
            "pinocchio::account_info::AccountInfo::is_writable",
            "pinocchio::account_info::AccountInfo::is_owned_by",
            "pinocchio::account_info::AccountInfo::lamports",
            "pinocchio::account_info::AccountInfo::data_len",
            "pinocchio::account_info::AccountInfo::try_borrow_data",
            "pinocchio::account_info::AccountInfo::try_borrow_mut_data",
            "pinocchio::account_info::AccountInfo::try_borrow_mut_lamports",
            "pinocchio::account_info::AccountInfo::resize",
        ]
        generics = [
            "<pinocchio::account_info::Ref<'_, T> as core::ops::deref::Deref>::deref",
            "<pinocchio::account_info::RefMut<'_, T> as core::ops::deref::Deref>::deref",
            "<pinocchio::account_info::RefMut<'_, T> as core::ops::deref::DerefMut>::deref_mut",
            "pinocchio::account_info::RefMut::<'a, T>::map",
        ]
        descriptors = ([{"corpus": name, "function": function, "generics": {}} for function in functions]
                       + [{"corpus": name, "function": function, "generics": {"T": "[u8]"}} for function in generics])
        shared = "<pinocchio::account_info::Ref<'_, T> as core::ops::drop::Drop>::drop"
        exclusive = "<pinocchio::account_info::RefMut<'_, T> as core::ops::drop::Drop>::drop"
        expected = frozenset({("guard/drop_shared", shared, (("T", "[u8]"),)),
                              ("guard/drop_exclusive", exclusive, (("T", "[u8]"),))})
        self.assertEqual(selection.KNOWN_OMISSIONS[name], expected)
        plan = selection.prepare(run.CORPUS, auth, descriptors, {name})
        self.assertEqual(plan["corpora"][name]["selected_records"], 54)
        self.assertEqual(plan["corpora"][name]["omitted_records"], 2)
        wrong_generic = frozenset({("guard/drop_shared", shared, (("T", "u64"),)),
                                   ("guard/drop_exclusive", exclusive, (("T", "[u8]"),))})
        with patch.dict(selection.KNOWN_OMISSIONS, {name: wrong_generic}):
            with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                selection.prepare(run.CORPUS, auth, descriptors, {name})
        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
            selection.prepare(run.CORPUS, auth, descriptors[:-1], {name})

    def test_wincode_instruction_clone_stays_unselected_and_its_control_stays_absent(self):
        name = "instruction_extensions_wincode"
        auth = run.authenticate(only={name})
        functions = [
            "solana_instruction::account_meta::AccountMeta::new",
            "solana_instruction::account_meta::AccountMeta::new_readonly",
            "<solana_instruction::account_meta::AccountMeta as core::clone::Clone>::clone",
            "solana_system_interface::instruction::create_account_allow_prefund",
        ]
        descriptors = [{"corpus": name, "function": function, "generics": {}} for function in functions]
        clone = "<solana_instruction::Instruction as core::clone::Clone>::clone"
        expected = frozenset((rid, clone, ()) for rid in (
            "clone/empty", "clone/data-only", "clone/metas-only", "clone/duplicates", "clone/oom/1", "clone/oom/2"))
        self.assertEqual(selection.KNOWN_OMISSIONS[name], expected)
        plan = selection.prepare(run.CORPUS, auth, descriptors, {name})
        self.assertEqual(plan["corpora"][name]["selected_records"], 37)
        self.assertEqual(plan["corpora"][name]["omitted_records"], 6)
        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
            selection.prepare(run.CORPUS, auth,
                              [*descriptors, {"corpus": name, "function": clone, "generics": {}}], {name})
        controls = [c for c in run.load_family_controls() if c["corpus"] == name]
        self.assertFalse(any("instruction clone ordered duplicate flags" in c["label"]
                             for c in controls))
        self.assertTrue(any("prefund wincode amount and owner" in c["label"]
                            for c in controls))

    def test_optional_pubkey_whole_corpus_fixture_needs_each_explicit_identity(self):
        """An explicit policy fixture; the current registry selects this corpus."""
        name = "sdk_values_spl_pod_0_7_3"
        selected = "raw_runtime_pinocchio_0_9_2"
        auth = run.authenticate(only={name, selected})
        files = {name + ".json", selected + ".json"}
        # The source manifests are authenticated above; this selector fixture
        # retains exactly two already-authenticated files from those drivers.
        auth = {"manifests": {driver: {**manifest, "corpora": {
                    file: row for file, row in manifest["corpora"].items() if file in files}}
                    for driver, manifest in auth["manifests"].items()},
                "summaries": {file: row for file, row in auth["summaries"].items() if file in files}}
        descriptors = [{"corpus": selected, "function": "pinocchio::syscalls::sol_get_clock_sysvar", "generics": {}}]
        function = ("spl_pod::optional_keys::<impl core::convert::From<spl_pod::optional_keys::OptionalNonZeroPubkey> "
                    "for core::option::Option<solana_address::Address>>::from")
        ids = (
            "into_option/0", "into_option/1", "into_option/2", "into_option/3", "into_option/4", "into_option/5",
            "into_option/6", "into_option/7", "into_option/8", "into_option/9", "into_option/10", "into_option/11",
            "into_option/12", "into_option/13", "into_option/14", "into_option/15", "into_option/16", "into_option/17",
            "into_option/18", "into_option/19", "into_option/20", "into_option/21", "into_option/22", "into_option/23",
            "into_option/24", "into_option/25", "into_option/26", "into_option/27", "into_option/28", "into_option/29",
            "into_option/30", "into_option/31", "into_option/32", "into_option/33",
        )
        expected = frozenset((rid, function, ()) for rid in ids)
        self.assertNotIn(name, selection.KNOWN_OMISSIONS)
        with patch.dict(selection.KNOWN_OMISSIONS, {name: expected}, clear=True), tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for file in files:
                (root / file).write_bytes((run.CORPUS / file).read_bytes())
            plan = selection.prepare(root, auth, descriptors, {selected}, complete=True)
            self.assertEqual(plan["corpora"][name]["selected_records"], 0)
            self.assertEqual(plan["corpora"][name]["omitted_records"], 34)
            self.assertEqual(plan["omitted_corpora"], [name])
            selection.check_omissions("", plan)
            for wrong in [expected - {("into_option/0", function, ())},
                          expected | {("into_option/new", function, ())}]:
                with self.subTest(allowed=wrong), patch.dict(selection.KNOWN_OMISSIONS, {name: wrong}):
                    with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                        selection.prepare(root, auth, descriptors, {selected}, complete=True)
            with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                selection.prepare(root, auth,
                                  [*descriptors, {"corpus": name, "function": function, "generics": {}}],
                                  {selected, name}, complete=True)

    @unittest.skipUnless(os.environ.get("SOLANA_CONFORMANCE_SELECTION_LEAN") == "1", "explicit Lean test mode")
    def test_pod_and_unaligned_u16_have_checkers_without_stale_whole_corpus_exceptions(self):
        """The recorded releases now have actual compiled checkers for all 42 identities."""
        cases = [
            ("sdk_values_solana_zero_copy_1_0_1", "solana-zero-copy", "1.0.1",
             "solana_zero_copy::unaligned::<impl core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from",
             ("into_u16/0", "into_u16/1", "into_u16/2", "into_u16/3",
              "into_u16/4", "into_u16/5", "into_u16/6", "into_u16/7")),
            ("sdk_values_spl_pod_0_7_3", "spl-pod", "0.7.3",
             ("spl_pod::optional_keys::<impl core::convert::From<spl_pod::optional_keys::OptionalNonZeroPubkey> "
              "for core::option::Option<solana_address::Address>>::from"),
             ("into_option/0", "into_option/1", "into_option/2", "into_option/3", "into_option/4", "into_option/5",
              "into_option/6", "into_option/7", "into_option/8", "into_option/9", "into_option/10", "into_option/11",
              "into_option/12", "into_option/13", "into_option/14", "into_option/15", "into_option/16", "into_option/17",
              "into_option/18", "into_option/19", "into_option/20", "into_option/21", "into_option/22", "into_option/23",
              "into_option/24", "into_option/25", "into_option/26", "into_option/27", "into_option/28", "into_option/29",
              "into_option/30", "into_option/31", "into_option/32", "into_option/33")),
        ]
        names = {name for name, _, _, _, _ in cases}
        auth = run.authenticate(only=names)
        with tempfile.TemporaryDirectory() as directory:
            evidence = Path(directory)
            runner = run.Runner(evidence, 60)
            checker = run.Checker(runner, ["SdkValues"])
            code, output = checker.run("describe", run.CORPUS, sorted(names), describe=True, divergences=False)
            self.assertEqual(code, 0, output)
            listings = [line.removeprefix("CHECKERS\t") for line in output.splitlines()
                        if line.startswith("CHECKERS\t")]
            self.assertEqual(len(listings), 1, output)
            descriptors = json.loads(listings[0])
            self.assertEqual(sorted((row["corpus"], row["function"], tuple(sorted(row["generics"].items())))
                                    for row in descriptors),
                             sorted((name, function, ()) for name, _, _, function, _ in cases))
            plan = selection.prepare(run.CORPUS, auth, descriptors, names)
            for name, crate, version, function, ids in cases:
                with self.subTest(corpus=name):
                    data = json.loads((run.CORPUS / (name + ".json")).read_text())
                    self.assertEqual(data["crates"], [{"name": crate, "version": version}])
                    manifest = next(row for row in auth["manifests"].values()
                                    if name + ".json" in row["corpora"])
                    self.assertEqual([row['version'] for row in manifest['resolution']['modeled'][crate]], [version])
                    self.assertEqual(run.native_dependencies.selected_version(
                        run.RUST / manifest['driver'], manifest['resolution'], crate), version)
                    exact = frozenset((rid, function, ()) for rid in ids)
                    self.assertEqual(frozenset((row["id"], row["function"], tuple(sorted(row["generics"].items())))
                                               for row in data["records"]), exact)
                    self.assertNotIn(name, selection.KNOWN_OMISSIONS)
                    self.assertEqual(plan["corpora"][name]["selected_records"], len(ids))
                    self.assertEqual(plan["corpora"][name]["omitted_records"], 0)
                    with patch.dict(selection.KNOWN_OMISSIONS, {name: exact}):
                        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                            selection.prepare(run.CORPUS, auth, descriptors, names)
                    with self.assertRaisesRegex(ValueError, "no registered checker keys selected"):
                        selection.prepare(run.CORPUS, auth,
                                          [row for row in descriptors if row["corpus"] != name], names)
            checker.selection = plan
            checker.spare_writes = evidence / "spare-writes.json"
            checker.spare_writes.write_text(json.dumps(run.spare_writers()))
            code, output = checker.run("original", run.CORPUS, sorted(names))
            self.assertEqual(code, 0, output)
            selection.check_omissions(output, plan)

    def test_fixed_control_with_no_selected_target_is_reported(self):
        name = "borsh_1_6_1"
        data = json.loads((run.CORPUS / (name + ".json")).read_text())
        first = next(row for row in data["records"] if row["function"].endswith("::u8_slice"))
        descriptor = {"corpus": name, "function": first["function"], "generics": first["generics"]}
        checker = object.__new__(run.Checker)
        # Exercise the control filter itself with an explicit test selection.
        checker.selection = {"corpora": {name: {"selected_ids": [row["id"] for row in data["records"]
                             if (row["function"], row["generics"]) ==
                                (descriptor["function"], descriptor["generics"])]}}}
        checker.omitted_controls = []
        controls = run.selected_fixed_controls(checker, run.CORPUS, {name})
        self.assertNotIn("writer chunk", [row[0] for row in controls])
        omitted = next(row for row in checker.omitted_controls if row["label"] == "writer chunk")
        self.assertTrue(omitted["full_target_ids"])
        self.assertEqual(omitted["reason"], "target absent from selected records")
        checker.selection = None
        self.assertEqual(run.selected_fixed_controls(checker, run.CORPUS, {name}),
                         [row for row in run.CONTROLS if row[1] == name])

    def test_malformed_fixed_control_is_not_omitted(self):
        name = "bytemuck_1_25_2"
        data = json.loads((run.CORPUS / (name + ".json")).read_text())
        checker = object.__new__(run.Checker)
        checker.selection = {"corpora": {name: {"selected_ids": [data["records"][0]["id"]]}}}
        checker.omitted_controls = []
        def malformed(_):
            raise ValueError("malformed control")
        def no_full_target(rows):
            run._first(rows, lambda _: False)
        for mutate, error in [(malformed, "malformed control"), (no_full_target, "no record matches")]:
            with self.subTest(error=error), patch.object(run, "CONTROLS", [("bad", name, mutate, "MISMATCH")]):
                with self.assertRaisesRegex(ValueError, error):
                    run.selected_fixed_controls(checker, run.CORPUS, {name})
        self.assertEqual(checker.omitted_controls, [])


class WholeCorpusSelection(unittest.TestCase):
    """Real shared recordings with synthetic checker descriptors and one local exception.

Copy the complete existing driver, its inputs and all three recorded files; no
synthetic shortened manifest and no Rust or Lean subprocess is used here. The
companion Pod descriptors test dispatch, not current registered-model coverage;
the complete-registry test of NativeAuthentication checks that separate boundary.
"""

    selected = "sdk_values_solana_program_option_2_2_1"
    companion = "sdk_values_spl_pod_0_5_1"
    omitted = "sdk_values_solana_zero_copy_1_0_1"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.corpus = self.root / "corpus"
        manifests = self.corpus / "manifests"
        manifests.mkdir(parents=True)
        manifest = run.CORPUS / "manifests/sdk-values-v2.json"
        shutil.copyfile(manifest, manifests / manifest.name)
        for path in json.loads(manifest.read_text())["inputs"]:
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(run.ROOT / path, target)
        for name in (self.selected, self.companion, self.omitted):
            shutil.copyfile(run.CORPUS / (name + ".json"), self.corpus / (name + ".json"))
        self.auth = run.authenticate(self.corpus, self.root)
        # This test fixture has a literal exception, independent of current checker keys.
        exceptions = patch.dict(selection.KNOWN_OMISSIONS, {
            self.omitted: frozenset(
                (rid, "solana_zero_copy::unaligned::<impl core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from", ())
                for rid in ("into_u16/0", "into_u16/1", "into_u16/2", "into_u16/3",
                            "into_u16/4", "into_u16/5", "into_u16/6", "into_u16/7")
            ),
        }, clear=True)
        exceptions.start()
        self.addCleanup(exceptions.stop)
        self.descriptors = []
        for name in (self.selected, self.companion):
            for row in self.records(name):
                descriptor = {"corpus": name, "function": row["function"], "generics": row["generics"]}
                if descriptor not in self.descriptors:
                    self.descriptors.append(descriptor)

    def records(self, name):
        return json.loads((self.corpus / (name + ".json")).read_text())["records"]

    def prepare(self):
        return selection.prepare(self.corpus, self.auth, self.descriptors, {self.selected, self.companion}, complete=True)

    def checker(self, plan):
        evidence = self.root / "evidence"
        evidence.mkdir(exist_ok=True)
        runner = run.Runner(evidence, 60)
        runner.run = Mock(return_value=(0, ""))
        checker = run.Checker(runner, None)
        checker.selection = plan
        return checker

    def test_complete_shared_driver_omission_has_no_checker_or_record_credit(self):
        originals = {p.name: p.read_bytes() for p in self.corpus.glob("*.json")}
        plan = self.prepare()
        self.assertEqual(plan["omitted_corpora"], [self.omitted])
        self.assertEqual(set(plan["selected_summaries"]), {self.selected + ".json", self.companion + ".json"})
        omitted = plan["corpora"][self.omitted]
        self.assertEqual(omitted["checkers"], [])
        self.assertEqual(omitted["selected_records"], 0)
        self.assertEqual(omitted["selected_ids"], [])
        self.assertEqual(omitted["omitted_records"], len(self.records(self.omitted)))
        self.assertEqual(plan["omissions"], [{"corpus": self.omitted, **{k: r[k] for k in ("id", "function", "generics")}}
                                             for r in self.records(self.omitted)])
        selection.check_omissions("", plan)
        with self.assertRaisesRegex(ValueError, "omitted-record counts differ"):
            selection.check_omissions(f"OMITTED\t{self.omitted}\t{omitted['omitted_records']}\n", plan)
        self.assertEqual({p.name: p.read_bytes() for p in self.corpus.glob("*.json")}, originals)

    def test_requested_corpus_without_keys_is_not_a_whole_corpus_omission(self):
        with self.assertRaisesRegex(ValueError, "no registered checker keys selected"):
            selection.prepare(self.corpus, self.auth, self.descriptors,
                              {self.selected, self.companion, self.omitted}, complete=True)

    def test_empty_registry_cannot_pass_by_omitting_every_corpus(self):
        with self.assertRaisesRegex(ValueError, "at least one corpus"):
            selection.prepare(self.corpus, self.auth, [], set(), complete=True)
        self.descriptors.clear()
        with self.assertRaisesRegex(ValueError, "no registered checker keys selected"):
            self.prepare()

    def test_registered_checker_cannot_be_hidden_as_a_whole_corpus_omission(self):
        row = self.records(self.omitted)[0]
        self.descriptors.append({"corpus": self.omitted, "function": row["function"], "generics": row["generics"]})
        with self.assertRaisesRegex(ValueError, "registered checker excluded"):
            self.prepare()

    def test_missing_selected_key_still_fails_with_whole_corpus_omissions(self):
        self.descriptors.append({"corpus": self.selected, "function": "missing::selected", "generics": {}})
        with self.assertRaisesRegex(ValueError, "no records for selected checker"):
            self.prepare()

    def test_duplicate_selected_key_still_fails(self):
        self.descriptors.append(copy.deepcopy(self.descriptors[0]))
        with self.assertRaisesRegex(ValueError, "duplicate checker selection"):
            self.prepare()

    def test_whole_corpus_tampering_fails_before_and_after_selection(self):
        plan = self.prepare()
        path = self.corpus / (self.omitted + ".json")
        data = json.loads(path.read_text())
        data["records"][0]["outcome"]["result"] = "changed omitted native outcome"
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "hash differs"):
            run.authenticate(self.corpus, self.root)
        with self.assertRaisesRegex(ValueError, "changed after complete authentication"):
            self.prepare()
        with self.assertRaisesRegex(ValueError, "wholly omitted corpus changed"):
            self.checker(plan).run("check", self.corpus, None)

    def test_omitted_identities_and_counts_are_validated_even_with_updated_hashes(self):
        path = self.corpus / (self.omitted + ".json")
        original = path.read_text()
        for mutate, error in ((lambda rows: rows.append(copy.deepcopy(rows[0])), "duplicate"),
                              (lambda rows: rows[0].update(id=""), "malformed record id"),
                              (lambda rows: rows[0].update(function=""), "malformed checker function"),
                              (lambda rows: rows[0].update(generics={"T": 1}), "malformed checker generic")):
            with self.subTest(error=error):
                data = json.loads(original)
                mutate(data["records"])
                path.write_text(json.dumps(data))
                entry = self.auth["manifests"]["sdk-values-v2"]["corpora"][path.name]
                entry.update(sha256=run.sha256(path), records=len(data["records"]))
                with self.assertRaisesRegex(ValueError, error):
                    self.prepare()
        path.write_text(original)
        entry.update(sha256=run.sha256(path), records=len(json.loads(original)["records"]) + 1)
        with self.assertRaisesRegex(ValueError, "authenticated record count differs"):
            self.prepare()

    def test_unexpected_and_missing_files_fail_before_checker_dispatch(self):
        plan = self.prepare()
        checker = self.checker(plan)
        extra = self.corpus / "unregistered_0_0_0.json"
        extra.write_text("{}")
        with self.assertRaisesRegex(ValueError, "without a driver"):
            run.authenticate(self.corpus, self.root)
        with self.assertRaisesRegex(ValueError, "without registered checkers or authenticated omissions"):
            checker.run("check", self.corpus, None)
        extra.unlink()
        (self.corpus / (self.omitted + ".json")).unlink()
        with self.assertRaisesRegex(ValueError, "authenticated corpora without a file"):
            checker.run("check", self.corpus, None)
        checker.runner.run.assert_not_called()

    def test_global_dispatch_sends_only_nonempty_selected_keys_and_omissions_to_lean(self):
        self.descriptors = [d for d in self.descriptors
                            if d["function"] != "solana_program_option::COption::<T>::as_ref"]
        selection.KNOWN_OMISSIONS[self.selected] = frozenset(
            (rid, "solana_program_option::COption::<T>::as_ref", (("T", "u64"),))
            for rid in ("as_ref/none", "as_ref/zero", "as_ref/max")
        )
        plan = self.prepare()
        checker = self.checker(plan)
        checker.run("check", self.corpus, None)
        argv = checker.runner.run.call_args.args[1]
        self.assertEqual(set(argv[argv.index("--only") + 1].split(",")), {self.selected, self.companion})
        omissions = json.loads(Path(argv[argv.index("--omit-records") + 1]).read_text())
        self.assertTrue(omissions)
        self.assertEqual({row["corpus"] for row in omissions}, {self.selected})
        checker.selection = None
        checker.run("default", self.corpus, None)
        argv = checker.runner.run.call_args.args[1]
        self.assertNotIn("--only", argv)
        self.assertNotIn("--omit-records", argv)

    def test_global_controls_keep_selected_mutations_and_reject_the_unknown_file(self):
        checker = self.checker(self.prepare())
        checker.runner.run.return_value = (1, "no registered checker; no records for")
        with patch.object(run, "CONTROLS", []), patch.object(run, "KIND_CONTROLS", []), \
                patch.object(run, "_semantic_controls", return_value=[]), \
                patch.object(run, "_spare_after_nonzero_control", return_value=None), \
                patch.object(run, "load_family_controls", return_value=[]):
            controls = run.run_controls(checker.runner, checker, self.corpus, None)
        self.assertEqual(len(controls), 5)
        self.assertEqual({row["corpus"] for row in controls if "corpus" in row}, {self.selected, self.companion})
        self.assertEqual(controls[-1]["validator"], "authenticated file set")
        self.assertIn("unregistered_0_0_0", controls[-1]["error"])
        self.assertEqual(checker.runner.run.call_count, 4)

    def test_model_only_keeps_full_authentication_audit_and_separate_omission_counts(self):
        plan = self.prepare()
        output = "".join(name + "\n" + "".join(
            f"  ok   {c['records']}/{c['records']}  {c['function']} [{json.dumps(c['generics'])}]  -> harness stub\n"
            for c in plan["corpora"][name]["checkers"])
            for name in (self.selected, self.companion))
        evidence = self.root / "model-only"
        evidence.mkdir()
        from argparse import Namespace
        args = Namespace(evidence_dir=evidence, timeout=60, family=None, corpus=None, registered_checkers=True)
        def runner_result(_self, name, *_args, **_kwargs):
            return 0, {"lean-version": run.LEAN.rpartition(":v")[2],
                       "checker-keys": "CHECKERS\t" + json.dumps(self.descriptors), "check": output}.get(name, "")
        with ExitStack() as stack:
            stack.enter_context(patch.object(run, "CORPUS", self.corpus))
            auth = stack.enter_context(patch.object(run, "authenticate", return_value=self.auth))
            stack.enter_context(patch.object(run.Checker, "build"))
            stack.enter_context(patch.object(run.Runner, "run", runner_result))
            returns = {"generate_registry": True, "readme_tables_current": True, "source_map": {},
                       "family_modules": ["Fixture"], "checked_axioms": {}, "load_divergences": [],
                       "spare_writers": [], "regionless_corpora": [], "load_requires_theorems": [],
                       "decides_audit_source": "", "load_not_tested": [], "load_requires_open": [],
                       "load_cross_function": [], "precondition_control_index": {}, "run_controls": []}
            for name, value in returns.items():
                stack.enter_context(patch.object(run, name, return_value=value))
            audit = stack.enter_context(patch.object(run, "checked_decides", return_value={"controls": []}))
            with redirect_stdout(io.StringIO()):
                run.model_only(args)
            auth.assert_called_once_with(only=None)
            self.assertTrue(audit.call_args.kwargs["complete"])
        status = json.loads((evidence / "run-status.json").read_text())
        self.assertEqual(status["status"], "passed")
        self.assertIsNone(status["families"])
        self.assertEqual(status["corpora"], sorted([self.selected, self.companion]))
        self.assertEqual(status["records"], len(self.records(self.selected)) + len(self.records(self.companion)))
        self.assertEqual(status["checkers"], len(self.descriptors))
        self.assertEqual(status["omitted_corpora"], [self.omitted])
        self.assertEqual(status["whole_corpus_omitted_records"], len(self.records(self.omitted)))
        counts = json.loads((evidence / "counts.json").read_text())
        with self.assertRaisesRegex(ValueError, "count report has"):
            run.check_counts({self.selected: {}, self.companion: {}}, plan["selected_summaries"])
        with self.assertRaisesRegex(ValueError, "count report corpora differ"):
            run.check_counts({**counts, self.omitted: {}}, plan["selected_summaries"])


    def test_authenticated_unknown_whole_corpus_requires_explicit_permission_even_when_empty(self):
        name = "unknown_whole_fixture"
        path = self.corpus / (name + ".json")
        for rows in ([record("unknown", "fixture::unknown", {})], []):
            with self.subTest(records=len(rows)):
                path.write_text(json.dumps({"schema": run.SCHEMA, "corpus": name,
                                           "crates": [{"name": "fixture", "version": "1.0.0"}],
                                           "records": rows}))
                self.auth["manifests"]["sdk-values-v2"]["corpora"][path.name] = {
                    "sha256": run.sha256(path), "records": len(rows)}
                if rows:
                    self.auth["summaries"][path.name] = run.validate_corpus(path)
                else:
                    with self.assertRaisesRegex(ValueError, "no records"):
                        run.validate_corpus(path)
                    # Check the selector boundary too, without relaxing the native validator.
                    self.auth["summaries"][path.name] = {"records": 0}
                self.assertNotIn(name, selection.KNOWN_OMISSIONS)
                with self.assertRaisesRegex(ValueError, "wholly omitted corpus has no reviewed exception"):
                    self.prepare()
        # Even the empty case requires an explicit corpus entry.
        selection.KNOWN_OMISSIONS[name] = frozenset()
        plan = self.prepare()
        self.assertEqual(set(plan["omitted_corpora"]), {self.omitted, name})
        self.assertEqual(plan["corpora"][name]["authenticated_records"], 0)
        self.assertNotIn(path.name, plan["selected_summaries"])

    def test_complete_loss_of_a_registered_corpus_is_not_an_implicit_exception(self):
        self.prepare()
        descriptors = [d for d in self.descriptors if d["corpus"] != self.selected]
        with self.assertRaisesRegex(ValueError, "wholly omitted corpus has no reviewed exception"):
            selection.prepare(self.corpus, self.auth, descriptors, {self.companion}, complete=True)

    def test_new_whole_corpus_checker_requires_removing_the_stale_exception(self):
        descriptor = {"corpus": self.omitted,
                      "function": "solana_zero_copy::unaligned::<impl core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from",
                      "generics": {}}
        descriptors = self.descriptors + [descriptor]
        names = {self.selected, self.companion, self.omitted}
        with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
            selection.prepare(self.corpus, self.auth, descriptors, names, complete=True)
        del selection.KNOWN_OMISSIONS[self.omitted]
        plan = selection.prepare(self.corpus, self.auth, descriptors, names, complete=True)
        self.assertEqual(plan["omitted_corpora"], [])
        self.assertEqual(plan["omissions"], [])
        self.assertEqual(plan["corpora"][self.omitted]["selected_records"], 8)

    def test_whole_corpus_identity_change_is_rejected_after_updated_authentication(self):
        path = self.corpus / (self.omitted + ".json")
        original = path.read_text()
        for change in (lambda rows: rows.append(record("new", "fixture::unknown", {})),
                       lambda rows: rows.pop(),
                       lambda rows: rows[0].update(id="renamed"),
                       lambda rows: rows[0].update(function="fixture::changed"),
                       lambda rows: rows[0].update(generics={"T": "u32"})):
            data = json.loads(original)
            change(data["records"])
            path.write_text(json.dumps(data))
            self.auth["manifests"]["sdk-values-v2"]["corpora"][path.name].update(
                sha256=run.sha256(path), records=len(data["records"]))
            self.auth["summaries"][path.name] = run.validate_corpus(path)
            with self.assertRaisesRegex(ValueError, "unreviewed or stale record omissions"):
                self.prepare()

    def test_whole_corpus_removal_after_authentication_is_rejected(self):
        (self.corpus / (self.omitted + ".json")).unlink()
        with self.assertRaises(FileNotFoundError):
            self.prepare()

    def test_stale_whole_corpus_policy_survives_neither_file_nor_authentication_removal(self):
        name = self.omitted + ".json"
        (self.corpus / name).unlink()
        del self.auth["manifests"]["sdk-values-v2"]["corpora"][name]
        del self.auth["summaries"][name]
        with self.assertRaisesRegex(ValueError, "reviewed omission corpora missing from complete authentication"):
            self.prepare()
        # A scoped replay still ignores unrelated reviewed corpus entries.
        plan = selection.prepare(self.corpus, self.auth, self.descriptors, {self.selected, self.companion})
        self.assertFalse(plan["complete"])
        self.assertEqual(set(plan["corpora"]), {self.selected, self.companion})


@unittest.skipUnless(os.environ.get("SOLANA_CONFORMANCE_SELECTION_LEAN") == "1", "explicit Lean test mode")
class LeanRunner(Selection):
    def setUp(self):
        super().setUp()
        self.fixture = run.ROOT / "SolanalibTest/Conformance/SelectionMain.lean"
        self.plan = self.prepare()
        self.omissions = self.root / "omissions.json"
        self.omissions.write_text(json.dumps(self.plan["omissions"]))

    def execute(self, *, selected=True, describe=False):
        args = run.lean_command(self.fixture, [str(self.root), "--only", "selection_fixture"])
        if selected:
            args += ["--omit-records", str(self.omissions)]
        if describe:
            args += ["--describe-checkers"]
        result = subprocess.run(args, cwd=run.REPO, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=60)
        return result.returncode, result.stdout

    def changed(self, mutate):
        mutate(self.data["records"])
        self.path.write_text(json.dumps(self.data))
        code, output = self.execute()
        self.assertEqual(code, 1, output)
        return output

    def test_describe_reads_only_compiled_keys(self):
        self.path.unlink()
        code, output = self.execute(selected=False, describe=True)
        self.assertEqual(code, 0, output)
        rows = json.loads(next(line.removeprefix("CHECKERS\t") for line in output.splitlines()
                               if line.startswith("CHECKERS\t")))
        self.assertEqual(rows, self.descriptors)

    def test_selected_success_reports_checked_and_omitted_separately(self):
        code, output = self.execute()
        self.assertEqual(code, 0, output)
        selection.check_omissions(output, self.plan)
        run.check_counts(run.parse_counts(output), self.plan["selected_summaries"])
        self.assertIn("All 2 selected records", output)
        self.assertIn("2 authenticated records omitted", output)

    def test_complete_corpus_default_rejects_unknown_keys(self):
        code, output = self.execute(selected=False)
        self.assertEqual(code, 1, output)
        self.assertIn("no registered checker", output)
        self.assertNotIn("OMITTED", output)

    def test_complete_corpus_default_output_is_unchanged(self):
        self.data["records"] = self.data["records"][:2]
        self.path.write_text(json.dumps(self.data))
        code, output = self.execute(selected=False)
        self.assertEqual(code, 0, output)
        self.assertEqual(output, "selection_fixture\n  ok   2/2  fixture::read [T = u64]  -> synthetic selected checker\n"
                                "All 2 records admitted by the registered references.\n")

    def test_changed_selected_function_cannot_become_omitted(self):
        output = self.changed(lambda rows: rows[0].update(function="fixture::write"))
        self.assertIn("no registered checker", output)

    def test_changed_selected_generic_cannot_become_omitted(self):
        output = self.changed(lambda rows: rows[0].update(generics={"T": "u8"}))
        self.assertIn("no registered checker", output)

    def test_malformed_selected_record_is_rejected(self):
        self.assertIn("unreadable record", self.changed(lambda rows: rows[0].pop("args")))

    def test_changed_selected_outcome_reaches_the_checker(self):
        self.assertIn("MISMATCH selection_fixture/read-0", self.changed(lambda rows: rows[0]["outcome"].update(result=8)))

    def test_selected_checker_without_records_fails(self):
        self.assertIn("no records for", self.changed(lambda rows: rows.__delitem__(slice(0, 2))))

    def test_changed_omitted_identity_is_rejected(self):
        self.assertIn("omitted identity changed", self.changed(lambda rows: rows[2].update(function="fixture::other")))

    def test_duplicate_omitted_record_is_rejected(self):
        self.assertIn("occurred 2 times", self.changed(lambda rows: rows.append(copy.deepcopy(rows[2]))))

    def test_missing_omitted_record_is_rejected(self):
        self.assertIn("occurred 0 times", self.changed(lambda rows: rows.pop()))

    def test_omission_table_cannot_remove_a_registered_key(self):
        malicious = {"corpus": "selection_fixture", "id": "read-0", "function": "fixture::read", "generics": {"T": "u64"}}
        self.omissions.write_text(json.dumps([*self.plan["omissions"], malicious]))
        code, output = self.execute()
        self.assertEqual(code, 1, output)
        self.assertIn("registered checker cannot be omitted", output)

    def test_global_whole_corpus_omission_keeps_real_checker_and_structural_controls(self):
        corpus = self.root / "complete"
        corpus.mkdir()
        shutil.copyfile(self.path, corpus / self.path.name)
        omitted = "wholly_unselected_fixture"
        omitted_path = corpus / (omitted + ".json")
        omitted_path.write_text(json.dumps({**self.data, "corpus": omitted,
                                           "records": [record("unselected", "fixture::other")]}))
        entries = {p.name: {"sha256": run.sha256(p), "records": len(json.loads(p.read_text())["records"])}
                   for p in corpus.glob("*.json")}
        auth = {"manifests": {"fixture": {"corpora": entries}},
                "summaries": {p.name: run.validate_corpus(p) for p in corpus.glob("*.json")}}
        evidence = self.root / "complete-evidence"
        evidence.mkdir()
        runner = run.Runner(evidence, 60)
        checker = object.__new__(run.Checker)
        checker.runner, checker.families, checker.driver = runner, [], self.fixture
        checker.omitted_controls = []
        selection.KNOWN_OMISSIONS[omitted] = frozenset({
            ("unselected", "fixture::other", (("T", "u64"),)),
        })
        checker.selection = selection.prepare(corpus, auth, self.descriptors, {"selection_fixture"}, complete=True)
        code, output = checker.run("complete-check", corpus, None)
        self.assertEqual(code, 0, output)
        run.check_counts(run.parse_counts(output), checker.selection["selected_summaries"])
        selection.check_omissions(output, checker.selection)
        self.assertNotIn(omitted, output)
        controls = run.run_controls(runner, checker, corpus, None)
        self.assertEqual({row["control"] for row in controls}, {
            "unregistered function in selection_fixture", "checker without records in selection_fixture",
            "semantic change of the first record of each checker in selection_fixture", "unregistered corpus file"})
        self.assertEqual(controls[-1]["validator"], "authenticated file set")

    def test_divergence_controls_use_selected_records_and_retain_omissions(self):
        self.data["records"][0]["id"] = "bad/selected"
        self.data["records"][0]["outcome"]["result"] = 8
        self.data["records"][2]["id"] = "bad/omitted"
        self.data["records"] = [self.data["records"][2], *self.data["records"][:2], self.data["records"][3]]
        omitted = copy.deepcopy(self.data["records"][0])
        self.path.write_text(json.dumps(self.data))
        self.auth = self.authentication()
        evidence = self.root / "controls"
        evidence.mkdir()
        runner = run.Runner(evidence, 60)
        checker = object.__new__(run.Checker)
        checker.runner, checker.families, checker.driver = runner, [], self.fixture
        self.allowed_omissions.remove(("write", "fixture::write", (("T", "u64"),)))
        self.allowed_omissions.add(("bad/omitted", "fixture::write", (("T", "u64"),)))
        checker.selection = self.prepare()
        checker.divergences = evidence / "divergences.json"
        divergences = [{"corpus": "selection_fixture", "records": "bad/*", "model": "synthetic",
                        "reason": "synthetic rejected value"}]
        checker.divergences.write_text(json.dumps(divergences))
        results = run._divergence_controls(runner, checker, self.root, divergences)
        self.assertEqual(len(results), 3)
        for directory in evidence.glob("control-divergence-*"):
            rows = json.loads((directory / self.path.name).read_text())["records"]
            self.assertEqual(next(row for row in rows if row["id"] == "bad/omitted"), omitted)
        rows = json.loads((evidence / "control-divergence-0-0" / self.path.name).read_text())["records"]
        clone = next(row for row in rows if row["id"].startswith("control#"))
        self.assertEqual(clone["function"], "fixture::read")


@unittest.skipUnless(os.environ.get("SOLANA_CONFORMANCE_SELECTION_LEAN") == "1", "explicit Lean test mode")
class AnchorExitControls(unittest.TestCase):
    def test_system_model_observation_mutations(self):
        """Compile the finite model sensitivity cases once, outside the generic runner fixture."""
        fixture = run.ROOT / "SolanalibTest/Conformance/Library/Controls/AnchorSystemObservation.lean"
        result = subprocess.run(run.lean_command(fixture),
                                cwd=run.REPO, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_registered_wrapper_exit_controls_reach_their_compiled_checkers(self):
        """An omitted helper control cannot substitute for the exit check of a selected wrapper."""
        families = ["AnchorSystem", "AnchorSplTokenOperations"]
        names = {"anchor_system_0_32_1", "anchor_spl_token_0_32_1"}
        with tempfile.TemporaryDirectory() as directory:
            evidence = Path(directory)
            runner = run.Runner(evidence, 60)
            checker = run.Checker(runner, families)
            code, output = checker.run("describe", run.CORPUS, sorted(names), describe=True)
            self.assertEqual(code, 0, output)
            descriptors = json.loads(next(line.removeprefix("CHECKERS\t") for line in output.splitlines()
                                          if line.startswith("CHECKERS\t")))
            checker.selection = selection.prepare(run.CORPUS, run.authenticate(only=names), descriptors, names)
            checker.spare_writes = evidence / "spare-writes.json"
            checker.spare_writes.write_text(json.dumps(run.spare_writers()))
            code, output = checker.run("original", run.CORPUS, sorted(names))
            self.assertEqual(code, 0, output)
            controls = [control for control in run.load_family_controls()
                        if control["family"] in families and control["label"].startswith("registered ")]
            self.assertEqual({control["family"] for control in controls}, set(families))
            for index, control in enumerate(controls):
                with self.subTest(control=control["label"]):
                    name = control["corpus"]
                    rid = control["mutate"].record_id
                    self.assertIn(rid, checker.selection["corpora"][name]["selected_ids"])
                    changed = evidence / f"changed-{index}"
                    changed.mkdir()
                    run.apply_control(run.CORPUS, changed, name, control["mutate"])
                    code, output = checker.run(f"check-{index}", changed, [name])
                    self.assertEqual(code, 1, output)
                    self.assertIn(f"MISMATCH {name}/{rid}", output)
                    self.assertIn(control["expected"], output)


@unittest.skipUnless(os.environ.get("SOLANA_CONFORMANCE_SELECTION_LEAN") == "1", "explicit Lean test mode")
class TokenEpochControls(unittest.TestCase):
    def test_epoch_boundary_controls_reach_their_registered_wrapper_checkers(self):
        """A generic fee check does not replace the check of the selected public wrapper."""
        name = "token_state_8_0_1"
        labels = {
            "epoch fee equality applies newer value",
            "inverse epoch equality applies newer value",
            "epoch fee retains unrelated receiver fields",
            "inverse epoch excess rate is not zero fee",
            "inverse epoch checked addition does not wrap",
            "epoch fee narrowing precedes zero cap",
            "inverse epoch zero input precedes invalid rate",
        }
        with tempfile.TemporaryDirectory() as directory:
            evidence = Path(directory)
            runner = run.Runner(evidence, 60)
            checker = run.Checker(runner, ["TokenExtensionVersions"])
            code, output = checker.run("describe", run.CORPUS, [name], describe=True)
            self.assertEqual(code, 0, output)
            descriptors = json.loads(next(line.removeprefix("CHECKERS\t") for line in output.splitlines()
                                          if line.startswith("CHECKERS\t")))
            checker.selection = selection.prepare(run.CORPUS, run.authenticate(only={name}), descriptors, {name})
            checker.spare_writes = evidence / "spare-writes.json"
            checker.spare_writes.write_text(json.dumps(run.spare_writers()))
            code, output = checker.run("original", run.CORPUS, [name])
            self.assertEqual(code, 0, output)
            controls = [control for control in run.load_family_controls()
                        if control["family"] == "TokenExtensionVersions" and control["label"] in labels]
            self.assertEqual({control["label"] for control in controls}, labels)
            self.assertEqual(len(controls), len(labels))
            for index, control in enumerate(controls):
                with self.subTest(control=control["label"]):
                    rid = control["mutate"].record_id
                    self.assertEqual(control["corpus"], name)
                    self.assertIn(rid, checker.selection["corpora"][name]["selected_ids"])
                    changed = evidence / f"changed-{index}"
                    changed.mkdir()
                    run.apply_control(run.CORPUS, changed, name, control["mutate"])
                    code, output = checker.run(f"check-{index}", changed, [name])
                    self.assertEqual(code, 1, output)
                    self.assertIn(f"MISMATCH {name}/{rid}", output)


if __name__ == "__main__":
    unittest.main()
