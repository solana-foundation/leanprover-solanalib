"""Portable package boundaries and adversarial source/model evidence controls."""

import copy
import fnmatch
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib
import unittest
from unittest.mock import patch

import check_solana_specs as checker
import solana_source_map as source_map
from import_tiers import check as check_imports
from solana_specs_config import (
    COMMON_ROOT, COMMON_TEST_ROOT, LIBRARY_ROOTS, PRODUCTION_ROOTS, TEST_ROOTS,
    SDK_ROOTS, package_roots, package_configuration, module_root, test_root,
)


ROOT = Path(__file__).resolve().parents[2]
SPECS = ROOT / "packages/solanalib-specs"
MODEL = ROOT / "packages/solanalib-runtime"
FIXTURE_ROOT = "Solanalib.Specs.ExampleSdk"
FIXTURE_TEST = test_root(FIXTURE_ROOT)
FIXTURE_LIBRARIES = (COMMON_ROOT, FIXTURE_ROOT, FIXTURE_TEST)
FOUNDATION_MODULES = {
    "Solanalib.Contracts", "Solanalib.Contracts.Outcome", "Solanalib.Contracts.Family",
    "Solanalib.Contracts.Callback", "Solanalib.Contracts.Capabilities", "Solanalib.Contracts.Versioning",
}


def configure(package, libraries=FIXTURE_LIBRARIES):
    """An offline package using the same recursive root/test convention."""
    package.mkdir(parents=True, exist_ok=True)
    text = 'name = "spec-audit-control"\ndefaultTargets = ' + json.dumps(list(libraries)) + "\n"
    for name in libraries:
        text += f'[[lean_lib]]\nname = "{name}"\nglobs = ["{name}", "{name}.+"]\n'
        (package / name.replace(".", "/")).mkdir(parents=True, exist_ok=True)
        (package / (name.replace(".", "/") + ".lean")).write_text("module\n@[expose] public section\n")
    (package / "lakefile.toml").write_text(text)
    (package / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())


def attach_foundation(package, foundation):
    with (package / "lakefile.toml").open("a") as configuration:
        configuration.write('\n[[lean_lib]]\nname = "Solanalib.Contracts"\nsrcDir = '
                            + json.dumps(str(foundation.resolve()))
                            + '\nglobs = ["Solanalib.Contracts", "Solanalib.Contracts.+"]\n')


def declaration(name, module=FIXTURE_ROOT, *, head="Nat", definition=False,
                theorem=False, contract=None, reference=None, sample=None, parameters=0,
                universes=0, private=False):
    return {"name": name, "module": module, "is_definition": definition,
            "is_theorem": theorem, "is_private": private, "type_head": head,
            "conclusion_contract": contract, "conclusion_reference": reference,
            "conclusion_sample": sample, "parameters": parameters,
            "universe_parameters": universes}


def fake_evidence(modules):
    """Python controls test map validation; the opt-in tests derive these with Lean."""
    declarations = []
    for stem, kind in (("total", "RealizedBy"), ("outcome", "Holds"), ("generic", "FamilyReference")):
        prefix = FIXTURE_ROOT + "." + stem
        contract, reference = prefix + "_contract", prefix + "_run"
        sample = prefix + "_sample" if kind == "FamilyReference" else None
        declarations.extend([
            declaration(contract, head="Solanalib.Contracts.Model.Family" if sample else "Solanalib.Contracts.Model",
                        definition=True),
            declaration(reference, definition=True, parameters=3 if sample else 2),
            declaration(prefix + "_reference", head="Solanalib.Contracts.Model." + kind,
                        theorem=True, contract=contract, reference=reference),
            declaration(prefix + "_satisfiable", theorem=True, contract=contract, sample=sample,
                        head="Solanalib.Contracts.Model.FamilySatisfiable" if sample else "Solanalib.Contracts.Model.Satisfiable"),
        ])
        if kind != "RealizedBy":
            declarations.append(declaration(
                prefix + "_has_execution", theorem=True, contract=contract, reference=reference, sample=sample,
                head="Solanalib.Contracts.Model.FamilyHasExecution" if sample else "Solanalib.Contracts.Model.HasExecution"))
        if sample:
            declarations.append(declaration(sample, definition=True))
        declarations.append(declaration(FIXTURE_TEST + "." + stem, FIXTURE_TEST, theorem=True, head="Eq"))
    return {"audited_modules": sorted(modules), "declarations": declarations,
            "audited_constants": len(declarations), "audited_theorems": 11,
            "source_sha256": {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in modules.items()}}


def document_for(package, modules, evidence):
    production, _ = package_roots(package)
    foundations = checker.foundation_sources(package)
    modules = modules | foundations
    reviewed_modules = [name for name in modules
                        if module_root(name) in production or name in foundations]
    models, api = [], []
    cases = [("total", "RealizedBy"), ("outcome", "Holds"), ("generic", "FamilyReference")]
    if any(d["name"] == FIXTURE_ROOT + ".separate_contract" for d in evidence["declarations"]):
        cases.append(("separate", "FamilyReference"))
    for stem, kind in cases:
        prefix = FIXTURE_ROOT + "." + stem
        identifier = "example-sdk::" + stem
        row = {"id": identifier, "kind": "full", "contract": prefix + "_contract",
               "reference": prefix + "_run", "witness_kind": kind,
               "witnesses": [prefix + "_reference"],
               "satisfiability_witnesses": [prefix + "_satisfiable"],
               "assumptions": [], "model_gaps": [], "remaining_requirements": [],
               "rust_proof_status": "open"}
        if kind != "RealizedBy":
            row["execution_witnesses"] = [prefix + "_has_execution"]
        if kind == "FamilyReference":
            row["sample"] = prefix + "_sample"
        if stem == "separate":
            row["family"] = prefix + "_family"
        models.append(row)
        api.append({"id": identifier, "source_id": "example", "line": 2,
                    "anchor_text": "pub fn read() {}", "status": "contracted", "models": [identifier],
                    "clients": [FIXTURE_TEST + "." + stem], "model_dependencies": [],
                    "scope": "Mathematical control, without a Rust implementation claim.",
                    "binding_obligations": ["Prove the separate Rust implementation binding."],
                    "rust_names": ["example_sdk::" + stem], "inventory_bindings": []})
    return {"schema_version": 2, "interfaces": [{
                "id": "example", "crate": "example-sdk-1.0.0", "path": "src/lib.rs",
                "repository": "https://github.com/example/sdk", "revision": "1" * 40,
                "path_in_repository": "sdk/src/lib.rs",
                "sha256": hashlib.sha256(b"// control\npub fn read() {}\n").hexdigest(),
            }], "abstractions": [{
                "id": "control", "modules": reviewed_modules,
                "model_sha256": {name: hashlib.sha256(modules[name].read_bytes()).hexdigest()
                                 for name in reviewed_modules},
                "declarations": [d["name"] for d in evidence["declarations"]
                                 if d["module"] in reviewed_modules and not d["is_private"]],
                "source_ids": ["example"], "argument": "Synthetic audit control.",
                "limitations": ["No SDK source implementation is proved."],
            }], "models": models, "api": api}


class PackageBoundaries(unittest.TestCase):
    def test_every_canonical_library_belongs_to_one_root_package(self):
        configuration = package_configuration(SPECS)
        libraries = configuration["_root_libraries"]
        self.assertEqual({row["package"] for row in libraries}, {"solanalib"})
        self.assertEqual(len({row["buildDir"] for row in libraries}), 1)
        for source in (SPECS, MODEL, ROOT / "packages/solanalib-contracts"):
            self.assertFalse((source / "lakefile.toml").exists())
            self.assertFalse((source / "lakefile.lean").exists())

    def test_every_registered_sdk_and_test_root_is_a_recursive_selectable_library(self):
        production, tests = package_roots(SPECS)
        self.assertEqual(set(production), set(PRODUCTION_ROOTS))
        self.assertEqual(set(tests), set(TEST_ROOTS))
        configuration = package_configuration(SPECS)
        self.assertEqual([library["name"] for library in configuration["lean_lib"]], list(LIBRARY_ROOTS))

    def test_independent_workflow_covers_package_and_audit_inputs(self):
        workflow = (ROOT / ".github/workflows/ci.yml").read_text()
        triggers = workflow.split("jobs:", 1)[0]
        # An unfiltered pull_request trigger includes every nested model,
        # configuration, source registry, generator and negative-control edit.
        self.assertIn("  pull_request:", triggers)
        self.assertNotIn("paths:", triggers)
        self.assertNotIn("paths-ignore:", triggers)
        self.assertIn("check_solana_specs.py --fetch-sdk", workflow)
        self.assertIn("python3 tools/model-audit/import_tiers.py", workflow)
        self.assertIn("-p 'test_import_tiers.py'", workflow)
        self.assertIn("-p 'test_solana_*.py'", workflow)
        self.assertIn("SOLANA_SPECS_INTEGRATION_TESTS: '1'", workflow)
        self.assertIn("python3 scripts/ci-sdk-groups.py", workflow)
        self.assertIn("python3 scripts/ci-sdk-groups.py --build all", workflow)

    def test_import_policy_keeps_models_specs_and_implementations_separate(self):
        model = "packages/solanalib-runtime/Solanalib/Runtime/Example.lean"
        for root in SDK_ROOTS:
            library = f"packages/solanalib-specs/{root.replace(chr(46), chr(47))}/Example.lean"
            with self.subTest(root=root):
                self.assertEqual(check_imports({model: "", library: "import Solanalib.Runtime.Example\n"}), [])
                for target in ("ProgramLogic.Basic", "CompilerSupport", "ExternalLogic", "ApplicationLib.Example",
                               "ExternalRuntime.core.Example", test_root(root) + ".Example", COMMON_TEST_ROOT):
                    self.assertTrue(check_imports({library: f"import {target}\n"}), target)
                for origin in (model, "toolchains/x/y/ExternalProofs/core/Example.lean", "external-runtime/ExternalRuntime/core/Example.lean"):
                    self.assertTrue(check_imports({origin: f"import {root}.Example\n", library: ""}), origin)


class Discovery(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="solanalib-specs-discovery-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        configure(self.package)

    def test_root_names_identify_libraries_and_reject_release_suffixes(self):
        self.assertEqual(package_roots(self.package),
                         ((COMMON_ROOT, FIXTURE_ROOT), (FIXTURE_TEST,)))
        path = self.package / "lakefile.toml"
        original = path.read_text()
        for name in ("example_sdk_1_0_0", "ExampleSdk", "example-sdk"):
            with self.subTest(name=name):
                path.write_text(original.replace(FIXTURE_ROOT, name))
                with self.assertRaisesRegex(ValueError, "Unsupported production specification root"):
                    package_roots(self.package)
        path.write_text(original)

    def test_discovers_unstaged_nested_modules(self):
        path = self.package / FIXTURE_ROOT.replace(".", "/") / "Nested/NotImported.lean"
        path.parent.mkdir(parents=True)
        path.write_text("module\n")
        self.assertIn(FIXTURE_ROOT + ".Nested.NotImported", checker.discover(self.package))

    def test_internal_imports_cannot_point_to_absent_source_modules(self):
        aggregate = self.package / (FIXTURE_ROOT.replace(".", "/") + ".lean")
        aggregate.write_text(f"module\npublic import {FIXTURE_ROOT}.Missing\n")
        with self.assertRaisesRegex(ValueError, "Missing specification import"):
            checker.discover(self.package)
        (self.package / FIXTURE_ROOT.replace(".", "/") / "Missing.lean").write_text("module\n")
        self.assertIn(FIXTURE_ROOT + ".Missing", checker.discover(self.package))

    def test_rejects_unregistered_sources_and_missing_roots(self):
        unknown = self.package / "Unregistered.lean"
        unknown.write_text("module\n")
        with self.assertRaisesRegex(ValueError, "Unregistered specification source"):
            checker.discover(self.package)
        unknown.unlink()
        (self.package / (FIXTURE_ROOT.replace(".", "/") + ".lean")).unlink()
        with self.assertRaisesRegex(ValueError, "Missing or linked specification root"):
            checker.discover(self.package)

    def test_rejects_linked_modules_and_directories(self):
        target = self.package / "linked"
        target.symlink_to(SPECS / "Solanalib/Specs/Core", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "Linked specification source directory"):
            checker.discover(self.package)
        target.unlink()
        (self.package / COMMON_ROOT.replace(".", "/")).rmdir()
        (self.package / COMMON_ROOT.replace(".", "/")).symlink_to(SPECS / COMMON_ROOT.replace(".", "/"), target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "linked specification root"):
            checker.discover(self.package)

    def test_rejects_uncovered_globs_missing_tests_and_duplicate_libraries(self):
        path = self.package / "lakefile.toml"
        original = path.read_text()
        for changed, message in (
            (original.replace(f'"{FIXTURE_ROOT}", "{FIXTURE_ROOT}.+"', f'"{FIXTURE_ROOT}"'), "recursive coverage"),
            (original.replace(f'[[lean_lib]]\nname = "{FIXTURE_TEST}"\nglobs = ["{FIXTURE_TEST}", "{FIXTURE_TEST}.+"]\n', ""), "no separate test root"),
            (original + f'[[lean_lib]]\nname = "{COMMON_ROOT}"\n', "duplicate specification libraries"),
        ):
            with self.subTest(message=message):
                path.write_text(changed)
                with self.assertRaisesRegex(ValueError, message):
                    package_roots(self.package)
        path.write_text(original)

    def test_partial_module_inventory_is_rejected_before_lean(self):
        modules = checker.discover(self.package)
        modules.pop(FIXTURE_TEST)
        with patch.object(checker.subprocess, "run") as lean:
            with self.assertRaisesRegex(ValueError, "complete module inventory"):
                checker.audit(self.package, modules)
            lean.assert_not_called()


class ModelEvidence(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="solanalib-specs-map-control-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        configure(self.package)
        self.modules = checker.discover(self.package)
        self.evidence = fake_evidence(self.modules)
        self.document = document_for(self.package, self.modules, self.evidence)

    def verify(self, document=None, evidence=None, modules=None):
        (self.package / "source-map.json").write_text(json.dumps(document or self.document))
        return checker.verify_map(self.package, modules or self.modules, evidence or self.evidence)

    def test_total_outcome_and_type_indexed_families_are_distinct_closed_models(self):
        result = self.verify()
        self.assertEqual(result["model_ids"], sorted(row["id"] for row in self.document["models"]))
        self.assertEqual(result["models_checked"], len(self.document["models"]))
        self.assertEqual(result["contract_execution_witnesses_checked"], 2)
        self.assertEqual(result["family_models_checked"], 1)
        self.assertEqual(result["rust_proof_status"], "open")

    def test_complete_review_rejects_missing_duplicate_and_changed_modules(self):
        for change in ("missing", "duplicate", "hash", "unknown_declaration", "incomplete_audit"):
            with self.subTest(change=change):
                document, evidence = copy.deepcopy(self.document), copy.deepcopy(self.evidence)
                row = document["abstractions"][0]
                if change == "missing":
                    row["modules"].remove(COMMON_ROOT)
                    row["model_sha256"].pop(COMMON_ROOT)
                elif change == "duplicate":
                    document["abstractions"].append({**copy.deepcopy(row), "id": "duplicate"})
                elif change == "hash":
                    row["model_sha256"][COMMON_ROOT] = "0" * 64
                elif change == "unknown_declaration":
                    row["declarations"].append("DoesNotExist")
                else:
                    evidence["audited_modules"].remove(FIXTURE_TEST)
                with self.assertRaises(ValueError):
                    self.verify(document, evidence)

    def test_new_or_changed_sources_invalidate_an_earlier_audit(self):
        fresh = self.package / FIXTURE_ROOT.replace(".", "/") / "New.lean"
        fresh.write_text("module\n")
        with self.assertRaisesRegex(ValueError, "complete current module inventory"):
            self.verify()
        fresh.unlink()
        original = self.package / (FIXTURE_ROOT.replace(".", "/") + ".lean")
        original.write_text(original.read_text() + "\n-- edited after the audit\n")
        with self.assertRaisesRegex(ValueError, "exact audited source identities"):
            self.verify()

    def test_complete_model_inventory_rejects_omissions_and_duplicates(self):
        for change in ("omitted", "duplicate_id", "duplicate_contract", "extra_public_contract"):
            with self.subTest(change=change):
                document, evidence = copy.deepcopy(self.document), copy.deepcopy(self.evidence)
                if change == "omitted":
                    document["models"].pop()
                elif change == "duplicate_id":
                    document["models"].append(copy.deepcopy(document["models"][0]))
                elif change == "duplicate_contract":
                    document["models"].append({**document["models"][0], "id": "copy"})
                else:
                    evidence["declarations"].append(declaration(
                        FIXTURE_ROOT + ".unlisted_contract", definition=True, head="Solanalib.Contracts.Model"))
                with self.assertRaises(ValueError):
                    self.verify(document, evidence)

    def test_closed_exact_witnesses_reject_parameters_private_proofs_and_wrong_relations(self):
        for field, value in (("parameters", 1), ("universe_parameters", 1), ("is_private", True),
                             ("is_theorem", False), ("type_head", "Eq"),
                             ("conclusion_contract", FIXTURE_ROOT + ".outcome_contract"),
                             ("conclusion_reference", FIXTURE_ROOT + ".other_run"),
                             ("conclusion_sample", FIXTURE_ROOT + ".generic_sample")):
            with self.subTest(field=field):
                evidence = copy.deepcopy(self.evidence)
                witness = next(d for d in evidence["declarations"] if d["name"] == FIXTURE_ROOT + ".total_reference")
                witness[field] = value
                with self.assertRaises(ValueError):
                    self.verify(evidence=evidence)

    def test_family_execution_requires_the_same_named_sample_and_run(self):
        for field, value in (("conclusion_sample", None), ("conclusion_sample", FIXTURE_ROOT + ".other_sample"),
                             ("conclusion_reference", FIXTURE_ROOT + ".other_run"), ("parameters", 1)):
            with self.subTest(field=field, value=value):
                evidence = copy.deepcopy(self.evidence)
                witness = next(d for d in evidence["declarations"] if d["name"] == FIXTURE_ROOT + ".generic_has_execution")
                witness[field] = value
                with self.assertRaises(ValueError):
                    self.verify(evidence=evidence)

    def test_separate_family_binds_its_entire_contract_function_exactly(self):
        document, evidence = copy.deepcopy(self.document), copy.deepcopy(self.evidence)
        model = document["models"][2]
        family = FIXTURE_ROOT + ".generic_family"
        model["family"] = family
        indexed = declaration(family, definition=True, head="Solanalib.Contracts.Model.Family")
        indexed["family_contract"] = model["contract"]
        evidence["declarations"].append(indexed)
        document["abstractions"][0]["declarations"].append(family)
        for row in evidence["declarations"]:
            if row["name"] == model["contract"]:
                row.update(type_head="Solanalib.Contracts.Model", parameters=1)
            elif row["is_theorem"] and row["conclusion_contract"] == model["contract"]:
                row["conclusion_contract"] = family
        self.verify(document, evidence)
        for field, value in (("family_contract", None), ("family_contract", FIXTURE_ROOT + ".outcome_contract"),
                             ("parameters", 1), ("universe_parameters", 1), ("is_private", True)):
            with self.subTest(field=field, value=value):
                changed = copy.deepcopy(evidence)
                next(row for row in changed["declarations"] if row["name"] == family)[field] = value
                with self.assertRaises(ValueError):
                    self.verify(document, changed)
        # Registering the family must not remove the source-facing contract
        # from either the module review or the complete model inventory.
        changed = copy.deepcopy(document)
        changed["abstractions"][0]["declarations"].remove(model["contract"])
        with self.assertRaisesRegex(ValueError, "absent from reviewed declaration inventory"):
            self.verify(changed, evidence)

    def test_holds_and_family_cannot_omit_inhabited_execution(self):
        for index in (1, 2):
            for field in ("execution_witnesses", "satisfiability_witnesses"):
                with self.subTest(index=index, field=field):
                    document = copy.deepcopy(self.document)
                    document["models"][index][field] = []
                    with self.assertRaises(ValueError):
                        self.verify(document)

    def test_witnesses_cannot_hide_outside_the_reviewed_declaration_inventory(self):
        document = copy.deepcopy(self.document)
        document["abstractions"][0]["declarations"].remove(FIXTURE_ROOT + ".total_reference")
        with self.assertRaisesRegex(ValueError, "absent from reviewed declaration inventory"):
            self.verify(document)

    def test_source_contracts_are_closed_and_their_type_cannot_be_spoofed_by_a_name(self):
        for field, value in (("type_head", "Nat"), ("parameters", 1), ("universe_parameters", 1),
                             ("is_private", True), ("is_definition", False)):
            with self.subTest(field=field):
                evidence = copy.deepcopy(self.evidence)
                declaration = next(d for d in evidence["declarations"] if d["name"] == FIXTURE_ROOT + ".total_contract")
                declaration[field] = value
                with self.assertRaises(ValueError):
                    self.verify(evidence=evidence)

    def test_model_extent_is_separate_from_open_rust_status(self):
        self.verify()  # Complete mathematical models retain open Rust obligations.
        for kind, gaps, remaining, status in (("full", ["missing branch"], [], "open"),
                                               ("partial", [], [], "open"),
                                               ("full", [], [], "proved")):
            with self.subTest(kind=kind, status=status):
                document = copy.deepcopy(self.document)
                document["models"][0].update(kind=kind, model_gaps=gaps,
                                               remaining_requirements=remaining, rust_proof_status=status)
                with self.assertRaises(ValueError):
                    self.verify(document)
        document = copy.deepcopy(self.document)
        document["models"][0].update(kind="observation", model_gaps=["Only an observation projection."])
        self.verify(document)

    def test_closed_common_helpers_can_be_registered_as_supporting_models(self):
        document, evidence = copy.deepcopy(self.document), copy.deepcopy(self.evidence)
        helper = copy.deepcopy(document["models"][0])
        helper.update(id="common::helper", kind="supporting", contract=COMMON_ROOT + ".helperContract",
                      reference=COMMON_ROOT + ".helperRun", witnesses=[COMMON_ROOT + ".helperReference"],
                      satisfiability_witnesses=[COMMON_ROOT + ".helperSatisfiable"])
        document["models"].append(helper)
        for original, replacement in (("total_contract", "helperContract"), ("total_run", "helperRun"),
                                      ("total_reference", "helperReference"), ("total_satisfiable", "helperSatisfiable")):
            row = copy.deepcopy(next(d for d in evidence["declarations"] if d["name"] == FIXTURE_ROOT + "." + original))
            row.update(name=COMMON_ROOT + "." + replacement, module=COMMON_ROOT)
            if row["conclusion_contract"]:
                row["conclusion_contract"] = helper["contract"]
            if row["conclusion_reference"]:
                row["conclusion_reference"] = helper["reference"]
            evidence["declarations"].append(row)
            document["abstractions"][0]["declarations"].append(row["name"])
        result = self.verify(document, evidence)
        self.assertIn("common::helper", result["model_ids"])
        self.assertEqual(result["contracted_api_entries"], len(document["api"]))

    def test_api_cannot_claim_another_crate_or_production_theorem_as_a_client(self):
        for field, value in (("source_id", "unknown"), ("status", "proved"),
                             ("models", ["unregistered"]), ("clients", [FIXTURE_ROOT + ".total_reference"]),
                             ("contracts", [FIXTURE_ROOT + ".total_contract"]), ("line", False)):
            with self.subTest(field=field):
                document = copy.deepcopy(self.document)
                document["api"][0][field] = value
                with self.assertRaises(ValueError):
                    self.verify(document)
        document = copy.deepcopy(self.document)
        document["interfaces"][0]["crate"] = "different-sdk-1.0.0"
        with self.assertRaisesRegex(ValueError, "different source crate"):
            self.verify(document)

    def test_one_contract_can_retain_multiple_exact_source_releases(self):
        document = self.reviewed_alias_document()
        document["api"][-1]["inventory_bindings"] = [{
            "identity": "next-frozen-id", "source_name": "example_sdk::total",
            "package": {"name": "example-sdk", "version": "2.0.0"}}]
        result = self.verify(document)
        self.assertEqual(result["models_checked"], 3)
        self.assertEqual(result["contracted_api_entries"], 4)
        names = source_map.rust_identities(document)[document["models"][0]["id"]]
        self.assertEqual({row["crate_version"] for row in names}, {"1.0.0", "2.0.0"})
        document["api"][-1]["inventory_bindings"][0]["package"]["version"] = "1.0.0"
        with self.assertRaisesRegex(ValueError, "does not match the exact API source identity"):
            self.verify(document)

    def test_exact_binding_objects_reject_name_package_and_duplicate_conflicts(self):
        binding = {"identity": "frozen-id", "source_name": "example_sdk::total",
                   "package": {"name": "example-sdk", "version": "1.0.0"}}
        document = copy.deepcopy(self.document)
        document["api"][0]["inventory_bindings"] = [binding]
        self.assertEqual(self.verify(document)["inventory_bindings_checked"], 1)
        for change in ("name", "version", "duplicate", "other_api", "bare_id"):
            with self.subTest(change=change):
                changed = copy.deepcopy(document)
                if change == "name":
                    changed["api"][0]["inventory_bindings"][0]["source_name"] = "different"
                elif change == "version":
                    changed["api"][0]["inventory_bindings"][0]["package"]["version"] = "2.0.0"
                elif change == "duplicate":
                    changed["api"][0]["inventory_bindings"].append(copy.deepcopy(binding))
                elif change == "other_api":
                    changed["api"][1]["rust_names"].append(binding["source_name"])
                    changed["api"][1]["inventory_bindings"] = [copy.deepcopy(binding)]
                else:
                    changed["api"][0]["inventory_bindings"] = ["frozen-id"]
                with self.assertRaises(ValueError):
                    self.verify(changed)

    def reviewed_alias_document(self):
        document = copy.deepcopy(self.document)
        interface = copy.deepcopy(document["interfaces"][0])
        interface.update(id="reviewed-next", crate="example-sdk-2.0.0")
        document["interfaces"].append(interface)
        alias = copy.deepcopy(document["api"][0])
        alias.update(id="example-sdk@2.0.0::total", source_id="reviewed-next")
        document["api"].append(alias)
        document["applicability_scope"] = ["Synthetic source review; no Rust body proof."]
        document["applicability_sources"] = {"example": {
            "package": "example-sdk", "source": {
                "kind": "registry", "url": "https://github.com/rust-lang/crates.io-index", "revision": ""},
            "reviewed_on": "2026-11-11", "evidence": ["Synthetic immutable releases."],
            "releases": {version: {
                "archive_url": f"https://static.crates.io/crates/example-sdk/example-sdk-{version}.crate",
                "sha256": "a" * 64} for version in ["1.0.0", "2.0.0"]}}}
        document["applicability"] = {}
        for api in document["api"][:-1]:
            versions = ["1.0.0", "2.0.0"] if api is document["api"][0] else ["1.0.0"]
            name = api["rust_names"][0]
            document["applicability"][api["models"][0]] = {"profiles": [{
                "id": "direct", "source": "example", "releases": versions,
                "items": [{"releases": versions, "item": name, "implementation": name}],
                "target": [{"field": "os", "include": ["solana"], "reason": "Only this body is reviewed."}],
                "target_features": {"none": ["static-syscalls"], "reason": "Require the dynamic declaration."},
                "conditions": ["Keep the source interface an explicit assumption."],
                "argument": "The exact reviewed declaration reuses the same complete model.",
                "evidence": ["https://example.invalid/review/" + "a" * 40]}]}
        return document

    def test_reviewed_api_alias_reuses_a_model_without_changing_build_conditions(self):
        document = self.reviewed_alias_document()
        before = checker.normalized_applicability(document)
        result = self.verify(document)
        self.assertEqual(result["contracted_api_entries"], 4)
        self.assertEqual(checker.normalized_applicability(document), before)

    def test_manual_partial_source_metadata_does_not_admit_a_build(self):
        from applicability import lookup

        document = self.reviewed_alias_document()
        model = document["models"][0]
        model.update(kind="partial", model_gaps=["General source transport is not established."])
        document["applicability"][model["id"]] = {"profiles": []}
        before = checker.normalized_applicability(document)
        self.assertEqual(self.verify(document)["models_checked"], 3)
        self.assertEqual(checker.normalized_applicability(document), before)
        self.assertEqual(len(source_map.rust_identities(document)[model["id"]]), 2)
        for version in ("1.0.0", "2.0.0"):
            build = {"package": "example-sdk", "version": version,
                     "source": document["applicability_sources"]["example"]["source"],
                     "target": [{"field": "os", "value": "solana"}],
                     "features": [], "target_features": [], "dependencies": []}
            selected = lookup(before, build, [model["id"]])["models"][0]
            self.assertEqual(selected["status"], "unsupported")
            self.assertEqual(selected["identities"], [])
            self.assertEqual(selected["profiles"], [])
            self.assertEqual(selected["consumers"], [])

    def test_manual_partial_exception_requires_explicit_empty_direct_profiles(self):
        for change in ("full", "no_gap", "missing_record", "missing_applicability",
                       "consumers", "empty_names", "unreviewed_nonempty_profile",
                       "wrong_crate", "wrong_binding"):
            with self.subTest(change=change):
                document = self.reviewed_alias_document()
                model, alias = document["models"][0], document["api"][-1]
                reviewed = copy.deepcopy(document["applicability"][model["id"]])
                model.update(kind="partial", model_gaps=["General source transport is not established."])
                document["applicability"][model["id"]] = {"profiles": []}
                if change == "full":
                    model.update(kind="full", model_gaps=[])
                elif change == "no_gap":
                    model["model_gaps"] = []
                elif change == "missing_record":
                    document["applicability"].pop(model["id"])
                elif change == "missing_applicability":
                    document.pop("applicability")
                elif change == "consumers":
                    document["applicability"][model["id"]] = {
                        "consumers": [document["models"][1]["id"]]}
                elif change == "empty_names":
                    alias["rust_names"] = []
                elif change == "unreviewed_nonempty_profile":
                    document["applicability"][model["id"]] = reviewed
                    alias["rust_names"] = ["example_sdk::unreviewed"]
                elif change == "wrong_crate":
                    document["interfaces"][-1]["crate"] = "different-sdk-2.0.0"
                else:
                    alias["inventory_bindings"] = [{"identity": "frozen-id",
                        "source_name": "example_sdk::total",
                        "package": {"name": "example-sdk", "version": "1.0.0"}}]
                with self.assertRaises(ValueError):
                    self.verify(document)

    def test_partial_nonempty_profiles_still_require_the_reviewed_source_alias(self):
        document = self.reviewed_alias_document()
        document["models"][0].update(kind="partial", model_gaps=["A manual provider remains required."])
        before = checker.normalized_applicability(document)
        self.verify(document)
        self.assertEqual(checker.normalized_applicability(document), before)
        document["api"][-1]["rust_names"] = ["example_sdk::unreviewed"]
        with self.assertRaisesRegex(ValueError, "exact reviewed applicability profile"):
            self.verify(document)

    def test_api_alias_rejects_wrong_model_name_version_and_missing_profile(self):
        for change in ("model", "name", "second_name", "empty_names", "version", "single_release", "missing_profile",
                       "missing_applicability", "unreviewed_release", "reexport"):
            with self.subTest(change=change):
                document = self.reviewed_alias_document()
                alias = document["api"][-1]
                profile = document["applicability"][alias["models"][0]]["profiles"][0]
                if change == "model":
                    alias["models"] = document["api"][1]["models"]
                elif change == "name":
                    alias["rust_names"] = ["example_sdk::unreviewed"]
                elif change == "second_name":
                    alias["rust_names"].append("example_sdk::unreviewed")
                elif change == "empty_names":
                    alias["rust_names"] = []
                elif change == "version":
                    document["interfaces"][-1]["crate"] = "example-sdk-2.0.1"
                elif change == "single_release":
                    document["interfaces"][-1]["crate"] = "example-sdk-2.0.1"
                    document["api"] = document["api"][1:]
                elif change == "missing_profile":
                    document["applicability"][alias["models"][0]]["profiles"] = []
                elif change == "missing_applicability":
                    document.pop("applicability")
                elif change == "unreviewed_release":
                    document["applicability_sources"]["example"]["releases"].pop("2.0.0")
                else:
                    profile["identity_dependency"] = "other-sdk"
                    profile["dependencies"] = [{"package": "other-sdk", "releases": ["2.0.0"],
                                                "reason": "A different crate owns the reexport."}]
                with self.assertRaises(ValueError):
                    self.verify(document)


class FoundationEvidence(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="solanalib-specs-foundation-")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.package, self.foundation = root / "specs", root / "library"
        configure(self.package)
        shutil.copytree(ROOT / "packages/solanalib-contracts", self.foundation, ignore=shutil.ignore_patterns(".lake"))
        attach_foundation(self.package, self.foundation)
        self.modules = checker.discover(self.package)
        self.sources = self.modules | checker.foundation_sources(self.package)
        self.evidence = fake_evidence(self.sources)
        self.document = document_for(self.package, self.modules, self.evidence)

    def verify(self, document=None, evidence=None):
        (self.package / "source-map.json").write_text(json.dumps(document or self.document))
        return checker.verify_map(self.package, self.modules, evidence or self.evidence)

    def test_real_foundation_files_are_reviewed_without_entering_sdk_model_inventory(self):
        foundations = checker.foundation_sources(self.package)
        self.assertEqual(set(foundations), FOUNDATION_MODULES)
        self.assertTrue(set(self.modules).isdisjoint(foundations))
        for name, path in foundations.items():
            self.assertTrue(path.is_relative_to(self.foundation))
            self.assertEqual(self.evidence["source_sha256"][name], hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertIn(name, self.document["abstractions"][0]["modules"])
        self.assertEqual(self.verify()["models_checked"], 3)

    def test_missing_foundation_file_is_rejected_before_lean(self):
        for name in FOUNDATION_MODULES:
            with self.subTest(module=name):
                path = self.sources[name]
                original = path.read_bytes()
                path.unlink()
                with patch.object(checker.subprocess, "run") as lean:
                    with self.assertRaisesRegex(ValueError, "Missing or linked library foundation source"):
                        checker.audit(self.package, self.modules)
                    lean.assert_not_called()
                path.write_bytes(original)

    def test_changed_foundation_file_invalidates_both_audit_and_review_hashes(self):
        for name in FOUNDATION_MODULES:
            with self.subTest(module=name):
                path = self.sources[name]
                original = path.read_bytes()
                path.write_bytes(original + b"\n-- changed after the audit\n")
                with self.assertRaisesRegex(ValueError, "exact audited source identities"):
                    self.verify()
                changed = copy.deepcopy(self.evidence)
                changed["source_sha256"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
                with self.assertRaisesRegex(ValueError, "Reviewed specification content differs"):
                    self.verify(evidence=changed)
                path.write_bytes(original)

    def test_foundation_cannot_be_omitted_from_receipt_or_review(self):
        name = "Solanalib.Contracts.Callback"
        for field in ("audited_modules", "source_sha256", "review"):
            with self.subTest(field=field):
                evidence, document = copy.deepcopy(self.evidence), copy.deepcopy(self.document)
                if field == "audited_modules":
                    evidence[field].remove(name)
                elif field == "source_sha256":
                    evidence[field].pop(name)
                else:
                    document["abstractions"][0]["modules"].remove(name)
                    document["abstractions"][0]["model_sha256"].pop(name)
                with self.assertRaises(ValueError):
                    self.verify(document, evidence)

    def test_new_foundation_source_cannot_hide_outside_the_fixed_inventory(self):
        (self.foundation / "Solanalib/Contracts/Unimported.lean").write_text("module\n")
        with self.assertRaisesRegex(ValueError, "Unregistered library foundation source"):
            self.verify()


class FragmentedSourceMap(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="solanalib-specs-fragments-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        configure(self.package)
        self.modules = checker.discover(self.package)
        self.evidence = fake_evidence(self.modules)
        self.original = document_for(self.package, self.modules, self.evidence)
        interface = self.original["interfaces"][0]
        self.fragment = {
            "packages": {interface["crate"]: {
                "repository": interface["repository"], "revision": interface["revision"],
                "path_prefix": "sdk/"}},
            "interfaces": {interface["id"]: {
                key: value for key, value in interface.items()
                if key not in {"id", "repository", "revision", "path_in_repository"}}},
            "abstractions": {row["id"]: {
                "modules": row["model_sha256"], "source_ids": row["source_ids"],
                "argument": row["argument"], "limitations": row["limitations"]}
                for row in self.original["abstractions"]},
            "models": {row["id"]: {"contract": row["contract"], "witness_kind": row["witness_kind"]}
                       for row in self.original["models"]},
            "api": {row["id"]: {key: value for key, value in row.items()
                                if key not in {"id", "inventory_bindings", "models", "status"}}
                    for row in self.original["api"]},
        }
        self.index = {"schema_version": 3, "fragments": ["source-map/control.json"]}
        (self.package / "source-map").mkdir()
        self.save()

    def save(self):
        (self.package / "source-map.json").write_text(json.dumps(self.index))
        (self.package / "source-map/control.json").write_text(json.dumps(self.fragment))

    def verify(self):
        self.save()
        return checker.verify_map(self.package, self.modules, self.evidence)

    def test_defaults_preserve_every_exact_model_and_api_identity(self):
        expanded = source_map.load_source_map(self.package)
        self.assertEqual(expanded["interfaces"], self.original["interfaces"])
        self.assertEqual(expanded["models"], self.original["models"])
        self.assertEqual(expanded["api"], self.original["api"])
        self.assertEqual(self.verify()["models_checked"], 3)
        self.assertNotIn("declarations", expanded["abstractions"][0])

    def test_binding_package_is_derived_from_the_exact_source_crate(self):
        row = next(iter(self.fragment["api"].values()))
        row.pop("rust_names")
        row["bindings"] = {"project:123": "example_sdk::total"}
        self.save()
        expanded = source_map.load_source_map(self.package)["api"][0]
        self.assertEqual(expanded["inventory_bindings"], [{"identity": "project:123",
            "source_name": "example_sdk::total", "package": {"name": "example-sdk", "version": "1.0.0"}}])
        self.assertEqual(expanded["rust_names"], ["example_sdk::total"])
        self.assertEqual(self.verify()["inventory_bindings_checked"], 1)

    def test_rust_identities_use_the_exact_source_crate_and_called_item(self):
        rows = list(self.fragment["api"].values())
        rows[0]["rust_names"] = ["<example_sdk::Value<'a> as example_sdk::Read<&'a [u8]>>::read"]
        rows[1]["rust_names"] = ["example_sdk::io::<impl example_sdk::Read<u8> for u64>::read",
                                 "example_sdk::syscalls::<impl example_sdk::Value>::read"]
        self.save()
        expanded = source_map.load_source_map(self.package)
        identities = source_map.rust_identities(expanded)
        first, second, third = (row["id"] for row in expanded["api"])
        package = {"crate_name": "example-sdk", "crate_version": "1.0.0"}
        self.assertEqual(identities[first], [{**package, "item": "example_sdk::Read::read",
            "implementation": "<example_sdk::Value<'a> as example_sdk::Read<&'a [u8]>>::read"}])
        self.assertEqual(identities[second], [
            {**package, "item": "example_sdk::Read::read",
             "implementation": "example_sdk::io::<impl example_sdk::Read<u8> for u64>::read"},
            {**package, "item": "example_sdk::syscalls::<impl example_sdk::Value>::read",
             "implementation": "example_sdk::syscalls::<impl example_sdk::Value>::read"}])
        self.assertEqual(identities[third], [{**package, "item": "example_sdk::generic",
                                              "implementation": "example_sdk::generic"}])

    def test_rust_item_path_rejects_unsupported_name_forms(self):
        self.assertEqual(source_map.rust_item_path(
            "<<A as b::B>::C as d::D<fn(u8) -> u8>>::m"), "d::D::m")
        for name in ("<A as b::B>::m::{closure#0}", "<A as dyn b::B>::m", "<A as b::B::m"):
            with self.assertRaises(ValueError):
                source_map.rust_item_path(name)

    def test_module_hash_review_does_not_hide_an_unregistered_contract(self):
        self.fragment["models"].pop(next(iter(self.fragment["models"])))
        with self.assertRaisesRegex(ValueError, "Incomplete model inventory"):
            self.verify()

    def test_entire_reviewed_content_and_closed_witness_types_remain_checked(self):
        review = next(iter(self.fragment["abstractions"].values()))
        digest = review["modules"][COMMON_ROOT]
        review["modules"][COMMON_ROOT] = "0" * 64
        with self.assertRaisesRegex(ValueError, "Reviewed specification content differs"):
            self.verify()
        review["modules"][COMMON_ROOT] = digest
        witness = next(row for row in self.evidence["declarations"]
                       if row["name"] == FIXTURE_ROOT + ".total_reference")
        witness["parameters"] = 1
        with self.assertRaisesRegex(ValueError, "Model witness has parameters"):
            self.verify()

    def test_fragment_digest_seals_contents_as_well_as_selection(self):
        original = source_map.source_map_digest(self.package)
        next(iter(self.fragment["abstractions"].values()))["argument"] += " Updated review."
        self.save()
        self.assertNotEqual(source_map.source_map_digest(self.package), original)
        self.assertEqual(len(source_map.source_map_hashes(self.package)), 2)

    def test_rejects_duplicate_json_keys_and_conflicting_fragment_identities(self):
        path = self.package / "source-map/control.json"
        path.write_text('{"models": {}, "models": {}}')
        with self.assertRaisesRegex(ValueError, "Duplicate source-map key"):
            source_map.load_source_map(self.package)
        self.save()
        self.index["fragments"].append("source-map/other.json")
        (self.package / "source-map/other.json").write_text(json.dumps({
            "models": self.fragment["models"]}))
        self.save()
        with self.assertRaisesRegex(ValueError, "Duplicate models identity"):
            source_map.load_source_map(self.package)

    def test_rejects_unknown_defaults_links_paths_and_unregistered_fragments(self):
        model = next(iter(self.fragment["models"].values()))
        model["rust_proof_status"] = "proved"
        with self.assertRaisesRegex(ValueError, "Unknown model .* fields"):
            self.verify()
        model.pop("rust_proof_status")
        self.save()
        for name in ("../control.json", "source-map/../control.json", "/tmp/control.json"):
            with self.subTest(path=name):
                self.index["fragments"] = [name]
                self.save()
                with self.assertRaisesRegex(ValueError, "Invalid source-map fragment path"):
                    source_map.load_source_map(self.package)
        self.index["fragments"] = ["source-map/control.json"]
        self.save()
        extra = self.package / "source-map/ignored.json"
        extra.write_text("{}")
        with self.assertRaisesRegex(ValueError, "cover every available"):
            source_map.load_source_map(self.package)
        extra.unlink()
        target = self.package / "elsewhere.json"
        target.write_text("{}")
        fragment = self.package / "source-map/control.json"
        fragment.unlink()
        fragment.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "Missing or linked"):
            source_map.load_source_map(self.package)

    def test_missing_witness_override_cannot_be_replaced_by_an_assumption(self):
        model = next(iter(self.fragment["models"].values()))
        model["witness"] = FIXTURE_ROOT + ".missing_reference"
        with self.assertRaisesRegex(ValueError, "Unknown Model witness declaration"):
            self.verify()


# These are synthetic mathematical controls, never assessed Rust proofs. Copy
# only the maintained outcome/contract/family vocabulary into isolated builds.
LEAN_FIXTURE = r'''module
public import Solanalib.Contracts.Family
@[expose] public section
set_option autoImplicit false
namespace Solanalib.Specs.ExampleSdk
open Solanalib.Contracts.Model

def total_contract : Solanalib.Contracts.Model Nat Nat Nat :=
  .returning (fun _ _ => True) (fun before args value after => value = args ∧ after = before)
def total_run (before args : Nat) : Nat × Nat := (args, before)
theorem total_reference : total_contract.RealizedBy total_run := by
  intro before args _
  exact ⟨rfl, rfl⟩
theorem total_satisfiable : total_contract.Satisfiable := ⟨0, 0, trivial⟩

structure Operations where
  run : Nat → Nat → Nat × Nat
  other : Nat → Nat → Nat × Nat
def operations : Operations := ⟨total_run, total_run⟩
def other_operations : Operations := operations
def open_operations (_ : Nat) : Operations := operations
theorem projected_reference : total_contract.RealizedBy operations.run := total_reference

def outcome_contract : Solanalib.Contracts.Model Nat Nat Nat where
  requires := fun before _ => before = 0
  post := fun before args outcome => outcome = .returned args before
def outcome_run (before args : Nat) (outcome : Outcome Nat Nat Empty Empty) : Prop :=
  outcome = .returned args before
theorem outcome_reference : outcome_contract.Holds outcome_run := by
  intro before args outcome _ step
  exact step
theorem outcome_satisfiable : outcome_contract.Satisfiable := ⟨0, 0, rfl⟩
theorem outcome_has_execution : outcome_contract.HasExecution outcome_run :=
  ⟨0, 0, .returned 0 0, rfl, rfl⟩

def generic_contract : Family where
  Index := Type
  State := fun _ => Unit
  Args := id
  Value := id
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => {
    requires := fun _ _ => True
    post := fun before args outcome => outcome = .returned args before }
def generic_run : FamilyRun generic_contract :=
  fun _ before args outcome => outcome = .returned args before
def generic_sample : generic_contract.Index := Unit
theorem generic_reference : FamilyReference generic_contract generic_run := by
  intro index before args outcome _ step
  exact step
theorem generic_satisfiable : FamilySatisfiable generic_contract generic_sample :=
  ⟨(), (), trivial⟩
theorem generic_has_execution : FamilyHasExecution generic_contract generic_run generic_sample :=
  ⟨(), (), .returned () (), trivial, rfl⟩

def separate_contract (Value : Type) : Solanalib.Contracts.Model Unit Value Value where
  requires := fun _ _ => True
  post := fun before args outcome => outcome = .returned args before
def separate_family : Family where
  Index := Type
  State := fun _ => Unit
  Args := id
  Value := id
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun Value => separate_contract Value
def separate_run : FamilyRun separate_family :=
  fun _ before args outcome => outcome = .returned args before
def separate_sample : separate_family.Index := Nat
theorem separate_reference : FamilyReference separate_family separate_run := by
  intro Value before args outcome _ step
  exact step
theorem separate_satisfiable : FamilySatisfiable separate_family separate_sample := ⟨(), (3 : Nat), trivial⟩
theorem separate_has_execution : FamilyHasExecution separate_family separate_run separate_sample :=
  ⟨(), (3 : Nat), .returned (3 : Nat) (), trivial, rfl⟩

def other_run : Nat → Nat → Nat × Nat := total_run
theorem wrong_reference : total_contract.RealizedBy other_run := total_reference
theorem mention_only : total_contract = total_contract := rfl
theorem assumed (proof : total_contract.RealizedBy total_run) :
    total_contract.RealizedBy total_run := proof
theorem empty_parameter (impossible : Empty) : total_contract.RealizedBy total_run := nomatch impossible
theorem implicit_empty {impossible : Empty} : total_contract.RealizedBy total_run := nomatch impossible
theorem empty_satisfiability (impossible : Empty) : total_contract.Satisfiable := nomatch impossible
theorem universe_parameter.{u} :
    (let _marker : Sort (u + 1) := PUnit.{u + 1}; total_contract.RealizedBy total_run) := total_reference
private theorem hidden_reference : total_contract.RealizedBy total_run := total_reference

def other_sample : generic_contract.Index := Unit
theorem wrong_sample : FamilyHasExecution generic_contract generic_run other_sample := generic_has_execution
def empty_run : Nat → Nat → Outcome Nat Nat Empty Empty → Prop := fun _ _ _ => False
theorem empty_relation_holds : outcome_contract.Holds empty_run := by
  intro _ _ _ _ impossible
  exact False.elim impossible
theorem assumed_execution (proof : outcome_contract.HasExecution empty_run) :
    outcome_contract.HasExecution empty_run := proof
end Solanalib.Specs.ExampleSdk
'''


def lean_package(package, foundation=ROOT / "packages/solanalib-contracts"):
    configure(package)
    # Own the same neutral vocabulary in the single package of this fixture.
    # The source files are local; these controls need no network or SDK files.
    attach_foundation(package, foundation)
    configuration = package / "lakefile.toml"
    configuration.write_text(configuration.read_text().replace(
        f'[[lean_lib]]\nname = "{COMMON_ROOT}"\n',
        f'[[lean_lib]]\nname = "{COMMON_ROOT}"\nneeds = ["Solanalib.Contracts"]\n'))
    for relative in ("Solanalib/Specs/Core.lean", "Solanalib/Specs/Core/Outcome.lean", "Solanalib/Specs/Core/Family.lean"):
        target = package / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((SPECS / relative).read_bytes())
    (package / (FIXTURE_ROOT.replace(".", "/") + ".lean")).write_text(LEAN_FIXTURE)
    (package / (FIXTURE_TEST.replace(".", "/") + ".lean")).write_text('''module
public import Solanalib.Specs.ExampleSdk
@[expose] public section
namespace SolanalibTest.Specs.ExampleSdk
theorem total : Solanalib.Specs.ExampleSdk.total_run 3 4 = (4, 3) := rfl
theorem outcome : Solanalib.Specs.ExampleSdk.outcome_run 0 7 (.returned 7 0) := rfl
theorem generic : Solanalib.Specs.ExampleSdk.generic_run Nat () (7 : Nat) (.returned (7 : Nat) ()) := rfl
theorem separate : Solanalib.Specs.ExampleSdk.separate_run Nat () (7 : Nat) (.returned (7 : Nat) ()) := rfl
end SolanalibTest.Specs.ExampleSdk
''')


@unittest.skipUnless(os.environ.get("SOLANA_SPECS_INTEGRATION_TESTS") == "1",
                     "set SOLANA_SPECS_INTEGRATION_TESTS=1 to run isolated Lean package tests")
class ModuleResolution(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not shutil.which("lake"):
            raise RuntimeError("the pinned Lean toolchain is required for Solana integration tests")

    def run_lake(self, directory, *args):
        result = subprocess.run(["lake", *args], cwd=directory, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout)
        return result.stdout

    def test_audit_seals_actual_foundation_modules_and_rejects_later_changes(self):
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-foundation-audit-") as temporary:
            root = Path(temporary)
            package, foundation = root / "specs", root / "library"
            shutil.copytree(ROOT / "packages/solanalib-contracts", foundation, ignore=shutil.ignore_patterns(".lake"))
            lean_package(package, foundation)
            self.run_lake(package, "build")
            modules = checker.discover(package)
            evidence = checker.audit(package, modules)
            self.assertEqual(set(evidence["source_sha256"]) - set(modules), FOUNDATION_MODULES)
            self.assertEqual(set(evidence["audited_modules"]) - set(modules), FOUNDATION_MODULES)
            known = {row["name"]: row for row in evidence["declarations"]}
            self.assertEqual(known["Solanalib.Contracts.Model.Holds"]["module"], "Solanalib.Contracts")
            self.assertEqual(known["Solanalib.Contracts.Model.Callback.Run"]["module"], "Solanalib.Contracts.Callback")
            self.assertNotIn("Solanalib.Specs.Core.Holds", known)
            document = document_for(package, modules, evidence)
            (package / "source-map.json").write_text(json.dumps(document))
            self.assertEqual(checker.verify_map(package, modules, evidence)["models_checked"], 4)
            path = foundation / "Solanalib/Contracts/Callback.lean"
            path.write_bytes(path.read_bytes() + b"\n-- changed after the audit\n")
            with self.assertRaisesRegex(ValueError, "exact audited source identities"):
                checker.verify_map(package, modules, evidence)

    def test_audit_uses_actual_lean_contract_reference_and_sample_identities(self):
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-witness-control-") as temporary:
            package = Path(temporary)
            lean_package(package)
            self.run_lake(package, "build")
            modules = checker.discover(package)
            evidence = checker.audit(package, modules)
            document = document_for(package, modules, evidence)
            source_map = package / "source-map.json"
            source_map.write_text(json.dumps(document))
            checked = checker.verify_map(package, modules, evidence)
            self.assertEqual(checked["model_ids"], sorted(row["id"] for row in document["models"]))
            known = {d["name"]: d for d in evidence["declarations"]}
            self.assertEqual(known[FIXTURE_ROOT + ".universe_parameter"]["universe_parameters"], 1)
            self.assertEqual(known[FIXTURE_ROOT + ".universe_parameter"]["parameters"], 0)
            self.assertEqual(known[FIXTURE_ROOT + ".generic_reference"]["parameters"], 0)
            self.assertEqual(known[FIXTURE_ROOT + ".separate_family"]["family_contract"],
                             FIXTURE_ROOT + ".separate_contract")
            hidden = next(d["name"] for d in evidence["declarations"]
                          if d["name"].endswith(".hidden_reference"))
            projection = {"projection": FIXTURE_ROOT + ".Operations.run",
                          "receiver": FIXTURE_ROOT + ".operations"}
            self.assertEqual(known[FIXTURE_ROOT + ".projected_reference"]["conclusion_reference"], projection)
            projected = copy.deepcopy(document)
            projected["models"][0].update(reference=projection,
                                         witnesses=[FIXTURE_ROOT + ".projected_reference"])
            source_map.write_text(json.dumps(projected))
            checker.verify_map(package, modules, evidence)
            # Definitional equality is insufficient: the exact reviewed field
            # and receiver must be the ones named by the closed witness.
            for field, replacement, message in (
                ("receiver", ".other_operations", "does not establish"),
                ("projection", ".Operations.other", "does not establish"),
                ("receiver", ".open_operations", "closed monomorphic receiver"),
                ("projection", ".total_run", "closed monomorphic receiver"),
            ):
                with self.subTest(projection=field, replacement=replacement):
                    changed = copy.deepcopy(projected)
                    changed["models"][0]["reference"][field] = FIXTURE_ROOT + replacement
                    source_map.write_text(json.dumps(changed))
                    with self.assertRaisesRegex(ValueError, message):
                        checker.verify_map(package, modules, evidence)
            controls = [
                (0, "witnesses", "total_contract", "not a theorem"),
                (0, "witnesses", "outcome_reference", "does not establish"),
                (0, "witnesses", "wrong_reference", "does not establish"),
                (0, "witnesses", "mention_only", "does not establish"),
                (0, "witnesses", "assumed", "has parameters"),
                (0, "witnesses", "empty_parameter", "has parameters"),
                (0, "witnesses", "implicit_empty", "has parameters"),
                (0, "witnesses", "universe_parameter", "has parameters"),
                (0, "satisfiability_witnesses", "empty_satisfiability", "has parameters"),
                (0, "satisfiability_witnesses", "total_reference", "does not establish"),
                (2, "execution_witnesses", "wrong_sample", "does not establish"),
            ]
            for index, field, name, message in controls:
                with self.subTest(control=name):
                    changed = copy.deepcopy(document)
                    changed["models"][index][field] = [FIXTURE_ROOT + "." + name]
                    source_map.write_text(json.dumps(changed))
                    with self.assertRaisesRegex(ValueError, message):
                        checker.verify_map(package, modules, evidence)
            changed = copy.deepcopy(document)
            changed["models"][0]["witnesses"] = [hidden]
            source_map.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "not public"):
                checker.verify_map(package, modules, evidence)
            # Holds over an empty relation is valid partial correctness. Its
            # only proposed execution witness assumes the desired conclusion.
            changed = copy.deepcopy(document)
            changed["models"][1].update(reference=FIXTURE_ROOT + ".empty_run",
                witnesses=[FIXTURE_ROOT + ".empty_relation_holds"],
                execution_witnesses=[FIXTURE_ROOT + ".assumed_execution"])
            source_map.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "has parameters"):
                checker.verify_map(package, modules, evidence)

    def test_family_cannot_claim_a_different_contract_function_with_the_same_postcondition(self):
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-family-binding-") as temporary:
            package = Path(temporary)
            lean_package(package)
            source = package / (FIXTURE_ROOT.replace(".", "/") + ".lean")
            source.write_text(source.read_text().replace(
                "contract := fun Value => separate_contract Value",
                "contract := fun _ => { requires := fun _ _ => True\n"
                "                         post := fun before args outcome => outcome = .returned args before }"))
            self.run_lake(package, "build")
            modules = checker.discover(package)
            evidence = checker.audit(package, modules)
            document = document_for(package, modules, evidence)
            (package / "source-map.json").write_text(json.dumps(document))
            with self.assertRaisesRegex(ValueError, "does not bind exactly the registered source contract"):
                checker.verify_map(package, modules, evidence)

    def test_audit_refuses_stale_compiled_sources(self):
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-stale-control-") as temporary:
            package = Path(temporary)
            lean_package(package)
            self.run_lake(package, "build")
            source = package / (FIXTURE_ROOT.replace(".", "/") + ".lean")
            # A stale OLean omits this deliberately invalid synthetic axiom.
            source.write_text(source.read_text() + "\naxiom unsafeStaleWitness : False\n")
            with self.assertRaisesRegex(ValueError, "Specification axiom audit failed"):
                checker.audit(package, checker.discover(package))

    def test_axiom_audit_rejects_an_unused_private_proof(self):
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-axiom-control-") as temporary:
            package = Path(temporary)
            configure(package)
            path = package / FIXTURE_ROOT.replace(".", "/") / "Unused.lean"
            path.parent.mkdir(parents=True, exist_ok=True)
            # The root never imports this invalid synthetic fixture.
            path.write_text('''module
@[expose] public section
private axiom unsafeWitness : False
private theorem unusedProof : False := unsafeWitness
''')
            self.run_lake(package, "build")
            with self.assertRaisesRegex(ValueError, "Unexpected axiom.*unsafeWitness"):
                checker.audit(package, checker.discover(package))

    def test_sdk_libraries_and_stale_artifacts_do_not_shadow_other_packages(self):
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-packages-") as temporary:
            root = Path(temporary)
            specs = root / "specs"
            lean_package(specs)
            self.run_lake(specs, "build")
            client = root / "client"
            library = client / "toolchain/ExternalRuntime/core"
            library.mkdir(parents=True)
            (client / "lean-toolchain").write_bytes((ROOT / "lean-toolchain").read_bytes())
            (client / "lakefile.toml").write_text('''name = "resolution-client"
defaultTargets = ["Smoke"]
[[require]]
name = "spec-audit-control"
path = "../specs"
[[require]]
name = "resolution-external-runtime"
path = "toolchain"
[[require]]
name = "resolution-other-sdk"
path = "other-sdk"
[[lean_lib]]
name = "Smoke"
[[lean_lib]]
name = "ModelContract"
''')
            (client / "ModelContract.lean").write_text('''module
@[expose] public section
structure ModelContract where
  marker : Nat
''')
            (client / "toolchain/lakefile.toml").write_text('''name = "resolution-external-runtime"
[[lean_lib]]
name = "ExternalRuntime"
globs = ["ExternalRuntime.core.*"]
''')
            (library / "PackageResolutionSentinel.lean").write_text('''module
@[expose] public section
namespace ExternalRuntime.core
def packageResolutionSentinel : Nat := 7
end ExternalRuntime.core
''')
            other_sdk = client / "other-sdk"
            other_sdk.mkdir()
            (other_sdk / "lakefile.toml").write_text('''name = "resolution-other-sdk"
[[lean_lib]]
name = "other_sdk"
''')
            (other_sdk / "other_sdk.lean").write_text('''module
@[expose] public section
namespace other_sdk
def versionResolutionSentinel : Nat := 20
end other_sdk
''')
            imports = ("public import Solanalib.Specs.ExampleSdk\npublic import ModelContract\n"
                       "public import other_sdk\npublic import ExternalRuntime.core.PackageResolutionSentinel\n")
            (client / "Smoke.lean").write_text("module\n" + imports + '''@[expose] public section
example : ExternalRuntime.core.packageResolutionSentinel = 7 := rfl
example : (⟨7⟩ : ModelContract).marker = 7 := rfl
example : Solanalib.Specs.ExampleSdk.total_run 1 2 = (2, 1) := rfl
example : other_sdk.versionResolutionSentinel = 20 := rfl
''')
            # No source in the spec package may acquire ownership of ExternalRuntime,
            # even if an earlier build left this empty output directory behind.
            (specs / ".lake/build/lib/lean/ExternalRuntime").mkdir(parents=True, exist_ok=True)
            self.run_lake(client, "build")


class SourceCoverage(unittest.TestCase):
    def sdk_document(self, content):
        return {"interfaces": [{
            "id": "account", "crate": "example-1.0.0", "path": "src/lib.rs",
            "repository": "https://github.com/example/sdk", "revision": "1" * 40,
            "path_in_repository": "account/src/lib.rs", "sha256": hashlib.sha256(content).hexdigest(),
        }], "api": [{"id": "read", "source_id": "account", "line": 2,
                      "anchor_text": "pub fn read() {}"}]}

    def test_fetched_sdk_is_hashed_and_each_anchor_is_checked(self):
        content = b"// reviewed SDK\npub fn read() {}\n"
        document = self.sdk_document(content)
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-sdk-control-") as temporary:
            registry = Path(temporary)
            with patch("check_solana_specs.urllib.request.urlopen", return_value=io.BytesIO(content)) as fetch:
                checker.fetch_sdk(document, registry)
            fetch.assert_called_once_with(
                "https://raw.githubusercontent.com/example/sdk/" + "1" * 40 + "/account/src/lib.rs", timeout=60)
            self.assertEqual(checker.verify_sources(document, registry), (1, 1))
            document["api"][0]["line"] = 1
            with self.assertRaisesRegex(ValueError, "API source anchor changed"):
                checker.verify_sources(document, registry)
            document["api"][0]["line"] = 200
            with self.assertRaisesRegex(ValueError, "API source anchor changed"):
                checker.verify_sources(document, registry)

    def test_changed_sdk_cannot_be_fetched_or_counted_as_reviewed(self):
        content = b"// reviewed SDK\npub fn read() {}\n"
        document = self.sdk_document(content)
        with tempfile.TemporaryDirectory(prefix="solanalib-specs-sdk-changed-") as temporary:
            registry = Path(temporary)
            with patch("check_solana_specs.urllib.request.urlopen", return_value=io.BytesIO(content + b"// change\n")):
                with self.assertRaisesRegex(ValueError, "Reviewed SDK source differs"):
                    checker.fetch_sdk(document, registry)
            source = registry / "example-1.0.0/src/lib.rs"
            self.assertFalse(source.exists())
            source.parent.mkdir(parents=True)
            source.write_bytes(content + b"// change\n")
            with self.assertRaisesRegex(ValueError, "Reviewed SDK source differs"):
                checker.verify_sources(document, registry)

    def test_mutable_source_ref_is_rejected_before_network_access(self):
        document = self.sdk_document(b"// reviewed SDK\npub fn read() {}\n")
        document["interfaces"][0]["revision"] = "main"
        with patch("check_solana_specs.urllib.request.urlopen") as fetch:
            with self.assertRaisesRegex(ValueError, "Non-immutable SDK source"):
                checker.fetch_sdk(document, Path("unused"))
            fetch.assert_not_called()

    def test_duplicate_interfaces_and_traversal_are_rejected_before_fetch(self):
        original = self.sdk_document(b"// reviewed SDK\npub fn read() {}\n")
        for change in ("duplicate", "crate", "path", "repository_path"):
            with self.subTest(change=change):
                document = copy.deepcopy(original)
                if change == "duplicate":
                    document["interfaces"].append(copy.deepcopy(document["interfaces"][0]))
                elif change == "repository_path":
                    document["interfaces"][0]["path_in_repository"] = "../../escape.rs"
                else:
                    document["interfaces"][0][change] = "../../escape"
                with patch("check_solana_specs.urllib.request.urlopen") as fetch:
                    with self.assertRaises(ValueError):
                        checker.fetch_sdk(document, Path("unused"))
                    fetch.assert_not_called()


if __name__ == "__main__":
    unittest.main()
