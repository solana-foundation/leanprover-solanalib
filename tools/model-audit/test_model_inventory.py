"""Nested model sources must enter source review and the complete proof audit."""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))


def load(name):
    spec = importlib.util.spec_from_file_location(name, TOOLS / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


INVENTORY = load("runtime_inventory")
SOURCE_MAP = load("runtime_source_map")
LAKEFILE = '''name = "model-fixture"
[[lean_lib]]
name = "Solanalib.Runtime"
globs = ["Solanalib.Runtime", "Solanalib.Runtime.+"]
'''


class ModelInventoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "lakefile.toml").write_text(LAKEFILE)
        (self.root / "Solanalib").mkdir()
        (self.root / "Solanalib/Runtime.lean").write_text("import Solanalib.Runtime.Example\n")
        (self.root / "Solanalib/Runtime").mkdir(parents=True)
        self.example = self.root / "Solanalib/Runtime/Example.lean"
        self.example.write_text("namespace Solanalib.Runtime\ndef example : Nat := 0\nend Solanalib.Runtime\n")

    def add_nested(self):
        nested = self.root / "Solanalib/Runtime/Review/Extra.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("namespace Solanalib.Runtime\ntheorem extra_identity : 1 + 1 = 2 := rfl\nend Solanalib.Runtime\n")
        return nested

    def test_recursive_inventory_includes_an_unimported_nested_module(self):
        self.add_nested()
        unrelated = self.root / "SolanalibTest/Runtime/Extra.lean"
        unrelated.parent.mkdir(parents=True)
        unrelated.write_text("theorem test_only : True := True.intro\n")
        self.assertEqual(INVENTORY.model_modules(self.root),
                         ["Solanalib.Runtime", "Solanalib.Runtime.Example", "Solanalib.Runtime.Review.Extra"])

    def test_nested_addition_invalidates_existing_source_correspondence(self):
        manifest = self.root / "sources.json"
        manifest.write_text(json.dumps({
            "entries": [{"id": "runtime"}],
            "correspondence": [{
                "id": "example", "modules": ["Solanalib.Runtime.Example"],
                "model_sha256": {"Solanalib.Runtime.Example": hashlib.sha256(
                    self.example.read_bytes()).hexdigest()},
                "source_ids": ["runtime"], "declarations": ["Solanalib.Runtime.example"],
                "treatment": "source-read", "section": "example",
                "argument": "The source returns zero.", "assumptions": [],
                "limitations": ["No full source refinement."]}]}))
        declarations = [{"name": "Solanalib.Runtime.example", "module": "Solanalib.Runtime.Example"}]

        def verify():
            sources = {str(path.relative_to(self.root)): path.read_text()
                       for path in INVENTORY.model_files(self.root)}
            return SOURCE_MAP.verify_correspondence(manifest, sources, declarations)

        self.assertEqual(verify()["modules"], 1)
        self.add_nested()
        with self.assertRaisesRegex(ValueError, "Incomplete correspondence coverage"):
            verify()

    def test_export_imports_nested_modules_without_changing_the_aggregate(self):
        aggregate = (self.root / "Solanalib/Runtime.lean").read_bytes()
        self.add_nested()
        template = "-- Plain audit\nimport Solanalib.Runtime\nimport Lean\n"
        rendered = INVENTORY.render_export(self.root, template)
        self.assertIn("import Solanalib.Runtime.Review.Extra\n", rendered)
        self.assertEqual((self.root / "Solanalib/Runtime.lean").read_bytes(), aggregate)

    def test_missing_nested_audit_module_is_rejected(self):
        self.add_nested()
        complete = {"audited_modules": INVENTORY.model_modules(self.root)}
        INVENTORY.check_audit_modules(self.root, complete)
        with self.assertRaisesRegex(ValueError, "every configured model module"):
            INVENTORY.check_audit_modules(self.root, {
                "audited_modules": ["Solanalib.Runtime", "Solanalib.Runtime.Example"]})

    def test_changed_lake_selection_requires_inventory_support(self):
        for changed in (
            LAKEFILE.replace('"Solanalib.Runtime.+"', '"Solanalib.Runtime.*"'),
            'srcDir = "src"\n' + LAKEFILE,
            LAKEFILE + 'srcDir = "src"\n',
            LAKEFILE + 'roots = ["DifferentRoot"]\n',
        ):
            with self.subTest(configuration=changed):
                (self.root / "lakefile.toml").write_text(changed)
                with self.assertRaisesRegex(ValueError, "configuration changed"):
                    INVENTORY.model_files(self.root)

    def test_lean_configuration_cannot_override_the_reviewed_toml(self):
        (self.root / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage modelFixture\n"
            "lean_lib Solanalib.Runtime where\n  srcDir := \"OtherSources\"\n")
        with self.assertRaisesRegex(ValueError, r"lakefile\.lean"):
            INVENTORY.model_files(self.root)

    def test_symlinked_lean_configuration_is_rejected(self):
        (self.root / "alternate.lean").write_text("import Lake\n")
        (self.root / "lakefile.lean").symlink_to("alternate.lean")
        with self.assertRaisesRegex(ValueError, r"lakefile\.lean"):
            INVENTORY.model_files(self.root)

    def test_dangling_lean_configuration_symlink_is_rejected(self):
        (self.root / "lakefile.lean").symlink_to("missing.lean")
        with self.assertRaisesRegex(ValueError, r"lakefile\.lean"):
            INVENTORY.model_files(self.root)

    def test_lean_configuration_is_rejected_before_parsing_toml(self):
        (self.root / "lakefile.lean").write_text("import Lake\n")
        (self.root / "lakefile.toml").write_text("invalid = [\n")
        with self.assertRaisesRegex(ValueError, r"lakefile\.lean"):
            INVENTORY.model_files(self.root)

    def test_export_quotes_each_module_component(self):
        self.add_nested()
        for name in ("Review.Extra.lean", "Space Name.lean", "λ.lean"):
            (self.root / "Solanalib/Runtime" / name).write_text("namespace Solanalib.Runtime\nend Solanalib.Runtime\n")
        aggregate = (self.root / "Solanalib/Runtime.lean").read_bytes()
        rendered = INVENTORY.render_export(self.root, "import Solanalib.Runtime\nimport Lean\n")
        for name in ("Solanalib.Runtime.Review.Extra", "Solanalib.Runtime.«Review.Extra»",
                     "Solanalib.Runtime.«Space Name»", "Solanalib.Runtime.«λ»"):
            self.assertIn(f"import {name}\n", rendered)
        self.assertEqual((self.root / "Solanalib/Runtime.lean").read_bytes(), aggregate)

    def test_audit_accepts_equivalent_quoted_and_unicode_names(self):
        self.add_nested()
        for name in ("Review.Extra.lean", "λ.lean"):
            (self.root / "Solanalib/Runtime" / name).write_text("namespace Solanalib.Runtime\nend Solanalib.Runtime\n")
        INVENTORY.check_audit_modules(self.root, {"audited_modules": [
            "«Solanalib».«Runtime»", "Solanalib.Runtime.«Example»", "Solanalib.Runtime.λ",
            "Solanalib.Runtime.«Review.Extra»", "«Solanalib».«Runtime».«Review».Extra",
        ]})

    def test_literal_dot_cannot_be_substituted_with_a_nested_audit_module(self):
        (self.root / "Solanalib/Runtime/Review.Extra.lean").write_text(
            "namespace Solanalib.Runtime\nend Solanalib.Runtime\n")
        with self.assertRaisesRegex(ValueError, "every configured model module"):
            INVENTORY.check_audit_modules(self.root, {"audited_modules": [
                "Solanalib.Runtime", "Solanalib.Runtime.Example", "Solanalib.Runtime.Review.Extra",
            ]})

    def test_duplicate_normalized_audit_names_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "every configured model module"):
            INVENTORY.check_audit_modules(self.root, {"audited_modules": [
                "Solanalib.Runtime", "Solanalib.Runtime.Example", "Solanalib.Runtime.«Example»",
            ]})

    def test_directory_symlink_cannot_hide_a_module_from_discovery(self):
        shared = self.root / "Shared"
        shared.mkdir(parents=True)
        (shared / "Extra.lean").write_text("axiom hidden : False\n")
        (self.root / "Solanalib/Runtime/Linked").symlink_to("../../Shared", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "Symbolic links in model sources"):
            INVENTORY.model_files(self.root)

    def test_source_file_symlink_is_rejected(self):
        target = self.root / "Shared.lean"
        target.write_text("axiom hidden : False\n")
        (self.root / "Solanalib/Runtime/Linked.lean").symlink_to("../../Shared.lean")
        with self.assertRaisesRegex(ValueError, "Symbolic links in model sources"):
            INVENTORY.model_files(self.root)

    def test_cyclic_directory_symlink_is_rejected_without_recursing(self):
        (self.root / "Solanalib/Runtime/Loop").symlink_to(".", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "Symbolic links in model sources"):
            INVENTORY.model_files(self.root)


class ModuleNameTests(unittest.TestCase):
    def test_paths_preserve_components_and_strip_only_the_final_suffix(self):
        for path, expected in (
            ("Solanalib/Runtime/Example.lean", "Solanalib.Runtime.Example"),
            ("Solanalib/Runtime/Proof'.lean", "Solanalib.Runtime.Proof'"),
            ("Solanalib/Runtime/Space Name.lean", "Solanalib.Runtime.«Space Name»"),
            ("Solanalib/Runtime/λ.lean", "Solanalib.Runtime.«λ»"),
            ("Solanalib/Runtime/Review.Extra.lean", "Solanalib.Runtime.«Review.Extra»"),
            ("Solanalib/Runtime/Review/Extra.lean", "Solanalib.Runtime.Review.Extra"),
            ("Solanalib/Runtime/Review.lean/Extra.lean", "Solanalib.Runtime.«Review.lean».Extra"),
            ("Solanalib/Runtime/Trace.lean.lean", "Solanalib.Runtime.«Trace.lean»"),
        ):
            for value in (path, Path(path)):
                with self.subTest(path=value):
                    self.assertEqual(INVENTORY.module_name(value), expected)

    def test_normalization_preserves_quoted_component_identity(self):
        for name, expected in (
            ("«Solanalib».«Runtime».«Example»", "Solanalib.Runtime.Example"),
            ("Solanalib.Runtime.λ", "Solanalib.Runtime.«λ»"),
            ("Solanalib.Runtime.«λ»", "Solanalib.Runtime.«λ»"),
            ("Solanalib.Runtime.«Review.Extra»", "Solanalib.Runtime.«Review.Extra»"),
            ("Solanalib.Runtime.«Review».«Extra»", "Solanalib.Runtime.Review.Extra"),
            ("Solanalib.Runtime.«Space Name».λ", "Solanalib.Runtime.«Space Name».«λ»"),
        ):
            with self.subTest(name=name):
                self.assertEqual(INVENTORY.normalize_module(name), expected)

    def test_module_path_map_keeps_literal_dot_and_nested_paths_distinct(self):
        paths = ["Solanalib/Runtime/Review.Extra.lean", "Solanalib/Runtime/Review/Extra.lean",
                 "Solanalib/Runtime/Review.lean/Extra.lean"]
        self.assertEqual(INVENTORY.module_paths(paths), {
            "Solanalib.Runtime.«Review.Extra»": "Solanalib/Runtime/Review.Extra.lean",
            "Solanalib.Runtime.Review.Extra": "Solanalib/Runtime/Review/Extra.lean",
            "Solanalib.Runtime.«Review.lean».Extra": "Solanalib/Runtime/Review.lean/Extra.lean",
        })


class CorrespondenceNameTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.manifest = Path(temporary.name) / "sources.json"
        self.set_modules([
            ("Solanalib/Runtime/Example.lean", "Solanalib.Runtime.Example", "Solanalib.Runtime.example"),
        ])

    def set_modules(self, modules):
        self.sources = {"Solanalib/Runtime.lean": "namespace Solanalib.Runtime\nend Solanalib.Runtime\n"}
        self.rows = []
        self.declarations = []
        for index, (path, module, declaration) in enumerate(modules):
            self.sources[path] = f"def {declaration} : Nat := {index}\n"
            self.rows.append({
                "id": f"argument-{index}", "modules": [module],
                "model_sha256": {module: hashlib.sha256(self.sources[path].encode()).hexdigest()},
                "source_ids": ["runtime"], "declarations": [declaration],
                "treatment": "source-read", "section": "example",
                "argument": "The source returns the declared natural number.",
                "assumptions": [], "limitations": ["No full source refinement."],
            })
            self.declarations.append({"name": declaration, "module": module})

    def verify(self):
        self.manifest.write_text(json.dumps({
            "entries": [{"id": "runtime"}], "correspondence": self.rows,
        }))
        return SOURCE_MAP.verify_correspondence(self.manifest, self.sources, self.declarations)

    def set_distinct_dot_modules(self):
        self.set_modules([
            ("Solanalib/Runtime/Review.Extra.lean", "Solanalib.Runtime.«Review.Extra»", "Solanalib.Runtime.literal"),
            ("Solanalib/Runtime/Review/Extra.lean", "Solanalib.Runtime.Review.Extra", "Solanalib.Runtime.nested"),
        ])

    def test_quoted_paths_and_literal_dots_keep_distinct_correspondences(self):
        self.set_modules([
            ("Solanalib/Runtime/Review.Extra.lean", "Solanalib.Runtime.«Review.Extra»", "Solanalib.Runtime.literal"),
            ("Solanalib/Runtime/Review/Extra.lean", "Solanalib.Runtime.Review.Extra", "Solanalib.Runtime.nested"),
            ("Solanalib/Runtime/Space Name.lean", "Solanalib.Runtime.«Space Name»", "Solanalib.Runtime.spaced"),
            ("Solanalib/Runtime/λ.lean", "Solanalib.Runtime.«λ»", "Solanalib.Runtime.unicode"),
        ])
        self.declarations[-1]["module"] = "Solanalib.Runtime.λ"
        result = self.verify()
        self.assertEqual(result["modules"], 4)
        self.assertEqual(result["referenced_declarations"], 4)
        self.assertTrue(result["reviewed_model_hashes_checked"])

    def test_equivalent_quoted_names_match_modules_hashes_and_declarations(self):
        self.rows[0]["modules"] = ["«Solanalib».«Runtime».Example"]
        digest = self.rows[0]["model_sha256"].pop("Solanalib.Runtime.Example")
        self.rows[0]["model_sha256"] = {"Solanalib.Runtime.«Example»": digest}
        self.declarations[0]["module"] = "«Solanalib».«Runtime».«Example»"
        self.assertEqual(self.verify()["modules"], 1)

    def test_duplicate_normalized_modules_in_one_argument_are_rejected(self):
        self.rows[0]["modules"].append("«Solanalib».«Runtime».«Example»")
        with self.assertRaisesRegex(ValueError, "Invalid correspondence modules"):
            self.verify()

    def test_duplicate_normalized_modules_across_arguments_are_rejected(self):
        duplicate = {**self.rows[0], "id": "duplicate",
                     "modules": ["«Solanalib».«Runtime».«Example»"]}
        self.rows.append(duplicate)
        with self.assertRaisesRegex(ValueError, "Repeated correspondence module"):
            self.verify()

    def test_duplicate_normalized_hash_keys_are_rejected(self):
        self.rows[0]["model_sha256"]["«Solanalib».«Runtime».«Example»"] = (
            self.rows[0]["model_sha256"]["Solanalib.Runtime.Example"])
        with self.assertRaisesRegex(ValueError, "Missing reviewed model identity"):
            self.verify()

    def test_literal_dot_module_cannot_use_the_hash_of_a_nested_module(self):
        self.set_distinct_dot_modules()
        self.rows[0]["model_sha256"]["Solanalib.Runtime.«Review.Extra»"] = (
            self.rows[1]["model_sha256"]["Solanalib.Runtime.Review.Extra"])
        with self.assertRaisesRegex(ValueError, "Reviewed model content differs"):
            self.verify()

    def test_literal_dot_hash_identity_cannot_be_replaced_by_a_nested_name(self):
        self.set_distinct_dot_modules()
        digest = self.rows[0]["model_sha256"].pop("Solanalib.Runtime.«Review.Extra»")
        self.rows[0]["model_sha256"] = {"Solanalib.Runtime.Review.Extra": digest}
        with self.assertRaisesRegex(ValueError, "Missing reviewed model identity"):
            self.verify()

    def test_literal_dot_declaration_cannot_be_assigned_to_a_nested_module(self):
        self.set_distinct_dot_modules()
        self.declarations[0]["module"] = "Solanalib.Runtime.Review.Extra"
        with self.assertRaisesRegex(ValueError, "Unknown or misplaced correspondence declaration"):
            self.verify()


if __name__ == "__main__":
    unittest.main()
