"""Run the actual model exporter on isolated Lean dependency-audit controls."""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "packages/solanalib-runtime"
EXPORTER = Path(__file__).with_name("AuditRuntime.lean.in")
SPEC = importlib.util.spec_from_file_location(
    "runtime_inventory", Path(__file__).with_name("runtime_inventory.py"))
INVENTORY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(INVENTORY)


class ModelAxiomAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.toolchain = (ROOT / "lean-toolchain").read_text().strip()
        cls.environment = os.environ.copy()
        cls.environment["ELAN_TOOLCHAIN"] = cls.toolchain
        for variable in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
            cls.environment.pop(variable, None)
        elan = shutil.which("elan")
        resolved = (subprocess.run([elan, "which", "lake"], cwd=MODEL,
                                   env=cls.environment, text=True, capture_output=True,
                                   timeout=30) if elan else None)
        if resolved is None or resolved.returncode:
            detail = resolved.stderr.strip() if resolved else "elan is not on PATH"
            raise RuntimeError(
                f"The installed pinned Lean toolchain {cls.toolchain} is required "
                f"for the model axiom-audit controls; no control was skipped. {detail}"
            )
        cls.lake = resolved.stdout.strip()

    def export_fixture(self, body, *, extra_sources=None, render_all=False):
        with tempfile.TemporaryDirectory(prefix="model-axiom-audit-") as temporary:
            package = Path(temporary)
            (package / "Solanalib/Runtime").mkdir(parents=True)
            (package / "lean-toolchain").write_text(self.toolchain + "\n")
            (package / "lakefile.toml").write_text(
                'name = "model-axiom-audit"\ndefaultTargets = ["Solanalib.Runtime"]\n\n'
                '[[lean_lib]]\nname = "AuditDependency"\n\n'
                '[[lean_lib]]\nname = "Solanalib.Runtime"\n'
                'globs = ["Solanalib.Runtime", "Solanalib.Runtime.+"]\n'
            )
            # Keep the forbidden dependency outside the model module prefix. A
            # direct-axiom rejection must not mask missing proof-body traversal.
            (package / "AuditDependency.lean").write_text(
                "module\n@[expose] public section\n"
                "namespace AuditDependency\naxiom forbidden : False\n"
                "end AuditDependency\n"
            )
            (package / "Solanalib/Runtime.lean").write_text(
                "module\npublic import Solanalib.Runtime.Fixture\n"
            )
            (package / "Solanalib/Runtime/Fixture.lean").write_text(
                "module\npublic import AuditDependency\npublic import Lean\n"
                "@[expose] public section\nnamespace Solanalib.Runtime.AuditFixture\n"
                + textwrap.dedent(body).strip() + "\nend Solanalib.Runtime.AuditFixture\n"
            )
            for name, source in (extra_sources or {}).items():
                path = package / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(textwrap.dedent(source).strip() + "\n")
            template = EXPORTER.read_text()
            if render_all:
                template = INVENTORY.render_export(package, template)
            (package / "Export.lean").write_text(template)
            built = subprocess.run([self.lake, "build"], cwd=package,
                                   env=self.environment, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   timeout=120)
            self.assertEqual(built.returncode, 0, built.stdout)
            result = subprocess.run(
                [self.lake, "--quiet", "--log-level=error", "--no-build", "lean", "Export.lean"],
                cwd=package, env=self.environment, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120,
            )
            if render_all and result.returncode == 0:
                summary = json.loads(result.stdout.splitlines()[-1])
                self.assertEqual(summary["kind"], "audit_summary")
                # Compare the real Lean module names with the live source tree,
                # before the temporary package is removed.
                INVENTORY.check_audit_modules(package, summary)
            return result

    def assert_rejected(self, body, axiom="AuditDependency.forbidden"):
        result = self.export_fixture(body)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(f"Unexpected axiom {axiom} in ", result.stdout)
        self.assertNotIn('"kind":"audit_summary"', result.stdout)
        return result.stdout

    def test_rejects_unused_public_theorem(self):
        self.assert_rejected("theorem unused : False := AuditDependency.forbidden")

    def test_rejects_unused_private_theorem(self):
        output = self.assert_rejected(
            "private theorem unused : False := AuditDependency.forbidden"
        )
        self.assertIn("_private.Solanalib.Runtime.Fixture", output)

    def test_rejects_proof_valued_definition(self):
        self.assert_rejected("def proof : False := AuditDependency.forbidden")

    def test_rejects_standalone_model_axiom(self):
        self.assert_rejected("axiom unused : False", "Solanalib.Runtime.AuditFixture.unused")

    def test_rejects_transitive_public_use_of_private_proof(self):
        self.assert_rejected("""
            private theorem hidden : False := AuditDependency.forbidden
            theorem exposed : False := hidden
        """)

    def test_rejects_model_constant_outside_catalog_namespace(self):
        self.assert_rejected("""
            end Solanalib.Runtime.AuditFixture
            namespace OutsideCatalog
            theorem unused : False := AuditDependency.forbidden
            end OutsideCatalog
            namespace Solanalib.Runtime.AuditFixture
        """)

    def test_rejects_name_excluded_from_catalog(self):
        self.assert_rejected("theorem _unused : False := AuditDependency.forbidden")

    def test_rejects_theorem_without_source_range(self):
        self.assert_rejected("""
            open Lean Elab Command in
            run_cmd do
              liftCoreM <| addDecl <| Declaration.thmDecl {
                name := `Solanalib.Runtime.AuditFixture.withoutRange
                levelParams := []
                type := mkConst ``False
                value := mkConst ``AuditDependency.forbidden
              }
        """)

    def test_rejects_unused_nested_model_proof_with_rendered_imports(self):
        result = self.export_fixture(
            "theorem valid : True := True.intro",
            render_all=True,
            extra_sources={"Solanalib/Runtime/Review/Unused.lean": """
                module
                public import AuditDependency
                @[expose] public section
                namespace Solanalib.Runtime.NestedAudit
                private theorem unused : False := AuditDependency.forbidden
                end Solanalib.Runtime.NestedAudit
            """},
        )
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Unexpected axiom AuditDependency.forbidden in ", result.stdout)
        self.assertIn("_private.Solanalib.Runtime.Review.Unused", result.stdout)

    def test_accepts_unused_nested_private_proof_with_rendered_imports(self):
        result = self.export_fixture(
            "theorem valid : True := True.intro",
            render_all=True,
            extra_sources={"Solanalib/Runtime/Review/Unused.lean": """
                module
                @[expose] public section
                namespace Solanalib.Runtime.NestedAudit
                private theorem unused : 1 + 1 = 2 := rfl
                end Solanalib.Runtime.NestedAudit
            """},
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        summary = records[-1]
        self.assertEqual(summary["kind"], "audit_summary")
        self.assertEqual(summary["audited_modules"],
                         ["Solanalib.Runtime", "Solanalib.Runtime.Fixture", "Solanalib.Runtime.Review.Unused"])
        self.assertGreaterEqual(summary["audited_theorems"], 2)

    def test_accepts_escaped_module_components_with_rendered_imports(self):
        modules = {
            "Solanalib/Runtime/Borrow-Helper.lean": ("Solanalib.Runtime.«Borrow-Helper»", "hyphen"),
            "Solanalib/Runtime/Borrow.Helper.lean": ("Solanalib.Runtime.«Borrow.Helper»", "dot_component"),
            "Solanalib/Runtime/Borrow/Helper.lean": ("Solanalib.Runtime.Borrow.Helper", "nested_components"),
            "Solanalib/Runtime/α.lean": ("Solanalib.Runtime.α", "unicode"),
            "Solanalib/Runtime/Borrow'.lean": ("Solanalib.Runtime.Borrow'", "prime"),
        }
        extra_sources = {
            path: f"""
                module
                @[expose] public section
                namespace Solanalib.Runtime.NameAudit
                theorem {label} : True := True.intro
                end Solanalib.Runtime.NameAudit
            """
            for path, (_, label) in modules.items()
        }
        result = self.export_fixture(
            "theorem valid : True := True.intro",
            render_all=True,
            extra_sources=extra_sources,
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        rows, summary = records[:-1], records[-1]
        expected_modules = {"Solanalib.Runtime", "Solanalib.Runtime.Fixture"}
        expected_modules.update(module for module, _ in modules.values())
        self.assertEqual(set(summary["audited_modules"]), expected_modules)
        self.assertEqual(len(summary["audited_modules"]), len(expected_modules))
        by_name = {row["name"]: row for row in rows}
        # A dot inside a file component and a nested path must remain distinct
        # imports, module identities and theorem sources.
        for module, label in modules.values():
            with self.subTest(module=module):
                self.assertEqual(by_name[f"Solanalib.Runtime.NameAudit.{label}"]["module"], module)
        self.assertGreaterEqual(summary["audited_theorems"], len(modules) + 1)

    def test_rejects_unused_private_proof_in_quoted_module(self):
        for component in ("Borrow-Helper", "Borrow.Helper"):
            with self.subTest(component=component):
                result = self.export_fixture(
                    "theorem valid : True := True.intro",
                    render_all=True,
                    extra_sources={
                        f"Solanalib/Runtime/{component}.lean": """
                            module
                            public import AuditDependency
                            @[expose] public section
                            namespace Solanalib.Runtime.QuotedAudit
                            private theorem unused : False := AuditDependency.forbidden
                            end Solanalib.Runtime.QuotedAudit
                        """,
                        "Solanalib/Runtime/Borrow/Helper.lean": """
                            module
                            @[expose] public section
                            namespace Solanalib.Runtime.NestedControl
                            theorem valid : True := True.intro
                            end Solanalib.Runtime.NestedControl
                        """,
                    },
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("Unexpected axiom AuditDependency.forbidden in ", result.stdout)
                self.assertIn(component, result.stdout)
                self.assertNotIn('"kind":"audit_summary"', result.stdout)

    def test_rejects_unused_axiom_in_quoted_module(self):
        result = self.export_fixture(
            "theorem valid : True := True.intro",
            render_all=True,
            extra_sources={"Solanalib/Runtime/Borrow-Helper.lean": """
                module
                @[expose] public section
                namespace Solanalib.Runtime.QuotedAxiom
                axiom unused : False
                end Solanalib.Runtime.QuotedAxiom
            """},
        )
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Unexpected axiom Solanalib.Runtime.QuotedAxiom.unused in ", result.stdout)
        self.assertNotIn('"kind":"audit_summary"', result.stdout)

    def test_accepts_valid_private_proofs_and_allowed_axioms(self):
        result = self.export_fixture("""
            private theorem hidden_true : True := True.intro
            private theorem hidden_propext (p q : Prop) (h : p ↔ q) : p = q :=
              propext h
            private theorem hidden_choice : Nonempty Nat :=
              ⟨Classical.choice (show Nonempty Nat from ⟨0⟩)⟩
            private theorem hidden_quotient (r : Nat → Nat → Prop) (a b : Nat)
                (h : r a b) : Quot.mk r a = Quot.mk r b := Quot.sound h

            theorem true_result : True := hidden_true
            def equality_proof (p q : Prop) (h : p ↔ q) : p = q := propext h
            theorem choice_result : Nonempty Nat := hidden_choice
            theorem quotient_result (r : Nat → Nat → Prop) (a b : Nat)
                (h : r a b) : Quot.mk r a = Quot.mk r b := hidden_quotient r a b h
        """)
        self.assertEqual(result.returncode, 0, result.stdout)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        rows, summary = records[:-1], records[-1]
        self.assertEqual(summary["kind"], "audit_summary")
        self.assertEqual(summary["audited_modules"], ["Solanalib.Runtime", "Solanalib.Runtime.Fixture"])
        self.assertGreater(summary["audited_constants"], len(rows))
        self.assertGreater(summary["audited_theorems"], sum(row["kind"] == "theorem" for row in rows))
        expected_keys = {"name", "module", "kind", "type", "line", "column",
                         "start_line", "start_column", "end_line", "end_column", "doc", "axioms"}
        for row in rows:
            self.assertEqual(set(row), expected_keys)
            self.assertTrue(row["name"].startswith("Solanalib.Runtime."))
            self.assertNotIn("hidden_", row["name"])
        by_name = {row["name"]: row for row in rows}
        self.assertEqual(by_name["Solanalib.Runtime.AuditFixture.equality_proof"]["kind"], "definition")
        self.assertIn("propext", by_name["Solanalib.Runtime.AuditFixture.equality_proof"]["axioms"])
        self.assertIn("Classical.choice", by_name["Solanalib.Runtime.AuditFixture.choice_result"]["axioms"])
        self.assertIn("Quot.sound", by_name["Solanalib.Runtime.AuditFixture.quotient_result"]["axioms"])
        self.assertLessEqual({axiom for row in rows for axiom in row["axioms"]},
                             {"propext", "Classical.choice", "Quot.sound"})


if __name__ == "__main__":
    unittest.main()
