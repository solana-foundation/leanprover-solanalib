"""Header parsing and model-layer import controls."""
import unittest
from import_tiers import check, header_imports


class HeaderImports(unittest.TestCase):
    def test_reads_only_the_header(self):
        text = (
            "-- a comment\n/- ordinary /- nested -/ -/\nimport A.B\nimport «c-d».E\n"
            "\n/-! import F -/\ndef x := 1\n"
        )
        self.assertEqual(header_imports(text), [(3, ("A", "B")), (4, ("c-d", "E"))])

    def test_prelude_and_module_modifiers(self):
        self.assertEqual(header_imports("prelude\nimport A\n"), [(2, ("A",))])
        text = (
            "module\nprelude\npublic import A\nmeta import B\n"
            "public meta import C\nimport all D\nmeta import all E\n"
        )
        self.assertEqual(header_imports(text), [(i + 3, (m,)) for i, m in enumerate("ABCDE")])

    def test_comments_are_whitespace_between_header_tokens(self):
        # These forms are accepted by Lean.Parser.parseHeader, including adjacency.
        for trivia in (" ", "\n", "/- c -/", "/- c /- nested -/ -/", "-- c\n"):
            for suffix in ("", "/- trailing -/", "-- trailing\n"):
                with self.subTest(trivia=trivia, suffix=suffix):
                    source = "import" + trivia + "ExternalRuntime.core" + suffix
                    self.assertEqual(header_imports(source), [(1, ("ExternalRuntime", "core"))])
                    source = "module\n" + trivia.join(("public", "meta", "import", "A.B"))
                    self.assertEqual(header_imports(source), [(2, ("A", "B"))])

    def test_multiline_import_keeps_its_start_line(self):
        source = "module\n/- c\n c -/\nmeta\n/- nested /- c -/ -/ import\nall\nA.B\n"
        self.assertEqual(header_imports(source), [(4, ("A", "B"))])

    def test_escaped_identifiers_keep_component_boundaries(self):
        source = "import «A».«with space»\nimport «A.with.dot»\nimport A.«--/-»\n"
        self.assertEqual(header_imports(source), [
            (1, ("A", "with space")), (2, ("A.with.dot",)), (3, ("A", "--/-")),
        ])

    def test_unicode_and_identifier_suffixes(self):
        source = "import α.ℝ\nimport Café.x₀'!?\n"
        self.assertEqual(header_imports(source), [(1, ("α", "ℝ")), (2, ("Café", "x₀'!?"))])

    def test_doc_comments_and_commands_end_the_header(self):
        for command in (
            "/-! module docs -/", "/-- declaration docs -/", "public section",
            "meta section", "private def x := 1", 'def s := "import A"',
        ):
            with self.subTest(command=command):
                self.assertEqual(header_imports("import Lean\n" + command + "\nimport A\n"),
                                 [(1, ("Lean",))])

    def test_commented_imports_and_body_text_are_not_dependencies(self):
        source = (
            "-- import Bad\n/- import Bad /- import Worse -/ -/\nimport Good\n"
            'def s := "import Bad /-"\nimport Bad\n'
        )
        self.assertEqual(header_imports(source), [(3, ("Good",))])

    def test_multiple_imports_on_one_line(self):
        self.assertEqual(header_imports("import A import B\n"), [(1, ("A",)), (1, ("B",))])

    def test_incomplete_headers_report_errors(self):
        for source in ("import", "import /- unclosed", "import «unclosed", "import A."):
            with self.subTest(source=source), self.assertRaises(ValueError):
                header_imports(source)


class PackageBoundaries(unittest.TestCase):
    def test_runtime_has_no_root_or_backend_dependency(self):
        for target in ("Mathlib", "Solanalib", "Solanalib.Primitives.Lamports",
                       "Solanalib.RuntimeExtra", "SolanalibTest.Runtime.Example", "ExternalLogic", "ExecutionBinding"):
            with self.subTest(target=target):
                self.assertTrue(check({"packages/solanalib-runtime/Solanalib/Runtime/Basic.lean":
                                       f"import {target}\n"}))

    def test_runtime_tests_can_use_their_production_model(self):
        self.assertEqual(check({"packages/solanalib-runtime/SolanalibTest/Runtime/Example.lean":
                                "module\npublic import Solanalib.Runtime.Basic\n"}), [])

    def test_escaped_path_cannot_cross_a_package_boundary(self):
        self.assertTrue(check({"packages/solanalib-runtime/Solanalib/Runtime/Basic.lean":
                               'import Solanalib.Runtime.«../Primitives/Pubkey»\n'}))

    def test_sbpf_stays_within_its_own_library(self):
        path = "packages/solanalib-sbpf/Solanalib/SBPF/Memory.lean"
        self.assertEqual(check({path: "import Solanalib.SBPF.Value\nimport Std.Tactic.BVDecide\n"}), [])
        for target in ("Mathlib", "Solanalib.Runtime", "SolanalibTest.SBPF.MemoryTest"):
            with self.subTest(target=target):
                self.assertTrue(check({path: f"import {target}\n"}))

    def test_root_source_directories_are_not_registered(self):
        self.assertTrue(check({"Solanalib/Example.lean": "import Init\n"}))

    def test_unknown_owned_module_is_rejected(self):
        self.assertTrue(check({"packages/solanalib-runtime/Unknown.lean": "import Init\n"}))


if __name__ == "__main__":
    unittest.main()
