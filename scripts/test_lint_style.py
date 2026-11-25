"""The warning gate must reject violations without changing literal test data."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('lint_style', Path(__file__).with_name('lint-style.py'))
lint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lint)
HEADER = '''/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
'''


class StyleControls(unittest.TestCase):
    def messages(self, body):
        return [message for _, message in lint.violations(HEADER + body)]

    def test_long_line_is_an_error(self):
        self.assertTrue(self.messages('-- ' + 'x' * 101))

    def test_nested_comments_and_literals_are_not_lambda_syntax(self):
        self.assertEqual(self.messages('''import Init
/-! Notes: λ and $ are quoted syntax. -/
/- outer /- nested -/ λ -/
def utf8 := "λ $ data"
def character := 'λ'
def quote := "\\\"λ"
def «λ» := 1
'''), [])

    def test_lambda_and_application_are_rejected(self):
        self.assertTrue(self.messages('def f := λ x => x'))
        self.assertTrue(self.messages('def f := id $ 1'))

    def test_example_is_rejected_where_tests_are_named(self):
        body = '/-- `example` in prose. -/\ntheorem named : True := trivial\n'
        self.assertEqual([m for _, m in lint.violations(HEADER + body, True)], [])
        self.assertTrue([m for _, m in lint.violations(HEADER + 'example : True := trivial', True)])
        self.assertEqual(self.messages('example : True := trivial'), [])

    def test_public_import_order_is_checked(self):
        self.assertTrue(self.messages('/-! Module. -/\npublic import Init\n'))


if __name__ == '__main__':
    unittest.main()
