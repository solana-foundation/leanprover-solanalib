#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Controls for runtime module descriptions and dependency-audit completeness."""
import unittest

from check_runtime import validate_declarations, validate_modules


class RuntimeAuditTests(unittest.TestCase):
    def setUp(self):
        self.row = {'name': 'Solanalib.Runtime.example', 'kind': 'theorem',
                    'type': '1 = 1', 'axioms': ['propext']}
        self.summary = {'kind': 'audit_summary', 'audited_constants': 2, 'audited_theorems': 1}

    def test_complete_audit(self):
        validate_declarations([self.row], self.summary)

    def test_missing_summary_and_private_proof_counts(self):
        for summary in ({}, {**self.summary, 'audited_constants': 0},
                        {**self.summary, 'audited_theorems': 0}):
            with self.subTest(summary=summary), self.assertRaises(ValueError):
                validate_declarations([self.row], summary)

    def test_forbidden_axiom_duplicate_and_truncated_type(self):
        for rows in ([{**self.row, 'axioms': ['sorryAx']}], [self.row, self.row],
                     [{**self.row, 'type': '…'}], []):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                validate_declarations(rows, self.summary)

    def test_all_module_descriptions_required(self):
        rows = [{'module': 'Solanalib.Runtime.Basic', 'description': 'Runtime values.'}]
        modules = ['Solanalib.Runtime', 'Solanalib.Runtime.Basic']
        validate_modules(rows, modules)
        for changed in ([], rows + rows, [{**rows[0], 'description': ''}]):
            with self.subTest(rows=changed), self.assertRaises(ValueError):
                validate_modules(changed, modules)
        with self.assertRaises(ValueError):
            validate_modules(rows, modules + ['Solanalib.Runtime.Another'])


if __name__ == '__main__':
    unittest.main()
