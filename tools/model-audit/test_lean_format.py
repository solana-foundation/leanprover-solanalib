"""Kernel checks that wrapping preserves observable literal values."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from lean_format import format_source

ROOT = Path(__file__).resolve().parents[2]


class LiteralValues(unittest.TestCase):
    def test_formatted_metadata_has_the_original_lean_values(self):
        values = [
            '  multiple  spaces ' * 20 + ' trailing   ',
            ('Escapes: "quote" and \\path; λ; separators: \u0085 \u2028 \u2029. ' * 12),
            'x' * 280,
            ('tab\t and newline\n in escaped model data. ' * 10),
        ]
        literals = [json.dumps(value, ensure_ascii=False) for value in values]
        declarations = []
        checks = []
        for index, literal in enumerate(literals):
            declarations.append(format_source(f'def rendered{index} : String := {literal}\n'))
            checks.append(f'example : rendered{index} = {literal} := rfl\n')
        literal_list = '[' + ', '.join(['"https://example.invalid/' + 'x' * 130 + '"', *literals]) + ']'
        declarations.append(format_source(f'def rows : List String := {literal_list}\n'))
        checks.append(f'example : rows = {literal_list} := rfl\n')
        interpolation = 's!"' + 'prefix ' * 10 + '{(List.range 12).filter (fun value => value > 4)} ' + 'suffix ' * 12 + '"'
        declarations.append(format_source(f'def interpolation : String := {interpolation}\n'))
        checks.append(f'example : interpolation = {interpolation} := rfl\n')
        # Trimming code must not remove spaces immediately before a literal newline.
        declarations.append(format_source('def multiline : String := "kept spaces  \nsecond line"  \n'))
        checks.append('example : multiline = "kept spaces  \\nsecond line" := rfl\n')
        clean = format_source('def extraneous : Nat := 4 \t\n\n')
        self.assertEqual(clean, 'def extraneous : Nat := 4\n')
        declarations.append(clean)
        checks.append('example : extraneous = 4 := rfl\n')
        with tempfile.TemporaryDirectory(prefix='solanalib-string-gaps-') as temporary:
            source = Path(temporary) / 'Values.lean'
            source.write_text('import Init\n' + ''.join(declarations + checks))
            result = subprocess.run(['lake', 'env', 'lean', str(source)],
                                    cwd=ROOT / 'packages/solanalib-contracts',
                                    text=True, capture_output=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
