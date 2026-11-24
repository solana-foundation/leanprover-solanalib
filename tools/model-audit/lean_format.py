"""Deterministic wrapping for Lean and generated catalogs.

Only comments and whitespace change. Lean string gaps wrap metadata without
changing string values; no split occurs inside an escape or before whitespace
that the gap would consume. This is a generator helper, not a Lean parser.
"""
from pathlib import Path
import re
import sys
import textwrap

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from lean_source import code_only

HEADER = '''/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
'''


def _wrap_lines(source):
    result = []
    masks = code_only(source, '~').split('\n')
    literal_lines = set()
    for start, end in _strings(source):
        literal_lines.update(range(source.count('\n', 0, start), source.count('\n', 0, end) + 1))
    for number, (line, mask) in enumerate(zip(source.split('\n'), masks)):
        if len(line) <= 100 or re.search(r'https?://', line):
            result.append(line)
            continue
        indent = len(line) - len(line.lstrip())
        if (line.lstrip().startswith('--') and number not in literal_lines) or (
                set(mask.strip()) <= {'~'} and number not in literal_lines):
            prefix = ' ' * indent + ('-- ' if line.lstrip().startswith('--') else '')
            body = line.lstrip().removeprefix('-- ').removeprefix('--') if line.lstrip().startswith('--') else line.lstrip()
            result.extend(textwrap.wrap(body, width=100, initial_indent=prefix,
                                        subsequent_indent=prefix, break_long_words=False,
                                        break_on_hyphens=False, replace_whitespace=False))
            continue
        continuation = ' ' * (indent + (4 if mask.lstrip().startswith('· ') else 2))
        while len(line) > 100:
            # The location of a tactic is one syntactic unit: don't split `at h₁ h₂`.
            location = mask.rfind(' at ')
            limit = min(99, location + 1) if location >= 0 else 99
            cuts = [m.start() for m in re.finditer(r' +', line)
                    if indent + 3 < m.start() <= limit and mask[m.start()] == ' ']
            if not cuts:
                # A qualified identifier is indivisible. Put a following argument
                # on its own continuation line; lint records the token exception.
                following = re.search(r"^\s*[A-Za-z_][A-Za-z0-9_'.]*\."
                                      r"[A-Za-z0-9_'.]+(?P<space> +)\S", line)
                if following and following.start('space') > 99:
                    cuts = [following.start('space')]
                else:
                    break
            cut = cuts[-1]
            result.append(line[:cut].rstrip())
            consumed = cut + len(line[cut:]) - len(line[cut:].lstrip())
            line = continuation + line[consumed:]
            mask = continuation + mask[consumed:]
        result.append(line)
    return '\n'.join(result)


def _strings(source):
    """Yield literal spans, excluding nested comments and quoted identifiers."""
    i = 0
    while i < len(source):
        if source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif source[i] == '«':
            end = source.find('»', i)
            i = len(source) if end < 0 else end + 1
        elif source[i] == '"':
            start = i
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            yield start, i
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            match = re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.|[0-9]+)|[^'\\\n])'", source[i:])
            i += len(match[0]) if match else 1
        else:
            i += 1


def _wrap_strings(source):
    pieces = []
    cursor = 0
    tail = ''

    def append(text):
        nonlocal tail
        pieces.append(text)
        tail = (tail + text).rsplit('\n', 1)[-1]

    for start, end in _strings(source):
        append(source[cursor:start])
        cursor = end
        literal = source[start:end]
        # Existing gaps already have their deterministic generator layout.
        if '\n' in literal:
            append(literal)
            continue
        if len(tail) + len(literal) <= 92 or re.search(r'https?://', literal):
            append(literal)
            continue
        column = len(tail)
        line_start = source.rfind('\n', 0, start) + 1
        original_line = source[line_start:start]
        indent = len(original_line) - len(original_line.lstrip()) + 2
        if column > 80:
            # An earlier URL or literal may have occupied the original line.
            # Break outside the next literal before adding value-preserving gaps.
            append('\n' + ' ' * indent)
            column = indent
        units = re.findall(r'\\(?:u\{[0-9a-fA-F]+\}|.)|[^\\]', literal[1:-1])
        if source[max(0, start - 2):start] in {'s!', 'm!', 'f!'}:
            # A string gap is literal syntax. Within `{...}` it would instead
            # corrupt the interpolated Lean expression (even splitting a name).
            # Keep each complete interpolation as an indivisible unit.
            grouped = []
            expression = []
            depth = 0
            for unit in units:
                if unit == '{':
                    depth += 1
                if depth or expression:
                    expression.append(unit)
                    if unit == '}':
                        depth -= 1
                    if depth == 0:
                        grouped.append(''.join(expression))
                        expression = []
                else:
                    grouped.append(unit)
            if expression:
                grouped.append(''.join(expression))
            units = grouped
        parts = ['"']
        column += 1
        while sum(map(len, units)) + column + 1 > 92:
            total = 0
            ends = []
            for i, unit in enumerate(units):
                total += len(unit)
                if total + column + 1 > 92:
                    break
                # Whitespace after a gap would be eaten by the lexer of Lean.
                if i + 1 < len(units) and not units[i + 1].isspace():
                    ends.append((i + 1, unit.isspace()))
            if not ends:
                break
            spaces = [index for index, whitespace in ends if whitespace]
            cut = spaces[-1] if spaces else ends[-1][0]
            parts.extend((''.join(units[:cut]), '\\\n', ' ' * indent))
            units = units[cut:]
            column = indent
        parts.extend((''.join(units), '"'))
        append(''.join(parts))
    append(source[cursor:])
    return ''.join(pieces)


def strip_code_trailing_whitespace(source):
    """Trim code whitespace while preserving literal and quoted-identifier bytes."""
    lines = []
    masks = code_only(source, '~').split('\n')
    for line, mask in zip(source.split('\n'), masks):
        end = len(line.rstrip(' \t'))
        lines.append(line[:end] if not mask[end:].strip() else line)
    return '\n'.join(lines).rstrip(' \t\n') + '\n'


def format_source(source):
    return strip_code_trailing_whitespace(_wrap_lines(_wrap_strings(_wrap_lines(source))))


if __name__ == '__main__':
    for name in sys.argv[1:]:
        root = Path(name)
        sources = sorted(root.rglob('*.lean')) if root.is_dir() else [root]
        for source in sources:
            if '.lake' not in source.parts:
                source.write_text(format_source(source.read_text()))
