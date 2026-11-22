#!/usr/bin/env python3
# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Flag inanimate possessives in documentation, without rewriting source or data.

The rule accepts contractions and a small explicit vocabulary of people. It
checks documentation, Lean and Python message strings, Rust comments and the
comments in fenced examples. Code identifiers, recorded native data, quoted
source anchors, test fixtures and unchanged upstream lines remain literal.
The baseline records hashes of inherited lines, not exemptions for whole files.
"""
import argparse
import ast
from dataclasses import dataclass
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent.parent
BASELINE = 'scripts/prose-baseline.json'
CONTRACTIONS = {'he', 'she', 'it', 'that', 'what', 'there', 'here', 'where', 'when', 'why',
                'how', 'who', 'let'}
PEOPLE = {'person', 'people', 'author', 'authors', 'contributor', 'contributors',
          'maintainer', 'maintainers', 'developer', 'developers', 'programmer',
          'programmers', 'user', 'users', 'someone', 'anyone',
          'everyone', 'nobody', 'somebody', 'everybody', 'anybody',
          'euler', 'newton', 'fermat', 'bernoulli', 'cauchy', 'schwarz'}
POSSESSIVE = re.compile(
    r"(?<![\w'])((?:`[^`\n]+`)|(?:[\w][\w.:-]*))(?:['’]s\b|(?<=s)['’](?=\s+[A-Za-z`]))")
RUST_RAW = re.compile(r'(?:br|cr|r)(#*)"')
RUST_CHAR = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'")
FENCE = re.compile(r'^\s*(`{3,}|~{3,})')
COLON = re.compile(r'\s*:')
QUOTED_KEYS = {'contains', 'source_text', 'source_excerpt', 'snippet', 'needle',
               'excerpt', 'rust_source', 'expected_stdout', 'expected_stderr'}
PROSE_KEYS = {
    'description', 'summary', 'scope', 'reason', 'argument', 'conditions', 'method',
    'title', 'label', 'notes', 'note', 'model_gaps', 'remaining_requirements',
    'assumptions', 'limitations', 'differences', 'interpretation', 'source_argument',
    'affected_claims', 'resolution', 'behavior', 'test_scope', 'effect', 'status',
    'execution', 'cpu_limit', 'cold', 'warm', 'filesystem', 'excluded_time', 'memory',
    'cache_bytes', 'package_layout', 'subsequent_input_changes', 'rationale',
    'applicability_scope', 'evidence', 'review_scope', 'binding_obligations',
}


@dataclass(frozen=True)
class Fragment:
    start: int
    text: str
    kind: str


@dataclass(frozen=True)
class Finding:
    line: int
    word: str
    text: str


def blank(text):
    return re.sub(r'[^\n]', ' ', text)


def masked_markdown(text):
    """Mask literal spans, retaining offsets and comments in fenced examples.

    Inline code may cross a line break; its closing delimiter must have exactly
    the same length. A shorter or unmatched backtick cannot consume later prose.
    Block quotes mark literal quotations. Fenced examples are authored code, so
    their comments and message strings are checked using the relevant lexer.
    """
    result = []
    prose = []
    fence = None
    language = ''
    fenced = []

    def flush_prose():
        content = ''.join(prose)
        masked = list(content)
        ticks = list(re.finditer(r'`+', content))
        i = 0
        while i < len(ticks):
            start = ticks[i]
            end = next((j for j in range(i + 1, len(ticks))
                        if len(ticks[j].group()) == len(start.group())), None)
            if end is None:
                i += 1
                continue
            finish = ticks[end].end()
            if not re.match(r"(?:['’]s\b|['’]\s)", content[finish:]):
                masked[start.start():finish] = blank(content[start.start():finish])
            i = end + 1
        result.append(''.join(masked))
        prose.clear()

    def flush_fence():
        content = ''.join(fenced)
        masked = list(blank(content))
        if language in {'lean', 'lean4'}:
            fragments = lean_prose(content)
        elif language in {'rust', 'rs'}:
            fragments = rust_comments(content)
        elif language in {'python', 'py'}:
            try:
                fragments = list(python_prose(content))
            except (SyntaxError, tokenize.TokenError, IndentationError):
                fragments = hash_comments(content)
        elif language in {'toml', 'sh', 'bash', 'shell', 'yaml', 'yml'}:
            fragments = hash_comments(content)
        else:
            fragments = []
        for fragment in fragments:
            masked[fragment.start:fragment.start + len(fragment.text)] = fragment.text
        result.append(''.join(masked))
        fenced.clear()

    for line in text.splitlines(keepends=True):
        marker = FENCE.match(line)
        if fence is not None:
            if (marker and marker.group(1)[0] == fence[0]
                    and len(marker.group(1)) >= len(fence)
                    and not line[marker.end():].strip()):
                flush_fence()
                result.append(blank(line))
                fence = None
            else:
                fenced.append(line)
        elif marker:
            flush_prose()
            fence = marker.group(1)
            language = line[marker.end():].strip().split(' ', 1)[0].lower()
            result.append(blank(line))
        elif line.lstrip().startswith('>'):
            flush_prose()
            result.append(blank(line))
        else:
            prose.append(line)
    if fence is not None:
        flush_fence()
    flush_prose()
    return ''.join(result)


def lean_prose(text, strings=True):
    """Select nested Lean comments and message strings, preserving source offsets."""
    i = 0
    while i < len(text):
        if text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            yield Fragment(i, text[i:end], 'comment')
            i = end
        elif text.startswith('/-', i):
            start, depth = i, 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            yield Fragment(start, text[start:i], 'comment')
        elif text[i] in {'"', '«'}:
            start = i
            closing = '"' if text[i] == '"' else '»'
            i += 1
            while i < len(text):
                if text[i] == '\\' and closing == '"':
                    i += 2
                elif text[i] == closing:
                    i += 1
                    break
                else:
                    i += 1
            if strings and closing == '"':
                yield Fragment(start, text[start:i], 'message')
        else:
            i += 1


def lean_comments(text):
    yield from lean_prose(text, strings=False)


def rust_comments(text):
    """Select nested Rust comments, excluding ordinary, raw and byte strings."""
    i = 0
    while i < len(text):
        if text.startswith('//', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            yield Fragment(i, text[i:end], 'comment')
            i = end
        elif text.startswith('/*', i):
            start, depth = i, 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/*', i):
                    depth += 1
                    i += 2
                elif text.startswith('*/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            yield Fragment(start, text[start:i], 'comment')
        elif match := RUST_RAW.match(text, i):
            close = '"' + match.group(1)
            end = text.find(close, match.end())
            i = len(text) if end < 0 else end + len(close)
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif match := RUST_CHAR.match(text, i):
            i = match.end()
        else:
            i += 1


def hash_comments(text):
    """Select shell, TOML and YAML comments outside ordinary quoted strings."""
    for match in re.finditer(r'''(?m)(?:"(?:[^"\\\n]|\\.)*"|'[^'\n]*')|(?P<comment>\#[^\n]*)''', text):
        if match.group('comment') is not None:
            yield Fragment(match.start(), match.group(), 'comment')


def python_prose(text, generated=True):
    """Select comments and strings; test fixtures and quoted source stay literal."""
    lines = text.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    for token in tokenize.generate_tokens(io.StringIO(text).readline):
        if token.type == tokenize.COMMENT:
            yield Fragment(offsets[token.start[0] - 1] + token.start[1], token.string, 'comment')
    tree = ast.parse(text)
    selected = set()
    quoted = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Dict):
            for key, value in zip(node.keys, node.values):
                if isinstance(key, ast.Constant) and key.value in QUOTED_KEYS:
                    quoted.update(ast.walk(value))
        if isinstance(node, ast.keyword) and node.arg in QUOTED_KEYS:
            quoted.update(ast.walk(node.value))
    for node in ast.walk(tree):
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant):
            if isinstance(node.value.value, str):
                selected.add(node.value)
        if isinstance(node, ast.keyword) and node.arg in {'help', 'description', 'epilog'}:
            selected.update(n for n in ast.walk(node.value)
                            if isinstance(n, ast.Constant) and isinstance(n.value, str))
        if generated and isinstance(node, ast.Dict):
            for key, value in zip(node.keys, node.values):
                if (isinstance(key, ast.Constant) and key.value in PROSE_KEYS
                        and isinstance(value, (ast.Constant, ast.JoinedStr))):
                    if isinstance(value, ast.JoinedStr) or isinstance(value.value, str):
                        selected.add(value)
        if generated and isinstance(node, (ast.Constant, ast.JoinedStr)):
            first = node.values[0] if isinstance(node, ast.JoinedStr) and node.values else node
            if (isinstance(first, ast.Constant) and isinstance(first.value, str)
                    and re.match(r'\s*# [^\n]+\n', first.value)):
                selected.add(node)
        if (generated and node not in quoted and isinstance(node, ast.Constant)
                and isinstance(node.value, str)):
            selected.add(node)
    spans = set()
    for node in sorted(selected, key=lambda n: (n.lineno, n.col_offset)):
        start = offsets[node.lineno - 1] + len(lines[node.lineno - 1].encode()[:node.col_offset].decode())
        end = offsets[node.end_lineno - 1] + len(lines[node.end_lineno - 1].encode()[:node.end_col_offset].decode())
        if (start, end) not in spans:
            spans.add((start, end))
            literal = text[start:end]
            if re.search(r'(?m)^\s*(?:open|import|def|theorem)\b', literal):
                opening = re.match(r'(?i)[ru]*("""|\x27\x27\x27)', literal)
                if opening:
                    for fragment in lean_prose(literal[opening.end():-3]):
                        yield Fragment(start + opening.end() + fragment.start, fragment.text,
                                       'generated Lean prose')
                    continue
            yield Fragment(start, literal, 'docstring/help')
    if generated:
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Constant) and isinstance(node.value, str)
                    and '/-' in node.value and re.search(r'(?m)^\s*(?:open|import|def|theorem)\b', node.value)):
                continue
            start = offsets[node.lineno - 1] + len(lines[node.lineno - 1].encode()[:node.col_offset].decode())
            end = offsets[node.end_lineno - 1] + len(lines[node.end_lineno - 1].encode()[:node.end_col_offset].decode())
            literal = text[start:end]
            opening = re.match(r'(?i)[ru]*("""|\x27\x27\x27)', literal)
            if opening:
                body_start = opening.end()
                for fragment in lean_comments(literal[body_start:-3]):
                    yield Fragment(start + body_start + fragment.start, fragment.text, 'generated Lean comment')


def registry_prose(text, suffix):
    """Select explanatory registry fields; source anchors and recorded data stay literal."""
    if suffix == '.json':
        # JSON strings retain a direct source location, including multiline escapes.
        tokens = list(re.finditer(r'"(?:[^"\\]|\\.)*"', text))
        key = None
        prose_container = False
        for token in tokens:
            value = json.loads(token.group())
            if COLON.match(text, token.end()):
                key = value
                prose_container = key in PROSE_KEYS
                continue
            if key in QUOTED_KEYS:
                continue
            if prose_container:
                yield Fragment(token.start(), token.group(), 'registry')
    else:
        # TOML explanatory strings are ordinary or multiline strings assigned to
        # named fields. Other fields include exact Rust signatures and identities.
        pattern = re.compile(r'(?m)^\s*([\w-]+)\s*=\s*("""[\s\S]*?"""|\x27\x27\x27[\s\S]*?\x27\x27\x27|"(?:[^"\\\n]|\\.)*"|\x27[^\x27\n]*\x27)')
        for match in pattern.finditer(text):
            if match.group(1) in PROSE_KEYS:
                yield Fragment(match.start(2), match.group(2), 'registry')
        for match in re.finditer(r'(?m)^\s*#[^\n]*', text):
            yield Fragment(match.start(), match.group(), 'comment')


def prose_fragments(path, text):
    name = str(path)
    if name.endswith(('.md', '.md.in')):
        yield Fragment(0, text, 'markdown')
    elif name.endswith(('.lean', '.lean.in')):
        yield from lean_prose(text)
    elif name.endswith('.rs'):
        yield from rust_comments(text)
    elif name.endswith(('.py', '.py.in')):
        yield from python_prose(text, generated=not Path(name).name.startswith('test'))
    elif name.endswith(('.json', '.toml')):
        yield from registry_prose(text, Path(name).suffix)
    elif name.endswith(('.sh', '.yml', '.yaml')) or Path(name).name in {'Justfile', 'requirements.txt'}:
        yield from hash_comments(text)
        if name.endswith(('.yml', '.yaml')):
            for match in re.finditer(r'(?m)^\s*(?:- )?(?:name|description):[^\n]*', text):
                yield Fragment(match.start(), match.group(), 'help')


def line_hash(line):
    return hashlib.sha256(line.strip().encode()).hexdigest()


def check_text(path, text, inherited=()):
    allowed = set(inherited)
    lines = text.splitlines()
    findings = []
    seen = set()
    for fragment in prose_fragments(path, text):
        content = fragment.text
        offsets = None
        if fragment.kind == 'registry' and str(path).endswith('.json'):
            # Decode escaped punctuation, retaining an offset into the source
            # for each character so diagnostics and inherited-line checks agree.
            pieces, offsets = [], []
            for token in re.finditer(r'\\(?:u[0-9a-fA-F]{4}|.)|[^\\]', content[1:-1]):
                encoded = token.group()
                decoded = json.loads('"' + encoded + '"') if encoded.startswith('\\') else encoded
                pieces.append(decoded)
                offsets.extend([token.start() + 1] * len(decoded))
            content = ''.join(pieces)
        prose = masked_markdown(content)
        for match in POSSESSIVE.finditer(content):
            if not prose[match.start():match.end()].strip():
                continue
            noun = match.group(1).strip('`').lower()
            if noun in CONTRACTIONS or noun in PEOPLE:
                continue
            offset = fragment.start + (offsets[match.start()] if offsets is not None else match.start())
            line = text.count('\n', 0, offset) + 1
            if line_hash(lines[line - 1]) in allowed or offset in seen:
                continue
            seen.add(offset)
            findings.append(Finding(line, match.group(), lines[line - 1].strip()))
    return findings


def source_files(root):
    names = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=root)
    for name in sorted(set(names.decode().split('\0'))):
        if not name or not (root / name).is_file():
            continue
        if '/corpus/' in name or '/rust/prepared/' in name or name == BASELINE:
            continue
        if name.endswith(('.md', '.md.in', '.lean', '.lean.in', '.py', '.py.in', '.rs',
                          '.json', '.toml', '.sh', '.yml', '.yaml')) or Path(name).name in {'Justfile', 'requirements.txt'}:
            yield root / name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--json', action='store_true', help='Print findings and counts as JSON.')
    args = parser.parse_args()
    root = args.root.resolve()
    baseline_path = root / BASELINE
    baseline = json.loads(baseline_path.read_text())['inherited_lines'] if baseline_path.exists() else {}
    results = []
    paths = list(source_files(root))
    for path in paths:
        relative = path.relative_to(root).as_posix()
        for finding in check_text(relative, path.read_text(), baseline.get(relative, [])):
            results.append({'path': relative, 'line': finding.line,
                            'word': finding.word, 'text': finding.text})
    summary = {'files': len(paths), 'findings': len(results), 'items': results}
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        for item in results:
            print(f"{item['path']}:{item['line']}: rephrase {item['word']}: {item['text']}")
        print(f'Prose: {len(paths)} files checked; {len(results)} inanimate possessives')
    return bool(results)


if __name__ == '__main__':
    raise SystemExit(main())
