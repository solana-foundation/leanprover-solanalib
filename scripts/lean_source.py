"""Lean source scanning used by textual checks; comments and literals keep their width."""
import re


def code_only(source: str, mask_char: str = ' ') -> str:
    """Mask nested comments, string/character literals and quoted identifiers.

    Preserve offsets and newlines so a diagnostic still names the source location.
    Literal contents are data, including UTF-8 test cases containing lambda signs.
    """
    out = list(source)
    i = 0
    depth = 0
    while i < len(source):
        start = i
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
        elif source.startswith('--', i):
            i = source.find('\n', i)
            if i < 0:
                i = len(source)
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif source[i] == '«':
            end = source.find('»', i + 1)
            i = len(source) if end < 0 else end + 1
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            match = re.match(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.|[0-9]+)|[^'\\\n])'", source[i:])
            if match:
                i += len(match[0])
            else:
                i += 1
                continue
        else:
            i += 1
            continue
        for j in range(start, min(i, len(source))):
            if out[j] != '\n':
                out[j] = mask_char
    return ''.join(out)
