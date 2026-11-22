#!/usr/bin/env python3
"""Check model import boundaries using the pinned Lean header parser.

The parser recognizes Lean module headers without interpreting comments or strings as imports.
"""
import json
from pathlib import Path
import posixpath
import re
import tomllib

ROOT = Path(__file__).resolve().parents[2]


def has_prefix(module: tuple[str, ...], prefix: str) -> bool:
    components = tuple(prefix.split("."))
    return module[:len(components)] == components

# Lean.isIdFirst / Lean.isIdRest in the pinned Lean toolchain. The Python \w has
# different Unicode ranges. Escaped components can contain spaces or literal dots.
ID_FIRST = (
    r"a-zA-Z_\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
    r"\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9\u03b1-\u03ba\u03bc-\u03fb"
    r"\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
)
ID_REST = ID_FIRST + r"0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
IDENT = re.compile(f"[{ID_FIRST}][{ID_REST}]*")
ModuleName = tuple[str, ...]


class Header:
    """Read just the header, without interpreting commands or strings in the body."""

    def __init__(self, text: str):
        self.text, self.pos = text, 0

    def line(self) -> int:
        return self.text.count("\n", 0, self.pos) + 1

    def fail(self, message: str):
        raise ValueError(f"{self.line()}: {message}")

    def whitespace(self):
        text = self.text
        while self.pos < len(text):
            if text[self.pos].isspace():
                self.pos += 1
            elif text.startswith("--", self.pos):
                end = text.find("\n", self.pos)
                self.pos = len(text) if end < 0 else end
            elif text.startswith(("/--", "/-!"), self.pos):
                # Doc comments are commands, not header whitespace in Lean.
                return
            elif text.startswith("/-", self.pos):
                depth, self.pos = 1, self.pos + 2
                while self.pos < len(text) and depth:
                    if text.startswith("/-", self.pos):
                        depth, self.pos = depth + 1, self.pos + 2
                    elif text.startswith("-/", self.pos):
                        depth, self.pos = depth - 1, self.pos + 2
                    else:
                        self.pos += 1
                if depth:
                    self.fail("unterminated header comment")
            else:
                return

    def keyword(self, word: str) -> bool:
        self.whitespace()
        match = IDENT.match(self.text, self.pos)
        if match and match.group() == word and not self.text.startswith(".", match.end()):
            self.pos = match.end()
            return True
        return False

    def module_name(self) -> ModuleName:
        self.whitespace()
        parts = []
        while True:
            if self.text.startswith("«", self.pos):
                end = self.text.find("»", self.pos + 1)
                if end < 0:
                    self.fail("unterminated module identifier")
                parts.append(self.text[self.pos + 1:end])
                self.pos = end + 1
            elif match := IDENT.match(self.text, self.pos):
                parts.append(match.group())
                self.pos = match.end()
            else:
                self.fail("expected a module identifier after import")
            if not self.text.startswith(".", self.pos):
                return tuple(parts)
            self.pos += 1


def header_imports(text: str) -> list[tuple[int, ModuleName]]:
    """Explicit imports in the Lean `[module] [prelude] ([public] [meta] import [all] M)*` header."""
    header, imports = Header(text), []
    is_module = header.keyword("module")
    header.keyword("prelude")
    while True:
        header.whitespace()
        line = header.line()
        public = header.keyword("public")
        meta = header.keyword("meta")
        if not header.keyword("import"):
            return imports
        all_ = header.keyword("all")
        if not is_module and (public or meta or all_):
            header.fail("public, meta and all imports require a module header")
        if public and all_:
            header.fail("all cannot be combined with public import")
        imports.append((line, header.module_name()))


def module_text(module: ModuleName) -> str:
    return ".".join(part if IDENT.fullmatch(part) else f"«{part}»" for part in module)


def module_path(module: ModuleName) -> ModuleName:
    # Lean resolves escaped slashes and `..` through the filesystem as well.
    path = posixpath.normpath(posixpath.join(*module))
    if path == ".." or path.startswith(("/", "../")):
        raise ValueError(f"cannot classify a module path outside its package: {module_text(module)}")
    return tuple(path.split("/"))


def allowed_imports(path):
    runtime = "packages/solanalib-runtime/"
    if path.startswith(runtime):
        name = path[len(runtime):].removesuffix(".lean").replace("/", ".")
        tests = name == "SolanalibTest.Runtime" or name.startswith("SolanalibTest.Runtime.")
        if not tests and not (name == "Solanalib.Runtime" or name.startswith("Solanalib.Runtime.")):
            raise ValueError("unregistered runtime module: " + path)
        return ["Init", "Std", "Lean", "Solanalib.Runtime", *(["SolanalibTest.Runtime"] if tests else [])]
    if path.startswith("Solanalib/") or path == "Solanalib.lean":
        return ["Init", "Std", "Lean", "Mathlib", "Solanalib"]
    if path.startswith("SolanalibTest/") or path == "SolanalibTest.lean":
        return ["Init", "Std", "Lean", "Mathlib", "Solanalib", "SolanalibTest"]
    raise ValueError("unregistered package module: " + path)


def check(files):
    errors = []
    for path, source in files.items():
        try:
            allowed = allowed_imports(path)
            for line, module in header_imports(source):
                normalized = module_path(module)
                if not any(has_prefix(normalized, prefix) for prefix in allowed):
                    errors.append(f"{path}:{line}: may not import {module_text(module)}")
        except ValueError as error:
            errors.append(f"{path}: {error}")
    return errors


def source_files():
    files = []
    for package in [ROOT, *sorted((ROOT / "packages").glob("*"))]:
        for name in ("Solanalib", "SolanalibTest"):
            files.extend((package / name).rglob("*.lean"))
            aggregate = package / (name + ".lean")
            if aggregate.is_file():
                files.append(aggregate)
    return sorted(files)


def main():
    paths = source_files()
    errors = check({str(p.relative_to(ROOT)): p.read_text() for p in paths})
    for component in (ROOT / "packages/solanalib-runtime",):
        if any((component / name).exists() for name in ("lakefile.lean", "lakefile.toml")):
            errors.append(f"{component}: model sources must belong to the root package")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Import boundaries: {len(paths)} modules; one root package")


if __name__ == "__main__":
    main()
