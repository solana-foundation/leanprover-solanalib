# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Discover every module of the configured runtime library."""

from pathlib import Path
import json
import subprocess
import re
import tomllib
from typing import Iterable


def _render_module(parts: Iterable[str]) -> str:
    """Quote components conservatively without duplicating the Lean Unicode lexer."""
    quoted = []
    for part in parts:
        # Lean identifier escapes end at the first »; there is no escape for it.
        if "»" in part:
            raise ValueError(f"Module component cannot be quoted in Lean: {part!r}")
        quoted.append(part if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part)
                      else "«" + part + "»")
    return ".".join(quoted)


def normalize_module(name: str) -> str:
    """Normalize a Lean module name, retaining dots inside escaped components."""
    parts = []
    position = 0
    while position < len(name):
        if name[position] == "«":
            end = name.find("»", position + 1)
            if end < 0:
                raise ValueError(f"Unterminated module component: {name!r}")
            parts.append(name[position + 1:end])
            position = end + 1
        else:
            end = name.find(".", position)
            end = len(name) if end < 0 else end
            part = name[position:end]
            if not part or "«" in part or "»" in part:
                raise ValueError(f"Invalid module component: {name!r}")
            parts.append(part)
            position = end
        if position < len(name):
            if name[position] != "." or position + 1 == len(name):
                raise ValueError(f"Invalid module separator: {name!r}")
            position += 1
    if not parts:
        raise ValueError("Empty module name")
    return _render_module(parts)


def module_name(path: str | Path) -> str:
    """Convert an exact relative source path into a component-preserving name."""
    path = Path(path)
    if path.is_absolute() or ".." in path.parts or path.suffix != ".lean":
        raise ValueError(f"Invalid model source path: {path}")
    return _render_module([*path.parts[:-1], path.name.removesuffix(".lean")])


def module_paths(paths: Iterable[str]) -> dict[str, str]:
    """Index exact source paths by module identity, never by replacing dots."""
    result = {}
    for path in paths:
        name = module_name(path)
        if name in result:
            raise ValueError(f"Duplicate model module: {name}")
        result[name] = path
    return result


def model_files(root: Path) -> list[Path]:
    """Keep discovery tied to the supported Lake roots and recursive globs."""
    # Lake prefers lakefile.lean even when lakefile.toml also exists. Never
    # inventory or seal the TOML selection while building a different package.
    override = root / "lakefile.lean"
    if override.exists() or override.is_symlink():
        raise ValueError("Unsupported lakefile.lean: the model inventory requires lakefile.toml only")
    repository = root.parents[1]
    root_owned = (root.resolve() == (repository / "packages/solanalib-runtime").resolve()
                 and (repository / "lakefile.lean").is_file())
    if root_owned and (root / "lakefile.toml").exists():
        raise ValueError("Root-owned runtime must not have a nested lakefile.toml")
    if (root / "lakefile.toml").is_file():
        # Isolated audit controls use a local TOML configuration.
        package = tomllib.loads((root / "lakefile.toml").read_text())
        libraries = [library for library in package.get("lean_lib", [])
                     if library.get("name") == "Solanalib.Runtime"]
        if len(libraries) != 1:
            raise ValueError("Expected exactly one Solanalib.Runtime library")
        library = libraries[0]
        source_ok = (package.get("srcDir", ".") == "."
                     and library.get("srcDir", ".") == ".")
        expected_modules = None
    else:
        # Runtime sources belong to the single Lake package of the repository.
        repository = root.parents[1]
        if root.resolve() != (repository / "packages/solanalib-runtime").resolve():
            raise ValueError("Unrecognized runtime source directory")
        result = subprocess.run(["lake", "--quiet", "run", "libraryInventory", "Solanalib.Runtime"],
                                cwd=repository, check=True, capture_output=True, text=True)
        libraries = json.loads(result.stdout)
        if len(libraries) != 1 or libraries[0]["package"] != "solanalib":
            raise ValueError("Expected one root-owned Solanalib.Runtime library")
        library = libraries[0]
        source_ok = Path(library["srcDir"]).resolve() == root.resolve()
        expected_modules = {normalize_module(name) for name in library["modules"]}
    if (set(library.get("globs", [])) != {"Solanalib.Runtime", "Solanalib.Runtime.+"}
            or library.get("roots", ["Solanalib.Runtime"]) != ["Solanalib.Runtime"]
            or not source_ok):
        raise ValueError("Model library configuration changed; update its source inventory")
    aggregate = root / "Solanalib/Runtime.lean"
    directory = root / "Solanalib/Runtime"
    # Lake follows directory links, while pathlib discovery does not. Reject
    # linked source trees explicitly instead of claiming incomplete coverage.
    if (root / "Solanalib").is_symlink() or aggregate.is_symlink() or directory.is_symlink():
        raise ValueError("Symbolic links in model sources are unsupported")
    paths = list(directory.rglob("*"))
    links = sorted(str(path.relative_to(root)) for path in paths if path.is_symlink())
    if links:
        raise ValueError("Symbolic links in model sources are unsupported: " + ", ".join(links))
    files = [aggregate, *sorted(path for path in paths if path.is_file() and path.suffix == ".lean")]
    if expected_modules is not None and expected_modules != {
            module_name(path.relative_to(root)) for path in files}:
        raise ValueError("Lake module inventory differs from recursive runtime sources")
    return files


def model_modules(root: Path) -> list[str]:
    return [module_name(path.relative_to(root)) for path in model_files(root)]


def render_export(root: Path, template: str) -> str:
    """Import all configured modules, including those absent from the aggregate."""
    marker = "import Solanalib.Runtime\n"
    if template.count(marker) != 1:
        raise ValueError("Expected one model import in the export template")
    imports = "".join(f"import {module}\n" for module in model_modules(root))
    return template.replace(marker, imports, 1)


def check_audit_modules(root: Path, summary: dict) -> None:
    actual = [normalize_module(name) for name in summary.get("audited_modules", [])]
    if sorted(actual) != sorted(model_modules(root)):
        raise ValueError("Axiom audit does not cover every configured model module")
