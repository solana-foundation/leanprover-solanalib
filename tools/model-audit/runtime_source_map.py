# Copyright (c) 2026 Harmonic. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Solanalib Contributors
"""Validate immutable runtime-source anchors and any supplied local source copies."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from runtime_inventory import module_paths, normalize_module


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_source_map(manifest: Path, *, registry: Path | None = None,
                      agave_source: Path | None = None,
                      require_sources: bool = False) -> dict:
    entries = json.loads(manifest.read_text())["entries"]
    checked = 0
    identities = set()
    ids = set()
    file_hashes = {}
    for row in entries:
        if row["id"] in ids:
            raise ValueError(f"Duplicate source id: {row['id']}")
        ids.add(row["id"])
        if not re.fullmatch(r"[a-f0-9]{64}", row["sha256"]):
            raise ValueError(f"Invalid source hash: {row['id']}")
        if type(row["line"]) is not int or row["line"] < 1:
            raise ValueError(f"Invalid source line: {row['id']}")
        kind = row.get("source_kind", "cargo")
        if kind == "cargo":
            package_name, separator, version = row["crate"].rpartition("-")
            if not separator or not package_name or not version:
                raise ValueError(f"Invalid Cargo crate identity: {row['id']}")
            package_url = f"https://docs.rs/crate/{package_name}/{version}/source/" + row["path"]
        if "archive_sha256" in row:
            if kind != "cargo":
                raise ValueError(f"Invalid source archive pin: {row['id']}")
            archive_url = f"https://static.crates.io/crates/{package_name}/{row['crate']}.crate"
            if ("revision" in row or "path_in_repository" in row
                    or row.get("archive_url") != archive_url
                    or not isinstance(row["archive_sha256"], str)
                    or not re.fullmatch(r"[a-f0-9]{64}", row["archive_sha256"])):
                raise ValueError(f"Invalid source archive pin: {row['id']}")
            expected = package_url + "#" + str(row["line"])
            identity = (archive_url, row["archive_sha256"], row["path"])
        else:
            if (not isinstance(row.get("revision"), str)
                    or not re.fullmatch(r"[a-f0-9]{40}", row["revision"])):
                raise ValueError(f"Invalid source revision: {row['id']}")
            expected = (row["repository"] + "/blob/" + row["revision"] + "/"
                        + row["path_in_repository"] + "#L" + str(row["line"]))
            identity = (row["repository"], row["revision"], row["path_in_repository"])
        if row["url"] != expected:
            raise ValueError(f"Source URL does not match its identity: {row['id']}")
        identities.add(identity)
        if identity in file_hashes and file_hashes[identity] != row["sha256"]:
            raise ValueError(f"Conflicting source hashes: {row['id']}")
        file_hashes[identity] = row["sha256"]
        if kind == "git":
            if row["repository"] != "https://github.com/anza-xyz/agave":
                raise ValueError(f"Unsupported Git source repository: {row['id']}")
            if agave_source is None:
                continue
            source = agave_source / row["path_in_repository"]
        elif kind == "cargo":
            if "package_source_url" in row:
                if row["package_source_url"] != package_url:
                    raise ValueError(f"Package source URL differs: {row['id']}")
            if registry is None:
                continue
            package = registry / row["crate"]
            source = package / row["path"]
            if "revision" in row:
                vcs = json.loads((package / ".cargo_vcs_info.json").read_text())
                if vcs["git"]["sha1"] != row["revision"]:
                    raise ValueError(f"Cargo source revision differs: {row['id']}")
                if vcs["path_in_vcs"] + "/" + row["path"] != row["path_in_repository"]:
                    raise ValueError(f"Cargo source path differs: {row['id']}")
        else:
            raise ValueError(f"Unknown source kind: {kind}")
        if digest(source) != row["sha256"]:
            raise ValueError(f"Source content differs: {row['id']}")
        lines = source.read_text().splitlines()
        if row["line"] > len(lines) or lines[row["line"] - 1].strip() != row["anchor_text"]:
            raise ValueError(f"Source anchor differs: {row['id']}")
        checked += 1
    if require_sources and (not entries or checked != len(entries)):
        raise ValueError(f"Complete source verification required: checked {checked} of {len(entries)} anchors")
    return {"anchors": len(entries), "files": len(identities),
            "checked_source_anchors": checked,
            "local_source_hashes_checked": bool(entries) and checked == len(entries),
            "manifest_sha256": digest(manifest)}


def verify_correspondence(manifest: Path, sources: dict[str, str],
                          declarations: list[dict]) -> dict:
    """Check the identity and coverage of the manual source argument.

    This verifies references and exact reviewed model bytes, not semantic
    equivalence with Rust. The argument and its premises remain reviewable prose.
    """
    document = json.loads(manifest.read_text())
    entries = {row["id"] for row in document["entries"]}
    rows = document["correspondence"]
    known = {row["name"]: normalize_module(row["module"]) for row in declarations}
    paths = module_paths(sources)
    expected = set(paths) - {"Solanalib.Runtime"}
    covered = set()
    references = set()
    ids = set()
    for row in rows:
        name = row["id"]
        if name in ids:
            raise ValueError(f"Duplicate correspondence id: {name}")
        ids.add(name)
        modules = [normalize_module(module) for module in row["modules"]]
        if not modules or len(modules) != len(set(modules)):
            raise ValueError(f"Invalid correspondence modules: {name}")
        if covered.intersection(modules):
            raise ValueError(f"Repeated correspondence module: {name}")
        covered.update(modules)
        hashes = {normalize_module(module): digest
                  for module, digest in row["model_sha256"].items()}
        if len(hashes) != len(row["model_sha256"]) or set(hashes) != set(modules):
            raise ValueError(f"Missing reviewed model identity: {name}")
        for module in modules:
            if module not in paths:
                raise ValueError(f"Unknown correspondence module: {module}")
            path = paths[module]
            actual = hashlib.sha256(sources[path].encode()).hexdigest()
            if hashes[module] != actual:
                raise ValueError(f"Reviewed model content differs: {module}")
        if row["treatment"] not in {"source-read", "abstraction", "derived"}:
            raise ValueError(f"Invalid correspondence treatment: {name}")
        if row["treatment"] != "derived" and not row["source_ids"]:
            raise ValueError(f"Missing correspondence source: {name}")
        if not set(row["source_ids"]) <= entries:
            raise ValueError(f"Unknown correspondence source: {name}")
        if not row["declarations"]:
            raise ValueError(f"Missing correspondence declarations: {name}")
        for declaration in row["declarations"]:
            if known.get(declaration) not in modules:
                raise ValueError(f"Unknown or misplaced correspondence declaration: {declaration}")
            references.add(declaration)
        if not row["argument"].strip() or not row["section"].strip():
            raise ValueError(f"Missing correspondence argument: {name}")
        for field in ("assumptions", "limitations"):
            if not isinstance(row[field], list) or any(not item.strip() for item in row[field]):
                raise ValueError(f"Invalid correspondence {field}: {name}")
    if covered != expected:
        raise ValueError(f"Incomplete correspondence coverage: missing {sorted(expected - covered)}, extra {sorted(covered - expected)}")
    return {"arguments": len(rows), "modules": len(covered),
            "referenced_declarations": len(references),
            "reviewed_model_hashes_checked": True,
            "semantic_correspondence": "manual source argument, not a refinement proof"}
