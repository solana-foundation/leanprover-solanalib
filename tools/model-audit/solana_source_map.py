"""Load the reviewable SDK source map without storing expanded audit tables.

Schema 3 separates incremental review layers, records each crate pin once, and
uses explicit defaults for routine witness names and empty scope fields. Its
expansion retains the API/model shape of schema 2 for the source and coverage checks.
The source-map README documents the defaults; none supplies a Rust proof.
"""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re

from solana_source_archives import archive_pin, archive_source


SECTIONS = ("packages", "interfaces", "abstractions", "models", "api", "compatibility",
            "applicability_sources", "applicability")
HEADER_FIELDS = {"schema_version", "runtime_reference", "analysis", "binding_boundary",
                 "excluded_sources", "implementation_boundary", "fragments", "applicability_scope"}


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate source-map key in {path}: {key}")
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError(f"Non-JSON source-map value in {path}: {value}")

    return json.loads(path.read_text(), object_pairs_hook=unique, parse_constant=invalid_constant)


def source_map_files(package):
    """Return every manifest input, rejecting hidden or unregistered fragments."""
    package = Path(package)
    index = package / "source-map.json"
    if index.is_symlink():
        raise ValueError("Linked source-map index")
    document = read_json(index)
    if not isinstance(document, dict):
        raise ValueError("Source map must be a JSON object")
    if document.get("schema_version") == 2:
        return [index]
    if document.get("schema_version") != 3:
        raise ValueError("Source map requires schema_version 2 or 3 with a complete models inventory")
    if set(document) - HEADER_FIELDS:
        raise ValueError(f"Unknown source-map index fields: {sorted(set(document) - HEADER_FIELDS)}")
    names = document.get("fragments")
    if (not isinstance(names, list) or not names or any(not isinstance(name, str) for name in names)
            or len(names) != len(set(names))):
        raise ValueError("Missing or repeated source-map fragments")
    paths = []
    for name in names:
        relative = Path(name)
        if (relative.is_absolute() or relative.parts[:1] != ("source-map",)
                or len(relative.parts) != 2 or relative.suffix != ".json"
                or not re.fullmatch(r"[a-z0-9][a-z0-9_-]*\.json", relative.name)):
            raise ValueError(f"Invalid source-map fragment path: {name}")
        path = package / relative
        if path.parent.is_symlink() or path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing or linked source-map fragment: {name}")
        paths.append(path)
    available = set((package / "source-map").rglob("*.json"))
    if available != set(paths):
        raise ValueError("Source-map fragments must cover every available JSON fragment")
    return [index, *paths]


def source_map_hashes(package):
    package = Path(package)
    return {path.relative_to(package).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in source_map_files(package)}


def source_map_digest(package):
    """Seal both the layer selection and the exact bytes of every selected fragment."""
    hashes = source_map_hashes(package)
    if len(hashes) == 1:
        return hashes["source-map.json"]
    return hashlib.sha256(json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def mapping(value, label):
    if (not isinstance(value, dict)
            or any(not isinstance(key, str) or not key.strip() or not isinstance(row, dict)
                   for key, row in value.items())):
        raise ValueError(f"Invalid source-map {label} mapping")
    return value


def fields(row, allowed, label):
    if set(row) - set(allowed):
        raise ValueError(f"Unknown {label} fields: {sorted(set(row) - set(allowed))}")


def expand_model(identifier, compact):
    fields(compact, {"contract", "reference", "kind", "witness_kind", "witness",
                     "satisfiable", "execution", "sample", "family", "assumptions",
                     "model_gaps", "remaining_requirements"}, f"model {identifier}")
    contract = compact.get("contract")
    if not isinstance(contract, str) or not contract:
        raise ValueError(f"Missing model contract: {identifier}")
    stem = contract.removesuffix("_contract")
    kind = compact.get("witness_kind")
    if kind not in {"RealizedBy", "Holds", "FamilyReference"}:
        raise ValueError(f"Unknown model witness kind: {identifier}")
    result = {
        "id": identifier, "contract": contract, "kind": compact.get("kind", "full"),
        "reference": deepcopy(compact.get("reference", stem + "_run")),
        "witness_kind": kind,
        "witnesses": [compact.get("witness", stem + "_reference")],
        "satisfiability_witnesses": [compact.get("satisfiable", stem + "_satisfiable")],
        "assumptions": deepcopy(compact.get("assumptions", [])),
        "model_gaps": deepcopy(compact.get("model_gaps", [])),
        "remaining_requirements": deepcopy(compact.get("remaining_requirements", [])),
        "rust_proof_status": "open",
    }
    if kind != "RealizedBy":
        result["execution_witnesses"] = [compact.get("execution", stem + "_has_execution")]
    elif "execution" in compact:
        raise ValueError(f"Total reference model cannot register an outcome execution: {identifier}")
    if kind == "FamilyReference":
        result["sample"] = compact.get("sample", stem + "_sample")
        if "family" in compact:
            result["family"] = compact["family"]
    elif "family" in compact or "sample" in compact:
        raise ValueError(f"Non-family model cannot register a family or sample: {identifier}")
    return result


def expand_api(identifier, compact, interfaces):
    fields(compact, {"source_id", "line", "anchor_text", "status", "models", "clients",
                     "model_dependencies", "scope", "binding_obligations", "rust_names",
                     "bindings", "implementation_evidence"}, f"API {identifier}")
    source = interfaces.get(compact.get("source_id"))
    if source is None:
        raise ValueError(f"Unknown API source: {identifier}")
    crate = source["crate"]
    package, separator, version = crate.rpartition("-")
    if not separator or not package or not version:
        raise ValueError(f"Invalid API crate identity: {identifier}")
    bindings = compact.get("bindings", {})
    if (not isinstance(bindings, dict)
            or any(not isinstance(identity, str) or not identity or not isinstance(name, str) or not name
                   for identity, name in bindings.items())):
        raise ValueError(f"Invalid exact inventory bindings: {identifier}")
    result = {key: deepcopy(value) for key, value in compact.items()
              if key not in {"bindings", "rust_names"}}
    result.update({
        "id": identifier, "status": compact.get("status", "contracted"),
        "models": deepcopy(compact.get("models", [identifier])),
        "clients": deepcopy(compact.get("clients", [])),
        "model_dependencies": deepcopy(compact.get("model_dependencies", [])),
        "rust_names": deepcopy(compact.get("rust_names", list(dict.fromkeys(bindings.values())))),
        "inventory_bindings": [{"identity": identity, "source_name": name,
                                "package": {"name": package, "version": version}}
                               for identity, name in bindings.items()],
    })
    return result


RUST_PATH = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)*")


def _closing_bracket(name, start):
    """Index of the `>` closing the `<` at `start`; the `>` of `->` is not one."""
    depth = 0
    for index in range(start, len(name)):
        if name[index] == "<":
            depth += 1
        elif name[index] == ">" and name[index - 1] != "-":
            depth -= 1
            if depth == 0:
                return index
    raise ValueError(f"Unbalanced Rust name: {name}")


def _split_top_level(text, separator):
    """Split at the first `separator` outside brackets, or return None."""
    depth = 0
    for index, character in enumerate(text):
        if character in "<([":
            depth += 1
        elif character in ")]" or (character == ">" and index and text[index - 1] != "-"):
            depth -= 1
        elif depth == 0 and text.startswith(separator, index):
            return text[:index], text[index + len(separator):]
    return None


def rust_item_path(name):
    """The source item through which a registered Rust name is called.

    A method of a trait implementation, printed `<X as path::Trait<A>>::m` or, for
    an impl outside the modules of both trait and type, `module::<impl
    path::Trait<A> for X>::m`, is called as the trait method `path::Trait::m`.
    Every other name is its own item: inherent methods, including `<impl X>`
    blocks, free functions and provided trait methods. Unsupported forms fail.
    """
    if name.startswith("<"):
        end = _closing_bracket(name, 0)
        parts = _split_top_level(name[1:end], " as ")
        trait = parts and parts[1]
    else:
        start = name.find("::<impl ")
        if start < 0:
            return name
        end = _closing_bracket(name, start + 2)
        parts = _split_top_level(name[start + len("::<impl "):end], " for ")
        trait = parts and parts[0]
    method = name[end + 1:]
    if not re.fullmatch(r"::[A-Za-z_][A-Za-z0-9_]*", method):
        raise ValueError(f"Unsupported Rust name form: {name}")
    if not parts:
        return name
    path = trait.strip().split("<", 1)[0]
    if not RUST_PATH.fullmatch(path):
        raise ValueError(f"Unsupported trait path in Rust name: {name}")
    return path + method


def rust_identities(source_map):
    """The exact Rust identities of each model, derived from the `rust_names` of its APIs.

    Crate name and version come from the pinned source record of the API; the item
    path comes from `rust_item_path` and the implementation path is the name
    itself. A model keeps every identity of every API that lists it, in registry
    order and without repetition. A model with no API or no Rust name has none.
    """
    interfaces = {row["id"]: row for row in source_map.get("interfaces", [])}
    result = {}
    for api in source_map.get("api", []):
        package, separator, version = interfaces[api["source_id"]]["crate"].rpartition("-")
        if not separator or not package or not version:
            raise ValueError(f"Invalid API crate identity: {api['id']}")
        for name in api["rust_names"]:
            identity = {"crate_name": package, "crate_version": version,
                        "item": rust_item_path(name), "implementation": name}
            for model in api["models"]:
                identities = result.setdefault(model, [])
                if identity not in identities:
                    identities.append(identity)
    return result


def load_source_map(package):
    """Expand exact checked inputs; schema 2 remains supported for audit controls.

    Schema 3 reviews whole module contents, sealed by the recorded SHA-256. Its
    declaration inventory comes from the complete Lean audit, not another copy
    of those declarations in JSON. Contracts and witnesses remain registered
    individually and checked against their exact compiled types.
    """
    paths = source_map_files(package)
    document = read_json(paths[0])
    if document["schema_version"] == 2:
        if "_module_reviews" in document:
            raise ValueError("Whole-module reviews require source-map schema 3")
        return document
    sections = {name: {} for name in SECTIONS}
    for path in paths[1:]:
        fragment = read_json(path)
        if not isinstance(fragment, dict):
            raise ValueError(f"Source-map fragment must be an object: {path.name}")
        fields(fragment, SECTIONS, f"fragment {path.name}")
        for section in SECTIONS:
            for identifier, row in mapping(fragment.get(section, {}), section).items():
                if identifier in sections[section]:
                    raise ValueError(f"Duplicate {section} identity across source-map fragments: {identifier}")
                sections[section][identifier] = deepcopy(row)
    packages = sections["packages"]
    for crate, pin in packages.items():
        fields(pin, {"repository", "revision", "path_prefix", "source_archive"}, f"crate pin {crate}")
        if (not isinstance(pin.get("repository"), str)
                or not isinstance(pin.get("path_prefix", ""), str)
                or ("revision" not in pin and "source_archive" not in pin)
                or ("revision" in pin and not isinstance(pin["revision"], str))
                or ("revision" not in pin and "path_prefix" in pin)):
            raise ValueError(f"Invalid immutable crate pin: {crate}")
        if "source_archive" in pin:
            archive_pin(crate, pin["source_archive"])
    interfaces = {}
    for identifier, row in sections["interfaces"].items():
        if any(field in row for field in ("id", "repository", "revision", "source_archive")):
            raise ValueError(f"Source interface repeats its identity or crate pin: {identifier}")
        crate = row.get("crate")
        if crate not in packages:
            raise ValueError(f"Source interface has no pinned crate: {identifier}")
        pin = packages[crate]
        relative = row.get("path")
        if not isinstance(relative, str):
            raise ValueError(f"Source interface has no path: {identifier}")
        interfaces[identifier] = {"id": identifier, **row, "repository": pin["repository"]}
        if "revision" in pin:
            interfaces[identifier].update(
                revision=pin["revision"], path_in_repository=row.get(
                    "path_in_repository", pin.get("path_prefix", "") + relative))
        elif "path_in_repository" in row or "repository_bytes" in row:
            raise ValueError(f"Repository correspondence requires a Git pin: {identifier}")
        if "source_archive" in pin:
            interfaces[identifier]["source_archive"] = {
                **deepcopy(pin["source_archive"]), "member": crate + "/" + relative}
            archive_source(interfaces[identifier])
    if set(packages) != {row["crate"] for row in interfaces.values()}:
        raise ValueError("Unused crate pins in source-map fragments")
    abstractions = []
    for identifier, row in sections["abstractions"].items():
        fields(row, {"modules", "source_ids", "argument", "limitations", "assumptions",
                     "section", "treatment"}, f"review {identifier}")
        hashes = row.get("modules")
        if not isinstance(hashes, dict):
            raise ValueError(f"Missing reviewed module hashes: {identifier}")
        abstractions.append({**row, "id": identifier, "modules": list(hashes), "model_sha256": hashes})
    result = {key: deepcopy(value) for key, value in document.items() if key != "fragments"}
    result.update({"schema_version": 2, "_module_reviews": True,
                   "interfaces": list(interfaces.values()), "abstractions": abstractions,
                   "models": [expand_model(identifier, row) for identifier, row in sections["models"].items()],
                   "api": [expand_api(identifier, row, interfaces) for identifier, row in sections["api"].items()]})
    if sections["compatibility"]:
        for identifier, row in sections["compatibility"].items():
            fields(row, {"models", "releases", "reviewed_on", "argument", "differences"},
                   f"compatibility review {identifier}")
        result["compatibility"] = [{"id": identifier, **row}
                                   for identifier, row in sections["compatibility"].items()]
    if sections["applicability_sources"] or sections["applicability"]:
        result["applicability_sources"] = sections["applicability_sources"]
        result["applicability"] = sections["applicability"]
        from solana_applicability import normalized_applicability
        normalized_applicability(result)
    return result
