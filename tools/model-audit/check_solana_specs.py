#!/usr/bin/env python3
"""Check portable spec ownership, reviewed sources, coverage, and all proof axioms.

These checks validate evidence identity and contract inventory. They do not prove
semantic correspondence with the SDK, its memory representation, or a compiler.
"""

import argparse
from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib
import urllib.request

from solana_specs_config import COMMON_ROOT, package_roots, package_configuration, module_root, crate_root
from solana_source_map import (load_source_map, rust_item_path, source_map_digest,
                               source_map_files, source_map_hashes)
from solana_applicability import normalized_applicability
from solana_source_bytes import repository_bytes, from_repository, check_published
from solana_source_archives import archive_source, archive_key, fetch_archive
from solana_versions import compatibility_groups, verify_release_windows
from import_tiers import header_imports, module_path


ROOT = Path(__file__).resolve().parents[2]
PACKAGE = ROOT / "packages/solanalib-specs"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FOUNDATION_MODULES = (
    "Solanalib.Contracts",
    "Solanalib.Contracts.Outcome",
    "Solanalib.Contracts.Family",
    "Solanalib.Contracts.Callback",
    "Solanalib.Contracts.Capabilities",
    "Solanalib.Contracts.Versioning",
)


def check_capability_catalogs(package):
    """Reject drift between the typed bundles and their existing source registry."""
    result = subprocess.run(
        [sys.executable, str(package / "tools/generate_capabilities.py"), "--check"],
        cwd=package, text=True, capture_output=True, check=False,
    )
    if result.returncode:
        raise ValueError("Capability catalog check failed:\n" + result.stdout + result.stderr)
    result = subprocess.run(
        [sys.executable, str(package / "tools/version_compatibility.py"), "--check"],
        cwd=package, text=True, capture_output=True, check=False,
    )
    if result.returncode:
        raise ValueError("Version compatibility check failed:\n" + result.stdout + result.stderr)


def discover(package):
    """Audit every registered module and reject source roots outside the inventory of Lake."""
    production, tests = package_roots(package)
    roots = (*production, *tests)
    result = {}
    for root in roots:
        if (package / root.replace(".", "/")).is_symlink() or not (package / (root.replace(".", "/") + ".lean")).is_file():
            raise ValueError(f"Missing or linked specification root: {root}")
        paths = [package / (root.replace(".", "/") + ".lean"), *(package / root.replace(".", "/")).rglob("*")]
        for path in paths:
            if path.is_symlink():
                raise ValueError(f"Linked specification source: {path}")
            if not path.is_file() or path.suffix != ".lean":
                continue
            components = path.relative_to(package).with_suffix("").parts
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) for part in components):
                raise ValueError(f"Unsupported specification module name: {path}")
            result[".".join(components)] = path
    # A missing library registration must not turn a new source into unaudited
    # code. Ignore build output, but inspect all source directories, including
    # unstaged files in a worktree under active development.
    for directory, directories, files in os.walk(package):
        directories[:] = [name for name in directories if name not in {".lake", ".git"}]
        for name in directories:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f"Linked specification source directory: {Path(directory) / name}")
        for filename in files:
            if filename.endswith(".lean"):
                path = Path(directory) / filename
                module = ".".join(path.relative_to(package).with_suffix("").parts)
                if module not in result:
                    raise ValueError(f"Unregistered specification source: {path}")
    for name, path in result.items():
        for line, target in header_imports(path.read_text()):
            imported = module_path(target)
            if module_root(".".join(imported)) in roots and ".".join(imported) not in result:
                raise ValueError(f"Missing specification import: {name}:{line}: {'.'.join(imported)}")
    return dict(sorted(result.items()))


def foundation_sources(package):
    """The actual local neutral dependency, separate from SDK model ownership."""
    configuration = package_configuration(package)
    libraries = configuration.get("_root_libraries", configuration.get("lean_lib", []))
    selected = [row for row in libraries if row.get("name") == "Solanalib.Contracts"]
    if not selected:
        return {}
    if len(selected) != 1:
        raise ValueError("Library foundation needs exactly one local library")
    library = selected[0]
    foundation = package / library.get("srcDir", ".")
    if foundation.is_symlink() or not foundation.is_dir():
        raise ValueError("Missing or linked library foundation source directory")
    name = "Solanalib.Contracts"
    if (library.get("roots", [name]) != [name]
            or set(library.get("globs", [name])) not in ({name, name + ".+"}, {name + ".*"})):
        raise ValueError("Library foundation requires exact recursive coverage")
    sources = {name: foundation.joinpath(*name.split(".")).with_suffix(".lean")
               for name in FOUNDATION_MODULES}
    for name, path in sources.items():
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing or linked library foundation source: {name}")
    expected = set(sources.values())
    for directory, directories, files in os.walk(foundation):
        directories[:] = [name for name in directories if name not in {".lake", ".git"}]
        for name in directories:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f"Linked library foundation source directory: {Path(directory) / name}")
        for filename in files:
            if filename.endswith(".lean") and Path(directory) / filename not in expected:
                raise ValueError(f"Unregistered library foundation source: {Path(directory) / filename}")
    return dict(sorted(sources.items()))


AUDIT = r'''
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open Lean Elab Command Meta in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let roots : Array Name := #[__SPEC_ROOTS__]
    let selected := fun name => roots.any (fun root => Name.isPrefixOf root name)
    -- A reference is either a named operation or one exact field of a named
    -- closed operation bundle. Preserve the receiver and projection identity;
    -- reducing its body would erase which operation was actually reviewed.
    let referenceIdentity := fun expression : Expr => Id.run do
      if let some name := expression.constName? then
        return toJson name.toString
      let args := expression.getAppArgs
      if args.size == 1 then
        if let some projection := expression.getAppFn.constName? then
          if (env.getProjectionFnInfo? projection).isSome then
            if let some receiver := args[0]!.constName? then
              return Json.mkObj [("projection", toJson projection.toString),
                                 ("receiver", toJson receiver.toString)]
      return Json.null
    let modules := env.header.moduleNames.filter selected
    let mut declarations : Array Json := #[]
    let mut audited := 0
    let mut theorems := 0
    for (name, info) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      let moduleName := env.header.moduleNames[index.toNat]!
      unless selected moduleName || Name.isPrefixOf `Solanalib.Runtime moduleName ||
          Name.isPrefixOf `Solanalib.Contracts moduleName do continue
      if selected moduleName || Name.isPrefixOf `Solanalib.Contracts moduleName then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
        audited := audited + 1
        if info.isTheorem then theorems := theorems + 1
      let signature ← forallTelescope info.type fun parameters conclusion => do
        -- Canonical vocabulary: no alias normalization changes identity.
        let head := conclusion.getAppFn.constName?
        let args := conclusion.getAppArgs
        -- Reduce only the closed Family value to its constructor. Inspect the
        -- field itself without unfolding the source contract it names. An
        -- eta-expanded `fun index => source_contract index` is the same exact
        -- function; a specialization or an unrelated equivalent predicate is
        -- not accepted as that identity.
        let mut familyContract : Option Name := none
        if head == some `Solanalib.Contracts.Model.Family && parameters.isEmpty &&
            info.levelParams.isEmpty then
          if let some value ← whnfUntil (mkConst name) `Solanalib.Contracts.Model.Family.mk then
            let fields := value.getAppArgs
            if fields.size == 7 then
              let field := fields[6]!
              familyContract := (field.etaExpanded?.getD field).constName?
        let contract :=
          if head == some `Solanalib.Contracts.Model.RealizedBy && args.size == 5 then
            args[3]!.constName?
          else if head == some `Solanalib.Contracts.Model.Holds && args.size == 7 then
            args[5]!.constName?
          else if head == some `Solanalib.Contracts.Model.HasExecution && args.size == 7 then
            args[5]!.constName?
          else if head == some `Solanalib.Contracts.Model.Satisfiable && args.size == 6 then
            args[5]!.constName?
          else if (head == some `Solanalib.Contracts.Model.FamilyReference ||
                   head == some `Solanalib.Contracts.Model.FamilySatisfiable) && args.size == 2 then
            args[0]!.constName?
          else if head == some `Solanalib.Contracts.Model.FamilyHasExecution && args.size == 3 then
            args[0]!.constName?
          else none
        let reference :=
          if head == some `Solanalib.Contracts.Model.RealizedBy && args.size == 5 then
            referenceIdentity args[4]!
          else if (head == some `Solanalib.Contracts.Model.Holds ||
                   head == some `Solanalib.Contracts.Model.HasExecution) && args.size == 7 then
            referenceIdentity args[6]!
          else if head == some `Solanalib.Contracts.Model.FamilyReference && args.size == 2 then
            referenceIdentity args[1]!
          else if head == some `Solanalib.Contracts.Model.FamilyHasExecution && args.size == 3 then
            referenceIdentity args[1]!
          else Json.null
        let sample :=
          if head == some `Solanalib.Contracts.Model.FamilySatisfiable && args.size == 2 then
            args[1]!.constName?
          else if head == some `Solanalib.Contracts.Model.FamilyHasExecution && args.size == 3 then
            args[2]!.constName?
          else none
        return [
          ("type_head", toJson (head.map Name.toString)),
          ("conclusion_contract", toJson (contract.map Name.toString)),
          ("conclusion_reference", reference),
          ("conclusion_sample", toJson (sample.map Name.toString)),
          ("family_contract", toJson (familyContract.map Name.toString)),
          ("parameters", toJson parameters.size),
          ("universe_parameters", toJson info.levelParams.length)]
      declarations := declarations.push (Json.mkObj ([
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("is_private", toJson (Name.isPrefixOf `_private name)),
        ("is_definition", toJson info.isDefinition),
        ("projection_parameters", toJson ((env.getProjectionFnInfo? name).map (·.numParams))),
        ("is_theorem", toJson info.isTheorem)] ++ signature))
    IO.println (Json.mkObj [
      ("audited_modules", toJson ((modules.qsort Name.lt).map Name.toString)),
      ("audited_constants", toJson audited), ("audited_theorems", toJson theorems),
      ("declarations", toJson declarations)]).compress
'''


def audit(package, modules):
    if modules != discover(package):
        raise ValueError("Specification audit must include the complete module inventory")
    foundations = foundation_sources(package)
    sources = dict(sorted((modules | foundations).items()))
    source_hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}
    # A plain Lean file exposes imported private proof bodies to collectAxioms.
    with tempfile.TemporaryDirectory(prefix="solanalib-specs-audit-") as temporary:
        source = Path(temporary) / "Audit.lean"
        roots = ", ".join(f"`{name}" for name in sorted({module_root(name) for name in sources}))
        source.write_text("".join(f"import {name}\n" for name in sources)
                          + AUDIT.replace("__SPEC_ROOTS__", roots))
        result = subprocess.run(
            ["lake", "--quiet", "--log-level=error", "--wfail", "lean", str(source)],
            cwd=package_configuration(package).get("_canonical_root", package),
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)
        if result.returncode:
            raise ValueError(f"Specification axiom audit failed:\n{result.stdout}")
        lines = [line for line in result.stdout.splitlines() if line.startswith('{"')]
        if len(lines) != 1:
            raise ValueError(f"Unexpected specification audit output:\n{result.stdout}")
        evidence = json.loads(lines[0])
        actual = set(evidence["audited_modules"])
        if actual != set(sources):
            raise ValueError(f"Specification audit module mismatch: missing {sorted(set(sources) - actual)}, extra {sorted(actual - set(sources))}")
        evidence["audited_modules"] = sorted(actual)
        if not evidence["audited_constants"] or not evidence["audited_theorems"]:
            raise ValueError("Empty specification axiom audit")
        if (modules != discover(package) or foundations != foundation_sources(package)
                or source_hashes != {
                    name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}):
            raise ValueError("Specification sources changed during the audit")
        evidence["source_sha256"] = source_hashes
        return evidence


def sdk_path(root, interface):
    """Keep source-map entries inside the dedicated source directory."""
    crate, relative = Path(interface["crate"]), Path(interface["path"])
    if (len(crate.parts) != 1 or crate.is_absolute() or relative.is_absolute()
            or ".." in relative.parts or crate.name in {".", ".."}):
        raise ValueError(f"Invalid SDK source path: {interface['id']}")
    return root / crate / relative


def fetch_sdk(document, registry):
    """Fetch immutable source files and fail closed on any reviewed-hash mismatch."""
    interfaces = source_interfaces(document)
    groups, archives = {}, {}
    for interface in interfaces.values():
        declared = archive_source(interface)
        if declared is not None:
            groups.setdefault(archive_key(declared), []).append(interface)
    for interface in interfaces.values():
        declared = archive_source(interface)
        if declared is not None:
            key = archive_key(declared)
            if key not in archives:
                archives[key] = fetch_archive(groups[key], urllib.request.urlopen)
            content = archives[key][interface["id"]]
        else:
            repository = interface["repository"]
            revision = interface["revision"]
            source_path = interface["path_in_repository"]
            url = repository.replace("https://github.com/", "https://raw.githubusercontent.com/")
            url += f"/{revision}/{source_path}"
            with urllib.request.urlopen(url, timeout=60) as response:
                content = response.read()
            content = from_repository(interface, content)
        destination = sdk_path(registry, interface)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)


def verify_sources(document, registry):
    """Check complete file identities before checking the selected API line anchors."""
    sources = {}
    for interface in source_interfaces(document).values():
        content = sdk_path(registry, interface).read_bytes()
        check_published(interface, content)
        sources[interface["id"]] = content.decode().splitlines()
    for row in document["api"]:
        lines = sources[row["source_id"]]
        if not 1 <= row["line"] <= len(lines) or lines[row["line"] - 1].strip() != row["anchor_text"]:
            raise ValueError(f"API source anchor changed: {row['id']}")
    for group in compatibility_groups(document):
        for row in group["differences"]:
            lines = sources[row["source_id"]]
            if not 1 <= row["line"] <= len(lines) or lines[row["line"] - 1].strip() != row["anchor_text"]:
                raise ValueError(f"Version difference source anchor changed: {group['id']}")
    return len(sources), len(document["api"])


def strings(value, label, *, nonempty=False):
    if (not isinstance(value, list) or any(not isinstance(item, str) or not item.strip() for item in value)
            or len(value) != len(set(value)) or nonempty and not value):
        raise ValueError(f"Invalid or repeated {label}")
    return value


def records(value, label, key="id"):
    if not isinstance(value, list):
        raise ValueError(f"Missing {label} inventory")
    result = {}
    for row in value:
        if not isinstance(row, dict) or not isinstance(row.get(key), str) or not row[key].strip():
            raise ValueError(f"Invalid {label} identity")
        if row[key] in result:
            raise ValueError(f"Duplicate {label} identity: {row[key]}")
        result[row[key]] = row
    return result


def source_interfaces(document):
    interfaces = records(document.get("interfaces"), "source interface")
    archive_routes = {}
    for identifier, interface in interfaces.items():
        for field in ("crate", "path", "repository", "sha256"):
            if not isinstance(interface.get(field), str) or not interface[field]:
                raise ValueError(f"Missing source interface {field}: {identifier}")
        sdk_path(Path("source-registry"), interface)
        repository = interface["repository"]
        if (not re.fullmatch(r"https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)
                or not re.fullmatch(r"[0-9a-f]{64}", interface["sha256"])):
            raise ValueError(f"Non-immutable SDK source: {identifier}")
        declared = archive_source(interface)
        if "revision" in interface or "path_in_repository" in interface or declared is None:
            revision = interface.get("revision")
            source_path = Path(interface.get("path_in_repository", ""))
            if (not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision)
                    or not source_path.parts or source_path.is_absolute() or ".." in source_path.parts):
                raise ValueError(f"Non-immutable SDK source: {identifier}")
        elif "repository_bytes" in interface:
            raise ValueError(f"Repository byte correspondence requires a Git pin: {identifier}")
        repository_bytes(interface)
        route = archive_key(declared) if declared is not None else None
        crate = interface["crate"]
        if crate in archive_routes and archive_routes[crate] != route:
            raise ValueError(f"Inconsistent source archive declarations: {crate}")
        archive_routes[crate] = route
    return interfaces


def reviewed_declaration(known, name, covered, label, reviewed=None):
    if not isinstance(name, str) or name not in known:
        raise ValueError(f"Unknown {label} declaration: {name}")
    declaration = known[name]
    if (declaration.get("module") not in covered or declaration.get("is_private") is not False
            or name.startswith("_private.")):
        raise ValueError(f"{label} is not public in a reviewed production module: {name}")
    if reviewed is not None and name not in reviewed:
        raise ValueError(f"{label} is absent from reviewed declaration inventory: {name}")
    return declaration


def closed_witness(known, name, covered, reviewed, *, head, contract, reference=None, sample=None):
    witness = reviewed_declaration(known, name, covered, "Model witness", reviewed)
    if not witness.get("is_theorem"):
        raise ValueError(f"Model witness is not a theorem: {name}")
    if witness.get("parameters") != 0 or witness.get("universe_parameters") != 0:
        raise ValueError(f"Model witness has parameters: {name}")
    if (witness.get("type_head") != "Solanalib.Contracts.Model." + head
            or witness.get("conclusion_contract") != contract
            or witness.get("conclusion_reference") != reference
            or witness.get("conclusion_sample") != sample):
        raise ValueError(f"Model witness does not establish the exact registered contract/reference/sample relation: {name}")


def verify_reference(known, reference, covered, reviewed):
    if isinstance(reference, str):
        declaration = reviewed_declaration(known, reference, covered, "Model reference", reviewed)
        if not declaration.get("is_definition") or declaration.get("universe_parameters") != 0:
            raise ValueError(f"Model reference must be a named monomorphic definition: {reference}")
        return
    if not isinstance(reference, dict) or set(reference) != {"projection", "receiver"}:
        raise ValueError(f"Model reference must name an operation or an exact closed field projection: {reference}")
    projection = reviewed_declaration(known, reference["projection"], covered, "Reference projection", reviewed)
    receiver = reviewed_declaration(known, reference["receiver"], covered, "Reference receiver", reviewed)
    if (not projection.get("is_definition") or projection.get("universe_parameters") != 0
            or projection.get("projection_parameters") != 0
            or not receiver.get("is_definition") or receiver.get("universe_parameters") != 0
            or receiver.get("parameters") != 0):
        raise ValueError(f"Model reference projection must use an exact closed monomorphic receiver: {reference}")


def verify_models(document, known, covered, reviewed, production):
    models = records(document.get("models"), "model")
    contracts, registered_families = set(), set()
    for identifier, model in models.items():
        if model.get("kind") not in {"full", "partial", "observation", "supporting"}:
            raise ValueError(f"Unknown mathematical model kind: {identifier}")
        if model.get("rust_proof_status") != "open":
            raise ValueError(f"Rust implementation proof status must remain open: {identifier}")
        for field in ("assumptions", "model_gaps", "remaining_requirements"):
            strings(model.get(field), f"model {field}: {identifier}")
        if model["kind"] == "full" and (model["model_gaps"] or model["remaining_requirements"]):
            raise ValueError(f"Full mathematical model still has model gaps: {identifier}")
        if model["kind"] == "partial" and not (model["model_gaps"] or model["remaining_requirements"]):
            raise ValueError(f"Partial mathematical model must record its remaining scope: {identifier}")
        kind = model.get("witness_kind")
        if kind not in {"RealizedBy", "Holds", "FamilyReference"}:
            raise ValueError(f"Unknown model witness kind: {identifier}")
        contract_name, reference_name = model.get("contract"), model.get("reference")
        contract = reviewed_declaration(known, contract_name, covered, "Model contract", reviewed)
        family = kind == "FamilyReference"
        family_name = model.get("family")
        separate_family = family and family_name is not None
        root = module_root(contract["module"])
        if not family and family_name is not None:
            raise ValueError(f"Non-family model has a family definition: {identifier}")
        contract_type = "Solanalib.Contracts.Model.Family" if family and not separate_family else "Solanalib.Contracts.Model"
        if (not contract.get("is_definition") or contract.get("type_head") != contract_type
                or (not separate_family and contract.get("parameters") != 0)
                or (separate_family and (not isinstance(contract.get("parameters"), int)
                                        or contract["parameters"] < 1))
                or contract.get("universe_parameters") != 0
                or (root != COMMON_ROOT and not contract_name.endswith("_contract"))):
            raise ValueError(f"Model predicate is not the registered {contract_type} definition: {identifier}")
        if root not in production or not contract_name.startswith(root + "."):
            raise ValueError(f"Model predicate is outside its production namespace: {identifier}")
        if contract_name in contracts:
            raise ValueError(f"Repeated model contract: {contract_name}")
        contracts.add(contract_name)
        predicate_name = contract_name
        if separate_family:
            indexed = reviewed_declaration(known, family_name, covered, "Model family", reviewed)
            if (not indexed.get("is_definition") or indexed.get("type_head") != "Solanalib.Contracts.Model.Family"
                    or indexed.get("parameters") != 0 or indexed.get("universe_parameters") != 0
                    or indexed.get("family_contract") != contract_name
                    or not family_name.startswith(root + ".")):
                raise ValueError(f"Closed family does not bind exactly the registered source contract: {identifier}")
            if family_name in registered_families:
                raise ValueError(f"Repeated model family: {family_name}")
            registered_families.add(family_name)
            predicate_name = family_name
        verify_reference(known, reference_name, covered, reviewed)
        witnesses = strings(model.get("witnesses"), f"model witnesses: {identifier}", nonempty=True)
        satisfiability = strings(model.get("satisfiability_witnesses"), f"satisfiability witnesses: {identifier}")
        if len(satisfiability) != 1:
            raise ValueError(f"Model needs one precondition satisfiability witness: {identifier}")
        execution = strings(model.get("execution_witnesses", []), f"execution witnesses: {identifier}")
        if kind != "RealizedBy" and len(execution) != 1:
            raise ValueError(f"Outcome/family model needs one inhabited reference execution witness: {identifier}")
        if kind == "RealizedBy" and execution:
            raise ValueError(f"Total reference model does not register an unrelated outcome execution: {identifier}")
        sample_name = model.get("sample")
        if family:
            sample = reviewed_declaration(known, sample_name, covered, "Model sample", reviewed)
            if (not sample.get("is_definition") or sample.get("parameters") != 0
                    or sample.get("universe_parameters") != 0):
                raise ValueError(f"Family sample must be a named closed definition: {identifier}")
        elif sample_name is not None:
            raise ValueError(f"Non-family model has a family sample: {identifier}")
        for name in witnesses:
            closed_witness(known, name, covered, reviewed, head=kind,
                           contract=predicate_name, reference=reference_name)
        closed_witness(known, satisfiability[0], covered, reviewed,
                       head="FamilySatisfiable" if family else "Satisfiable",
                       contract=predicate_name, sample=sample_name)
        for name in execution:
            closed_witness(known, name, covered, reviewed,
                           head="FamilyHasExecution" if family else "HasExecution",
                           contract=predicate_name, reference=reference_name, sample=sample_name)
    # The source-facing inventory is complete even when a root does not import
    # a module or nobody mentions a newly added public contract in the map.
    expected = set()
    for name, declaration in known.items():
        module = declaration.get("module", "")
        root = module_root(module)
        if (root in production and root != COMMON_ROOT and declaration.get("is_definition")
                and declaration.get("is_private") is False
                and not name.startswith("_private.")
                and (name.endswith("_contract") or declaration.get("type_head") in
                     {"Solanalib.Contracts.Model", "Solanalib.Contracts.Model.Family"})):
            expected.add(name)
    versioned = {name for name in contracts | registered_families if not name.startswith(COMMON_ROOT + ".")}
    if expected != versioned:
        raise ValueError(f"Incomplete model inventory: missing {sorted(expected - versioned)}, extra {sorted(versioned - expected)}")
    return models


def reviewed_api_alias(row, interface, profiles):
    """Require exact defining profiles for registered source-call identities.

    The normalized profiles already validate source histories, immutable release
    evidence, item mappings and build conditions. This registration check does
    not replace selecting an eligible concrete build. A reexport profile cannot
    transfer the identity of its dependency to the facade.
    """
    package = re.fullmatch(r"(.+)-(\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?)", interface["crate"])
    names = strings(row.get("rust_names"), "API alias Rust names")
    return bool(package and names) and all(any(
        profile["package"] == package.group(1)
        and package.group(2) in profile["releases"]
        and profile["identity_dependency"] is None
        and profile["item"] == rust_item_path(name)
        and profile["implementation"] == name
        for profile in profiles) for name in names)


def verify_map(package, modules, audit_result, registry=None):
    document = load_source_map(package)
    production, tests = package_roots(package)
    if modules != discover(package):
        raise ValueError("Source-map validation needs the complete current module inventory")
    foundations = foundation_sources(package)
    sources = modules | foundations
    if set(audit_result.get("audited_modules", [])) != set(sources):
        raise ValueError("Source-map validation needs the complete audited module inventory")
    if audit_result.get("source_sha256") != {
            name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in sources.items()}:
        raise ValueError("Source-map validation needs the exact audited source identities")
    known = records(audit_result.get("declarations"), "audited declaration", "name")
    interfaces = source_interfaces(document)
    abstractions = records(document.get("abstractions"), "abstraction")
    covered, reviewed = set(), set()
    for identifier, row in abstractions.items():
        names = set(strings(row.get("modules"), f"reviewed modules: {identifier}", nonempty=True))
        hashes = row.get("model_sha256")
        if not isinstance(hashes, dict) or covered & names or names != set(hashes):
            raise ValueError(f"Invalid or repeated reviewed modules: {identifier}")
        covered |= names
        for name, expected in hashes.items():
            if (not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected)
                    or name not in sources or hashlib.sha256(sources[name].read_bytes()).hexdigest() != expected):
                raise ValueError(f"Reviewed specification content differs: {name}")
        if document.get("_module_reviews"):
            # Exact module hashes seal all public declarations. The complete
            # Lean audit supplies their identities, so a second generated list
            # cannot silently become stale or hide a newly added contract.
            declarations = [name for name, declaration in known.items()
                            if declaration.get("module") in names and declaration.get("is_private") is False
                            and not name.startswith("_private.")]
        else:
            declarations = strings(row.get("declarations"), f"reviewed declarations: {identifier}")
        for name in declarations:
            if known.get(name, {}).get("module") not in names:
                raise ValueError(f"Unknown or misplaced reviewed declaration: {name}")
        reviewed.update(declarations)
        if not set(strings(row.get("source_ids"), f"reviewed sources: {identifier}")) <= interfaces.keys():
            raise ValueError(f"Unknown reviewed source: {identifier}")
        if (not isinstance(row.get("argument"), str) or not row["argument"].strip()
                or not strings(row.get("limitations"), f"correspondence limitations: {identifier}", nonempty=True)):
            raise ValueError(f"Missing correspondence scope: {identifier}")
    expected = {name for name in modules if module_root(name) in production} | set(foundations)
    if covered != expected:
        raise ValueError(f"Incomplete module review: missing {sorted(expected - covered)}, extra {sorted(covered - expected)}")
    models = verify_models(document, known, covered, reviewed, production)
    api = records(document.get("api"), "API")
    bindings_seen = {}
    model_releases = {}
    source_bound_models = set()
    for row in api.values():
        if row.get("source_id") in interfaces:
            for model_id in strings(row.get("models"), "API models"):
                model_releases.setdefault(model_id, set()).add(interfaces[row["source_id"]]["crate"])
                if row.get("rust_names"):
                    source_bound_models.add(model_id)
    applicability_profiles = None
    for identifier, row in api.items():
        if row.get("source_id") not in interfaces:
            raise ValueError(f"Unknown API source: {identifier}")
        if row.get("status") not in {"contracted", "deferred"}:
            raise ValueError(f"Unknown coverage status: {identifier}")
        if (not isinstance(row.get("line"), int) or isinstance(row["line"], bool) or row["line"] < 1
                or not isinstance(row.get("anchor_text"), str) or not row["anchor_text"].strip()):
            raise ValueError(f"Missing API source anchor: {identifier}")
        if any(field in row for field in ("contracts", "witnesses", "satisfiability_witnesses", "execution_witnesses")):
            raise ValueError(f"API evidence must refer to models instead of duplicated witness fields: {identifier}")
        selected = strings(row.get("models"), f"API models: {identifier}")
        if row["status"] == "contracted" and not selected:
            raise ValueError(f"Contracted API lacks a mathematical model: {identifier}")
        if row["status"] == "deferred" and selected:
            raise ValueError(f"Deferred API cannot claim modeled coverage: {identifier}")
        interface = interfaces[row["source_id"]]
        # The module belongs to the library; the interface retains the exact
        # reviewed release and immutable source. A shared contract can have
        # API rows for several releases without inventing a versioned module.
        source_package, _, _ = interface["crate"].rpartition("-")
        public_root = crate_root(source_package)
        for model_id in selected:
            if model_id not in models:
                raise ValueError(f"Unknown API model: {identifier}: {model_id}")
            contract = models[model_id]["contract"]
            if not contract.startswith(public_root + "."):
                raise ValueError(f"API model has a different source crate: {identifier}: {model_id}")
            if model_id in source_bound_models and (
                    "applicability" in document or len(model_releases[model_id]) > 1):
                if applicability_profiles is None:
                    applicability_profiles = (
                        {model["model_id"]: model["profiles"] for model in
                         normalized_applicability(document)["models"]}
                        if "applicability" in document else {})
                profiles = applicability_profiles.get(model_id, [])
                record = document.get("applicability", {}).get(model_id)
                # A partial interface can retain exact source metadata for
                # manual conditional Entries while explicitly admitting no
                # automatic build. Consumer inheritance is not that case.
                manual_partial = (models[model_id]["kind"] == "partial"
                                  and bool(row.get("rust_names"))
                                  and isinstance(record, dict)
                                  and record.get("profiles") == []
                                  and "consumers" not in record and profiles == [])
                if not manual_partial and not reviewed_api_alias(row, interface, profiles):
                    raise ValueError(f"API model has a source-call registration without an exact "
                                     f"reviewed applicability profile: {identifier}: {model_id}")
        for name in strings(row.get("clients"), f"API clients: {identifier}"):
            declaration = known.get(name, {})
            if (not declaration.get("is_theorem") or declaration.get("is_private") is not False
                    or module_root(declaration.get("module", "")) not in tests):
                raise ValueError(f"API client is not a public mathematical test theorem: {identifier}: {name}")
        for name in strings(row.get("model_dependencies"), f"API model dependencies: {identifier}"):
            if name not in known:
                raise ValueError(f"Unknown API declaration: {identifier}: {name}")
        if (not isinstance(row.get("scope"), str) or not row["scope"].strip()
                or not strings(row.get("binding_obligations"), f"binding obligations: {identifier}", nonempty=True)):
            raise ValueError(f"Missing API scope or binding obligation: {identifier}")
        rust_names = strings(row.get("rust_names"), f"exact Rust names: {identifier}")
        bindings = row.get("inventory_bindings")
        if not isinstance(bindings, list):
            raise ValueError(f"Missing exact inventory bindings: {identifier}")
        local_ids = set()
        for binding in bindings:
            if not isinstance(binding, dict) or set(binding) != {"identity", "source_name", "package"}:
                raise ValueError(f"Invalid inventory binding: {identifier}")
            identity, source_name, package_identity = binding["identity"], binding["source_name"], binding["package"]
            if (not isinstance(identity, str) or not identity or identity in local_ids
                    or source_name not in rust_names or not isinstance(package_identity, dict)
                    or set(package_identity) != {"name", "version"}
                    or any(not isinstance(value, str) or not value for value in package_identity.values())
                    or f"{package_identity['name']}-{package_identity['version']}" != interface["crate"]):
                raise ValueError(f"Inventory binding does not match the exact API source identity: {identifier}")
            local_ids.add(identity)
            if identity in bindings_seen and bindings_seen[identity] != identifier:
                raise ValueError(f"Inventory identity has conflicting API bindings: {identity}")
            bindings_seen[identity] = identifier
    versions = compatibility_groups(document)
    files, checked = verify_sources(document, registry) if registry is not None else (0, 0)
    return {"reviewed_modules": len(covered), "api_entries": len(api),
            "version_compatibility_reviews": len(versions),
            "contracted_api_entries": sum(row["status"] == "contracted" for row in api.values()),
            "models_checked": len(models), "model_ids": sorted(models),
            "contract_reference_witnesses_checked": sum(len(row["witnesses"]) for row in models.values()),
            "contract_satisfiability_witnesses_checked": len(models),
            "contract_execution_witnesses_checked": sum(len(row.get("execution_witnesses", [])) for row in models.values()),
            "family_models_checked": sum(row["witness_kind"] == "FamilyReference" for row in models.values()),
            "inventory_bindings_checked": len(bindings_seen),
            "sdk_files_checked": files, "sdk_api_anchors_checked": checked,
            "rust_proof_status": "open",
            "correspondence": "manual source argument; Rust implementation bindings remain separate"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sources = parser.add_mutually_exclusive_group()
    sources.add_argument("--registry", type=Path, help="exact SDK crate sources in Cargo registry layout")
    sources.add_argument("--fetch-sdk", action="store_true", help="fetch and verify every pinned SDK source")
    parser.add_argument("--output", type=Path, help="optional validation receipt")
    args = parser.parse_args()
    manifest_hashes = source_map_hashes(PACKAGE)
    check_capability_catalogs(PACKAGE)
    modules = discover(PACKAGE)
    result = audit(PACKAGE, modules)
    with ExitStack() as stack:
        registry = args.registry
        if args.fetch_sdk:
            registry = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="solanalib-specs-sdk-")))
            document = load_source_map(PACKAGE)
            verify_release_windows(compatibility_groups(document))
            fetch_sdk(document, registry)
        checked = verify_map(PACKAGE, modules, result, registry)
    if source_map_hashes(PACKAGE) != manifest_hashes:
        raise ValueError("Source-map inputs changed during the audit")
    result.pop("declarations")
    result.update(checked)
    result["source_map_sha256"] = source_map_digest(PACKAGE)
    result["source_map_files_sha256"] = manifest_hashes
    result["allowed_axioms"] = sorted(ALLOWED_AXIOMS)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "source_sha256"}, sort_keys=True))


if __name__ == "__main__":
    main()
