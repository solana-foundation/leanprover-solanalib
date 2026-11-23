#!/usr/bin/env python3
"""Generate the complete function-version table and contract-equality controls.

--check checks generated files. --fetch-index independently checks the full
release census and every published stable version inside the binding windows.
Neither operation admits new source identities or changes a contract.
"""

import argparse
from collections import defaultdict
import json
from pathlib import Path
import sys

PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE.parents[1] / "tools/model-audit"))
from solana_source_map import load_source_map, rust_identities  # noqa: E402
from solana_versions import (compatibility_groups, model_sources, version_key,
                             version_ranges, verify_release_windows)  # noqa: E402
from generate_capabilities import declaration_modules
from lean_format import format_source, HEADER
from solana_specs_config import module_root  # noqa: E402
from solana_applicability import normalized_applicability, verify_source_census  # noqa: E402
from applicability import source_identity, version_choices  # noqa: E402


def cell(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def applicability_markdown(document, manifest):
    """Describe the shipped selection API, using only curated registry inputs."""
    if manifest is None:
        return []
    source_rows = document["applicability_sources"]

    def source_key(profile):
        return next(key for key, value in source_rows.items()
                    if value["package"] == profile["package"]
                    and source_identity(value["source"]) == profile["source"])

    def releases(profile):
        source = source_rows[source_key(profile)]
        universe = sorted(source["releases"], key=version_key)
        references = version_ranges(set(profile["releases"]), universe)
        ranges = profile.get("compatible_ranges", [])
        if ranges:
            return ("compatible " + " or ".join(f">={row['lower']}, <{row['upper']}" for row in ranges)
                    + "; reviewed references " + references)
        return references

    def requirements(profile):
        result = []
        for rule in profile["target"]:
            terms = []
            if rule["include"]:
                terms.append("in " + ", ".join(rule["include"]))
            if rule["exclude"]:
                terms.append("outside " + ", ".join(rule["exclude"]))
            result.append(rule["field"] + " " + " and ".join(terms) + ": " + rule["reason"])
        for field, name in (("features", "features"), ("target_features", "target features")):
            rule = profile[field]
            terms = []
            for key, label in (("all", "all"), ("any", "any"), ("none", "none")):
                if rule[key]:
                    terms.append(label + " of " + ", ".join(rule[key]))
            if terms:
                result.append(name + " " + "; ".join(terms) + ": " + rule["reason"])
        for dependency in profile["dependencies"]:
            versions = (version_choices(dependency) if dependency.get("compatible_ranges")
                        else "in {" + ", ".join(dependency["releases"]) + "}")
            result.append(dependency["package"] + " " + versions + ": " + dependency["reason"])
        if profile["identity_dependency"] is not None:
            result.append("Defining identity comes from the selected " + profile["identity_dependency"]
                          + " dependency")
        return "; ".join(result) or "No behavior-changing build restriction"

    entries = manifest["models"]
    lines = ["", "## Select a model for a resolved build", "",
             f"Every one of the {len(entries)} registered model entries has an applicability record.",
             "The lookup distinguishes exact reviewed releases from explicitly declared compatible ranges.",
             "Compatible ranges assume preservation of the modeled behavior, including relevant dependency",
             "operations and implementation-specific results; SemVer is evidence for that assumption, not a proof.",
             "Ranges stay within one Cargo compatibility line, retain the registry origin and exclude prereleases.",
             "Exact git revisions and profiles without a compatible range remain exact. No contract is weakened.",
             "Target, feature and dependency filters appear only where the source review records a behavior difference.",
             "Missing facts required by a profile produce `unresolved`; a known mismatch produces `unsupported`.", "",
             "```bash", "python3 tools/lookup_applicability.py --build build.json", "```", "",
             "Run from this package directory. Use `--model <registered-model-id>` to select one operation.",
             "The command also works in an installed specification bundle without repository tooling.",
             "It returns model, contract and catalog names, matching source item mappings, reasons for",
             "rejection and the existing interpretation conditions. See [the build and result schema](BINDINGS.md#selecting-a-reviewed-build).", "",
             "In Lean, `catalog.forBuild build` preserves the same keys, families, indices, roles and",
             "mathematical specifications, while selecting matching source-call identities at the actual release.",
             "Members without an existing source-call registration remain mathematical capabilities and",
             "receive no callable identity. The six source-less helpers inherit applicability through named consumers.", "",
             "The [curated source registry](source-map.json) records immutable archive checksums,",
             "exact git revisions and per-function source arguments. The [installed manifest](applicability.json)",
             "is generated from that registry. Neither matching nor source review supplies a Rust implementation proof."]
    if manifest["scope"]:
        lines += ["", "The shared interpretation boundary is:", ""]
        lines += ["- " + condition for condition in manifest["scope"]]
    grouped = defaultdict(list)
    for entry in entries:
        grouped[entry["catalog"]].append(entry)
    lines += ["", "## Function applicability", "",
              "Each profile is an alternative; all filters within that profile must hold.",
              "Renamed predecessor items are listed explicitly. The lookup prints the full interpretation",
              "conditions and source arguments for each alternative, including resolved dependency origins."]
    for catalog, selected in sorted(grouped.items()):
        lines += ["", "### " + catalog, "",
                  "| Model (role) | Applicable package releases and source mapping | Build profile |",
                  "| --- | --- | --- |"]
        for entry in selected:
            label = f"`{entry['model_id']}` ({entry['kind']})"
            if not entry["source_call"]:
                label += "; no source-call registration"
            if entry["consumers"]:
                values = [label, "Through " + "; ".join(f"`{name}`" for name in entry["consumers"]),
                          "Inherits mathematical applicability; no caller identity is copied"]
                lines.append("| " + " | ".join(cell(value) for value in values) + " |")
            elif not entry["profiles"]:
                lines.append("| " + cell(label) + " | none | No applicable reviewed profile |")
            else:
                for index, profile in enumerate(entry["profiles"]):
                    origin = profile["source"]
                    source = ("git " + origin["url"] + " at " + origin["revision"]
                              if origin["kind"] == "git" else "registry " + origin["url"])
                    operation = (f"{profile['package']} {releases(profile)}; {source}; "
                                 f"`{profile['implementation']}` (called item `{profile['item']}`)")
                    values = [label if index == 0 else "same model", operation,
                              profile["id"] + ": " + requirements(profile)]
                    lines.append("| " + " | ".join(cell(value) for value in values) + " |")
    return lines


def markdown(document, groups, manifest=None):
    identities = rust_identities(document)
    sources = model_sources(document)
    models = {row["id"]: row for row in document["models"]}
    membership = {model: group for group in groups for model in group["models"]}
    rows, unbound = defaultdict(list), []
    for model_id, model in sorted(models.items()):
        group = membership.get(model_id)
        if group and model_id != group["models"][0]:
            continue
        names = identities.get(model_id, [])
        if not names:
            pins = sorted({row["crate"] for row in sources.get(model_id, {}).values()})
            unbound.append((model["contract"], ", ".join(pins) or "No Rust source version"))
            continue
        crate = names[0]["crate_name"]
        versions = sorted({row["crate_version"] for row in names}, key=version_key)
        if group:
            versions = sorted(group["versions"], key=version_key)
            supported = version_ranges(versions, group["releases"])
            supported += f" ([review](#{group['id']}))"
        else:
            supported = ", ".join(versions)
        functions = sorted({row["implementation"] for row in names})
        for function in functions:
            rows[crate].append((function, model["kind"], supported, model["contract"]))
    lines = ["# Function version compatibility", "",
             "<!-- Generated by tools/version_compatibility.py; do not edit by hand. -->", "",
             "This catalog separates the released sources to which each existing mathematical",
             "contract applies from the exact Rust function bindings already registered in this checkout.",
             "Neither source review nor passing finite tests establish a Rust implementation proof."]
    lines += applicability_markdown(document, manifest)
    lines += ["", "## Registered exact bindings", "",
              "These are the existing public crate roots and source-call identities. The release",
              "applicability data above selects views of these catalogs without changing any contract.",
              "Consult the profiles of each model for other reviewed releases and build conditions.", "",
              "Ranges below abbreviate explicit registered versions, with no semver fallback.",
              "Where distinct contracts are retained, the generated equality controls compare their",
              "premises, outcomes and resource guarantees. Shared contracts need no self-equality check.",
              "The target, feature and dependency assumptions of each contract remain."]
    for crate, entries in sorted(rows.items()):
        lines += ["", "### " + crate, "", "| Function | Role | Registered releases | Contract |",
                  "| --- | --- | --- | --- |"]
        for function, role, versions, contract in sorted(entries):
            lines.append(f"| `{function}` | {role} | {versions} | `{contract}` |")
    lines += ["", "## Registered contract equality reviews", "",
              "These records identify exact registered versions and their source provenance.",
              "The generated controls compare distinct contract definitions, when a review retains them.",
              "Current released-source applicability is classified per model above."]
    for group in groups:
        argument = ("This section records the existing exact bindings. Current source applicability "
                    "is selected by the per-function profiles above and their immutable source reviews."
                    if manifest is not None else group["argument"])
        lines += ["", f"### {group['id']}", "",
                  f"Reviewed {group['reviewed_on']}; crate `{group['crate']}`.", "",
                  "Registered releases: " + ", ".join(f"`{v}`" for v in sorted(group["versions"], key=version_key)) + ".", "",
                  "Published releases in the review window: " + ", ".join(f"`{v}`" for v in group["releases"]) + ".", "",
                  argument, "", "| Version | Public contract | Pinned source |", "| --- | --- | --- |"]
        for version, model in sorted(group["versions"].items(), key=lambda pair: version_key(pair[0])):
            links = []
            for source in sources[model].values():
                if source["crate"] != f"{group['crate']}-{version}":
                    continue
                url = f"{source['repository']}/blob/{source['revision']}/{source['path_in_repository']}"
                links.append(f"[{source['path']}]({url})")
            lines.append(f"| {version} | `{models[model]['contract']}` | {'; '.join(links)} |")
        for difference in group["differences"]:
            source = next(row for row in document["interfaces"] if row["id"] == difference["source_id"])
            version = source["crate"].rpartition("-")[2]
            url = f"{source['repository']}/blob/{source['revision']}/{source['path_in_repository']}#L{difference['line']}"
            lines += ["", f"**Behavior differs in {version}:** {difference['reason']} ([source]({url}))."]
    lines += ["", "## Models without source-call registration", "",
              "These models remain in the inventory. Their source reviews do not supply a",
              "registered Rust function identity, so they are not callable version bindings.", "",
              "| Mathematical contract | Existing source review |", "| --- | --- |"]
    for contract, pins in unbound:
        lines.append(f"| `{contract}` | {pins} |")
    return "\n".join(lines) + "\n"


def equality_controls(document, groups):
    models = {row["id"]: row for row in document["models"]}
    # A release review can name one shared contract for several exact source
    # bindings. Keep equality checks only between distinct definitions.
    comparisons = [list(dict.fromkeys(models[model]["contract"] for model in group["models"]))
                   for group in groups]
    comparisons = [contracts for contracts in comparisons if len(contracts) > 1]
    contracts = {contract for comparison in comparisons for contract in comparison}
    declarations = declaration_modules({module_root(name) for name in contracts})
    imports = set()
    for contract in contracts:
        locations = declarations.get(contract, set())
        if len(locations) != 1:
            raise ValueError(f"Expected one contract module: {contract}")
        imports.update(locations)
    lines = ["module", "", "-- Generated by tools/version_compatibility.py; do not edit by hand.", ""]
    lines += ["public import " + module for module in sorted(imports)]
    lines += ["", "set_option autoImplicit false", "",
              "-- Compare whole contracts, including preconditions, errors and state effects."]
    for comparison in comparisons:
        for contract in comparison[1:]:
            lines += ["", f"example : {contract} =", f"    {comparison[0]} := rfl"]
    return format_source(HEADER + "\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--fetch-index", action="store_true")
    args = parser.parse_args()
    document = load_source_map(PACKAGE)
    groups = compatibility_groups(document)
    manifest = normalized_applicability(document) if "applicability" in document else None
    if args.fetch_index:
        verify_release_windows(groups)
        if manifest is not None:
            verify_source_census(document)
    generated = {PACKAGE / "VERSION_COMPATIBILITY.md": markdown(document, groups, manifest),
                 PACKAGE / "SolanalibTest/Specs/Core/VersionCompatibility.lean": equality_controls(document, groups)}
    if manifest is not None:
        generated[PACKAGE / "applicability.json"] = json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
    for path, text in generated.items():
        if args.check:
            if not path.is_file() or path.read_text() != text:
                raise SystemExit(f"Stale version compatibility output: {path.relative_to(PACKAGE)}")
        else:
            path.write_text(text)
    print(f"{'Checked' if args.check else 'Generated'} compatibility for {len(document['models'])} models; "
          f"{len(groups)} exact binding reviews; "
          f"{sum(len(row['profiles']) for row in manifest['models']) if manifest else 0} build profiles")


if __name__ == "__main__":
    main()
