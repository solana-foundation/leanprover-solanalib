"""Validate compact source reviews and export the installed applicability API.

The source-map fragments are review inputs. The exported manifest needs only
the self-contained runtime in packages/solanalib-specs/tools; it never loads raw audit logs.
"""

from datetime import date
import json
from pathlib import Path
import re
import sys
import urllib.request

TOOLS = Path(__file__).resolve().parents[2] / "packages/solanalib-specs/tools"
sys.path.insert(0, str(TOOLS))
from applicability import (CRATES_IO, SCHEMA_VERSION, exact_version, normalize_profile,
                           object_fields, source_identity, strings, text, validate_manifest)
from solana_source_map import rust_identities, rust_item_path
from solana_specs_config import module_root


def catalog_names(model):
    root = module_root(model["contract"])
    path = model["contract"][len(root) + 1:]
    namespace = ("Solanalib.Specs.Core.SupportingCapabilities" if root == "Solanalib.Specs.Core"
                 else root + ".Capabilities")
    key = re.sub(r"[^A-Za-z0-9_]", "_", path.removesuffix("_contract"))
    return namespace + ".catalog", namespace + ".Key." + key


def _source_records(document):
    sources = document.get("applicability_sources")
    if not isinstance(sources, dict) or not sources:
        raise ValueError("Applicability needs reviewed source histories")
    normalized = {}
    for identifier, value in sources.items():
        text(identifier, "applicability source id")
        object_fields(value, {"package", "source", "reviewed_on", "releases", "evidence"},
                      "applicability source")
        package = text(value.get("package"), "reviewed package")
        source = source_identity(value.get("source"))
        try:
            date.fromisoformat(value["reviewed_on"])
        except (KeyError, TypeError, ValueError):
            raise ValueError(f"Missing source review date: {identifier}") from None
        evidence = strings(value.get("evidence", []), "source evidence")
        if not evidence:
            raise ValueError(f"Missing source evidence: {identifier}")
        releases = value.get("releases")
        if not isinstance(releases, dict) or not releases:
            raise ValueError(f"Missing explicit source releases: {identifier}")
        for version, release in releases.items():
            exact_version(version, "reviewed source release")
            object_fields(release, {"archive_url", "sha256", "repository", "revision", "path_prefix",
                                    "evidence", "yanked"}, "release provenance")
            if source["kind"] == "registry":
                url = text(release.get("archive_url"), "immutable crate archive URL")
                if source["url"] == CRATES_IO and url != (
                        f"https://static.crates.io/crates/{package}/{package}-{version}.crate"):
                    raise ValueError(f"Archive URL disagrees with reviewed release: {identifier}@{version}")
                if not isinstance(release.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", release["sha256"]):
                    raise ValueError(f"Missing archive digest: {identifier}@{version}")
            if "revision" in release and (not isinstance(release["revision"], str)
                    or not re.fullmatch(r"[0-9a-f]{40}", release["revision"])):
                raise ValueError(f"Invalid source revision: {identifier}@{version}")
            if "yanked" in release and not isinstance(release["yanked"], bool):
                raise ValueError(f"Invalid yank status: {identifier}@{version}")
            for field in ("repository", "path_prefix"):
                if field in release:
                    text(release[field], f"release {field}", empty=field == "path_prefix")
            if "evidence" in release:
                strings(release["evidence"], "release evidence")
        normalized[identifier] = {"package": package, "source": source, "releases": releases}
    return normalized


def normalized_applicability(document):
    """Flatten explicit item mappings while preserving every existing model ID."""
    sources = _source_records(document)
    records = document.get("applicability")
    if not isinstance(records, dict):
        raise ValueError("Missing per-model applicability records")
    models = {row["id"]: row for row in document["models"]}
    identities = rust_identities(document)
    if set(records) != set(models):
        raise ValueError(f"Incomplete function applicability: missing {sorted(set(models) - set(records))}; "
                         f"unknown {sorted(set(records) - set(models))}")
    output = []
    for identifier, record in sorted(records.items()):
        object_fields(record, {"profiles", "consumers", "conditions"}, f"applicability {identifier}")
        if ("profiles" in record) == ("consumers" in record):
            raise ValueError(f"Applicability must choose profiles or consumers: {identifier}")
        consumers = strings(record.get("consumers", []), "consumer models")
        if "consumers" in record and not consumers:
            raise ValueError(f"Empty consumer inheritance: {identifier}")
        profiles = record.get("profiles", [])
        if not isinstance(profiles, list):
            raise ValueError(f"Invalid source profiles: {identifier}")
        flattened = []
        profile_ids = set()
        for profile in profiles:
            object_fields(profile, {"id", "source", "releases", "items", "identity_dependency", "target", "features",
                                    "target_features", "dependencies", "conditions", "argument", "evidence"},
                          "compact applicability profile")
            profile_id = text(profile.get("id"), "profile id")
            if profile_id in profile_ids:
                raise ValueError(f"Duplicate compact profile: {identifier}/{profile_id}")
            profile_ids.add(profile_id)
            dependencies = profile.get("dependencies", [])
            if not isinstance(dependencies, list) or any(not isinstance(value, dict) for value in dependencies):
                raise ValueError(f"Invalid dependency constraints: {identifier}/{profile_id}")
            source = sources.get(profile.get("source"))
            if source is None:
                raise ValueError(f"Unknown profile source: {identifier}/{profile_id}")
            releases = strings(profile.get("releases"), "applicable releases")
            if not releases or not set(releases) <= source["releases"].keys():
                raise ValueError(f"Profile admits an unreviewed source release: {identifier}/{profile_id}")
            items = profile.get("items")
            if not isinstance(items, list) or not items:
                raise ValueError(f"Missing explicit source item mappings: {identifier}/{profile_id}")
            covered = set()
            mappings = set()
            for index, mapping in enumerate(items):
                object_fields(mapping, {"releases", "compatible_ranges", "item", "implementation"}, "source item mapping")
                selected = strings(mapping.get("releases"), "mapped releases")
                if not selected or not set(selected) <= set(releases):
                    raise ValueError(f"Item mapping is outside its profile: {identifier}/{profile_id}")
                covered.update(selected)
                implementation = text(mapping.get("implementation"), "Rust implementation path")
                # Renames are explicit mapping rows; no name comes from the
                # currently registered source identity of the model or a later release.
                derived = rust_item_path(implementation)
                item = text(mapping.get("item", derived), "called Rust item")
                if item != derived:
                    raise ValueError(f"Called item disagrees with implementation: {item} != {derived}")
                key = (tuple(selected), item, implementation)
                if key in mappings:
                    raise ValueError(f"Duplicate source item mapping: {identifier}/{profile_id}")
                mappings.add(key)
                normalized = {key: value for key, value in profile.items()
                              if key not in {"source", "items", "id", "releases"}}
                normalized.update({"id": profile_id if len(items) == 1 else f"{profile_id}:{index}",
                                   "package": source["package"], "source": source["source"],
                                   "releases": selected, "item": item, "implementation": implementation})
                if "compatible_ranges" in mapping:
                    normalized["compatible_ranges"] = mapping["compatible_ranges"]
                normalized["dependencies"] = [
                    {**dependency, "source": dependency.get("source") or {
                        "kind": "registry", "url": CRATES_IO, "revision": ""}}
                    for dependency in dependencies]
                flattened.append(normalize_profile(normalized))
            if covered != set(releases):
                raise ValueError(f"Incomplete source item mapping: {identifier}/{profile_id}")
        model = models[identifier]
        catalog, key = catalog_names(model)
        output.append({"model_id": identifier, "contract": model["contract"], "kind": model["kind"],
                       "source_call": bool(identities.get(identifier)),
                       "catalog": catalog, "catalog_key": key, "profiles": flattened,
                       "consumers": consumers, "conditions": strings(record.get("conditions", []),
                                                                          "model conditions")})
    scope = document.get("applicability_scope")
    if scope is None:
        scope = [document["binding_boundary"]] if document.get("binding_boundary") else []
    return validate_manifest({"schema_version": SCHEMA_VERSION, "scope": scope, "models": output})


def manifest_text(document):
    return json.dumps(normalized_applicability(document), indent=2, ensure_ascii=False) + "\n"


def verify_source_census(document, fetch=None):
    """Check the complete recorded stable histories without admitting new releases."""
    def download(package, source):
        if source["url"] != CRATES_IO:
            raise ValueError(f"No automatic census fetcher for registry {source['url']}")
        if len(package) == 1:
            path = "1/" + package
        elif len(package) == 2:
            path = "2/" + package
        elif len(package) == 3:
            path = "3/" + package[0] + "/" + package
        else:
            path = package[:2] + "/" + package[2:4] + "/" + package
        with urllib.request.urlopen("https://index.crates.io/" + path, timeout=30) as response:
            return response.read().decode()

    fetch = download if fetch is None else fetch
    cached = {}
    for source in _source_records(document).values():
        if source["source"]["kind"] != "registry":
            continue
        key = (source["package"], source["source"]["url"])
        if key not in cached:
            rows = [json.loads(line) for line in fetch(source["package"], source["source"]).splitlines()]
            if any(row.get("name") != source["package"] for row in rows):
                raise ValueError(f"Wrong package census for {source['package']}")
            cached[key] = {row["vers"]: row for row in rows}
        actual = cached[key]
        stable = {version for version in actual if re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version)}
        recorded = {version for version in source["releases"] if re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version)}
        if stable != recorded:
            raise ValueError(f"Source census needs review: {source['package']}; "
                             f"unrecorded {sorted(stable - recorded)}, missing {sorted(recorded - stable)}")
        for version, evidence in source["releases"].items():
            if version not in actual or actual[version].get("cksum") != evidence["sha256"]:
                raise ValueError(f"Published archive digest differs: {source['package']}@{version}")


def lean_profile(profile, *, multiline=False, review=True):
    """Emit exact selection data and conditions, optionally including the review explanation."""
    def literal(value):
        return json.dumps(text(value, "Lean string", empty=True), ensure_ascii=False)

    def array(values, render=literal):
        return "[" + ", ".join(render(value) for value in values) + "]"

    def record(fields):
        if multiline:
            # Other Unicode line separators may occur inside string literals.
            return "{\n" + ",\n".join(
                "  " + name + " := " + value.replace("\n", "\n  ")
                for name, value in fields) + "\n}"
        return "{ " + ", ".join(name + " := " + value for name, value in fields) + " }"

    def source(value):
        return record([(key, literal(value[key])) for key in ("kind", "url", "revision")])

    def target(value):
        return record([("field", literal(value["field"])), ("«include»", array(value["include"])),
                       ("«exclude»", array(value["exclude"]))]
                      + ([("reason", literal(value["reason"]))] if review else []))

    def features(value):
        return record([(key, array(value[key])) for key in ("all", "any", "none")]
                      + ([("reason", literal(value["reason"]))] if review else []))

    def dependency(value):
        origin = "none" if value["source"] is None else "some " + source(value["source"])
        fields = [("package", literal(value["package"])), ("source", origin),
                  ("releases", array(value["releases"]))]
        if review:
            fields.append(("reason", literal(value["reason"])))
        if value.get("compatible_ranges"):
            fields.append(("compatibleRanges", array(value["compatible_ranges"], interval)))
        return record(fields)

    def interval(value):
        return record([("lower", literal(value["lower"])), ("upper", literal(value["upper"]))])

    fields = [("id", literal(profile["id"])), ("package", literal(profile["package"])),
              ("source", source(profile["source"])), ("releases", array(profile["releases"])),
              ("item", literal(profile["item"])), ("implementation", literal(profile["implementation"]))]
    if profile.get("compatible_ranges"):
        fields.append(("compatibleRanges", array(profile["compatible_ranges"], interval)))
    if profile["target"]:
        fields.append(("target", array(profile["target"], target)))
    for field, name in (("features", "features"), ("target_features", "targetFeatures")):
        if any(profile[field][key] for key in ("all", "any", "none")):
            fields.append((name, features(profile[field])))
    if profile["dependencies"]:
        fields.append(("dependencies", array(profile["dependencies"], dependency)))
    if profile["identity_dependency"] is not None:
        fields.append(("identityDependency", "some " + literal(profile["identity_dependency"])))
    for field in (("conditions", "evidence") if review else ("conditions",)):
        if profile[field]:
            fields.append((field, array(profile[field])))
    if review:
        fields.append(("argument", literal(profile["argument"])))
    return record(fields)
