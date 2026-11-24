"""Match reviewed function profiles against an explicitly resolved build.

An exported manifest needs only this module and the Python standard library.
In a repository checkout, lookup reads the current registry through the local loader.
Neither path requires network access, Cargo or Lean. Eligibility selects an existing
mathematical model; the returned interpretation conditions remain user obligations.
"""

from copy import deepcopy
import json
from pathlib import Path
import re


SCHEMA_VERSION = 1
CRATES_IO = "https://github.com/rust-lang/crates.io-index"
EXACT_VERSION = re.compile(
    r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)"
    r"(?:-[0-9A-Za-z]+(?:[.-][0-9A-Za-z]+)*)?(?:\+[0-9A-Za-z]+(?:[.-][0-9A-Za-z]+)*)?")
STABLE_VERSION = re.compile(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)")
BUILD_METADATA = re.compile(r"[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*")


def read_json(contents):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate JSON key: {key}")
            result[key] = value
        return result

    def invalid(value):
        raise ValueError(f"Non-JSON value: {value}")

    return json.loads(contents, object_pairs_hook=unique, parse_constant=invalid)


def object_fields(value, allowed, label):
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    extra = set(value) - set(allowed)
    if extra:
        raise ValueError(f"Unknown {label} fields: {sorted(extra)}")
    return value


def text(value, label, empty=False):
    if (not isinstance(value, str) or (not empty and not value.strip())
            or any(ord(c) < 32 or ord(c) == 127 for c in value)):
        raise ValueError(f"Invalid {label}")
    return value


def strings(value, label, empty=False):
    if not isinstance(value, list):
        raise ValueError(f"{label} must be a list")
    for item in value:
        text(item, label, empty=empty)
    if len(value) != len(set(value)):
        raise ValueError(f"Duplicate {label}")
    return list(value)


def exact_version(value, label="package version"):
    if not isinstance(value, str) or not EXACT_VERSION.fullmatch(value):
        raise ValueError(f"{label} must be an exact version: {value!r}")
    return value


def stable_version(value):
    """Cargo ranges ignore build metadata and do not admit prereleases."""
    if not isinstance(value, str):
        return None
    core, plus, metadata = value.partition("+")
    match = STABLE_VERSION.fullmatch(core)
    if match is None or (plus and not BUILD_METADATA.fullmatch(metadata)):
        return None
    return tuple(int(part) for part in match.groups())


def compatible_ranges(value, releases, source):
    """Validate explicit half-open ranges within one Cargo compatibility line.

    Exact releases retain the source-review evidence. Ranges extend eligibility
    under the recorded behavioral compatibility assumption, not extra review.
    """
    if not isinstance(value, list):
        raise ValueError("compatible_ranges must be a list")
    if value and (source is None or source["kind"] != "registry"):
        raise ValueError("Compatibility ranges require an explicit registry source")
    result = []
    for interval in value:
        object_fields(interval, {"lower", "upper"}, "compatibility range")
        bounds = [interval.get(key) for key in ("lower", "upper")]
        if any(not isinstance(bound, str) or not STABLE_VERSION.fullmatch(bound) for bound in bounds):
            raise ValueError("Range bounds must be stable major.minor.patch versions")
        lower, upper = map(stable_version, bounds)
        major, minor, patch = lower
        ceiling = ((major + 1, 0, 0) if major else
                   (0, minor + 1, 0) if minor else (0, 0, patch + 1))
        if not lower < upper <= ceiling:
            raise ValueError("Range must be nonempty and stay within one Cargo compatibility line")
        if not any(lower <= version < upper for release in releases
                   if (version := stable_version(release)) is not None):
            raise ValueError("Each compatibility range needs a reviewed reference release inside it")
        row = dict(zip(("lower", "upper"), bounds))
        if row in result:
            raise ValueError("Duplicate compatibility range")
        result.append(row)
    return result


def version_matches(requirement, actual):
    if actual in requirement["releases"]:
        return True
    version = stable_version(actual)
    return version is not None and any(
        stable_version(interval["lower"]) <= version < stable_version(interval["upper"])
        for interval in requirement.get("compatible_ranges", []))


def version_choices(requirement):
    references = ", ".join(requirement["releases"])
    ranges = requirement.get("compatible_ranges", [])
    if not ranges:
        return "reviewed releases {" + references + "}"
    return ("compatible ranges " + " or ".join(
        f">={interval['lower']}, <{interval['upper']}" for interval in ranges)
        + "; reviewed references {" + references + "}")


def source_identity(value):
    object_fields(value, {"kind", "url", "revision"}, "source identity")
    kind = value.get("kind")
    if not isinstance(kind, str) or kind not in {"registry", "git"}:
        raise ValueError("Source kind must be registry or git")
    url = text(value.get("url"), "source URL")
    revision = value.get("revision", "")
    if kind == "git":
        if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ValueError("Git source needs an exact lowercase 40-digit revision")
    elif revision != "":
        raise ValueError("Registry source has no git revision")
    return {"kind": kind, "url": url, "revision": revision}


def package_identity(value, label="package"):
    object_fields(value, {"package", "version", "source"}, label)
    return {"package": text(value.get("package"), f"{label} name"),
            "version": exact_version(value.get("version")),
            "source": source_identity(value.get("source"))}


def normalize_build(value):
    """Preserve unknown facts; an omitted feature set is not an empty set."""
    object_fields(value, {"package", "version", "source", "target", "features",
                          "target_features", "dependencies"}, "build")
    result = package_identity({key: value.get(key) for key in ("package", "version", "source")})
    facts = value.get("target", [])
    if not isinstance(facts, list):
        raise ValueError("Build target must be a list of field/value facts")
    seen = set()
    target = []
    for fact in facts:
        object_fields(fact, {"field", "value"}, "target fact")
        name = text(fact.get("field"), "target field")
        if name in seen:
            raise ValueError(f"Duplicate target fact: {name}")
        seen.add(name)
        target.append({"field": name, "value": text(fact.get("value"), "target value", empty=True)})
    result["target"] = target
    for name in ("features", "target_features"):
        result[name] = None if value.get(name) is None else strings(value[name], name)
    dependencies = value.get("dependencies", [])
    if not isinstance(dependencies, list):
        raise ValueError("Build dependencies must be a list of resolved packages")
    result["dependencies"] = [package_identity(item, "dependency") for item in dependencies]
    names = [item["package"] for item in result["dependencies"]]
    if len(names) != len(set(names)):
        raise ValueError("Ambiguous dependency package: supply the actual selected instance once")
    return result


def feature_filter(value, label):
    if value is None:
        value = {}
    object_fields(value, {"all", "any", "none", "reason"}, label)
    result = {key: strings(value.get(key, []), f"{label}.{key}") for key in ("all", "any", "none")}
    constrained = any(result.values())
    result["reason"] = text(value.get("reason", ""), f"{label} reason", empty=not constrained)
    if set(result["all"]) & set(result["none"]) or (
            result["any"] and set(result["any"]) <= set(result["none"])):
        raise ValueError(f"Contradictory {label}")
    return result


def normalize_profile(value):
    """Validate one flattened profile, shared by installed lookup and Lean data."""
    allowed = {"id", "package", "source", "releases", "compatible_ranges", "item", "implementation", "identity_dependency", "target",
               "features", "target_features", "dependencies", "conditions", "argument", "evidence"}
    object_fields(value, allowed, "profile")
    result = {key: text(value.get(key), f"profile {key}")
              for key in ("id", "package", "item", "implementation", "argument")}
    result["source"] = source_identity(value.get("source"))
    result["releases"] = strings(value.get("releases"), "profile releases")
    if not result["releases"]:
        raise ValueError("Profile releases must be nonempty")
    for version in result["releases"]:
        exact_version(version, "profile release")
    ranges = compatible_ranges(value.get("compatible_ranges", []), result["releases"], result["source"])
    if ranges:
        result["compatible_ranges"] = ranges
    target = value.get("target", [])
    if not isinstance(target, list):
        raise ValueError("Profile target must be a list")
    result["target"] = []
    seen = set()
    for rule in target:
        object_fields(rule, {"field", "include", "exclude", "reason"}, "target rule")
        field = text(rule.get("field"), "target field")
        if field in seen:
            raise ValueError(f"Duplicate profile target field: {field}")
        seen.add(field)
        include = strings(rule.get("include", []), "target include", empty=True)
        exclude = strings(rule.get("exclude", []), "target exclude", empty=True)
        if not include and not exclude:
            raise ValueError("Empty target rule; omit irrelevant target fields")
        if include and set(include) <= set(exclude):
            raise ValueError(f"Contradictory target rule: {field}")
        result["target"].append({"field": field, "include": include, "exclude": exclude,
                                 "reason": text(rule.get("reason"), "target behavior reason")})
    for name in ("features", "target_features"):
        result[name] = feature_filter(value.get(name), name)
    dependencies = value.get("dependencies", [])
    if not isinstance(dependencies, list):
        raise ValueError("Profile dependencies must be a list")
    result["dependencies"] = []
    seen = set()
    for dependency in dependencies:
        object_fields(dependency, {"package", "source", "releases", "compatible_ranges", "reason"}, "dependency constraint")
        name = text(dependency.get("package"), "dependency name")
        if name in seen:
            raise ValueError(f"Duplicate dependency constraint: {name}")
        seen.add(name)
        releases = strings(dependency.get("releases"), "dependency releases")
        if not releases:
            raise ValueError("Dependency constraint needs explicit reviewed releases")
        for version in releases:
            exact_version(version, "dependency release")
        requirement = {"package": name,
            "source": None if dependency.get("source") is None else source_identity(dependency["source"]),
            "releases": releases, "reason": text(dependency.get("reason"), "dependency behavior reason")}
        ranges = compatible_ranges(dependency.get("compatible_ranges", []), releases, requirement["source"])
        if ranges:
            requirement["compatible_ranges"] = ranges
        result["dependencies"].append(requirement)
    identity_dependency = value.get("identity_dependency")
    if identity_dependency is not None:
        text(identity_dependency, "defining dependency")
        if identity_dependency not in seen:
            raise ValueError("identity_dependency must name a constrained dependency")
    result["identity_dependency"] = identity_dependency
    result["conditions"] = strings(value.get("conditions", []), "interpretation conditions")
    result["evidence"] = strings(value.get("evidence", []), "source evidence")
    if not result["evidence"]:
        raise ValueError("Profile needs source evidence")
    return result


def validate_manifest(value):
    object_fields(value, {"schema_version", "scope", "models"}, "applicability manifest")
    if value.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("Unsupported applicability manifest schema")
    scope = strings(value.get("scope", []), "shared scope")
    models = value.get("models")
    if not isinstance(models, list) or not models:
        raise ValueError("Applicability manifest needs model records")
    records = []
    seen = set()
    for row in models:
        object_fields(row, {"model_id", "contract", "catalog", "catalog_key", "kind", "source_call", "profiles",
                           "consumers", "conditions"}, "model applicability")
        record = {key: text(row.get(key), f"model {key}")
                  for key in ("model_id", "contract", "catalog", "catalog_key", "kind")}
        if not isinstance(row.get("source_call"), bool):
            raise ValueError("Model source_call must be a Boolean derived from the source registry")
        record["source_call"] = row["source_call"]
        if record["model_id"] in seen:
            raise ValueError(f"Duplicate applicability model: {record['model_id']}")
        seen.add(record["model_id"])
        profiles = row.get("profiles", [])
        if not isinstance(profiles, list):
            raise ValueError("Model profiles must be a list")
        record["profiles"] = [normalize_profile(profile) for profile in profiles]
        profile_ids = [profile["id"] for profile in record["profiles"]]
        if len(profile_ids) != len(set(profile_ids)):
            raise ValueError(f"Duplicate profile id for {record['model_id']}")
        record["consumers"] = strings(row.get("consumers", []), "consumer models")
        record["conditions"] = strings(row.get("conditions", []), "model conditions")
        if profiles and record["consumers"]:
            raise ValueError("A model uses direct profiles or inherited consumers, not both")
        records.append(record)
    by_model = {row["model_id"]: row for row in records}
    completed, active = set(), set()

    def visit(identifier):
        if identifier not in by_model:
            raise ValueError(f"Unknown consumer model: {identifier}")
        if identifier in active:
            raise ValueError(f"Cyclic consumer inheritance: {identifier}")
        if identifier in completed:
            return
        active.add(identifier)
        for consumer in by_model[identifier]["consumers"]:
            visit(consumer)
        active.remove(identifier)
        completed.add(identifier)

    for identifier in by_model:
        visit(identifier)
    return {"schema_version": SCHEMA_VERSION, "scope": scope, "models": records}


def load_manifest(path=None):
    package = Path(__file__).resolve().parents[1]
    if path is None and (package / 'source-map.json').is_file():
        import sys
        support = package.parents[1] / 'tools/model-audit'
        if not (support / 'solana_source_map.py').is_file():
            raise ValueError('Registry lookup needs the repository loader; use --manifest with an exported manifest')
        sys.path.insert(0, str(support))
        from solana_source_map import load_source_map
        from solana_applicability import normalized_applicability
        return normalized_applicability(load_source_map(package))
    path = Path(path) if path is not None else package / 'applicability.json'
    return validate_manifest(read_json(path.read_text()))


def _source_name(source):
    return source["kind"] + " " + source["url"] + (
        " at " + source["revision"] if source["kind"] == "git" else "")


def match_profile(profile, build):
    """Explain each failed relevant constraint without demanding unrelated facts."""
    reasons = []

    def reject(code, message, unresolved=False):
        reasons.append({"code": code, "message": message,
                        "status": "unresolved" if unresolved else "unsupported"})

    if build["package"] != profile["package"]:
        reject("package_mismatch", f"Profile applies to {profile['package']}, not {build['package']}.")
    if build["source"] != profile["source"]:
        reject("source_mismatch", "Profile requires " + _source_name(profile["source"]) + ".")
    if not version_matches(profile, build["version"]):
        reject("release_excluded", f"Release {build['version']} is outside the profile constraint "
               + version_choices(profile) + ".")
    # Do not manufacture missing-fact obligations for a different source/version.
    if not reasons:
        facts = {fact["field"]: fact["value"] for fact in build["target"]}
        for rule in profile["target"]:
            field = rule["field"]
            if field not in facts:
                reject("target_unknown", f"Target fact {field} is required. {rule['reason']}", True)
            elif ((rule["include"] and facts[field] not in rule["include"])
                  or facts[field] in rule["exclude"]):
                reject("target_mismatch", f"Target {field}={facts[field]!r} does not match "
                       f"include={rule['include']}, exclude={rule['exclude']}. {rule['reason']}")
        for name in ("features", "target_features"):
            rule = profile[name]
            if not any(rule[key] for key in ("all", "any", "none")):
                continue
            actual = build[name]
            if actual is None:
                reject("features_unknown", f"Resolved {name} are required. {rule['reason']}", True)
                continue
            missing = sorted(set(rule["all"]) - set(actual))
            forbidden = sorted(set(rule["none"]) & set(actual))
            if missing or forbidden or (rule["any"] and not set(rule["any"]) & set(actual)):
                reject("features_mismatch", f"Resolved {name} do not match all={rule['all']}, "
                       f"any={rule['any']}, none={rule['none']}; actual={actual}. {rule['reason']}")
        selected = {dependency["package"]: dependency for dependency in build["dependencies"]}
        for requirement in profile["dependencies"]:
            actual = selected.get(requirement["package"])
            if actual is None:
                reject("dependency_unknown", f"Resolved dependency {requirement['package']} is required. "
                       + requirement["reason"], True)
            elif (not version_matches(requirement, actual["version"]) or
                  (requirement["source"] is not None and actual["source"] != requirement["source"])):
                reject("dependency_mismatch", f"Dependency {actual['package']}@{actual['version']} from "
                       f"{_source_name(actual['source'])} is outside the required source or "
                       f"{version_choices(requirement)}. {requirement['reason']}")
    status = ("unsupported" if any(row["status"] == "unsupported" for row in reasons)
              else "unresolved" if reasons else "eligible")
    return {"profile_id": profile["id"], "status": status, "reasons": reasons,
            "argument": profile["argument"], "conditions": list(profile["conditions"]),
            "evidence": list(profile["evidence"])}


def lookup(manifest, build, model_ids=None):
    """Return all matching models, including consumer-inherited mathematics.

    Consumer inheritance never copies the Rust item identity of the caller into the
    supporting model. Multiple eligible profiles can contribute distinct actual
    source mappings; their interpretation conditions remain attached per profile.
    """
    manifest = validate_manifest(manifest)
    build = normalize_build(build)
    records = {row["model_id"]: row for row in manifest["models"]}
    requested = set(records) if model_ids is None else set(model_ids)
    if requested - records.keys():
        raise ValueError(f"Unknown requested models: {sorted(requested - records.keys())}")
    results = {}

    def evaluate(identifier):
        if identifier in results:
            return results[identifier]
        row = records[identifier]
        result = {key: row[key] for key in ("model_id", "contract", "catalog", "catalog_key", "kind", "source_call")}
        result.update({"profiles": [], "identities": [], "consumers": [],
                       "conditions": list(row["conditions"]), "reasons": []})
        statuses = []
        for profile in row["profiles"]:
            outcome = match_profile(profile, build)
            result["profiles"].append(outcome)
            statuses.append(outcome["status"])
            if outcome["status"] == "eligible" and row["source_call"]:
                defining_package = build
                if profile["identity_dependency"] is not None:
                    defining_package = next(dependency for dependency in build["dependencies"]
                                            if dependency["package"] == profile["identity_dependency"])
                identity = {**{key: deepcopy(defining_package[key]) for key in ("package", "version", "source")},
                            "item": profile["item"], "implementation": profile["implementation"]}
                if identity not in result["identities"]:
                    result["identities"].append(identity)
        for consumer in row["consumers"]:
            answer = evaluate(consumer)
            statuses.append(answer["status"])
            result["consumers"].append({"model_id": consumer, "status": answer["status"],
                                        "conditions": answer["conditions"], "profiles": answer["profiles"],
                                        "reasons": answer["reasons"]})
        result["status"] = ("eligible" if "eligible" in statuses else "unresolved" if "unresolved" in statuses
                            else "unsupported")
        if not statuses:
            result["reasons"].append({"code": "no_applicable_profile", "status": "unsupported",
                                       "message": "No applicable source profile is registered for this model."})
        results[identifier] = result
        return result

    for identifier in sorted(requested):
        evaluate(identifier)
    output = [results[identifier] for identifier in sorted(requested)]
    status = ("eligible" if any(row["status"] == "eligible" for row in output)
              else "unresolved" if any(row["status"] == "unresolved" for row in output) else "unsupported")
    return {"schema_version": SCHEMA_VERSION, "status": status, "build": build,
            "scope": manifest["scope"], "models": output}
