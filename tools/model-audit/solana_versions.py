"""Function-level version reviews; an interval never authorizes an unlisted release.

The existing source registry remains authoritative for exact Rust identities.
Groups record a manual source argument and generate equality checks for the
complete mathematical contracts, including their preconditions and outcomes.
"""

from collections import defaultdict
from datetime import date
import json
import re
import urllib.request

from solana_source_map import fields, rust_identities


def version_key(version):
    """These reviews cover stable releases, including subsequently yanked ones."""
    if not isinstance(version, str) or not re.fullmatch(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)", version):
        raise ValueError(f"Expected an exact stable release: {version!r}")
    return tuple(map(int, version.split(".")))


def model_sources(document):
    sources = {row["id"]: row for row in document["interfaces"]}
    result = defaultdict(dict)
    for api in document["api"]:
        for model in api["models"]:
            result[model][api["source_id"]] = sources[api["source_id"]]
    return result


def compatibility_groups(document):
    """Validate explicit groups without guessing compatibility from names."""
    if not document.get("compatibility"):
        return []
    models = {row["id"]: row for row in document["models"]}
    sources = {row["id"]: row for row in document["interfaces"]}
    identities = rust_identities(document)
    seen_models, seen_ids, result = set(), set(), []
    for group in document.get("compatibility", []):
        fields(group, {"id", "models", "releases", "reviewed_on", "argument", "differences"}, "compatibility review")
        identifier = group.get("id")
        if (not isinstance(identifier, str) or not re.fullmatch(r"[a-z0-9][a-z0-9-]*", identifier)
                or identifier in seen_ids):
            raise ValueError("Invalid or repeated compatibility review identity")
        seen_ids.add(identifier)
        selected = group.get("models")
        if (not isinstance(selected, list) or not selected
                or any(not isinstance(model, str) or model not in models for model in selected)
                or len(selected) != len(set(selected)) or seen_models.intersection(selected)):
            raise ValueError(f"Unknown or repeated compatibility model: {identifier}")
        seen_models.update(selected)
        versions, expected = {}, None
        for model in selected:
            names = identities.get(model, [])
            if not names:
                raise ValueError(f"Compatibility model has no registered Rust identity: {model}")
            if len({row["crate_name"] for row in names}) != 1:
                raise ValueError(f"Compatibility member mixes source crates: {model}")
            by_release = defaultdict(set)
            for row in names:
                by_release[row["crate_version"]].add(
                    (row["crate_name"], row["item"], row["implementation"]))
            # One contract can retain several exact source bindings. Compare
            # the complete identity set of each release: comparing their union could
            # hide a different item or a missing implementation in one release.
            for version, signature in by_release.items():
                version_key(version)
                expected = signature if expected is None else expected
                if signature != expected or models[model]["kind"] != models[selected[0]]["kind"]:
                    raise ValueError(f"Compatibility review mixes functions or model roles: {identifier}")
                if version in versions:
                    raise ValueError(f"Repeated compatibility version: {identifier}: {version}")
                versions[version] = model
        crate = next(iter(expected))[0]
        releases = group.get("releases")
        if (not isinstance(releases, list) or not releases
                or any(not isinstance(release, str) for release in releases)):
            raise ValueError(f"Missing release window: {identifier}")
        if releases != sorted(set(releases), key=version_key) or not versions.keys() <= set(releases):
            raise ValueError(f"Invalid release window: {identifier}")
        try:
            date.fromisoformat(group["reviewed_on"])
        except (KeyError, ValueError, TypeError):
            raise ValueError(f"Missing review date: {identifier}") from None
        if not isinstance(group.get("argument"), str) or not group["argument"].strip():
            raise ValueError(f"Missing source correspondence argument: {identifier}")
        differences = group.get("differences", [])
        if not isinstance(differences, list):
            raise ValueError(f"Invalid behavior differences: {identifier}")
        different_versions = set()
        for row in differences:
            fields(row, {"source_id", "line", "anchor_text", "reason"}, "version difference")
            source = sources.get(row.get("source_id"))
            if source is None:
                raise ValueError(f"Unknown difference source: {identifier}")
            source_crate, _, version = source["crate"].rpartition("-")
            if (source_crate != crate or version not in releases or version in versions
                    or version in different_versions):
                raise ValueError(f"Conflicting or unrelated version difference: {identifier}")
            different_versions.add(version)
            if (type(row.get("line")) is not int or row["line"] < 1
                    or any(not isinstance(row.get(key), str) or not row[key].strip()
                           for key in ("anchor_text", "reason"))):
                raise ValueError(f"Missing difference evidence: {identifier}")
        result.append({**group, "crate": crate, "versions": versions, "differences": differences})
    return result


def version_ranges(versions, releases):
    """Compress only adjacent supported entries of the recorded release window."""
    groups, current = [], []
    for release in releases:
        if release in versions:
            current.append(release)
        elif current:
            groups.append(current)
            current = []
    if current:
        groups.append(current)
    return "; ".join(items[0] if len(items) == 1 else items[0] + "–" + items[-1] for items in groups)


def verify_release_windows(groups, fetch=None):
    """Check that a claimed range did not skip a published stable release.

    A release published later inside a window requires updating the review;
    it never becomes a supported identity merely by falling inside that range.
    Releases outside the window do not invalidate the review.
    """
    def download(crate):
        path = crate[:2] + "/" + crate[2:4] + "/" + crate
        with urllib.request.urlopen("https://index.crates.io/" + path, timeout=30) as response:
            return response.read().decode()

    fetch = download if fetch is None else fetch
    cached = {}
    for group in groups:
        crate = group["crate"]
        if crate not in cached:
            records = [json.loads(line) for line in fetch(crate).splitlines()]
            if any(row.get("name") != crate for row in records):
                raise ValueError(f"Wrong crate release index: {crate}")
            cached[crate] = {row["vers"] for row in records
                             if re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", row["vers"])}
        releases = group["releases"]
        lower, upper = version_key(releases[0]), version_key(releases[-1])
        actual = sorted((v for v in cached[crate] if lower <= version_key(v) <= upper), key=version_key)
        if actual != releases:
            raise ValueError(f"Release window needs review for {group['id']}: recorded {releases}, published {actual}")
