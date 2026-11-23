"""Strict, explicit retrieval of reviewed source bytes from published crates."""

import gzip
import hashlib
import io
from pathlib import PurePosixPath
import re
import tarfile
import zlib

from solana_source_bytes import check_published


# Bounds apply even when a declaration seals malformed or unusually large data.
MAX_ARCHIVE_BYTES = 32 * 1024 * 1024
MAX_TAR_BYTES = 128 * 1024 * 1024
MAX_MEMBER_BYTES = 16 * 1024 * 1024
MAX_MEMBERS = 10000
PIN_FIELDS = {"kind", "package", "version", "sha256"}
VERSION = r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)(?:-[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?(?:\+[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?"


def archive_pin(crate, declared):
    """Keep transport identity exact and independent of recorded Git provenance."""
    if (not isinstance(declared, dict) or set(declared) != PIN_FIELDS
            or any(not isinstance(value, str) for value in declared.values())
            or declared["kind"] != "crates-io"
            or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}", declared["package"])
            or not re.fullmatch(VERSION, declared["version"])
            or not re.fullmatch(r"[0-9a-f]{64}", declared["sha256"])
            or crate != declared["package"] + "-" + declared["version"]):
        raise ValueError(f"Invalid source archive declaration: {crate}")
    return declared


def canonical_path(path):
    return (isinstance(path, str) and bool(path) and "\\" not in path
            and not any(ord(char) < 32 or ord(char) == 127 for char in path)
            and not PurePosixPath(path).is_absolute()
            and all(part not in {"", ".", ".."} for part in path.split("/")))


def archive_source(interface):
    """Validate the expanded exact member; absence preserves repository fetches."""
    if "source_archive" not in interface:
        return None
    declared = interface["source_archive"]
    if not isinstance(declared, dict) or set(declared) != PIN_FIELDS | {"member"}:
        raise ValueError(f"Invalid source archive member: {interface['id']}")
    archive_pin(interface.get("crate"), {key: declared[key] for key in PIN_FIELDS})
    path = interface.get("path")
    if (not canonical_path(path) or not canonical_path(declared["member"])
            or declared["member"] != interface["crate"] + "/" + path
            or not isinstance(interface.get("sha256"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", interface["sha256"])):
        raise ValueError(f"Invalid source archive member: {interface['id']}")
    return declared


def archive_key(declared):
    return tuple(declared[key] for key in ("kind", "package", "version", "sha256"))


def archive_url(declared):
    name = declared["package"]
    return f"https://static.crates.io/crates/{name}/{name}-{declared['version']}.crate"


def archive_sources(content, interfaces):
    """Authenticate once, inspect bounded tar bytes, and check every selected file.

    No tar member is extracted to disk. Rejected archives cannot partially stage
    a group: the caller receives contents only after every selected hash passes.
    """
    if not interfaces:
        raise ValueError("Source archive has no selected interfaces")
    declared = archive_source(interfaces[0])
    if declared is None:
        raise ValueError("Source archive retrieval must be declared")
    for interface in interfaces:
        other = archive_source(interface)
        if other is None or archive_key(other) != archive_key(declared):
            raise ValueError("Source archive group has inconsistent declarations")
    if len(content) > MAX_ARCHIVE_BYTES:
        raise ValueError("Source archive exceeds compressed byte limit")
    if hashlib.sha256(content).hexdigest() != declared["sha256"]:
        raise ValueError("Source archive checksum differs")
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(content)) as stream:
            unpacked = stream.read(MAX_TAR_BYTES + 1)
    except (OSError, EOFError, zlib.error) as error:
        raise ValueError("Malformed source archive gzip") from error
    if len(unpacked) > MAX_TAR_BYTES:
        raise ValueError("Source archive exceeds uncompressed byte limit")
    if len(unpacked) % 512 or not unpacked.endswith(b"\0" * 1024):
        raise ValueError("Malformed source archive tar ending")
    crate = declared["package"] + "-" + declared["version"]
    wanted = {interface["source_archive"]["member"] for interface in interfaces}
    found, seen, end = {}, set(), 0
    try:
        with tarfile.open(fileobj=io.BytesIO(unpacked), mode="r:") as archive:
            for index, member in enumerate(archive):
                if index >= MAX_MEMBERS:
                    raise ValueError("Source archive exceeds member limit")
                name = member.name
                if (not canonical_path(name)
                        or not (name.startswith(crate + "/") or name == crate and member.isdir())
                        or name in seen):
                    raise ValueError(f"Invalid or duplicate source archive path: {name}")
                seen.add(name)
                if (not (member.isfile() or member.isdir()) or member.issparse()
                        or member.isdir() and member.size != 0):
                    raise ValueError(f"Source archive member is not a regular file or directory: {name}")
                if not 0 <= member.size <= MAX_MEMBER_BYTES:
                    raise ValueError(f"Source archive exceeds member byte limit: {name}")
                boundary = member.offset_data + ((member.size + 511) // 512) * 512
                if boundary > len(unpacked):
                    raise ValueError(f"Truncated source archive member: {name}")
                end = max(end, boundary)
                if name in wanted:
                    if not member.isfile():
                        raise ValueError(f"Selected source archive member is not a regular file: {name}")
                    found[name] = unpacked[member.offset_data:member.offset_data + member.size]
    except (tarfile.TarError, OSError, EOFError) as error:
        raise ValueError("Malformed source archive tar") from error
    if len(unpacked) - end < 1024 or any(unpacked[end:]):
        raise ValueError("Source archive has a missing or nonzero tar trailer")
    missing = wanted - found.keys()
    if missing:
        raise ValueError("Missing source archive members: " + ", ".join(sorted(missing)))
    result = {}
    for interface in interfaces:
        source = found[interface["source_archive"]["member"]]
        check_published(interface, source)
        result[interface["id"]] = source
    return result


def fetch_archive(interfaces, opener):
    """Fetch only the declared canonical archive, without a repository fallback."""
    declared = archive_source(interfaces[0])
    if declared is None:
        raise ValueError("Source archive retrieval must be declared")
    with opener(archive_url(declared), timeout=60) as response:
        content = response.read(MAX_ARCHIVE_BYTES + 1)
    return archive_sources(content, interfaces)
