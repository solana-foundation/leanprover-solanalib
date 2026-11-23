"""Exact, declared byte correspondence between Git and published Rust sources."""

import hashlib
import re


def repository_bytes(interface):
    """A reviewed alternative is opt-in; existing records keep exact equality."""
    if "repository_bytes" not in interface:
        return None
    declared = interface["repository_bytes"]
    if (not isinstance(declared, dict)
            or set(declared) != {"sha256", "transform"}
            or declared["transform"] != "lf-to-crlf"
            or not isinstance(declared["sha256"], str)
            or not re.fullmatch(r"[0-9a-f]{64}", declared["sha256"])):
        raise ValueError(f"Invalid repository byte correspondence: {interface['id']}")
    return declared


def checked_digest(content, expected, interface):
    if hashlib.sha256(content).hexdigest() != expected:
        raise ValueError(f"Reviewed SDK source differs: {interface['id']}")


def from_repository(interface, content):
    """Verify immutable Git bytes before the sole declared packaging conversion."""
    declared = repository_bytes(interface)
    checked_digest(content, declared["sha256"] if declared else interface["sha256"], interface)
    if declared:
        if b"\r" in content:
            raise ValueError(f"Repository source is not LF-only: {interface['id']}")
        content = content.replace(b"\n", b"\r\n")
        checked_digest(content, interface["sha256"], interface)
    return content


def check_published(interface, content):
    """Keep the compiled source untouched and verify the inverse byte equation."""
    declared = repository_bytes(interface)
    checked_digest(content, interface["sha256"], interface)
    if declared:
        git = content.replace(b"\r\n", b"\n")
        if b"\r" in git or git.replace(b"\n", b"\r\n") != content:
            raise ValueError(f"Published source is not exact CRLF: {interface['id']}")
        checked_digest(git, declared["sha256"], interface)
