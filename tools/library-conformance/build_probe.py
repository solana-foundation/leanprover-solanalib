"""Native configuration receipts for drivers that expose their compiled settings.

The explicitly selected profile of Cargo is recorded separately from the observed cfg values of the executable. A workspace or environment override of the panic strategy
cannot be hidden by reading the leaf Cargo.toml alone.
"""

from __future__ import annotations

from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def configuration(spec: dict, path: Path) -> dict | None:
    probe = spec.get("build_probe")
    scope = spec.get("scope")
    if probe is None:
        require(scope is None, f"{path}: an explicit scope requires build_probe")
        return None
    require(isinstance(probe, dict) and set(probe) == {"argument", "profile", "panic"},
            f"{path}: build_probe requires argument, profile and panic")
    require(probe["argument"] == "--build-config", f"{path}: unsupported build probe argument")
    require(probe["profile"] in {"dev", "abort", "wrapping", "optimized"},
            f"{path}: build probe requires a known recording profile")
    require(probe["panic"] in ("abort", "unwind"), f"{path}: invalid claimed panic strategy")
    require(scope in ("whole-signature-mock", "projected-wrapper", "linked-source"),
            f"{path}: invalid native scope")
    return {**probe, "scope": scope}


def profile_flags(probe: dict | None) -> list[str]:
    return ["--profile", probe["profile"]] if probe is not None else []


def validate(probe: dict, observed: dict, host: bool, label: str) -> None:
    expected = {"scope", "panic", "debug_assertions", "solana_cfg", "pointer_width",
                "little_endian", "signature_check_enabled"}
    require(isinstance(observed, dict) and set(observed) == expected,
            f"{label}: build probe fields differ")
    require(observed["scope"] == probe["scope"], f"{label}: compiled mock/source scope differs")
    require(observed["panic"] == probe["panic"], f"{label}: compiled panic strategy differs")
    for flag in ("debug_assertions", "solana_cfg", "little_endian", "signature_check_enabled"):
        require(isinstance(observed[flag], bool), f"{label}: build probe {flag} is not boolean")
    require(observed["solana_cfg"] == (not host), f"{label}: compiled Solana cfg differs")
    require(type(observed["pointer_width"]) is int and observed["pointer_width"] == 64
            and observed["little_endian"], f"{label}: compiled target representation differs")
    require(not observed["signature_check_enabled"],
            f"{label}: compile-only signature checking was enabled during native recording")


def attach(manifest: dict, probe: dict | None, observed: dict | None) -> None:
    if probe is None:
        return
    require(observed is not None, "missing native build observation")
    manifest["rust"]["profile"] = probe["profile"]
    manifest["rust"]["panic"] = observed["panic"]
    manifest["scope"] = observed["scope"]
    manifest["build_probe"] = {"argument": probe["argument"],
                               "profile_flags": profile_flags(probe), "observed": observed}


def authenticate(manifest: dict, probe: dict | None, host: bool, label: str) -> None:
    if probe is None:
        require("build_probe" not in manifest and "scope" not in manifest,
                f"{label}: unexpected opt-in build receipt")
        return
    receipt = manifest.get("build_probe")
    require(isinstance(receipt, dict) and set(receipt) == {"argument", "profile_flags", "observed"},
            f"{label}: missing or malformed build probe receipt")
    require(receipt["argument"] == probe["argument"]
            and receipt["profile_flags"] == profile_flags(probe),
            f"{label}: recorded profile command differs")
    validate(probe, receipt["observed"], host, label)
    require(manifest.get("scope") == receipt["observed"]["scope"],
            f"{label}: claimed mock/source scope differs from the executable")
    require(manifest.get("rust", {}).get("profile") == probe["profile"],
            f"{label}: claimed profile differs from the selected profile")
    require(manifest.get("rust", {}).get("panic") == receipt["observed"]["panic"],
            f"{label}: claimed panic strategy differs from the executable")
