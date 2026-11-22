#!/usr/bin/env python3
"""Replay finite Agave/model observations without editing either development.

The model-only replay needs Python 3.12 and the Lean 4.34.0 toolchain of the model. It checks
fresh model observations against the committed outputs of a recorded native run.
A full native replay additionally needs pinned Rust 1.97.1 and the sealed Agave
source archive. Cargo builds only program-runtime and its dependencies, under
its pinned lock; the driver links the exact emitted artifacts of Cargo.
"""

from __future__ import annotations

import argparse
import collections
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tarfile
import time
import tomllib
from datetime import datetime, timezone


REVISION = "a203300045b405f86c9c84308b2eae76af69ac3b"
ARCHIVE_SHA256 = "917912ac67fc0b6ffec94e33e1ce113db581e1f1706aa1ecbe4224b967b15f30"
ARCHIVE_URL = f"https://codeload.github.com/anza-xyz/agave/tar.gz/{REVISION}"
RUST = "1.97.1"
LEAN = "leanprover/lean4:v4.34.0"
AXIOM_THEOREM = "SolanalibTest.Conformance.Runtime.unsignedPrepare_eq"
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound"})
TARGET = "x86_64-unknown-linux-gnu"
ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
MODEL = REPO / "packages/solanalib-runtime"
EXTERNS = {
    "solana_account", "solana_account_info", "solana_instruction", "solana_pubkey",
    "solana_rent", "solana_sdk_ids", "solana_transaction_context",
    "solana_program_runtime", "solana_svm_callback", "solana_svm_feature_set",
}
ACCOUNT_OPERATIONS = {
    "read_fields", "set_lamports", "checked_add", "checked_sub", "set_data",
    "set_length", "set_owner", "set_executable", "can_data", "can_resize", "missing_account",
}
OUTPUT_COLUMNS = (
    "id", "kind", "outcome", "accounts", "resize_delta", "pop_outcome",
    "serialized_before", "serialized_after", "auxiliary",
)
HARNESS_FILES = (
    "run.py", "test_run.py", "README.md", "SolanalibTest/Conformance/Runtime.lean", "agave_cases.rs",
    "cpi_cases.rs", "accounts.tsv", "serialization.tsv", "cpi.tsv",
    "expected-native.tsv.gz", "expected-native.json",
)
NATIVE_INPUT_FILES = ("agave_cases.rs", "cpi_cases.rs", "accounts.tsv", "serialization.tsv", "cpi.tsv")
# The unparameterized constructors of the pinned Solanalib/Runtime/Error.lean.
# Custom errors need an explicit common wire encoding before adding such cases.
ERROR_NAMES = {
    "GenericError", "InvalidArgument", "InvalidInstructionData", "InvalidAccountData",
    "AccountDataTooSmall", "InsufficientFunds", "IncorrectProgramId", "MissingRequiredSignature",
    "AccountAlreadyInitialized", "UninitializedAccount", "UnbalancedInstruction", "ModifiedProgramId",
    "ExternalAccountLamportSpend", "ExternalAccountDataModified", "ReadonlyLamportChange",
    "ReadonlyDataModified", "DuplicateAccountIndex", "ExecutableModified", "RentEpochModified",
    "NotEnoughAccountKeys", "AccountDataSizeChanged", "AccountNotExecutable", "AccountBorrowFailed",
    "AccountBorrowOutstanding", "DuplicateAccountOutOfSync", "InvalidError", "ExecutableDataModified",
    "ExecutableLamportChange", "ExecutableAccountNotRentExempt", "UnsupportedProgramId", "CallDepth",
    "MissingAccount", "ReentrancyNotAllowed", "MaxSeedLengthExceeded", "InvalidSeeds", "InvalidRealloc",
    "ComputationalBudgetExceeded", "PrivilegeEscalation", "ProgramEnvironmentSetupFailure",
    "ProgramFailedToComplete", "ProgramFailedToCompile", "Immutable", "IncorrectAuthority",
    "BorshIoError", "AccountNotRentExempt", "InvalidAccountOwner", "ArithmeticOverflow",
    "UnsupportedSysvar", "IllegalOwner", "MaxAccountsDataAllocationsExceeded", "MaxAccountsExceeded",
    "MaxInstructionTraceLengthExceeded", "BuiltinProgramsMustConsumeComputeUnits",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def digest_json(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def checked_axioms(output: str) -> list[str]:
    """Require exactly the complete, allow-listed report of the expected theorem."""
    report = output.strip()
    if report == f"'{AXIOM_THEOREM}' does not depend on any axioms":
        return []
    match = re.fullmatch(rf"'{re.escape(AXIOM_THEOREM)}' depends on axioms:\s*\[([^\[\]]*)\]", report)
    require(match is not None, "missing or malformed proof axiom report")
    names = [name.strip() for name in match[1].split(",")] if match[1].strip() else []
    require(all(names) and len(names) == len(set(names)), "malformed proof axiom list")
    require(set(names) <= ALLOWED_AXIOMS, f"unapproved proof axioms: {sorted(set(names) - ALLOWED_AXIOMS)}")
    return sorted(names)


def expected_native(directory: Path) -> tuple[str, dict]:
    """Authenticate recorded native bytes and the exact native fixture inputs.

    Model sources deliberately have no fixed model-source hash constraint here: CI must
    evaluate their current behavior against the preserved native observations.
    """
    metadata = directory / "expected-native.json"
    archive = directory / "expected-native.tsv.gz"
    require(metadata.is_file() and not metadata.is_symlink(), "missing regular native provenance")
    require(archive.is_file() and not archive.is_symlink(), "missing regular native expected output")
    record = json.loads(metadata.read_text())
    require(record.get("schema_version") == 1 and record.get("revision") == REVISION
            and record.get("source_archive_sha256") == ARCHIVE_SHA256
            and record.get("source_archive_url") == ARCHIVE_URL
            and record.get("rust") == RUST and record.get("target") == TARGET,
            "recorded native source, compiler or target pin differs")
    sources = record.get("native_inputs_sha256")
    require(isinstance(sources, dict) and set(sources) == set(NATIVE_INPUT_FILES),
            "recorded native inputs are incomplete")
    for name, expected in sources.items():
        path = directory / name
        require(path.is_file() and not path.is_symlink() and sha256(path) == expected,
                f"native fixture differs from recorded execution: {name}")
    output = record.get("native_output", {})
    require(output.get("file") == archive.name and sha256(archive) == output.get("gzip_sha256"),
            "recorded native gzip digest differs")
    content = gzip.decompress(archive.read_bytes())
    require(len(content) == output.get("bytes") and hashlib.sha256(content).hexdigest() == output.get("sha256"),
            "recorded native output digest differs")
    native = content.decode()
    fixtures = load_fixtures(directory)
    require(output.get("cases") == len(fixtures)
            and set(parse_output(native, "recorded native")) == set(fixtures),
            "recorded native case set differs from fixtures")
    return native, record


def harness_inputs(directory: Path) -> dict:
    """Hash every source and fixture consumed by either runner or its controls."""
    require(directory.is_dir() and not directory.is_symlink(), f"invalid harness directory: {directory}")
    allowed = set(HARNESS_FILES)
    allowed.update(str(parent) for name in HARNESS_FILES
                   for parent in Path(name).parents if str(parent) != ".")
    paths = list(directory.rglob("*"))
    extra = {str(path.relative_to(directory)) for path in paths} - allowed
    require(not any(path.is_symlink() for path in paths), "linked harness input")
    require(not extra, f"unsealed harness entries: {sorted(extra)}")
    files = {}
    for name in HARNESS_FILES:
        path = directory / name
        require(path.is_file() and not path.is_symlink(), f"missing regular harness input: {path}")
        files[name] = sha256(path)
    return {"files": files, "files_sha256": digest_json(files)}


def snapshot_harness(evidence: Path, source: Path = ROOT) -> tuple[Path, dict]:
    """Use one retained byte snapshot for parsing, compilation and both executions."""
    payloads = {}
    require(not source.is_symlink(), "linked harness source")
    for name in HARNESS_FILES:
        path = source / name
        require(not any((source / parent).is_symlink() for parent in Path(name).parents),
                "linked harness input ancestor")
        require(path.is_file() and not path.is_symlink(), f"missing regular harness input: {path}")
        payloads[name] = path.read_bytes()
    files = {name: hashlib.sha256(data).hexdigest() for name, data in payloads.items()}
    sealed = {"files": files, "files_sha256": digest_json(files)}
    directory = evidence / "harness" / sealed["files_sha256"]
    if not directory.exists():
        directory.mkdir(parents=True)
        for name, data in payloads.items():
            (directory / name).parent.mkdir(parents=True, exist_ok=True)
            (directory / name).write_bytes(data)
    require(harness_inputs(directory) == sealed, "retained harness snapshot differs from its seal")
    return directory, sealed


def check_archive(archive: Path, directory: Path, expected: str,
                  allow_absent_links: bool = False, strict_representation: bool = False) -> dict:
    """Authenticate the archive and every archived file against the build tree."""
    require(sha256(archive) == expected, f"archive digest mismatch: {archive}")
    files = {}
    mode_differences = []
    link_differences = []
    with tarfile.open(archive, "r:gz") as contents:
        for member in contents:
            if member.isdir():
                continue
            parts = Path(member.name).parts
            require(len(parts) > 1 and ".." not in parts, f"unexpected archive path: {member.name}")
            relative = Path(*parts[1:])
            path = directory / relative
            if member.issym():
                if path.is_symlink():
                    require(os.readlink(path) == member.linkname, f"symlink mismatch: {path}")
                elif allow_absent_links and not path.exists():
                    link_differences.append({"path": str(relative), "archive_target": member.linkname,
                                             "extracted_representation": "absent"})
                else:
                    raise ValueError(f"expected symlink: {path}")
                content = member.linkname.encode()
            else:
                require(member.isfile(), f"unsupported archive member: {member.name}")
                require(path.is_file() and not path.is_symlink(), f"missing regular file: {path}")
                content = contents.extractfile(member).read()
                require(path.read_bytes() == content, f"source differs from archive: {path}")
                actual_mode = path.stat().st_mode & 0o777
                if bool(actual_mode & 0o111) != bool(member.mode & 0o111):
                    mode_differences.append({"path": str(relative), "archive_mode": oct(member.mode),
                                             "extracted_mode": oct(actual_mode)})
            files[str(relative)] = hashlib.sha256(content).hexdigest()
    require(bool(files), "empty source archive")
    if strict_representation:
        require(not mode_differences and not link_differences, "archive extraction representation differs")
        actual_files = {str(path.relative_to(directory)) for path in directory.rglob("*")
                        if path.is_file() or path.is_symlink()}
        require(actual_files == set(files), "pristine source has extra or missing files")
    return {"archive_sha256": expected, "file_count": len(files),
            "files_sha256": digest_json(files), "files": files,
            "executable_mode_differences": mode_differences, "symlink_differences": link_differences}


def pristine_source(archive: Path, evidence: Path) -> Path:
    """Create an isolated source input from the seal, preserving archived symlinks."""
    with tarfile.open(archive, "r:gz") as contents:
        roots = {Path(member.name).parts[0] for member in contents.getmembers()}
        require(len(roots) == 1, "archive does not have one source root")
        prefix = next(iter(roots))
        require(prefix not in {".", "..", "/"}, "invalid source archive root")
        destination = evidence / "source" / prefix
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            contents.extractall(destination.parent, filter="data")
    return destination


def model_inputs() -> dict:
    paths = [MODEL / "Solanalib/Runtime.lean", REPO / "lean-toolchain",
             REPO / "lakefile.lean", REPO / "lake-manifest.json"]
    paths += sorted((MODEL / "Solanalib/Runtime").rglob("*.lean"))
    files = {str(path.relative_to(REPO)): sha256(path) for path in paths}
    return {"files": files, "files_sha256": digest_json(files)}


def byte_list(value: str) -> list[int]:
    if value == "-":
        return []
    values = [int(part) for part in value.split(",")]
    require(all(0 <= value <= 255 for value in values), "fixture byte is out of range")
    return values


def load_fixtures(directory: Path = ROOT) -> dict:
    fixtures = {}
    for filename, kind, columns in (
        ("accounts.tsv", "account", 11), ("serialization.tsv", "serialization", 11),
        ("cpi.tsv", "cpi", 8),
    ):
        for line in (directory / filename).read_text().splitlines():
            if not line or line.startswith("#"):
                continue
            fields = line.split("\t")
            require(len(fields) == columns, f"invalid fixture row: {line}")
            require(fields[0] not in fixtures, f"duplicate fixture id: {fields[0]}")
            if kind == "account":
                require(fields[1] in ACCOUNT_OPERATIONS, f"unknown operation: {fields[1]}")
                integers = [2, 3, 4, 5, 7, 8, 9]
                booleans = [3, 4, 7]
                for index in (6, 10):
                    byte_list(fields[index])
            elif kind == "serialization":
                require(fields[1] in {"v0", "v1"}, "unknown fixture ABI")
                integers = [2, 3, 4, 5, 6, 8, 9]
                booleans = [4, 5, 8]
                byte_list(fields[7])
                if fields[10] != "-":
                    for edit in fields[10].split(";"):
                        offset, replacement = edit.split(":")
                        require(int(offset) >= 0, "negative edit offset")
                        byte_list(replacement)
            else:
                integers = [5, 6, 7]
                booleans = integers
                for index in range(1, 5):
                    byte_list(fields[index])
            for index in integers:
                require(fields[index].isdigit() and 0 <= int(fields[index]) < 2**64,
                        f"invalid u64 fixture value: {fields[index]}")
            for index in booleans:
                require(fields[index] in {"0", "1"}, "invalid fixture Boolean")
            fixtures[fields[0]] = {"kind": kind, "file": filename, "fields": fields}
    require(bool(fixtures), "empty fixture suite")
    return fixtures


def parse_output(contents: str, label: str) -> dict:
    rows = {}
    for line in contents.splitlines():
        fields = line.split("\t")
        require(len(fields) == len(OUTPUT_COLUMNS), f"malformed {label} output row")
        require(fields[0] not in rows, f"duplicate {label} output id: {fields[0]}")
        rows[fields[0]] = dict(zip(OUTPUT_COLUMNS, fields))
    return rows


def encoded_bytes(value: str) -> dict | None:
    if value == "-":
        return None
    require(len(value) % 2 == 0, "odd-length encoded byte string")
    decoded = bytes.fromhex(value)
    require(decoded.hex() == value, "noncanonical hex encoding")
    return {"length": len(decoded), "sha256": hashlib.sha256(decoded).hexdigest()}


def account_snapshot(value: str) -> list | None:
    if value == "-":
        return None
    accounts = []
    for item in value.split("|"):
        fields = item.split(",")
        require(len(fields) == 5, "malformed account snapshot")
        lamports, owner, data, executable, rent_epoch = fields
        require(len(owner) == 64 and encoded_bytes(owner)["length"] == 32, "invalid owner")
        require(encoded_bytes(data) is not None, "missing account data bytes")
        require(executable in {"0", "1"}, "invalid executable flag")
        require(0 <= int(lamports) < 2**64 and 0 <= int(rent_epoch) < 2**64, "unbounded account")
        accounts.append({"lamports": int(lamports), "owner_hex": owner, "data_hex": data,
                         "executable": executable == "1", "rent_epoch": int(rent_epoch)})
    return accounts


def check_outcome(value: str) -> None:
    require(value == "ok" or value in ERROR_NAMES, f"unrecognized outcome: {value}")


def check_cpi_auxiliary(value: str) -> None:
    match = re.fullmatch(
        r"info_len=(0|[1-9][0-9]*);return_program=([0-9a-f]{64});return=([0-9a-f]*);"
        r"cpi_count=(0|[1-9][0-9]*);stack=(0|[1-9][0-9]*)", value)
    require(match is not None, "missing or malformed CPI auxiliary observations")
    length, program, data, count, stack = match.groups()
    require(all(int(n) < 2**64 for n in (length, count, stack)), "unbounded CPI auxiliary observation")
    encoded_bytes(program)
    encoded_bytes(data)


def compare_outputs(model_text: str, native_text: str, fixtures: dict) -> dict:
    model = parse_output(model_text, "model")
    native = parse_output(native_text, "native")
    require(set(model) == set(fixtures), "model output case set differs from fixtures")
    require(set(native) == set(fixtures), "native output case set differs from fixtures")
    cases = []
    for case_id, fixture in fixtures.items():
        left, right = model[case_id], native[case_id]
        require(left["kind"] == right["kind"] == fixture["kind"], f"wrong kind: {case_id}")
        for row in (left, right):
            check_outcome(row["outcome"])
        check_outcome(right["pop_outcome"])
        compared = ["outcome", "serialized_before"]
        if left["outcome"] == "ok":
            compared += ["accounts", "resize_delta", "pop_outcome", "serialized_after", "auxiliary"]
            require(all(left[column] != "-" for column in ("accounts", "resize_delta", "pop_outcome")),
                    f"missing successful model state: {case_id}")
            check_outcome(left["pop_outcome"])
            if fixture["kind"] in {"serialization", "cpi"}:
                for row in (left, right):
                    for column in ("serialized_before", "serialized_after"):
                        require(row[column] not in {"-", ""}, f"missing successful buffer: {case_id}/{column}")
            if fixture["kind"] == "cpi":
                check_cpi_auxiliary(left["auxiliary"])
                check_cpi_auxiliary(right["auxiliary"])
        else:
            require(all(left[column] == "-" for column in ("accounts", "resize_delta", "pop_outcome", "auxiliary")),
                    f"unexpected model error state: {case_id}")
            if fixture["kind"] != "cpi":
                compared.append("serialized_after")
            else:
                require(left["serialized_after"] == "-", f"CPI error retained a model buffer: {case_id}")
        for column in compared:
            require(left[column] == right[column], f"conformance mismatch: {case_id}/{column}")
        for row in (left, right):
            for column in ("serialized_before", "serialized_after"):
                encoded_bytes(row[column])
        cases.append({
            "id": case_id, "kind": fixture["kind"], "fixture": fixture,
            "outcome": left["outcome"], "compared_fields": compared,
            "model_accounts": account_snapshot(left["accounts"]),
            "native_accounts": account_snapshot(right["accounts"]),
            "native_resize_delta": int(right["resize_delta"]),
            "native_pop_outcome": right["pop_outcome"],
            "native_auxiliary": right["auxiliary"],
            "serialized_before": encoded_bytes(right["serialized_before"]),
            "native_serialized_after": encoded_bytes(right["serialized_after"]),
            "error_state_compared": False,
        })
    return {"case_count": len(cases), "outcomes": dict(collections.Counter(c["outcome"] for c in cases)),
            "kinds": dict(collections.Counter(c["kind"] for c in cases)), "cases": cases}


class Runner:
    def __init__(self, evidence: Path, timeout: int):
        self.evidence = evidence
        self.timeout = timeout
        self.commands = []
        self.environment = os.environ.copy()
        for key in list(self.environment):
            if key in {"RUSTFLAGS", "RUSTDOCFLAGS", "RUSTC", "RUSTDOC", "RUSTC_WRAPPER",
                       "RUSTC_WORKSPACE_WRAPPER", "RUSTUP_TOOLCHAIN", "CARGO_ENCODED_RUSTFLAGS",
                       "CARGO_ENCODED_RUSTDOCFLAGS"} or key.startswith(
                           ("CARGO_PROFILE_", "CARGO_BUILD_", "CARGO_TARGET_")):
                del self.environment[key]
        self.environment["PYTHONDONTWRITEBYTECODE"] = "1"

    def run(self, name: str, arguments: list[str], cwd: Path, output: str | None = None) -> str:
        output = output or f"run-{name}.out"
        error = f"run-{name}.log"
        started = time.monotonic()
        with (self.evidence / output).open("w") as stdout, (self.evidence / error).open("w") as stderr:
            process = subprocess.Popen(arguments, cwd=cwd, env=self.environment,
                                       stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                code = process.wait(timeout=self.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                code = 124
        entry = {"name": name, "argv": arguments, "cwd": str(cwd), "exit_code": code,
                 "elapsed_seconds": round(time.monotonic() - started, 3),
                 "stdout": output, "stderr": error}
        self.commands.append(entry)
        write_json(self.evidence / "commands.json", self.commands)
        require(code == 0, f"{name} failed with exit {code}; see {error} and {output}")
        return (self.evidence / output).read_text()


def run_model(runner: Runner, harness: Path) -> str:
    """Evaluate the current model and enforce the axiom scope of the local theorem."""
    runner.run("model-build", ["lake", "build", "Solanalib.Runtime"], REPO)
    runner.run("model-driver", ["lake", "env", "lean", "--run", str(harness / "SolanalibTest/Conformance/Runtime.lean"), str(harness)],
               REPO, "model.tsv")
    audit = runner.evidence / "ModelCasesAudit.lean"
    audit.write_text((harness / "SolanalibTest/Conformance/Runtime.lean").read_text() + f"\n#print axioms {AXIOM_THEOREM}\n")
    output = runner.run("model-axioms", ["lake", "env", "lean", str(audit)], REPO)
    names = checked_axioms(output)
    write_json(runner.evidence / "model-axioms.json", {
        "theorem": AXIOM_THEOREM, "axioms": names, "allowed_axioms": sorted(ALLOWED_AXIOMS),
    })
    return output


def replay_model(args: argparse.Namespace) -> None:
    """Fresh Lean execution against authenticated, previously recorded native bytes."""
    evidence = args.evidence_dir.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    require((REPO / "lean-toolchain").read_text().strip() == LEAN, "model toolchain pin changed")
    runner = Runner(evidence, args.timeout)
    harness, harness_before = snapshot_harness(evidence)
    native, provenance = expected_native(harness)
    (evidence / "native.tsv").write_text(native)
    write_json(evidence / "native-provenance.json", provenance)
    write_json(evidence / "harness-before.json", harness_before)
    model_before = model_inputs()
    write_json(evidence / "model-before.json", model_before)
    version = runner.run("lean-version", ["lake", "env", "lean", "--version"], REPO).strip()
    require(version.startswith(f"Lean (version {LEAN.rpartition(':v')[2]},"), "unexpected Lean compiler version")
    write_json(evidence / "tool-identities.json", {"lean": {"pin": LEAN, "version": version}})
    run_model(runner, harness)
    comparison = compare_outputs((evidence / "model.tsv").read_text(), native, load_fixtures(harness))
    write_json(evidence / "comparison.json", comparison)
    require(harness_inputs(harness) == harness_before, "retained harness changed during execution")
    require(model_inputs() == model_before, "runtime model changed during execution")
    status = json.loads((evidence / "run-status.json").read_text())
    status.update(status="passed", case_count=comparison["case_count"],
                  native_execution="recorded", native_recorded_utc=provenance["recorded_utc"],
                  finished_utc=datetime.now(timezone.utc).isoformat())
    write_json(evidence / "run-status.json", status)
    artifacts = ["run-status.json", "commands.json", "native-provenance.json", "native.tsv", "model.tsv",
                 "harness-before.json", "model-before.json", "tool-identities.json", "comparison.json",
                 "ModelCasesAudit.lean", "model-axioms.json"]
    artifacts += [str((harness / name).relative_to(evidence)) for name in HARNESS_FILES]
    artifacts += [entry[key] for entry in runner.commands for key in ("stdout", "stderr")]
    write_json(evidence / "MANIFEST.json", {
        "schema_version": 1, "revision": REVISION, "case_count": comparison["case_count"],
        "evidence_kind": "fresh model comparison against recorded native outputs",
        "files": {name: sha256(evidence / name) for name in sorted(set(artifacts))},
    })
    print(f"Passed {comparison['case_count']} model cases against recorded native outputs; evidence: {evidence}")


def artifact_units(contents: str) -> list[dict]:
    units = []
    for line in contents.splitlines():
        entry = json.loads(line)
        if entry.get("reason") == "compiler-artifact":
            units.append({key: entry[key] for key in
                          ("package_id", "manifest_path", "target", "profile", "features", "filenames")})
    runtime = [unit for unit in units if unit["target"]["name"] == "solana_program_runtime"]
    require(len(runtime) == 1, "missing or ambiguous program-runtime artifact")
    require("agave-unstable-api" in runtime[0]["features"], "runtime API compiled out")
    return units


def registry_inputs(units: list[dict], source: Path) -> list[dict]:
    """Check registry archives and extracted files against the frozen Cargo lock."""
    lock = tomllib.loads((source / "Cargo.lock").read_text())
    locked = {(package["name"], package["version"]): package for package in lock["package"]
              if package.get("source", "").startswith("registry+")}
    packages = {}
    for unit in units:
        package_id = unit["package_id"]
        if not package_id.startswith("registry+"):
            require(Path(unit["manifest_path"]).is_relative_to(source),
                    f"unsealed nonregistry dependency: {package_id}")
            continue
        packages[package_id] = unit
    records = []
    for package_id, unit in sorted(packages.items()):
        name, version = package_id.rsplit("#", 1)[1].rsplit("@", 1)
        package = locked[name, version]
        directory = Path(unit["manifest_path"]).parent
        registry = directory.parent.name
        archive = directory.parents[2] / "cache" / registry / f"{name}-{version}.crate"
        checked = check_archive(archive, directory, package["checksum"])
        records.append({"package_id": package_id, "manifest_path": str(directory / "Cargo.toml"),
                        "archive": str(archive), "archive_sha256": checked["archive_sha256"],
                        "file_count": checked["file_count"], "files_sha256": checked["files_sha256"],
                        "executable_mode_differences": checked["executable_mode_differences"]})
    return records


def summary_markdown(comparison: dict, native_only: list[str]) -> str:
    counts = comparison["outcomes"]
    successes = counts.get("ok", 0)
    failures = comparison["case_count"] - successes
    return f"""# Agave conformance evidence

{comparison['case_count']} finite differential cases passed: {successes} successes and {failures} failures.
The native implementation is Agave 4.3.2 at `{REVISION}`, built with Rust {RUST},
its frozen Cargo.lock, and target `{TARGET}`. The other execution uses the
canonical Lean model under `{LEAN}`. Exact input hashes, commands, feature sets,
compiler artifacts and tool identities are recorded alongside this file.

| Case family | Cases |
| --- | ---: |
| Account setters and checks | {comparison['kinds'].get('account', 0)} |
| Serialization and read-back | {comparison['kinds'].get('serialization', 0)} |
| Nonempty CPI through Agave C-ABI translation | {comparison['kinds'].get('cpi', 0)} |

Successful cases compare all account fields, resize accounting and the pop result.
Serialization compares complete ABI v0/v1 bytes, including duplicate records and
the 255-reference limit. CPI successes compare the complete caller buffer after
return, current account-info length, return data, CPI count and stack height.
The native fixture callee checks the latest synchronized data before changing it;
the caller continuation observes the copy-back from that same invocation.

Each row of comparison.json states exactly which fields were compared. The raw
native.tsv and model.tsv preserve complete buffers. On failure, runtime Except
erases intermediate state: native partial effects are retained as observations
but are not asserted to be model states or transaction rollback. The invalid CPI
pointer produces raw CpiError::InvalidPointer; the driver compares its documented
ProgramFailedToComplete abstraction, without executing the enclosing SBF VM.

There are {len(native_only)} additional native-only borrow observations in
native-observations.log. They have no claimed runtime outstanding-borrow model.

This is finite conformance evidence, not a Rust body proof, complete Agave
refinement, or SBF/native equivalence theorem. The existing proofs of the runtime model are separate. SolanalibTest/Conformance/Runtime.lean kernel-checks only its no-signer specialization
of cpiPrepare for arbitrary primitive environments; no crypto is executed or
claimed verified here. The native CPI callee and its model counterpart are explicit
test fixtures, not contracts for a deployed program. Deployed CPI bodies are outside this test.

The native CPI feature vector enables syscall_parameter_address_restrictions and
leaves other SVMFeatureSet flags at their false defaults. Relevant selected paths
use ABI v1, configuration L, no PDA seeds, native callee dispatch and rent rate
5080. The Lean executions use the corresponding settings of mainnet. Other feature
paths, VM execution, bank admission, whole-transaction rollback, separate and direct account-data mappings (S and D) and
SDK Rust representation/body proofs remain outside these cases.
"""


def replay(args: argparse.Namespace) -> None:
    evidence = args.evidence_dir.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    runner = Runner(evidence, args.timeout)
    archive = args.source_archive.resolve()
    require(sha256(archive) == ARCHIVE_SHA256, "unexpected Agave archive digest")
    snapshot_source = pristine_source(archive, evidence)
    source = snapshot_source
    require(tomllib.loads((source / "rust-toolchain.toml").read_text())["toolchain"]["channel"] == RUST,
            "Agave toolchain pin changed")
    workspace = tomllib.loads((source / "Cargo.toml").read_text())["workspace"]["package"]
    require(workspace["version"] == "4.3.2" and workspace["rust-version"] == RUST, "Agave manifest pin changed")
    require((REPO / "lean-toolchain").read_text().strip() == LEAN, "model toolchain pin changed")
    harness, harness_before = snapshot_harness(evidence)
    fixtures = load_fixtures(harness)
    write_json(evidence / "harness-before.json", {
        "source_root": str(ROOT), "snapshot_root": str(harness), **harness_before,
    })
    before = check_archive(archive, snapshot_source, ARCHIVE_SHA256, strict_representation=True)
    write_json(evidence / "source-before.json", before)
    source = pristine_source(archive, evidence)
    built_source = check_archive(archive, source, ARCHIVE_SHA256, strict_representation=True)
    write_json(evidence / "build-source-before.json", built_source)
    model_before = model_inputs()
    write_json(evidence / "model-before.json", model_before)
    status = {"started_utc": datetime.now(timezone.utc).isoformat(), "status": "running"}
    write_json(evidence / "run-status.json", status)
    try:
        identities = {}
        for tool in ("rustc", "cargo"):
            binary = runner.run(f"locate-{tool}", ["rustup", "which", "--toolchain", RUST, tool], source).strip()
            version_args = [tool, f"+{RUST}", "-vV" if tool == "rustc" else "-V"]
            identities[tool] = {"path": binary, "sha256": sha256(Path(binary)),
                                "version": runner.run(f"version-{tool}", version_args, source).strip()}
        identities["lean"] = {"version": runner.run("lean-version", ["lake", "env", "lean", "--version"], REPO).strip()}
        require(identities["lean"]["version"].startswith(f"Lean (version {LEAN.rpartition(':v')[2]},"),
                "unexpected Lean compiler version")
        lean_binary = runner.run("locate-lean", ["elan", "which", "lean"], REPO).strip()
        identities["lean"].update(path=lean_binary, sha256=sha256(Path(lean_binary)))
        write_json(evidence / "tool-identities.json", identities)

        target = evidence / "target"
        cargo_args = ["cargo", f"+{RUST}", "build", "--locked", "--manifest-path",
                      str(source / "program-runtime/Cargo.toml"), "--target", TARGET,
                      "--target-dir", str(target), "--jobs", str(args.jobs), "--no-default-features",
                      "--features", "agave-unstable-api,dev-context-only-utils", "--message-format=json-render-diagnostics"]
        built = runner.run("native-build", cargo_args, source, "run-native-build.jsonl")
        units = artifact_units(built)
        registry = registry_inputs(units, source)
        write_json(evidence / "registry-inputs.json", registry)
        externs = {}
        for unit in units:
            name = unit["target"]["name"]
            if name in EXTERNS:
                require(name not in externs, f"ambiguous external crate artifact: {name}")
                externs[name] = next(path for path in unit["filenames"] if path.endswith(".rlib"))
        require(set(externs) == EXTERNS, "missing native crate artifact")
        binary = evidence / "agave-cases"
        rustc_args = ["rustc", f"+{RUST}", str(harness / "agave_cases.rs"), "--edition=2024", "--target", TARGET,
                      "-C", "target-cpu=x86-64-v2", "-C", "debug-assertions=yes", "-C", "overflow-checks=yes",
                      "-C", "debuginfo=line-tables-only", "-L", f"dependency={target / TARGET / 'debug/deps'}",
                      "-L", f"dependency={target / 'debug/deps'}", "-o", str(binary)]
        for name, path in sorted(externs.items()):
            rustc_args += ["--extern", f"{name}={path}"]
        runner.run("native-driver-build", rustc_args, source)
        runner.run("native-driver", [str(binary), str(harness)], source, "native.tsv")
        (evidence / "native-observations.log").write_text((evidence / "run-native-driver.log").read_text())
        audit_output = run_model(runner, harness)
        comparison = compare_outputs((evidence / "model.tsv").read_text(),
                                     (evidence / "native.tsv").read_text(), fixtures)
        write_json(evidence / "comparison.json", comparison)
        runner.run("comparison-controls", [sys.executable, "-B", str(harness / "test_run.py"), "-v"], REPO)
        native_only = [line for line in (evidence / "native-observations.log").read_text().splitlines()
                       if line.startswith("native_only\t")]
        require(len(native_only) == 4, "missing native-only borrow observations")
        (evidence / "SUMMARY.md").write_text(summary_markdown(comparison, native_only))
        configurations = []
        candidates = {ancestor / ".cargo" / filename for ancestor in [source, *source.parents]
                      for filename in ("config", "config.toml")}
        cargo_home = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))
        candidates.update(cargo_home / filename for filename in ("config", "config.toml"))
        for path in sorted(candidates):
            if path.is_file():
                configurations.append({"path": str(path), "sha256": sha256(path)})
        write_json(evidence / "native-build.json", {
            "revision": REVISION, "source_archive_url": ARCHIVE_URL,
            "cargo_lock_sha256": sha256(source / "Cargo.lock"), "target": TARGET,
            "source_root": str(source), "sealed_snapshot_root": str(snapshot_source),
            "configuration_hashes": configurations,
            "units": units, "native_binary_sha256": sha256(binary),
            "harness_files": harness_before["files"], "harness_root": str(harness),
            "native_cpi_profile": {"enabled_svm_features": ["syscall_parameter_address_restrictions"],
                                   "other_svm_features": False, "memory_config": "L", "abi": "v1",
                                   "sbpf_memory_mapping_version": "V3", "vm_executed": False,
                                   "rent_lamports_per_byte": 5080, "signer_seeds": []},
            "local_theorem_axiom_audit": audit_output.strip(),
        })
        status.update(status="passed", case_count=comparison["case_count"])
    except Exception as error:
        status.update(status="failed", error=str(error))
        raise
    finally:
        try:
            after = check_archive(archive, snapshot_source, ARCHIVE_SHA256, strict_representation=True)
            write_json(evidence / "source-after.json", after)
            require(before == after, "Agave source changed during execution")
            built_after = check_archive(archive, source, ARCHIVE_SHA256, strict_representation=True)
            write_json(evidence / "build-source-after.json", built_after)
            require(built_source == built_after, "Agave build input changed during execution")
            model_after = model_inputs()
            write_json(evidence / "model-after.json", model_after)
            require(model_before == model_after, "runtime model changed during execution")
            harness_after = harness_inputs(harness)
            write_json(evidence / "harness-after.json", harness_after)
            require(harness_before == harness_after, "retained harness changed during execution")
        except Exception as error:
            status.update(status="failed", preservation_error=str(error))
            raise
        finally:
            status["finished_utc"] = datetime.now(timezone.utc).isoformat()
            write_json(evidence / "run-status.json", status)
    artifacts = [
        "run-status.json", "commands.json", "tool-identities.json", "source-before.json", "source-after.json",
        "build-source-before.json", "build-source-after.json", "model-before.json", "model-after.json",
        "native-build.json", "registry-inputs.json", "comparison.json", "SUMMARY.md", "native.tsv", "model.tsv",
        "native-observations.log", "ModelCasesAudit.lean", "model-axioms.json", "harness-before.json", "harness-after.json",
    ]
    artifacts += [str((harness / name).relative_to(evidence)) for name in HARNESS_FILES]
    artifacts += [entry[key] for entry in runner.commands for key in ("stdout", "stderr")]
    write_json(evidence / "MANIFEST.json", {"schema_version": 1, "revision": REVISION,
        "evidence_kind": "finite native differential tests", "case_count": status["case_count"],
        "files": {name: sha256(evidence / name) for name in sorted(set(artifacts))}})
    print(f"Passed {status['case_count']} differential cases; evidence: {evidence}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--source-archive", type=Path, help="Pinned Agave archive for a native replay")
    source.add_argument("--model-only", action="store_true", help="Compare fresh Lean cases against recorded native outputs")
    parser.add_argument("--evidence-dir", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=900, help="maximum seconds per subprocess")
    args = parser.parse_args()
    args.evidence_dir.mkdir(parents=True, exist_ok=True)
    write_json(args.evidence_dir / "run-status.json", {
        "status": "running", "started_utc": datetime.now(timezone.utc).isoformat(),
    })
    try:
        require(args.jobs > 0 and args.timeout > 0, "jobs and timeout must be positive")
        if args.model_only:
            replay_model(args)
        else:
            replay(args)
    except Exception as error:
        state = json.loads((args.evidence_dir / "run-status.json").read_text())
        state.update(status="failed", error=str(error), finished_utc=datetime.now(timezone.utc).isoformat())
        write_json(args.evidence_dir / "run-status.json", state)
        print(f"Conformance replay failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
