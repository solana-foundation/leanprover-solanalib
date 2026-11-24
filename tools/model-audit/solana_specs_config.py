"""Registered public SDK module roots and root-owned library boundaries."""
from pathlib import Path
import json
import subprocess
import re
import tomllib

COMMON_ROOT = "Solanalib.Specs.Core"
COMMON_TEST_ROOT = "SolanalibTest.Specs.Core"
CRATE_ROOTS = {'anchor_lang': 'Solanalib.Specs.AnchorLang', 'anchor_spl': 'Solanalib.Specs.AnchorSpl', 'borsh': 'Solanalib.Specs.Borsh', 'bytemuck': 'Solanalib.Specs.Bytemuck', 'pinocchio': 'Solanalib.Specs.Pinocchio', 'pinocchio_associated_token_account': 'Solanalib.Specs.PinocchioAssociatedTokenAccount', 'pinocchio_system': 'Solanalib.Specs.PinocchioSystem', 'pinocchio_token': 'Solanalib.Specs.PinocchioToken', 'pinocchio_token_2022': 'Solanalib.Specs.PinocchioToken2022', 'pyth_solana_receiver_sdk': 'Solanalib.Specs.PythSolanaReceiverSdk', 'pythnet_sdk': 'Solanalib.Specs.PythnetSdk', 'solana_account_info': 'Solanalib.Specs.SolanaAccountInfo', 'solana_account_view': 'Solanalib.Specs.SolanaAccountView', 'solana_address': 'Solanalib.Specs.SolanaAddress', 'solana_address_lookup_table_interface': 'Solanalib.Specs.SolanaAddressLookupTableInterface', 'solana_borsh': 'Solanalib.Specs.SolanaBorsh', 'solana_curve25519': 'Solanalib.Specs.SolanaCurve25519', 'solana_define_syscall': 'Solanalib.Specs.SolanaDefineSyscall', 'solana_epoch_schedule': 'Solanalib.Specs.SolanaEpochSchedule', 'solana_cpi': 'Solanalib.Specs.SolanaCpi', 'solana_hash': 'Solanalib.Specs.SolanaHash', 'solana_instruction': 'Solanalib.Specs.SolanaInstruction', 'solana_instruction_view': 'Solanalib.Specs.SolanaInstructionView', 'solana_invoke': 'Solanalib.Specs.SolanaInvoke', 'solana_msg': 'Solanalib.Specs.SolanaMsg', 'solana_nullable': 'Solanalib.Specs.SolanaNullable', 'solana_program': 'Solanalib.Specs.SolanaProgram', 'solana_program_error': 'Solanalib.Specs.SolanaProgramError', 'solana_program_option': 'Solanalib.Specs.SolanaProgramOption', 'solana_pubkey': 'Solanalib.Specs.SolanaPubkey', 'solana_rent': 'Solanalib.Specs.SolanaRent', 'solana_sdk_ids': 'Solanalib.Specs.SolanaSdkIds', 'solana_sha256_hasher': 'Solanalib.Specs.SolanaSha256Hasher', 'solana_stake_interface': 'Solanalib.Specs.SolanaStakeInterface', 'solana_system_interface': 'Solanalib.Specs.SolanaSystemInterface', 'solana_sysvar': 'Solanalib.Specs.SolanaSysvar', 'solana_zero_copy': 'Solanalib.Specs.SolanaZeroCopy', 'spl_token_2022': 'Solanalib.Specs.SplToken2022', 'spl_token_2022_interface': 'Solanalib.Specs.SplToken2022Interface', 'spl_token_interface': 'Solanalib.Specs.SplTokenInterface', 'switchboard_on_demand': 'Solanalib.Specs.SwitchboardOnDemand', 'spl_associated_token_account_client': 'Solanalib.Specs.SplAssociatedTokenAccountClient', 'spl_memo': 'Solanalib.Specs.SplMemo', 'spl_token_metadata_interface': 'Solanalib.Specs.SplTokenMetadataInterface', 'pinocchio_log': 'Solanalib.Specs.PinocchioLog', 'solana_program_entrypoint': 'Solanalib.Specs.SolanaProgramEntrypoint', 'spl_pod': 'Solanalib.Specs.SplPod', 'spl_token': 'Solanalib.Specs.SplToken', 'spl_transfer_hook_interface': 'Solanalib.Specs.SplTransferHookInterface', 'anchor_lang_error': 'Solanalib.Specs.AnchorLangError', 'solana_instructions_sysvar': 'Solanalib.Specs.SolanaInstructionsSysvar', 'solana_loader_v3_interface': 'Solanalib.Specs.SolanaLoaderV3Interface', 'spl_associated_token_account_interface': 'Solanalib.Specs.SplAssociatedTokenAccountInterface'}
SDK_ROOTS = tuple(CRATE_ROOTS.values())

def test_root(root):
    return root.replace("Solanalib.Specs.", "SolanalibTest.Specs.", 1)

def module_root(name):
    parts = name.split(".")
    if len(parts) >= 3 and parts[0] in {"Solanalib", "SolanalibTest"} and parts[1] == "Specs":
        return ".".join(parts[:3])
    if name == "Solanalib.Contracts" or name.startswith("Solanalib.Contracts."):
        return "Solanalib.Contracts"
    return parts[0]

def crate_root(crate):
    source = crate.replace("-", "_")
    return CRATE_ROOTS.get(source, "Solanalib.Specs." + "".join(
        part[:1].upper() + part[1:] for part in source.split("_")))

PRODUCTION_ROOTS = (COMMON_ROOT, *SDK_ROOTS)
TEST_ROOTS = (COMMON_TEST_ROOT, *(test_root(root) for root in SDK_ROOTS))
LIBRARY_ROOTS = (COMMON_ROOT, COMMON_TEST_ROOT,
                 *(name for root in SDK_ROOTS for name in (root, test_root(root))))
SDK_DEPENDENCIES = {'Solanalib.Specs.AnchorLang': [], 'Solanalib.Specs.AnchorSpl': ['Solanalib.Specs.AnchorLang'], 'Solanalib.Specs.Borsh': [], 'Solanalib.Specs.Bytemuck': [], 'Solanalib.Specs.Pinocchio': [], 'Solanalib.Specs.PinocchioAssociatedTokenAccount': [], 'Solanalib.Specs.PinocchioSystem': [], 'Solanalib.Specs.PinocchioToken': [], 'Solanalib.Specs.PinocchioToken2022': [], 'Solanalib.Specs.PythSolanaReceiverSdk': ['Solanalib.Specs.Borsh', 'Solanalib.Specs.PythnetSdk', 'Solanalib.Specs.SolanaAddress'], 'Solanalib.Specs.PythnetSdk': ['Solanalib.Specs.Borsh'], 'Solanalib.Specs.SolanaAccountInfo': [], 'Solanalib.Specs.SolanaAccountView': [], 'Solanalib.Specs.SolanaAddress': ['Solanalib.Specs.Borsh'], 'Solanalib.Specs.SolanaAddressLookupTableInterface': [], 'Solanalib.Specs.SolanaBorsh': [], 'Solanalib.Specs.SolanaCurve25519': [], 'Solanalib.Specs.SolanaDefineSyscall': [], 'Solanalib.Specs.SolanaEpochSchedule': [], 'Solanalib.Specs.SolanaCpi': [], 'Solanalib.Specs.SolanaHash': [], 'Solanalib.Specs.SolanaInstruction': [], 'Solanalib.Specs.SolanaInstructionView': [], 'Solanalib.Specs.SolanaInvoke': [], 'Solanalib.Specs.SolanaMsg': [], 'Solanalib.Specs.SolanaNullable': [], 'Solanalib.Specs.SolanaProgram': [], 'Solanalib.Specs.SolanaProgramError': [], 'Solanalib.Specs.SolanaProgramOption': [], 'Solanalib.Specs.SolanaPubkey': [], 'Solanalib.Specs.SolanaRent': [], 'Solanalib.Specs.SolanaSdkIds': [], 'Solanalib.Specs.SolanaSha256Hasher': [], 'Solanalib.Specs.SolanaStakeInterface': ['Solanalib.Specs.Borsh', 'Solanalib.Specs.SolanaAddress'], 'Solanalib.Specs.SolanaSystemInterface': [], 'Solanalib.Specs.SolanaSysvar': ['Solanalib.Specs.SolanaRent'], 'Solanalib.Specs.SolanaZeroCopy': [], 'Solanalib.Specs.SplToken2022': ['Solanalib.Specs.SplToken2022Interface'], 'Solanalib.Specs.SplToken2022Interface': [], 'Solanalib.Specs.SplTokenInterface': [], 'Solanalib.Specs.SwitchboardOnDemand': [], 'Solanalib.Specs.SplAssociatedTokenAccountClient': [], 'Solanalib.Specs.SplMemo': [], 'Solanalib.Specs.SplTokenMetadataInterface': [], 'Solanalib.Specs.PinocchioLog': [], 'Solanalib.Specs.SolanaProgramEntrypoint': [], 'Solanalib.Specs.SplPod': [], 'Solanalib.Specs.SplToken': [], 'Solanalib.Specs.SplTransferHookInterface': [], 'Solanalib.Specs.AnchorLangError': [], 'Solanalib.Specs.SolanaInstructionsSysvar': [], 'Solanalib.Specs.SolanaLoaderV3Interface': [], 'Solanalib.Specs.SplAssociatedTokenAccountInterface': []}


def sdk_root(name: str) -> bool:
    """Library names identify modules; source versions belong in profiles."""
    return (re.fullmatch(r"Solanalib\.Specs\.[A-Z][A-Za-z0-9]*", name) is not None
            and re.search(r"_[0-9]+_[0-9]+_[0-9]+$", name) is None)


def package_configuration(package: Path) -> dict:
    """Read the canonical root package from Lake, or a closed control fixture."""
    repository = package.parents[1]
    canonical = (package.resolve() == (repository / "packages/solanalib-specs").resolve()
                 and (repository / "lakefile.lean").is_file())
    if not canonical:
        try:
            return tomllib.loads((package / "lakefile.toml").read_text())
        except (OSError, tomllib.TOMLDecodeError) as error:
            raise ValueError(f"Invalid specification package configuration: {error}") from error
    if any((package / name).exists() for name in ("lakefile.lean", "lakefile.toml")):
        raise ValueError("Canonical specifications must belong to the root Lake package")
    result = subprocess.run(["lake", "--quiet", "run", "solanalib/libraryInventory"],
                            cwd=repository, check=True, capture_output=True, text=True)
    libraries = json.loads(result.stdout)
    selected = []
    for library in libraries:
        if library["name"].startswith(("Solanalib.Specs.", "SolanalibTest.Specs.")):
            if (library["package"] != "solanalib"
                    or Path(library["srcDir"]).resolve() != package.resolve()):
                raise ValueError("Specification library has a different owner or source directory")
            selected.append({**library, "srcDir": "."})
    return {"lean_lib": selected, "_root_libraries": libraries,
            "_canonical_root": repository, "srcDir": "."}


def package_roots(package: Path) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Read and validate the selectable production/test libraries and their source roots.

    The audit uses the actual Lake configuration; fixture packages can register
    a smaller set, while repository controls require LIBRARY_ROOTS exactly.
    """
    configuration = package_configuration(package)
    libraries = [row for row in configuration.get("lean_lib", [])
                 if row.get("name") != "Solanalib.Contracts"]
    names = [library.get("name") for library in libraries]
    if (not libraries or any(not isinstance(name, str) for name in names)
            or len(names) != len(set(names))):
        raise ValueError("Missing or duplicate specification libraries")
    production = tuple(name for name in names if name.startswith("Solanalib.Specs."))
    tests = tuple(name for name in names if name.startswith("SolanalibTest.Specs."))
    if len(production) + len(tests) != len(names):
        raise ValueError("Unsupported production specification root")
    if COMMON_ROOT not in production:
        raise ValueError("Missing common specification root")
    if any(name != COMMON_ROOT and not sdk_root(name) for name in production):
        raise ValueError("Unsupported production specification root")
    if any(name != COMMON_TEST_ROOT and name.replace("SolanalibTest.", "Solanalib.", 1) not in production for name in tests):
        raise ValueError("Test specification root has no production root")
    if any(test_root(name) not in tests for name in production if name != COMMON_ROOT):
        raise ValueError("SDK specification root has no separate test root")
    defaults = configuration.get("defaultTargets", [])
    if ("_canonical_root" not in configuration
            and (len(defaults) != len(set(defaults)) or set(defaults) != set(names))):
        raise ValueError("Default specification targets must cover every library")
    for library in libraries:
        name = library["name"]
        globs = library.get("globs", library.get("roots", [name]))
        if library.get("roots", [name]) != [name] or library.get("srcDir", ".") != ".":
            raise ValueError(f"Unexpected specification library source root: {name}")
        # A retained single-file library needs no recursive glob. Once a
        # namespace directory exists, every new child must be covered as well.
        leaf = (globs == [name] and (package / (name.replace(".", "/") + ".lean")).is_file()
                and not (package / name.replace(".", "/")).exists())
        if (not isinstance(globs, list) or not all(isinstance(glob, str) for glob in globs)
                or not (leaf or name + ".*" in globs or name in globs and name + ".+" in globs)
                or any(glob not in {name, name + ".+", name + ".*"} for glob in globs)):
            raise ValueError(f"Specification library lacks exact recursive coverage: {name}")
    if configuration.get("srcDir", ".") != ".":
        raise ValueError("Unexpected specification package source directory")
    return production, tests
