# Solana library model tests

This suite records calls to the pinned Rust libraries and checks their results
against the registered [Solana library models](../../packages/solanalib-specs/README.md).
It checks values, state changes, call order and resource effects where the model
describes them. Syscall replies are controlled test inputs.

## Find tests for a model

- [LIBRARIES.md](../../packages/solanalib-specs/LIBRARIES.md) links the model and
  mathematical tests of each library. The source registry names individual contracts and clients.
- [Family modules](SolanalibTest/Conformance/Library/Families) connect Rust functions and type
  instantiations to the model declarations they check.
- Each [`driver.toml` of a native driver](rust) names its corpus files; its
  `Cargo.toml`, lockfile and configuration fix the tested versions and build.
  These file names remain versioned even when several releases share one model.

[Value-operation cases](REFERENCE.md#value-operations) cover Address comparison,
ProgramError conversions, MaybeNull at Address and concrete Mint cloning.
[Raw runtime and SDK utilities](REFERENCE.md#raw-runtime-and-sdk-utilities) cover
memory, PDA, sysvar, hash, logging and rent-exemption calls.
[Anchor context and diagnostic operations](REFERENCE.md#anchor-context-and-diagnostic-operations)
cover construction/signers, partial writes, error annotations and logging.
[Anchor System and checked transfer](REFERENCE.md#anchor-system-and-checked-transfer)
cover ordered CPI requests, callback exits, boxed errors and resource cleanup.
[Anchor account lifecycle](REFERENCE.md#anchor-account-lifecycle) covers
validation, consumed account slices, serialization, close and collection delegation.
[Token, loader and optional-value operations](REFERENCE.md#token-loader-and-optional-value-operations)
cover initialization, borrowed parents, callback cleanup, TLV sizing and epoch fees.

[Pinocchio accounts, entrypoints and transfer-hook resolution](REFERENCE.md#pinocchio-accounts-entrypoints-and-transfer-hook-resolution)
cover live borrow guards, callback exits, deserialization, logger cleanup and
ordered extra-account resolution. [Pubkey profiles](../../packages/solanalib-specs/source-notes/address-profiles.md)
record the concrete Borsh mappings and full-build selection limits.

[Modern Anchor and SDK profiles](REFERENCE.md#modern-anchor-and-sdk-profiles)
cover the reviewed 1.1.2 Anchor operations, Address readers, owned extension
unpack and checked instructions-sysvar loading. Exact source/build profiles
and callback, allocation, error and cleanup boundaries remain explicit.

[Program and Anchor profiles](REFERENCE.md#program-and-anchor-profiles) separate
exact Program 1.18.26/Anchor 0.29.0 observations from compatibility assumptions,
and link the existing selection tests, concrete Borsh selections and Rent
arithmetic/panic qualifications.
[Legacy interfaces](REFERENCE.md#legacy-program-and-anchor-interfaces) record
the Program 1.15.2/Anchor 0.27.0 observations and their separate compatibility assumptions.

A complete replay reports every registered model in `decides.json`, together
with the deciding checkers and precondition coverage. The shared array-construction
protocol has [mathematical scenario tests](../../packages/solanalib-specs/SolanalibTest/Specs/Core/OwnedArray.lean)
and [no native entry point](REFERENCE.md#models-without-a-native-entry-point).
The operational Token-2022 precondition check remains documented in the
[reference guide](REFERENCE.md#preconditions-requires).

## Run the tests

The root `solanalib` package owns `SolanalibTest.Conformance.Library` and the `solanalib-library-conformance` and `solanalib-selection-control` executables. Their outputs share the root artifact directory of the models. The runner builds these targets from the root; selected-family replay and axiom audits use ordinary `lake env lean` lookup.

From the repository root, with Python 3.12 and the recorded Lean toolchain:

```sh
# Replay the registered functions and build the runner, then check Python and Lean controls.
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --evidence-dir /tmp/slc-all
SOLANA_CONFORMANCE_SELECTION_LEAN=1 python3.12 -B -m unittest discover -s tools/library-conformance -p 'test_*.py'

# A single family or version-specific corpus.
python3.12 -B tools/library-conformance/run.py --model-only \
  --family AccountsV2 --evidence-dir /tmp/slc-accounts
python3.12 -B tools/library-conformance/run.py --model-only \
  --corpus solana_hash_4_3_0 --evidence-dir /tmp/slc-hash
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --family RawRuntime --family Utilities --evidence-dir /tmp/slc-utilities
```

`--registered-checkers` authenticates each complete corpus and selects exact
compiled checker keys. Omitted records receive no conformance credit;
[selection receipts](REFERENCE.md#registered-checker-selection) record them explicitly.
The result is in `run-status.json`. `counts.json`, `decides.json` and
`controls.json` give the checked calls, model coverage and negative controls;
subprocess commands and logs are retained alongside them.

Use a fresh evidence directory for each replay. Every control runs against a
complete, independent regular-file corpus copy. After its checks pass, only
copies identical to `control-baseline/` are removed; changed and extra files,
commands, output and selection receipts remain. Failed or unexpected controls
keep their full input directory, including timeouts and failed setup checks.

The default replay runs controls serially. `--control-jobs 4` runs up to four
independent full-corpus mutations at once with the compiled checker, as in CI.
Each still checks the complete selected corpus and keeps separate input files,
commands and output; the control list retains its original order. Selected-family
interpreted runs remain serial so that they do not race Lake builds. The final
status records the effective worker count.

To reproduce a compacted control from a successful run, restore its missing
baseline files without overwriting its changes, then run its original `argv`
from `commands.json` in the recorded `cwd` with the same toolchain and build:

```sh
control_evidence=/tmp/slc-all
control_dir="$control_evidence/control-family-0"
cp -n "$control_evidence"/control-baseline/*.json "$control_dir"/
```

Do not restore baseline files into failed controls or controls that intentionally
removed a whole corpus file; those directories are retained without compaction.

## Reproduce native results

Use the `nightly-2026-05-01` Rust pin of this suite in `rust-toolchain.toml`. Recording updates `corpus/` and its
manifests, so use a separate checkout if the committed fixtures should stay untouched.

```sh
# Record every driver twice and require matching results, then replay the registered functions.
python3.12 -B tools/library-conformance/run.py --record --twice \
  --evidence-dir /tmp/slc-native-all
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --evidence-dir /tmp/slc-native-all-check

# Or record and check one selected driver.
python3.12 -B tools/library-conformance/run.py --record --twice \
  --driver versions-solana-hash-4-3-0 --evidence-dir /tmp/slc-native
python3.12 -B tools/library-conformance/run.py --model-only \
  --corpus solana_hash_4_3_0 --evidence-dir /tmp/slc-native-check
```

Recording accepts `--target-dir` for an existing Cargo target root and `--offline`
when the locked crate sources are cached. Test profiles, source identities, observed fields and
case-selection details are in the [reference guide](REFERENCE.md).
The separate [Agave suite](../runtime-conformance/README.md) tests the runtime model.

## Maintain tests for a model

Use the existing `SolanalibTest.Specs.<Crate>` root, family checker and native driver. Cover
the meaningful success, error and boundary cases of the model, including state,
aliasing, callback order and cleanup when relevant. Negative controls should
reject an incorrect observable result. Test abstract protocols through Lean
scenarios when they have no native entry point. For callable profiles, check
the actual source identity at reference and compatible versions, and reject
unsupported builds or unresolved required facts. These synthetic selection
cases provide no additional native-execution evidence.

After changing a driver, record its complete corpus again. After adding or
changing a family registration or documented exception, regenerate and check:

```sh
python3.12 -B tools/library-conformance/run.py --generate-registry
```

Then repeat the model replay and enabled Lean selector tests above.
Keep supported versions and model identities in the existing source registry.
The [reference guide](REFERENCE.md#families) describes the checker and fixture formats.
