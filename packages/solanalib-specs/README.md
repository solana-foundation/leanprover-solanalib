# Solana library models

Pure Lean models of selected Solana library functions, using the
[shared contract vocabulary](../solanalib-contracts/README.md) and
[Solana runtime model](../solanalib-runtime/README.md).
These selectable libraries belong to the root `solanalib` Lake package, which includes Mathlib. Their Lean imports stay within the shared contracts, runtime and SDK models, Lean core and Std.

[LIBRARIES.md](LIBRARIES.md) lists the libraries, function groups and tests.
The [source registry](source-map.json) defines the individual contracts,
references, witnesses and source identities. A library root covers only its
registered functions.

The [model and test standard](../../docs/model-standard.md) describes how to register contracts, record their scope and validate their claims. The [gap index](../../docs/model-gaps.md) is generated from the existing registries and conformance policies.

## Use the models

Import the library root, such as `Solanalib.Specs.SolanaHash`, and use the declaration for the
Rust item, such as `Solanalib.Specs.SolanaHash.Hash.to_bytes_contract`. Identical behavior across
reviewed releases shares one declaration; different behavior has a named variant.
[VERSION_COMPATIBILITY.md](VERSION_COMPATIBILITY.md) and `applicability.json`
record the supported releases and build conditions. Select the matching catalog
with the [build lookup](BINDINGS.md#selecting-a-reviewed-build); `Catalog.forBuild`
retains the same contracts while selecting their applicable source identities.

A contract relates inputs and initial state to outcomes. `Family` retains type,
callback and other interpretation parameters. Returns include ordinary errors;
unwinds retain their reached state; terminal exits have no post-state.
The common vocabulary also describes references, borrow guards, owned resources,
codecs and ordered dependency calls.

Each library exports a generated `Capabilities` catalog. Clients assume
`Capabilities.Spec catalog needs operations` for the members they use, under one
operation assignment. Observations and supporting relations keep their declared
scope; they do not replace the full API model. Shared supporting families have
[their own catalog](Solanalib/Specs/Core/SupportingCapabilities.lean).

These assumptions are distinct from Rust body proofs. Reference-correctness,
satisfiability and finite-execution witnesses establish properties of the models.
[BINDINGS.md](BINDINGS.md) describes their interpretation obligations and the
explicit execution correspondences. [Source notes](source-notes) explain the comparison
with the pinned libraries, including effects, failure order and version differences.

## Tests

Every library has a separate `SolanalibTest.Specs.<Crate>` root, linked from [LIBRARIES.md](LIBRARIES.md).
The shared [scenario tests](SolanalibTest/Specs/Core.lean) cover callbacks,
ownership, cleanup and model composition. Build all 108 production and scenario libraries from the repository root:

```sh
python3.12 scripts/ci-sdk-groups.py --build all
```

The [library conformance suite](../../tools/library-conformance/README.md)
checks native calls against the registered models and provides per-driver
reproduction commands. From the repository root:

```sh
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --evidence-dir /tmp/slc-all
SOLANA_CONFORMANCE_SELECTION_LEAN=1 python3.12 -B -m unittest discover -s tools/library-conformance -p 'test_*.py'
```

Its report identifies every deciding model and any recorded test exception.
Abstract protocols without a native entry point use mathematical scenario tests.
The runtime has its own [Agave comparisons](../../tools/runtime-conformance/README.md).

## Build and audit

Use the recorded Lean toolchain and Python 3.12. From the repository root:

```sh
python3.12 packages/solanalib-specs/tools/generate_capabilities.py --check
python3.12 packages/solanalib-specs/tools/version_compatibility.py --check
python3.12 tools/model-audit/check_solana_specs.py --fetch-sdk
python3.12 tools/model-audit/import_tiers.py
SOLANA_SPECS_INTEGRATION_TESTS=1 python3.12 -B -m unittest discover -s tools/model-audit -p 'test_solana_*.py'
```

The audit checks source anchors and hashes, exact contract/reference/sample
witnesses, all registered modules and standard axiom dependencies. After changing
registration, run the two generators without `--check`; do not edit generated
catalogs, applicability data or tables manually.

For release-census maintenance, add `--fetch-index` to the version check. This
compares the frozen source census against the live registry and reports new
releases for review; it does not admit them or extend any compatibility range.
Pending release reviews are tracked in the [gap index](../../docs/model-gaps.md), separately from reviewed model coverage.

The [registry guide](source-map/README.md) and [contribution instructions](../../CONTRIBUTING.md) describe the Rust identities, registration and review obligations.
Justify model changes with the pinned library sources, mathematical proofs and conformance tests.

## Package consumption

Require the root package from Git at an immutable commit, then import the desired library:

```lean
require solanalib from git
  "https://github.com/solana-foundation/leanprover-solanalib" @ "<immutable-commit>"
```

For example, `import Solanalib.Specs.PinocchioToken` selects that model. The source folders under `packages/` have no separate Lake package configuration: all `Solanalib` and `SolanalibTest` modules share one artifact directory for both ordinary Lean lookup and Lake builds. Choose an immutable commit available from the specified Git repository.
