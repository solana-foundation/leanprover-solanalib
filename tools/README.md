# Package checks

Use the pinned Lean 4.34.0 toolchain and Python 3.12. The audit and replay tools use the Python standard library.

From the repository root:

```sh
lake update
lake exe cache get Solanalib.lean SolanalibTest.lean Oracle.lean
lake --wfail build Solanalib SolanalibTest sbpf-oracle \
  Solanalib.Runtime SolanalibTest.Runtime Solanalib.Contracts \
  SolanalibTest.Conformance.Runtime SolanalibTest.Conformance.Library \
  solanalib-library-conformance solanalib-selection-control
python3.12 scripts/ci-sdk-groups.py --build all
lake --wfail test
bash scripts/lint-style.sh
python3.12 scripts/check-module-ownership.py
python3.12 scripts/check-lean-loading.py
python3.12 tools/model-audit/import_tiers.py
  --workspace tools/library-conformance
SOLANA_SPECS_INTEGRATION_TESTS=1 python3.12 -B -m unittest discover -s tools/model-audit -p 'test_*.py'
python3.12 -B -m unittest discover -s tools/runtime-conformance -p 'test_*.py'
python3.12 -B tools/runtime-conformance/run.py --model-only --evidence-dir /tmp/solanalib-runtime-check
python3.12 packages/solanalib-specs/tools/generate_capabilities.py --check
python3.12 packages/solanalib-specs/tools/version_compatibility.py --check
python3.12 tools/model-audit/check_solana_specs.py --fetch-sdk
SOLANA_CONFORMANCE_SELECTION_LEAN=1 python3.12 -B -m unittest discover -s tools/library-conformance -p 'test_*.py'
python3.12 tools/library-conformance/run.py --model-only --registered-checkers --control-jobs "$(nproc)" \
  --evidence-dir /tmp/solanalib-library-check
python3.12 tools/model-audit/check_runtime.py
python3.12 scripts/build-docs.py
```

The [runtime source guide](../packages/solanalib-runtime/source-map/README.md) documents source-byte checks. Without upstream source copies, the audit records zero checked source anchors. The [native guide](runtime-conformance/README.md) documents Agave reproduction with Rust 1.97.1.

All 115 libraries are separately selectable targets in the root Lake package and share its artifact directory. The ordinary-loading check imports a representative from every library both statically and through `Lean.importModules`; run the builds first. For smaller changes, select the affected targets and their relevant audits. The [CI guide](../docs/ci.md) describes the workflow jobs and configured timeouts.

The docs builder collects every production module explicitly and renders one site. `lake build Solanalib:docs` alone is insufficient because runtime, contracts and SDK models have separate library targets in the same package. The builder also checks the output manifest of doc-gen4 after removing old project pages so cached HTML cannot hide missing module coverage.
