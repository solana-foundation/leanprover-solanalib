# Package checks

Use the pinned Lean 4.34.0 toolchain and Python 3.12. The audit and replay tools use the Python standard library.

From the repository root:

```sh
lake --wfail build Solanalib SolanalibTest sbpf-oracle
lake --wfail test
lake --wfail build Solanalib.Runtime SolanalibTest.Runtime
bash scripts/lint-style.sh
python3.12 scripts/check-module-ownership.py
python3.12 scripts/check-lean-loading.py
python3.12 tools/model-audit/import_tiers.py
python3.12 -B -m unittest discover -s tools/model-audit -p 'test_*.py'
python3.12 -B -m unittest discover -s tools/runtime-conformance -p 'test_*.py'
python3.12 -B tools/runtime-conformance/run.py --model-only --evidence-dir /tmp/solanalib-runtime-check
python3.12 tools/model-audit/check_runtime.py
python3 scripts/build-docs.py
```

The [runtime source guide](../packages/solanalib-runtime/source-map/README.md) documents source-byte checks. Without upstream source copies, the audit records zero checked source anchors. The [native guide](runtime-conformance/README.md) documents Agave reproduction with Rust 1.97.1.

The docs builder collects every production module explicitly and renders one site. `lake build Solanalib:docs` alone is insufficient because `Solanalib` and `Solanalib.Runtime` remain separate library targets in the same package. The builder also checks the output manifest of doc-gen4 after removing old project pages so cached HTML cannot hide missing module coverage.
