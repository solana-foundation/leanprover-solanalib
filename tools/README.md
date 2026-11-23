# Package checks

Start with [Getting started](../docs/getting-started.md). Use the pinned Lean 4.34.0 toolchain of the repository. The Justfile prepares Python 3.12 through uv. The audit and replay tools use the Python standard library.

From the repository root:

```sh
just setup
just check-all
```

`check-all` runs the following suites. Select a focused target while developing; the [test index](../docs/tests.md) links every scenario, checker, Python control file and native driver.

| Target | Checks |
| --- | --- |
| `build`, `test` | Root library, sBPF oracle, regressions and System transfer conservation. |
| `test-examples` | The worked transfer proof through a warnings-as-errors build and ordinary Lean loading. |
| `test-runtime` | Runtime production/scenario libraries and offline conformance controls. |
| `test-specs` | Shared contracts and every registered SDK production/scenario pair. |
| `test-conformance` | Both authenticated native recordings, model replay, negative controls and compiled selection controls. |
| `lint` | Lean style, local documentation links, generated test/gap indexes and whitespace. |
| `audit-runtime` | Runtime source correspondence, module inventory and complete proof dependencies. |
| `audit` | Builds/scenarios above, source/axiom/witness checks, generator checks, Python and compiled controls, import rules, module roots, module ownership and ordinary loading. |
| `docs` | The complete production documentation site and output coverage check. |

Fresh native reproduction is separate from `check-all`. `test-native-runtime` takes the pinned Agave archive and a fresh evidence directory; it uses Rust 1.97.1. `test-native-library` takes a discovered driver name and a fresh evidence directory; it uses `nightly-2026-05-01` and records twice without replacing committed corpora. The [extension walkthroughs](../docs/extending.md) give complete commands, recording promotion and source-review steps. The [runtime native guide](runtime-conformance/README.md) and [SDK testing guide](library-conformance/README.md) describe the fixtures and evidence formats.

All 116 libraries are separately selectable targets in the root Lake package and share its artifact directory. The ordinary-loading check imports a representative from every library both statically and through `Lean.importModules`; run the builds first. The [CI guide](../docs/ci.md) describes the workflow jobs and configured timeouts.

The [runtime source guide](../packages/solanalib-runtime/source-map/README.md) documents source-byte checks. An audit run without upstream source copies records zero checked source anchors.

The docs builder collects every production module explicitly and renders one site. `lake build Solanalib:docs` alone is insufficient because runtime, contracts and SDK models have separate library targets in the same package. The builder also checks the output manifest of doc-gen4 after removing old project pages so cached HTML cannot hide missing module coverage.
