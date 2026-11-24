# CI checks

The [regular workflow](../.github/workflows/ci.yml) runs on pull requests, pushes to main and manual dispatch. It has no source-path filters. Lean builds use `--wfail`, and Python steps use Python 3.12.

| Job | Checks | Configured timeout |
| --- | --- | ---: |
| Lint | Lean style, prose, source-layer imports, documentation links, upstream references, generated test/gap indexes and their controls. | 10 minutes |
| Root library | Root library, tutorial, tests, sBPF oracle, module roots and unique Lake ownership. | 25 minutes |
| Runtime | Runtime and scenario builds, authenticated Agave replay, comparator controls, source-correspondence hashes and complete proof dependencies. Local upstream source copies are not supplied, so this job does not check their bytes. | 15 minutes |
| Contracts | Shared contract vocabulary. | 10 minutes |
| SDK groups | Six disjoint groups cover all 108 production and scenario libraries, with their complete import closures. | 25 minutes per group |
| SDK audit | All SDK libraries, compiled negative controls, generated catalogs and applicability, complete proof dependencies and fetched source bytes. | 30 minutes |
| Library replay | All 116 libraries, ordinary and dynamic Lean loading, checker registry, authenticated observations, negative controls and compiled selection controls. Exact omissions are recorded separately. | 45 minutes |

These are workflow settings, not measured hosted-CI runtimes. Hosted setup time, cache transfer, disk performance and peak aggregate memory have not been measured for this branch. The jobs configure four Lean threads; the library replay uses four workers for independent negative controls. Local `just` recipes use the available processors for those controls, with `SOLANALIB_CONTROL_JOBS` as an optional override.

The library runner is serial by default. `--control-jobs` runs independent mutations concurrently. It retains every selected record, mutation and failure assertion, with separate input copies and outputs, synchronized command receipts and deterministic result ordering. Omitted records receive no conformance credit.

Lean jobs cache `.lake/packages` and `.lake/build`. Cache keys include the root Lake configuration, manifest, toolchain and relevant Lean sources; shared-model changes invalidate dependent SDK groups. Lake checks restored artifacts against current inputs. The workflows fetch the pinned Mathlib cache for the two direct package imports, `Mathlib.Tactic.Linter.Style` and `Mathlib.Tactic.Linter.Header`.

## Documentation

The [documentation workflow](../.github/workflows/docs.yml) runs on manual dispatch and changes to its listed source/configuration paths on main. It builds and deploys the production API site to GitHub Pages. The pinned doc-gen4 build collects all production modules from Lake and checks every expected page. Runtime, contracts and SDK libraries share the root artifact directory. The docs job has a 40-minute timeout.

Local documentation generation uses the available processors. Set `SOLANALIB_DOC_JOBS` to choose the number of concurrent documentation processes for the available memory.

The fixed per-declaration heartbeat limit of the pinned generator leaves two presentation gaps: the entry for `Solanalib.Specs.Core.AnchorSplSupport.Ready` in [Admission.lean](../packages/solanalib-specs/Solanalib/Specs/Core/AnchorSplSupport/Admission.lean), and generated equation details for `Solanalib.Specs.AnchorLang.Capabilities.reference` in [Capabilities.lean](../packages/solanalib-specs/Solanalib/Specs/AnchorLang/Capabilities.lean). Their definitions, proof checks and source links remain available. The build lists these limitations in `solanalib-warnings.json` and fails on unexpected warnings from owned modules. Upstream Lean documentation also emits equation-generation warnings.

## Native reproduction

The [native workflow](../.github/workflows/native.yml) runs monthly, on published releases or manually. It includes a cold build of all owned Lean, the pinned Agave oracle on Rust 1.97.1, and every discovered library driver on `nightly-2026-05-01`. The 131 drivers form 16 Cargo workspaces, with at most four workspaces active in the matrix. Each workspace resolves dependencies afresh from exact modeled-provider pins. Drivers build separately and run twice; complete fresh corpus bytes must match the authenticated recordings used by regular CI. Incidental dependency changes that alter an observation fail the job.

The configured native-job timeouts are 60 minutes for cold Lean, 90 minutes for Agave and 120 minutes per library workspace. Native reproduction uploads its evidence as workflow artifacts. The ordinary runtime and library replay jobs do not upload theirs. Native reproduction is separate from the mathematical proofs and from replaying a recording.

Run `just check-all` for the complete regular local suite, including production documentation. Fresh native reproduction uses the separate recipes in the [extension guide](extending.md).
