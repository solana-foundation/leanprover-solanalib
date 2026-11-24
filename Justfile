# Solanalib: see docs/tests.md for the complete suite inventory.
set shell := ["bash", "-euc"]
export MATHLIB_NO_CACHE_ON_UPDATE := "1"
python := "uv run --no-project --python 3.12 python"
control_jobs := env_var_or_default("SOLANALIB_CONTROL_JOBS", `nproc`)
native_jobs := env_var_or_default("CARGO_BUILD_JOBS", `nproc`)

default:
    @just --list

# Fetch the committed dependency revisions and the small public Mathlib cache.
setup:
    lake -Kenv=dev env lean --version
    lake exe cache get Mathlib.Tactic.Linter.Style Mathlib.Tactic.Linter.Header
    {{python}} --version

# Build the runtime and contract libraries, with warnings as errors.
build:
    lake --wfail build

# Build the exploratory sBPF model, its regressions and the oracle executable.
test-sbpf:
    lake --wfail build Solanalib.SBPF SolanalibTest.SBPF sbpf-oracle

# Check the tutorial proof through Lake and ordinary Lean loading.
test-examples:
    lake --wfail build SolanalibTest.Examples
    lake env lean -DwarningAsError=true examples/SolanalibTest/Examples/CheckedTransfer.lean

# Build all fourteen runtime scenarios and run the offline harness controls.
test-runtime:
    lake --wfail build Solanalib.Runtime SolanalibTest.Runtime SolanalibTest.Conformance.Runtime
    {{python}} -B -m unittest discover -s tools/runtime-conformance -p 'test_*.py'

# Build shared contracts and every SDK production/scenario library.
test-specs:
    lake --wfail build Solanalib.Contracts
    {{python}} scripts/ci-sdk-groups.py --build all

# Replay the authenticated Agave recording with model and comparison controls.
replay-runtime: test-runtime
    {{python}} -B tools/runtime-conformance/run.py --model-only --evidence-dir "$(mktemp -d "${TMPDIR:-/tmp}/solanalib-runtime.XXXXXX")"

# Replay both authenticated native recordings with controls; runs no Rust.
test-conformance: replay-runtime
    lake --wfail build SolanalibTest.Conformance.Library solanalib-library-conformance solanalib-selection-control
    {{python}} -B tools/library-conformance/run.py --model-only --registered-checkers --control-jobs {{control_jobs}} --evidence-dir "$(mktemp -d "${TMPDIR:-/tmp}/solanalib-library.XXXXXX")"
    SOLANA_CONFORMANCE_SELECTION_LEAN=1 {{python}} -B -m unittest discover -s tools/library-conformance -p 'test_*.py'

# Check style and prose, local links, upstream references and both generated indexes.
lint:
    bash scripts/lint-style.sh
    {{python}} scripts/check-prose.py
    {{python}} scripts/check-doc-links.py
    {{python}} scripts/check-upstream-references.py
    {{python}} scripts/generate-test-index.py --check
    {{python}} tools/model-audit/generate_gap_index.py --check
    git diff --check

# Check runtime source correspondence and all proof dependencies.
audit-runtime:
    {{python}} tools/model-audit/check_runtime.py

# Complete source/proof/generator audits and compiled negative controls.
audit: build test-sbpf test-examples test-runtime test-specs lint audit-runtime check-generated
    {{python}} -B -m unittest discover -s scripts -p 'test_*.py'
    SOLANA_SPECS_INTEGRATION_TESTS=1 {{python}} -B -m unittest discover -s tools/model-audit -p 'test_*.py'
    just audit-specs
    {{python}} tools/model-audit/import_tiers.py
    lake --wfail build SolanalibTest.Conformance.Library solanalib-library-conformance solanalib-selection-control
    {{python}} scripts/check-module-ownership.py
    {{python}} scripts/check-lean-loading.py

# Build and postprocess the documentation of every production library.
docs: check-generated
    {{python}} scripts/build-docs.py

# Open the generated site in the default browser.
docs-open: docs
    {{python}} -m webbrowser .lake/build/doc/index.html

# All regular local CI suites, including docs; fresh native reproduction is separate.
check-all: audit test-conformance docs

# Refresh one reviewed runtime correspondence row; leaves other rows untouched.
refresh-runtime-seal correspondence:
    {{python}} tools/model-audit/refresh_runtime_correspondence.py {{quote(correspondence)}}

# Refresh one reviewed SDK library abstraction after catalog generation.
refresh-sdk-seal abstraction:
    {{python}} tools/model-audit/refresh_sdk_abstraction.py {{quote(abstraction)}}

# Seal reviewed gap inputs without changing the explicit review date or scope.
refresh-gap-review:
    {{python}} tools/model-audit/refresh_gap_review.py

# Generate gap and complete test indexes; requires current reviewed gap inputs.
generate-indexes:
    {{python}} tools/model-audit/generate_gap_index.py
    {{python}} scripts/generate-test-index.py

# Generate SDK capabilities, applicability data and complete-family controls.
generate-specs:
    {{python}} packages/solanalib-specs/tools/generate_capabilities.py
    {{python}} packages/solanalib-specs/tools/version_compatibility.py

# Generate committed Lean and human guides, plus an ignored applicability export.
# Reviewed source and gap seals must be current before generating indexes.
generate: generate-specs generate-conformance generate-indexes

# Check committed generated artifacts and validate an independent machine export.
# Ordinary Lake builds use the committed Lean and need no Python generation.
check-generated:
    {{python}} packages/solanalib-specs/tools/generate_capabilities.py --check
    {{python}} packages/solanalib-specs/tools/version_compatibility.py --check
    {{python}} -B tools/library-conformance/run.py --check-registry
    {{python}} tools/model-audit/generate_gap_index.py --check
    {{python}} scripts/generate-test-index.py --check

# Audit SDK source bytes, exact witness identities and proof dependencies.
audit-specs:
    {{python}} tools/model-audit/check_solana_specs.py --fetch-sdk

# Generate the checker registry and reference tables, then check freshness.
generate-conformance:
    {{python}} -B tools/library-conformance/run.py --generate-registry
    {{python}} -B tools/library-conformance/run.py --check-registry

# Replay one SDK corpus and its applicable negative controls.
test-library-corpus corpus:
    {{python}} -B tools/library-conformance/run.py --model-only --corpus {{quote(corpus)}} --control-jobs {{control_jobs}} --evidence-dir "$(mktemp -d "${TMPDIR:-/tmp}/solanalib-library-corpus.XXXXXX")"

# Reproduce Agave with Rust 1.97.1 and a sealed archive; prints its evidence path.
test-native-runtime archive evidence:
    {{python}} -B tools/runtime-conformance/run.py --source-archive {{quote(archive)}} --jobs {{native_jobs}} --timeout 3600 --evidence-dir {{quote(evidence)}}

# Reproduce one SDK driver twice with its frozen nightly; keep committed recordings.
test-native-library driver evidence:
    {{python}} -B tools/library-conformance/run.py --record --twice --no-write-corpus --driver {{quote(driver)}} --target-dir .lake/native-library --evidence-dir {{quote(evidence)}}

# Adopt a passed, fully checked Agave evidence directory into the replay pair.
adopt-runtime-recording evidence:
    {{python}} -B tools/runtime-conformance/adopt_recording.py {{quote(evidence)}}

# Record one reviewed SDK driver twice and update its complete corpora and manifest.
record-native-library driver evidence:
    {{python}} -B tools/library-conformance/run.py --record --twice --driver {{quote(driver)}} --target-dir .lake/native-library --evidence-dir {{quote(evidence)}}

# Remove local build artifacts; keep dependency checkouts.
clean:
    lake clean

# Remove the entire .lake directory, including deps. Forces a full re-setup.
clean-all:
    rm -rf .lake
