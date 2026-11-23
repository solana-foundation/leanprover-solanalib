# Authoring models, tests and gap records

Use the shared `Solanalib.Runtime` account, public-key and instruction types for Solana developments. Keep runtime balances as `Nat` values with the source bound in `Account.WF`. Keep all libraries in the root `solanalib` package and one build directory, with separately selectable targets and one owner per module. Add modules to the explicit roots/globs of the owning library and its appropriate aggregator. Source layers keep their existing import boundaries; the Mathlib dependency of the single package does not widen model imports.

## Record the claim where it is defined

| Development | Authoritative inputs |
| --- | --- |
| Runtime operation | [Source correspondence](../packages/solanalib-runtime/source-map/sources.json), [source notes](../packages/solanalib-runtime/source-notes/README.md), [trust boundary](../packages/solanalib-runtime/TRUST.md), scenario tests and [Agave conformance](../tools/runtime-conformance/README.md). |
| SDK model | [Source registry](../packages/solanalib-specs/source-map/README.md): immutable source/build profile, exact Rust identity, contract/reference, model role, witnesses, assumptions, gaps and mathematical clients. |
| Native observation | Driver manifest, lockfile, recorded bytes and checker in [library conformance](../tools/library-conformance/README.md), or the corresponding Agave fixture. |
| Cross-layer connection | The relevant execution theorem and [gap review record](gap-review.json); shared value types do not establish a simulation from sBPF execution to the runtime relation. |

For a source-facing model, name the exact reference revision/archive, source function, target/features/dependency profile, represented results, errors and state effects. State the used assumptions and omitted behavior. Preserve the difference between full, partial, observation and supporting models, and between exact reviewed releases and assumed compatible ranges. Unknown build facts cannot become an eligible match. A crate import, catalog membership or passing sample does not establish whole-crate coverage.

Do not change the code or definitions being verified to make a proof succeed. Keep source representation obligations separate from mathematical results that do not use them. Every added premise must support the substantive result; do not retain an unused premise or add a trivial lemma solely to mention it. External CPI invocation stays opaque at the actual invocation boundary, with the outcome and effects of the callee supplied by an explicit contract.

## Keep gap records connected to evidence

The [generated gap index](model-gaps.md) reads existing runtime correspondence IDs, SDK model IDs, conformance exception IDs and pending releases from the recorded release census. It records intentional scope separately from open source bindings, release applicability reviews and test evidence. Its review metadata adds a review date and resolution criteria without copying the authoritative coverage state into another editable registry. Changing a sealed input requires reviewing the affected records and refreshing the hashes in [gap-review.json](gap-review.json); generation never silently assigns a new review date.

Each derived record contains a stable ID, affected declarations and source functions where present, exact source/build conditions or their canonical references, omitted or assumed behavior, affected claims, tests/witnesses or counterexample references, status, resolution criterion and the last index review. That review is explicitly distinct from a new review of the pinned Rust sources. New cross-layer gaps use the same fields in the review record. Keep IDs stable when wording or file locations change.

For a new SDK limitation, update the `model_gaps` and `remaining_requirements` of that model, its role and source applicability as needed. For a runtime limitation, update the corresponding source-correspondence record and argument. A missing native entry point needs a reason in `not-tested.toml`; an undecided precondition needs its own `requires-open.toml` entry. A missing exact checker needs an explicit finite selection record. These are different conditions: closing one does not close an implementation proof or another test gap. Do not relabel a supporting observation as a complete operational model to remove a gap.

Generate and check the index with Python 3.12:

```sh
python3.12 tools/model-audit/generate_gap_index.py
python3.12 tools/model-audit/generate_gap_index.py --check
# Optional full derived records for review; keep generated receipts outside Git.
python3.12 tools/model-audit/generate_gap_index.py --check --json /tmp/solanalib-gaps.json
```

## Validate the affected claim

1. Build the affected production and scenario libraries with `lake --wfail build`, then run the root test driver where relevant. Cover success, rejection, rollback, numeric/length boundaries, call ordering and side effects. Keep closed reference-correctness and satisfiability witnesses, execution witnesses for relational references, and exact family/reference/sample identities. A satisfiable example is not universal source correctness.
2. Replay the affected authenticated native recordings and their negative controls. Compare every represented observable, including errors and state effects. For a nondeterministic relation, check that the native outcome is admitted; do not compare it with an arbitrary witness. Preserve complete native inputs when selecting checkers. Omitted observations and skipped controls earn no conformance credit, and newly missing or stale exception identities must fail.
3. When source behavior, a driver or a recording changes, reproduce native observations using the recorded compiler, lockfiles, target and features. The Agave suite uses Rust 1.97.1; the library suite separately pins `nightly-2026-05-01`. A host observation supports its stated target/build scope. Native reproduction remains separate from replaying an existing recording and from a Rust implementation proof.
4. Refresh the affected source/model hashes and generated catalogs, applicability outputs, version tables and indexes in the same change. Run source, identity, ownership, import-layer, placeholder and complete axiom audits. Audit all owned declarations, including private/generated declarations; display filters cannot narrow proof coverage. Runtime and SDK proofs use only `propext`, `Classical.choice` and `Quot.sound`. The existing sBPF native-decision dependency is separately recorded; do not broaden that boundary.

Use the exact commands in the [runtime guide](../packages/solanalib-runtime/README.md), [SDK guide](../packages/solanalib-specs/README.md), conformance guides and [CI description](ci.md). Small committed recordings and native drivers stay with their models; fetched source archives, compiler outputs and large transient receipts stay outside Git. A mathematical helper with no native operation keeps a documented testing rationale and meaningful Lean scenarios.

## Review

A review states which behavior changed, which claims and source/build profiles it affects, which inputs and generated evidence were refreshed, and which relevant checks passed. Link precise remaining gaps. Preserve existing API compatibility by default. Sign commits and follow the contribution and copyright conventions of the repository.

For module or dependency changes, test a fresh Git consumer at the exact commit. Root, runtime, contracts, SDK and test modules must load with plain `lake env lean` and `Lean.importModules`; run the runtime replay through `lean --run`. Check every selectable library. A Lake-aware editor or `lake lean` result alone does not exercise ordinary module lookup.
