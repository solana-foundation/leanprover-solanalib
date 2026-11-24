# Extending Solanalib

Start with [Getting started](getting-started.md) and [CONTRIBUTING.md](../CONTRIBUTING.md). This guide follows two existing operations through every layer of a contribution. Their names make the commands runnable in a clean checkout: replaying the walkthrough does not require inventing a new API. When adding an operation, use these as templates, give the new operation its own declarations and registry identity, and make the edits described before each command block. Do not register a second copy of either example.

Run commands at the repository root, in one Bash session per walkthrough, after `just setup`. Keep the checked-in Lean, Rust and dependency pins. The native runtime walkthrough requires Linux x86-64, Rust 1.97.1, `curl` and a C/C++ toolchain. The SDK native walkthrough uses the separate `nightly-2026-05-01` Rust toolchain. The [native CI workflow](../.github/workflows/native.yml) lists their setup and additional native build packages. Native builds need substantially more disk space and time than replaying committed recordings.

## Runtime walkthrough

Use `setLamports` in [Borrowed.lean](../packages/solanalib-runtime/Solanalib/Runtime/Borrowed.lean) as the example. A read-only account rejects even a same-value write; an external debit fails before the writability check. Checked addition tests overflow before calling the setter. These are observable choices, so a change must preserve the selected Agave behavior or explicitly record a model gap.

### 1. Read the source and change the model and scenario

Read the pinned Agave 4.3.2 `transaction-context/src/instruction_accounts.rs`, using the archive in step 4. Review the actual operation, error order and state effects. Edit the following files in this order; the existing setter is the worked instance:

| File | Change |
| --- | --- |
| [Solanalib/Runtime/Borrowed.lean](../packages/solanalib-runtime/Solanalib/Runtime/Borrowed.lean) | Add or change the operation without assuming its result. Keep source representation obligations separate from the mathematical definition. |
| [SolanalibTest/Runtime/Regression.lean](../packages/solanalib-runtime/SolanalibTest/Runtime/Regression.lean) | Add a successful case, a real rejection and a boundary or ordering case. The existing `lamports_same_value_untouched` checks that a permitted no-op does not mark an account touched. |
| [Solanalib/Runtime.lean](../packages/solanalib-runtime/Solanalib/Runtime.lean), [SolanalibTest/Runtime.lean](../packages/solanalib-runtime/SolanalibTest/Runtime.lean) | Import a new production or scenario module if one was needed. Existing modules already belong to the recursive runtime library targets. |
| [source-map/sources.json](../packages/solanalib-runtime/source-map/sources.json) | Extend the `context-and-setters` correspondence row: declarations, reviewed modules, source IDs, argument, assumptions and remaining limitations. Add a source entry if the operation needs a new source anchor. |
| [source-notes/agave-4.3.2.md](../packages/solanalib-runtime/source-notes/agave-4.3.2.md) | Update the `account-mutation` argument when its explanation changes. |

Add an operation to its existing reviewed module when that is the right home. A new module also needs its own source-correspondence coverage; placing a file in the source tree is insufficient. A new source root needs Lake ownership and import-policy changes as described in the new-crate section.

Build the changed layer and its scenarios, and run the offline harness controls:

```sh
just test-runtime
```

### 2. Seal the reviewed source correspondence

After the source review, refresh only the Lean hashes of the reviewed correspondence row. The [refresh tool](../tools/model-audit/refresh_runtime_correspondence.py) rejects missing, duplicate or unknown rows and noncanonical module paths. It does not approve source claims or refresh unrelated records:

```sh
just refresh-runtime-seal context-and-setters
just audit-runtime
```

`just audit-runtime` checks the module inventory, reviewed Lean hashes, source-correspondence arguments and complete proof dependencies. Without local upstream source copies it records zero checked source anchors. The source review above remains necessary; the [runtime source guide](../packages/solanalib-runtime/source-map/README.md) gives the commands for checking upstream bytes and line anchors.

### 3. Extend the shared native/model case

Edit [accounts.tsv](../tools/runtime-conformance/accounts.tsv) with the input and expected observation for the new case. The existing `lamports_readonly_noop`, `lamports_external_readonly_debit` and `checked_add_overflow_before_readonly` cases illustrate rejection and ordering. Both implementations consume the same fixture identity.

For a new operation kind, also extend [agave_cases.rs](../tools/runtime-conformance/agave_cases.rs) and [SolanalibTest/Conformance/Runtime.lean](../tools/runtime-conformance/SolanalibTest/Conformance/Runtime.lean). Use the real Agave operation on the native side and the actual model operation on the Lean side. Change [test_run.py](../tools/runtime-conformance/test_run.py) if the output or fixture format gains a field, including a malformed or mismatching observation that must fail. Serialization and CPI additions instead use [serialization.tsv](../tools/runtime-conformance/serialization.tsv), [cpi.tsv](../tools/runtime-conformance/cpi.tsv) and [cpi_cases.rs](../tools/runtime-conformance/cpi_cases.rs), as appropriate; this setter example does not need those files changed.

### 4. Reproduce and retain fresh Agave evidence

The archive has SHA-256 `917912ac67fc0b6ffec94e33e1ce113db581e1f1706aa1ecbe4224b967b15f30`; the runner checks it and the pinned compiler. It builds in the fresh evidence directory, checks source preservation, compares Lean with native observations and runs the comparison controls:

```sh
solanalib_agave_archive=$(mktemp /tmp/solanalib-agave.XXXXXX.tar.gz)
curl --fail --location https://codeload.github.com/anza-xyz/agave/tar.gz/a203300045b405f86c9c84308b2eae76af69ac3b --output "$solanalib_agave_archive"
solanalib_runtime_evidence=$(mktemp -d /tmp/solanalib-native-runtime.XXXXXX)
just test-native-runtime "$solanalib_agave_archive" "$solanalib_runtime_evidence"
```

Inspect the `SUMMARY.md` of that directory, `comparison.json`, `native-build.json` and `MANIFEST.json`. Its case counts are finite observations; the four native-only borrow observations do not become Lean equivalence claims. Retain this evidence outside Git.

When fixtures or native inputs changed, replace both [expected-native.tsv.gz](../tools/runtime-conformance/expected-native.tsv.gz) and [expected-native.json](../tools/runtime-conformance/expected-native.json) from that successful run. The [adoption tool](../tools/runtime-conformance/adopt_recording.py) checks every manifest digest, required artifacts, passed status, revision, target, archive, compiler and current native inputs. It authenticates the complete candidate through the replay loader before replacing either recording file. On an unchanged checkout it reproduces the observations but refreshes the provenance of the run; that rehearsal does not need to become a contribution.

```sh
just adopt-runtime-recording "$solanalib_runtime_evidence"
just replay-runtime
```

The replay authenticates the compressed bytes, metadata and fixture hashes before comparing observations. Never hand-edit the recording to make a model change pass.

### 5. Refresh the gap and navigation records

The `limitations` and `assumptions` of the `context-and-setters` row are the authority for `runtime:context-and-setters` in [model-gaps.md](model-gaps.md). Describe an unresolved mismatch there, with its affected declarations and source conditions; do not remove the limitation because a finite fixture passed. For a separate correspondence row, use a separate stable ID.

Review the changed inputs in [docs/gap-review.json](gap-review.json), including the review date and scope. Then use the [gap-seal tool](../tools/model-audit/refresh_gap_review.py) and regenerate the gap and test indexes. The tool preserves the explicit review date, policies and scope. This seals the review you just performed; it is not an automatic source review:

```sh
just refresh-gap-review
just generate-indexes
just lint
just check-all
```

Also update the runtime [README scenario table](../packages/solanalib-runtime/README.md#tests) for a new scenario file. The generated changes are `docs/model-gaps.md` and `docs/tests.md`; keep them with the reviewed source and recording changes. `check-all` runs both recorded replay suites along with the proof/source audits.

## SDK walkthrough

Follow `solana-system-interface::instruction::transfer_operational` through the System interface crate. It constructs an instruction; it does not execute a transfer or invoke a callee. This is a relation-based generic contract, so it exercises all three required witnesses. Its earlier returned-value observation is a separate model, as explained in [Getting started](getting-started.md#understand-the-boundary).

### 1. Define the contract, reference and closed witnesses

Read the pinned `solana-system-interface` 3.2.0 `src/instruction.rs` source and [value-request-system.md](../packages/solanalib-specs/source-notes/value-request-system.md). Review the allocation of the chosen function, feature-selected serialization, failure and cleanup order. For a new function, edit these files in order:

| File | Change |
| --- | --- |
| [Solanalib/Specs/SolanaSystemInterface/Operational.lean](../packages/solanalib-specs/Solanalib/Specs/SolanaSystemInterface/Operational.lean) | Define the indexed arguments/providers, `_contract : Family`, relation-based `_run`, closed `_reference : FamilyReference`, explicit `_sample`, `_satisfiable : FamilySatisfiable`, and `_has_execution : FamilyHasExecution`. For transfer these all use the `transfer_operational_` stem. |
| [Solanalib/Specs/SolanaSystemInterface/Instruction.lean](../packages/solanalib-specs/Solanalib/Specs/SolanaSystemInterface/Instruction.lean) | Add shared argument or returned-value definitions only if the new function needs them. Preserve the distinction between an operational contract and an observation. |
| [Solanalib/Specs/SolanaSystemInterface.lean](../packages/solanalib-specs/Solanalib/Specs/SolanaSystemInterface.lean) | Import a new production module if one was added. |
| [SolanalibTest/Specs/SolanaSystemInterface/Operational.lean](../packages/solanalib-specs/SolanalibTest/Specs/SolanaSystemInterface/Operational.lean) | Add successful composition and real failure/cleanup scenarios. The transfer scenarios preserve signer flags, wincode selection and the actual fresh provider resources; allocation unwind must not call the serializer or drop an unowned vector. |
| [SolanalibTest/Specs/SolanaSystemInterface.lean](../packages/solanalib-specs/SolanalibTest/Specs/SolanaSystemInterface.lean) | Import a new scenario module if needed. |

For this example, the family index chooses state, resource, error and exit types. `transfer_operational_reference` covers every index. Satisfiability and execution use the same explicit sample and the same `_run`; a witness for another family or sample does not count. The precondition of the contract is `True`. Rust `u64` representation is a separate source-binding obligation, not an otherwise unused model premise. Provider relations retain actual intermediate states and non-returning exits; they do not assume serializer success or rollback.

```sh
lake --wfail build Solanalib.Specs.SolanaSystemInterface SolanalibTest.Specs.SolanaSystemInterface
```

### 2. Register the function and its applicability

Edit [source-map/solana-system-interface.json](../packages/solanalib-specs/source-map/solana-system-interface.json). The existing model key is `solana-system-interface::instruction::transfer_operational`, with `witness_kind: FamilyReference`. The loader derives the `_reference`, `_satisfiable`, `_has_execution`, `_sample` and `_run` names from the contract stem; use explicit registry fields when those names differ. Record model role, assumptions and any `model_gaps` or `remaining_requirements` as appropriate to the new model.

The API key `solana-system-interface@3.2.0::instruction::transfer` links that model to the immutable source entry `value-request::solana-system-interface-3.2.0::src/instruction.rs`, the function anchor, exact `rust_names`, scenario declarations, model dependencies and open binding obligations. Add a corresponding API entry for a new function and every reviewed source identity; do not replace it with a crate-wide claim.

Extend [source-map/solana-system-interface.json](../packages/solanalib-specs/source-map/solana-system-interface.json) for the new model. Record exact reviewed releases and build facts separately from assumed compatible ranges. Transfer distinguishes bincode and wincode, with wincode selected when both features are enabled. Preserve unknown-fact rejection, defining providers for reexports, and known range exceptions. This registry is the input; the top-level generated `applicability.json` is not an editing surface.

Update the reviewed modules, source IDs, argument and limitations of the `library::solana_system_interface` abstraction in `source-map/solana-system-interface.json`, and the source note if its explanation changes. Update [LIBRARIES.md](../packages/solanalib-specs/LIBRARIES.md) to name the additional modeled subset. Add a shared source entry to [source-map/core.json](../packages/solanalib-specs/source-map/core.json) only if the change really adds shared Core vocabulary or its source review; this transfer example needs no such edit.

Use the [shared-clause format](../packages/solanalib-specs/source-map/README.md#shared-clauses) for conditions, assumptions, obligations and review arguments. Keep per-function exceptions explicit; a clause reference selects exact text and supplies no source or build facts.

### 3. Generate catalogs and refresh the reviewed hashes

Generate the capability module and applicability outputs first. They may change the source bytes that the abstraction records:

```sh
just generate-specs
```

Review the changes to [Capabilities.lean](../packages/solanalib-specs/Solanalib/Specs/SolanaSystemInterface/Capabilities.lean), [VERSION_COMPATIBILITY.md](../packages/solanalib-specs/VERSION_COMPATIBILITY.md), and [SolanalibTest/Specs/Core/VersionCompatibility.lean](../packages/solanalib-specs/SolanalibTest/Specs/Core/VersionCompatibility.lean). These preserve complete family identities and generate equality and rejection controls. The ignored `packages/solanalib-specs/applicability.json` export contains the complete machine lookup data; keep it out of Git. Use the [SDK seal tool](../tools/model-audit/refresh_sdk_abstraction.py) to refresh only the module hashes of the reviewed abstraction after reviewing those outputs:

```sh
just refresh-sdk-seal 'library::solana_system_interface'
just test-specs
just audit-specs
```

The audit checks source bytes, registrations, closed witness identities and the proof dependencies. A refreshed hash alone establishes none of those semantic claims.

### 4. Add a native observation and a theorem-backed checker

For transfer, use the existing `instructions-3-4-0-wincode` driver and its wincode profile. The following is the complete native/checker edit set for this path:

| File | Change |
| --- | --- |
| [rust/instructions-common/system.rs](../tools/library-conformance/rust/instructions-common/system.rs) | Call the real SDK function on concrete inputs and record the observed value, including flags, order and bytes. Keep this shared operation code focused on the SDK function. |
| [rust/instructions-3-4-0-wincode/src/main.rs](../tools/library-conformance/rust/instructions-3-4-0-wincode/src/main.rs) | Register or invoke the case in this driver. |
| [rust/instructions-3-4-0-wincode/driver.toml](../tools/library-conformance/rust/instructions-3-4-0-wincode/driver.toml) | Keep every shared input and owned corpus declared. This driver owns three corpora; it is not limited to the System corpus. |
| [rust/instructions-3-4-0-wincode/Cargo.toml](../tools/library-conformance/rust/instructions-3-4-0-wincode/Cargo.toml) and its [workspace](../tools/library-conformance/rust/workspaces/profile-03/Cargo.toml) | Keep exact modeled dependency pins and the selected compiler profile. A dependency change requires reviewing the source/build profile and recording identity. Cargo resolves incidental dependencies afresh; temporary lockfiles stay outside Git. |
| [Families/Instructions/Builder.lean](../tools/library-conformance/SolanalibTest/Conformance/Library/Families/Instructions/Builder.lean) | Decode the observation and check the actual model reference. `transferOperationalChecker` uses `transfer_operational_run` with the selected format and its evaluation theorem. A checker must not prove only a handwritten copy of the expected bytes. |
| [Families/Instructions.lean](../tools/library-conformance/SolanalibTest/Conformance/Library/Families/Instructions.lean) | Register the checker for `solana_system_interface_3_2_0_wincode`, with its exact contract, reference, model/observation role and constraints. |

If the shared `system.rs` input changes, also reproduce every driver whose `driver.toml` names it: `instructions-3-4-0-bincode` and `instructions-3-4-0-wincode`. The former has its own complete dependency/profile and corpus set. An observation added only in `instructions-3-4-0-wincode/src/main.rs` needs only that driver. Do not leave the authenticated input hash of another driver stale.

Changing a member or shared dependency `Cargo.toml` requires reproducing every driver in that workspace: all member manifests constrain Cargo resolution. A source-only change requires reproducing the drivers that compile or include that source. Keep the declared `profile` and any `[build_probe].profile` consistent with the workspace profile.

Regenerate [SolanalibTest/Conformance/Library/Registry.lean](../tools/library-conformance/SolanalibTest/Conformance/Library/Registry.lean) and the generated tables in [REFERENCE.md](../tools/library-conformance/REFERENCE.md), then check them and build the checker runners:

```sh
just generate-conformance
lake --wfail build SolanalibTest.Conformance.Library solanalib-library-conformance solanalib-selection-control
```

### 5. Record twice, replay and check rejection controls

First retain two agreeing native runs without changing the Git recordings:

```sh
solanalib_sdk_evidence=$(mktemp -d /tmp/solanalib-native-library.XXXXXX)
just test-native-library instructions-3-4-0-wincode "$solanalib_sdk_evidence"
```

Inspect the evidence manifests, complete corpora and driver logs. After reviewing the results, record both runs again with corpus writing enabled. This updates all three owned corpora, [corpus/manifests/instructions-3-4-0-wincode.json](../tools/library-conformance/corpus/manifests/instructions-3-4-0-wincode.json) and their exact driver, source-input, compiler and resolved-provider identities:

```sh
just record-native-library instructions-3-4-0-wincode "$(mktemp -d /tmp/solanalib-library-record.XXXXXX)"
just test-library-corpus solana_system_interface_3_2_0_wincode
just test-conformance
```

The complete corpus set is [solana_instruction_3_4_0_wincode.json](../tools/library-conformance/corpus/solana_instruction_3_4_0_wincode.json), [solana_system_interface_3_2_0_wincode.json](../tools/library-conformance/corpus/solana_system_interface_3_2_0_wincode.json) and [solana_instruction_view_1_0_0.json](../tools/library-conformance/corpus/solana_instruction_view_1_0_0.json). Native output and recording metadata are generated, not hand-edited.

Replay authenticates native inputs and runs semantic mutations, wrong-case/kind/family controls and precondition-selection controls. Report selected, omitted and rejected observations separately. The checked-in omissions are finite test gaps, not proofs or newly covered records. Add a new omission only with an explicit reason in the applicable [not-tested.toml](../tools/library-conformance/not-tested.toml), [requires-open.toml](../tools/library-conformance/requires-open.toml) or reviewed selection rule, then regenerate the registry tables and gap index. The [testing reference](../tools/library-conformance/REFERENCE.md) explains each category.

### 6. Refresh the gap and test indexes

Put unresolved model behavior in the `model_gaps` or `remaining_requirements` of that model in `source-map/solana-system-interface.json`. Keep API binding obligations separate. The aggregate `sdk:rust-implementation-bindings` gap remains open even when native replay passes. Update a native omission at its authoritative input, rather than editing the generated gap page.

Review [gap-review.json](gap-review.json), including its date and scope, then use the [gap-seal tool](../tools/model-audit/refresh_gap_review.py) and generate both indexes:

```sh
just refresh-gap-review
just generate-indexes
just lint
just check-all
```

Keep generated Lean, `VERSION_COMPATIBILITY.md`, `docs/model-gaps.md` and `docs/tests.md` with the source, scenario, checker and recording changes. `just check-generated` rejects stale committed outputs and validates a temporary machine export. Lean builds consume the committed catalogs without running Python. Cite the resulting checks and remaining limits in the review description.

## Adding a new crate

Follow the SDK walkthrough, with these additional registration changes:

1. Choose a version-neutral `Solanalib.Specs.<Crate>` module root and matching `SolanalibTest.Specs.<Crate>` root, both under `packages/solanalib-specs`. Add their root aggregators and separately selectable `lean_lib` targets to the root [lakefile.lean](../lakefile.lean). Keep the one-package layout and one module owner; do not introduce another Lake package sharing `Solanalib/`.
2. Create `source-map/<crate>.json` with the crate pins, interfaces, API items, models, abstraction and reviewed applicability sources/profiles. Add it to the `fragments` of `source-map.json`. Use `core.json` only for shared Core vocabulary. Reuse the text and binding clauses described in the [registry guide](../packages/solanalib-specs/source-map/README.md#shared-clauses). Check the source-root/import policy in [solana_specs_config.py](../tools/model-audit/solana_specs_config.py) and [import_tiers.py](../tools/model-audit/import_tiers.py); do not allow forbidden dependencies to accommodate a new crate.
3. Add the production/scenario pair to exactly one group in [scripts/ci-sdk-groups.json](../scripts/ci-sdk-groups.json). Add the row of the crate to `LIBRARIES.md` and a source note. Generate its capability module, applicability outputs and test index using the commands above; the index discovers every scenario file, not just the crate aggregator.
4. Add a native driver directory with `Cargo.toml`, `src/main.rs` and `driver.toml`, or extend a compatible existing driver. Pin each modeled direct/transitive dependency exactly and add the driver to a compatible workspace under `rust/workspaces/`. Use optional `pin-` aliases with `default-features = false` for transitive constraints, as described in the [native dependency rules](../tools/library-conformance/REFERENCE.md#native-dependencies). Declare all shared inputs and a unique complete corpus set. Add a checker family and its import/registration before generating the registry. Reproduce each affected driver twice, record its manifest and replay the full suite.
5. Run the same `just check-all`. It builds every registered SDK pair, checks module ownership and ordinary Lean loading, and checks complete witness/source coverage. Because the package surface changed, also test a fresh root Git consumer following [package consumption](../packages/solanalib-specs/README.md#package-consumption), and check that each new library resolves through plain `lake env lean`.

No registry entry, capability bundle, successful scenario or finite replay establishes a Rust-body proof. Keep the [model standard](model-standard.md), [binding obligations](../packages/solanalib-specs/BINDINGS.md) and [gap index](model-gaps.md) accurate as the modeled surface grows.
