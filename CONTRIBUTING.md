# Contributing to Solanalib

Start with [Getting started](docs/getting-started.md), then follow the relevant [extension walkthrough](docs/extending.md). Downstream developments should pin an immutable repository revision.

## Choose the right layer

Use the shared `Solanalib.Runtime` public-key, account and instruction types for Solana developments. Account balances remain `Nat` values with the `u64` bound in `Account.WF`. The root library also holds lamport and time notations, numeric and finance models, sBPF, and the [System transfer conservation theorem](Solanalib/Transfer.lean). The shared `Solanalib.Contracts.Model` vocabulary is the one contract type; `Solanalib.Specs.Core` reexports it and adds Solana-specific models.

All libraries belong to the root `solanalib` Lake package. Keep them separately selectable, with one module owner and one shared artifact directory. Runtime source imports stay within the runtime and Lean libraries. SDK source imports use contracts, runtime, shared SDK models, Lean core and Std. The Mathlib dependency of the package does not widen those source boundaries. Compiler, program-logic and application dependencies belong outside these model layers. A separate binding to the Rust implementation must discharge source selection, memory representation and execution correspondence obligations.

## Write and register a model

- Organize source-facing declarations by library and Rust item. Use the `_contract` suffix, for example `Solanalib.Specs.SolanaDefineSyscall.definitions.sol_sha512_contract`. Keep new module roots and stable IDs version-neutral.
- Register one contract for every reviewed release with the same behavior, through applicability profiles and `Catalog.forBuild`. Introduce a distinct contract when behavior differs.
- The [SDK registry](packages/solanalib-specs/source-map/README.md) defines the modeled subset, roles, declarations, witnesses, Rust identities and source/build conditions. Keep [LIBRARIES.md](packages/solanalib-specs/LIBRARIES.md) consistent with that subset. Runtime changes update the [source-correspondence registry](packages/solanalib-runtime/source-map/sources.json) and its source argument.
- Register a new module in its root imports, Lake ownership, import policy and source audit. Put SDK production modules under `Solanalib.Specs.<Crate>` and scenarios under `SolanalibTest.Specs.<Crate>`.
- Every registered contract needs closed reference-correctness and precondition-satisfiability witnesses, without external term or universe parameters. A relation-based reference also needs a closed `HasExecution` witness for that exact contract and reference.
- Generic APIs use `Family`. Correctness covers every index; satisfiability and execution name one explicit sample. The audit checks exact family, reference and sample identities. A separately named family must match a parameterized contract at every index; register the contract too.
- Preserve lifecycle, callback effects, error order and composition. Every premise must support a substantive result. Do not change the code or definitions being verified to make a proof succeed.
- Record interpretation obligations in [BINDINGS.md](packages/solanalib-specs/BINDINGS.md), source details in its source note, and limitations in the authoritative gap fields. Model proofs and differential observations do not prove Rust bodies. CPI stays opaque at its actual signature; supplied outcomes do not prove the callee correct.
- Use small, self-contained library or runtime examples. Justify models with the pinned library sources, mathematical proofs and conformance tests.

## Preserve source and version meaning

- Compatibility is per function. Distinguish exact reviewed releases from explicitly assumed compatible ranges. SemVer is evidence, not a proof of every modeled observable.
- Record immutable archives or Git revisions, actual defining Rust identities, target, features, dependencies and other behavior-changing build conditions. Reexports retain the identity of their resolved provider. Unknown required build facts cannot become eligible matches.
- Keep known exceptions outside the corresponding range. Profiles without ranges and exact Git sources remain exact; prereleases need explicit reviewed entries. Never weaken a contract to enlarge coverage or imply that unlisted releases were inspected or tested.
- Keep the recorded Lean, native compiler and dependency pins; deliberate version changes need their own review. Error-construction allocation failure retains the common boundary in `BINDINGS.md`.
- Generate capability catalogs, applicability data, version tables and complete-contract equality controls from the source registry. Preserve family indices and model roles. A capability bundle adds no model coverage or Rust correctness.
- Use exact `rust_names` matching the selected Rust item and implementation, including the defining crate/version. The [identity guide](packages/solanalib-specs/source-map/README.md#rust-identities) explains the exact Rust item and implementation paths.
- Clients request explicit propositional assumptions on their chosen capability subset under one fixed operation assignment. Preserve members without source-call registration. A verification tool that binds these contracts to Rust code must supply the source-call contracts and a shared execution representation.
- A reviewed-module edit needs renewed source review and matching hashes. The [extension tools](docs/extending.md) refresh only the selected seals; running a tool does not review uninspected code.

## Lean style and file ownership

Use a copyright comment, imports, then a `/-! ... -/` module description, in that order. Use descriptive declaration names, spaces around infix operators except exponentiation, and lines of at most 100 characters in Lean. Keep new Markdown prose unwrapped. The [Lean style guide](skills/lean-best-practices/SKILL.md) has the file template, numeric proofs and common elaboration mistakes; the checked-in toolchain and current contribution rules govern this repository.

For inanimate subjects, express possession with an `of` phrase or a noun modifier, such as “the setters of the runtime” or “runtime setters”. Keep possessives of people and contractions. `just lint` checks Markdown prose and fenced comments, Lean comments and message strings, Python comments and message strings, Rust comments, and explanatory registry fields. It preserves code identifiers, quoted source, literal test fixtures, recorded data and unchanged upstream text.

For simple `Nat` or `Int` aliases, the existing style prefers notation where it makes arithmetic tactics straightforward. Bridge bounded integers through `.toNat` when proving conservation properties. Use bundled structures for domain shapes with concrete parameters. Add useful extensionality and projection lemmas; mark only normalization rules with `@[simp]`. Import the narrow modules needed by a proof.

Preserve existing notices. Solana Foundation files use `Copyright (c) <YEAR> Solana Foundation. All rights reserved.`, the Apache-2.0 license line, and `Authors: Solanalib Contributors`. Harmonic-authored files use `Copyright (c) 2026 Harmonic. All rights reserved.` with the same license and Authors lines. Do not add assistant/model attribution or co-author trailers to commits or PR descriptions. Sign commits and describe the change and its purpose.

## Validate and explain the change

The [test index](docs/tests.md) lists every scenario, checker, Python control suite and native driver. The [model standard](docs/model-standard.md) defines claims and gap records; the [walkthroughs](docs/extending.md) give the file changes and commands in order. Run focused checks while developing and the regular local suites before review:

```sh
just check-all
```

This builds all libraries and the tutorial, runs root/runtime/SDK scenarios, source and complete axiom audits, Python and compiled controls, both authenticated recording replays and production documentation. Fresh native reproduction is separate and required when a driver or fixture changes; its two suites have different pinned Rust compilers. The [CI guide](docs/ci.md) lists the workflow jobs and their scope.

A review should say which behavior and source/build profiles changed, which evidence was refreshed, what passed and what remains open. Report selected and omitted replay observations separately. Commit generated Lean, the version guide and the test/gap indexes; `just check-generated` checks them. Keep rendered documentation, machine applicability exports, downloaded archives and transient receipts out of Git. For a new primitive in the existing root library, update its root aggregator and explicit Lake globs, add a mirrored scenario and update that test aggregator. For runtime and SDK additions, follow the fuller registration paths in the walkthroughs.

For module or dependency changes, also test a fresh Git consumer at the exact commit, ordinary `lake env lean` and `Lean.importModules` loading, module ownership and documentation coverage.
