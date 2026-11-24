# Contributing to Solanalib

Solanalib is only useful if people can trust what a model says and what it leaves out. Most of this guide follows from that: a model states exactly what it covers, every claim has evidence that can be rerun, and nothing is asserted that was not checked.

Start with [Getting started](docs/getting-started.md). When you are ready to add something, [Extending Solanalib](docs/extending.md) gives the file changes and commands in order for a runtime rule, a crate function and a new crate. This guide explains the rules those walkthroughs assume. The [model standard](docs/model-standard.md) defines claims and gap records in full.

Each rule below is marked **checked** when a script or the build rejects a violation, and **review** when a reviewer is expected to catch it.

## Where a change belongs

| You want to | Put it in | May import |
| --- | --- | --- |
| Model runtime behavior: accounts, checks, execution, CPI, transactions | `packages/solanalib-runtime`, namespace `Solanalib.Runtime` | Lean core and Std, the runtime itself |
| Extend the contract vocabulary | `packages/solanalib-contracts`, namespace `Solanalib.Contracts` | Lean core and Std |
| Model a function of a Rust crate | `packages/solanalib-specs`, namespace `Solanalib.Specs.<Crate>`; shared pieces in `Solanalib.Specs.Core` | Lean core and Std, runtime, contracts, the shared core and registered crate dependencies |
| Add a scenario test | The matching `SolanalibTest` tree of the same package | The above, plus the test roots of the same package |

- **Checked.** No library imports Mathlib. `just audit` runs the import-tier check.
- **Checked.** Everything is one Lake package, `solanalib`, with one build directory. Do not add a `lakefile` under `packages/` or `tools/`, and do not add Lean sources at the repository root. Every module has exactly one owning library.
- **Review.** Use the shared `Solanalib.Runtime` types for public keys, accounts and instructions. Do not define a second account or key type.
- **Review.** Compilers, program logics and proofs about a specific application belong in a separate repository that depends on this one.
- **Review.** [`packages/solanalib-sbpf`](packages/solanalib-sbpf/README.md) is an exploration with its own, looser rules. The rest of this guide is about the runtime, contract and crate packages.

## What a model may claim

These rules matter more than any style rule. A change that breaks one of them is not mergeable, however clean the Lean is.

| Do | Do not |
| --- | --- |
| Follow the pinned source. Check order, error order and state effects come from the Rust code at the recorded revision. | Change a definition, or the statement being proved, to make a proof go through. |
| Model unknown behavior as a parameter or a relation: `Prims` for hashes, `Program` for program behavior, `BankEnv` for bank inputs, profile fields for feature gates. | Introduce an `axiom`, or assume a successful result that the model should compute. |
| Keep CPI opaque at the invocation boundary. The effect of a callee comes from an explicit contract. | Treat a supplied callee outcome as a proof that the callee is correct. |
| Say what the model leaves out, in the docstring and in the gap record. | Describe an observation or supporting model as a complete operational model. |
| Record the exact release, target, features and dependencies a contract was reviewed against. | Imply that unlisted releases were inspected. SemVer is evidence, not proof. |
| Add a premise only when the result needs it. | Keep an unused premise, or add a trivial lemma only so that something mentions it. |
| Introduce a new, named contract when behavior differs between releases. | Weaken an existing contract so that it covers more releases. |

- **Checked.** Runtime, contract and crate proofs depend only on `propext`, `Classical.choice` and `Quot.sound`. `sorry` fails the build. `native_decide` fails the axiom audit. The audits cover every owned declaration, including private and generated ones.
- **Review.** A model proof plus a passing native replay supports correspondence with the Rust code. It is not a proof about the Rust implementation, and nothing in the repository should say that it is. Interpretation obligations go in [BINDINGS.md](packages/solanalib-specs/BINDINGS.md), runtime assumptions in [TRUST.md](packages/solanalib-runtime/TRUST.md).

## Lean code

### File layout

Every model file has the same shape. Copy it from a neighbor.

```lean
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.System

@[expose] public section

/-!
# Lamport conservation for System transfers

What the file models, which source it follows, and what stays outside.
-/

namespace Solanalib.Runtime

end Solanalib.Runtime
```

- **Checked.** The first six lines contain the copyright line, the Apache 2.0 line and `Authors: <Project> Contributors`. Keep the notice a file already has; use your own organization for a new file.
- **Checked.** The `/-! ... -/` module description comes after the imports.
- **Checked.** Lines are at most 100 characters, except lines with a URL. Write `fun`, not `λ`. Write `<|` or `|>`, not `$`. `autoImplicit` is off.
- **Review.** Write a module description for every new file: what is modeled, the source it follows, what is not covered, and a link to the source note.
- **Review.** Import the few modules a file needs. Production files in the runtime do not use `open`.

### Names

| Kind | Convention | Examples |
| --- | --- | --- |
| Types and propositions | `UpperCamelCase` | `TxState`, `SetterStep`, `NoCpi` |
| Well-formedness | Always `WF` in the namespace of the type | `Account.WF`, `BankEnv.WF` |
| Runtime definitions | `lowerCamelCase`, translating the Rust name | `set_lamports` becomes `setLamports` |
| Rust constants | Keep the Rust spelling | `U64_MAX`, `MAX_ACCOUNT_DATA_LEN` |
| Error constructors | Keep the Rust spelling and order | `.MissingRequiredSignature` |
| Theorems | `snake_case`, conclusion first, `_of_` before hypotheses | `acct_setAcct_ne`, `leNat_leBytes_of_lt` |
| Lemmas that build a structure | In the namespace of that structure | `SetterStep.of_setLamports`, `LamportFrame.trans` |
| Crate declarations | The Rust path as namespace, the Rust name in `snake_case`, then a role suffix | `Solanalib.Specs.SolanaHash.Hash.to_bytes_contract` |
| Shared core declarations | `lowerCamelCase` | `Core.Hash.toBytesContract` |

- **Review.** Name variables and hypotheses for what they are: `before`, `after`, `transferred`, `written`. Older runtime files use `ts`, `sc` and `h`; follow the file you are editing, and use descriptive names in new files.
- **Review.** Name a variant for its behavior, not its version: `log_modern_contract` and `log_legacy_program_contract`, not `log_v2_contract`. Version numbers belong in docstrings, the registry and Rust-named items.
- **Review.** Keep module roots and registry IDs stable and version-neutral. Renaming one breaks downstream developments and recorded evidence.

### Definitions

- Unsigned integers are `Nat`, and signed counters are `Int`. A `u64` bound is a clause of a `WF` predicate, used only by the results that need it. Do not model arithmetic with `UInt64`.
- A checked operation returns `Except` with the real error type, or `Option`. Write the checks as an `if ... then .error ... else if ...` chain in the order of the Rust code. That order is observable and tests depend on it.
- Write recursion by hand where a proof must unfold it, instead of `mapM` or `foldlM`.
- Derive `DecidableEq` and `Repr` on data types so that tests can close goals by evaluation.
- Mark a lemma `@[simp]` only when it is a normalization rule. Use `private` for helper lemmas that no other file should cite.
- In a crate file, prefer a thin `snake_case` facade over the shared core definition, as an `abbrev`, when the same behavior serves several crates.

Not used in the model packages, and not accepted without a strong reason stated in the pull request: `axiom`, `sorry`, `native_decide`, `opaque`, `partial`, `unsafe`, `noncomputable`, custom `macro` or `notation`, and the `grind` and `aesop` tactics.

### Proofs

- Prefer proofs that follow the definition: `unfold` the function, `split` on its checks, and close each branch, using `·` bullets. Finish arithmetic with `omega`.
- Prefer `simp only [...]` in the middle of a proof. A bare `simp` is acceptable as the closing step.
- Use term mode for short structural lemmas such as `refl` and `trans`.
- Scope options to one declaration with `set_option ... in`. Do not raise `maxHeartbeats` or `maxRecDepth` for a whole production file.

### Docstrings and comments

A docstring says which Rust item the declaration stands for and what it does not establish.

```lean
/-- `set_lamports`. A call on an account outside the transaction fails with
`MissingAccount`, as `try_borrow_instruction_account` does. `SetterStep.balance`
proves the invariant for mathematical integers; the correspondence with the
runtime `i128` counter also requires bounded account counts and `u64` balances. -/
```

- Give every definition, structure and inductive a docstring. Give a theorem one when its statement is a result someone will cite; short helper lemmas can go without.
- Name the Rust function. Put file and line anchors in the source note and the registry, where the audit checks them.
- State limits plainly: "does not establish", "remains an explicit contract", "leaves the invocation opaque".
- Write impersonal, declarative prose. No "we", no "simply" or "clearly", no praise of the result.
- Do not commit `TODO`, `FIXME` or commented-out code. An open obligation is a gap record, not a comment.

## Tests

Every model change comes with scenario tests in the same pull request.

- Write named theorems, not `example`, `#eval` or `#guard`. The name states the behavior: `misaligned_input_rejected`, `size_mismatch_rejected_before_alignment`, `empty_slice_alignment_checked`. Crate test names are registered as clients in the source registry.
- Cover a success, every distinct rejection, the order of two competing errors, and the numeric or length boundaries. Add a negative control that shows the contract rejects a wrong result, such as `contract_rejects_wrong_value`.
- Close goals by evaluation: `rfl`, `decide` or `cbv`. A test must not assume the result it checks.
- Make fixtures show what they test. Nonuniform bytes make byte order visible; distinct keys make aliasing visible.
- Say in the docstring what the witness does not prove, for example that it does not verify a signature or correspond to a deployed bank.
- End a larger scenario with an existence theorem so that the scenario is not vacuous.

## Registering the change

Lean code alone is not a complete contribution. The registries are what connect a declaration to its source and its evidence.

**Runtime.** Add the module to the root imports and to [modules.json](packages/solanalib-runtime/source-map/modules.json). Add it to a correspondence row in [sources.json](packages/solanalib-runtime/source-map/sources.json) with its declarations, source IDs, argument, assumptions and limitations. Update the [source note](packages/solanalib-runtime/source-notes/agave-4.3.2.md) when the argument changes.

**Crate function.** One function has a contract, a reference, and closed witnesses for reference correctness and satisfiability. A relational reference also needs a `HasExecution` witness. The usual names for a function `x` are `x_contract`, `x_run`, `x_reference`, `x_satisfiable`, `x_sample` and `x_has_execution`; a total function uses `x_model`. Generic APIs use `Family`: correctness covers every index, while satisfiability and execution name one explicit sample. Register the function in the [source registry](packages/solanalib-specs/source-map/README.md) with its exact Rust identity, the reviewed releases and the build conditions, and keep [LIBRARIES.md](packages/solanalib-specs/LIBRARIES.md) in step.

**Versions.** Compatibility is per function. Keep exact reviewed releases apart from assumed compatible ranges, keep known exceptions outside a range, and give prereleases explicit entries. A reexport keeps the identity of the crate that defines the item. An unknown build fact never becomes a match.

**Gaps.** Record a limitation where it is defined: the correspondence row for the runtime, `model_gaps` and `remaining_requirements` for a crate model, `not-tested.toml` or `requires-open.toml` for a missing native test. Do not remove a limitation because a finite test passed.

## Files you do not edit by hand

| File | Change it by | Checked by |
| --- | --- | --- |
| `Capabilities.lean` of each crate, `VERSION_COMPATIBILITY.md` | `just generate-specs` | `just check-generated` |
| Conformance `Registry.lean` and reference tables | `just generate-conformance` | `just check-generated` |
| `docs/model-gaps.md`, `docs/tests.md` | `just generate-indexes` | `just lint` |
| Native recordings and corpora | A fresh native run, then the adoption recipe in the [walkthroughs](docs/extending.md) | `just test-conformance` |

Reviewed files carry a hash seal. After you have reviewed an edited runtime module against its source, run `just refresh-runtime-seal <row>`; for a crate abstraction, `just refresh-sdk-seal <id>`; for gap inputs, `just refresh-gap-review`. A seal records that a review happened. Running the tool on code you did not review is the one thing in this guide that no check can catch, so do not do it.

Never edit a recording to make a model change pass. Commit generated Lean, the version guide and both indexes. Keep rendered documentation, downloaded archives and evidence directories out of Git.

## Prose

- For things, write "the setters of the runtime" or "runtime setters", not a possessive. Possessives of people and contractions are fine. **Checked** by `just lint` in Markdown, Lean comments and strings, Python and Rust comments, and registry text.
- Keep Markdown paragraphs on one line; do not hard-wrap them.
- State facts and their scope. Avoid adjectives that grade the work.

## Before you open a pull request

```sh
just setup
just check-all
```

`just check-all` builds every library with warnings as errors, runs all scenario tests, the source and axiom audits, both native replays with their negative controls, and the documentation build. While developing, use the narrower targets: `just test-runtime`, `just test-specs`, `just lint`, `just audit-runtime`. The [test index](docs/tests.md) lists every suite and the [CI guide](docs/ci.md) the jobs that run on a pull request.

- When a native driver, fixture or modeled source behavior changes, reproduce the native observations as well. The two suites pin different Rust compilers; see the [walkthroughs](docs/extending.md).
- When modules or dependencies change, also test a fresh Git consumer at the exact commit and plain `lake env lean` loading.
- On macOS, the Justfile needs an `nproc` command on the path, and some audit tests need a temporary directory that is not a symlink, for example `TMPDIR=/private/tmp`. CI runs on Linux.

## Commits and pull requests

- Sign your commits.
- Give the pull request a [Conventional Commits](https://www.conventionalcommits.org/) title such as `feat(runtime): model stake withdraw`; it becomes the commit on `main`.
- Do not add assistant or model attribution, or co-author trailers for tools, to commits or pull request descriptions.
- Keep one concern per pull request. A model change, its tests, its registry entries and its regenerated files travel together.

The description says:

1. Which behavior changed, and which source and build profiles it affects.
2. Which evidence was refreshed: seals, generated files, recordings.
3. What you ran and what passed. Report selected and omitted replay observations separately.
4. What remains open, with a link to the gap record.

Do not claim more than the checks show. "Replayed the committed recording" and "reproduced natively" are different statements, and so are "reviewed against 3.2.0" and "compatible with 3.x".
