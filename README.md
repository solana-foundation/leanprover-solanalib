<div align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-dark.png">
    <source media="(prefers-color-scheme: light)" srcset="https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-light.png">
    <img alt="Solanalib: Lean toolbox for Solana" width="100%" src="https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-light.png">
  </picture>
</div>

<p align="center">
  <a href="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/ci.yml"><img alt="CI" src="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/ci.yml/badge.svg"></a>
  <a href="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/docs.yml"><img alt="Docs" src="https://github.com/solana-foundation/leanprover-solanalib/actions/workflows/docs.yml/badge.svg"></a>
  <a href="LICENSE"><img alt="License: Apache-2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue"></a>
</p>

**Solanalib is a [Lean 4](https://lean-lang.org/) library that models the Solana runtime and the Rust crates Solana programs are built on, so you can state and prove properties of a program without modeling Solana yourself.**

To prove anything about a Solana program you first need a precise account of what surrounds it: what an account is, when the runtime rejects a write, what a cross-program invocation does to the caller, what `spl-token` or Anchor returns for a given input. Solanalib is that account, written once, tested against the real implementations and shared. It aims to be for Solana what [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) is for mathematics.

Status: **experimental.** The models are usable today; names and module layout may still change, so depend on a fixed commit.

📚 **Generated docs:** <https://solana-foundation.github.io/leanprover-solanalib/>

---

## How it helps you

| If you are | Solanalib gives you |
| --- | --- |
| **Verifying a program** as a developer or auditor | Runtime types and checks to state your invariants against, and contracts for the SDK calls your program makes. You write the proof about your logic; the definitions of accounts, rent, signers, CPI and token operations are already there. |
| **Building a verification tool** or an AI proving agent | A shared target. Rust translated to Lean calls into `anchor-lang`, `pinocchio` or `spl-token`; Solanalib supplies a contract for each of those calls, so your tool does not ship its own model of the ecosystem. |
| **Studying the runtime** | A readable, executable definition of transaction processing that follows Agave 4.3.2, with source notes that tie each module to the Rust it describes. |

## What is in it

Everything lives in one Lake package, `solanalib`, on Lean 4.34.0 with the matching Mathlib. Import only the libraries you need.

### `Solanalib.Runtime`: the Solana runtime

A model of transaction execution that follows [Agave 4.3.2](https://github.com/anza-xyz/agave/tree/a203300045b405f86c9c84308b2eae76af69ac3b): accounts and rent, transaction admission and fees, durable nonces, instruction execution, cross-program invocation, syscalls, program-derived addresses, sysvars, the program cache, and commit and rollback. It also supplies the `Pubkey`, `Account` and instruction types used by every other library here. See the [runtime guide](packages/solanalib-runtime/README.md).

Theorems come with the model. For example, [`transfer_preserves_total`](packages/solanalib-runtime/Solanalib/Runtime/Transfer.lean) proves that every successful System transfer keeps the total lamports of the transaction unchanged, including when account indices alias.

### `Solanalib.Specs.<Crate>`: 53 Rust crates

Contracts for functions of the crates programs depend on. A contract relates the inputs and initial state of a function to its possible outcomes, including errors and panics.

| Area | Crates |
| --- | --- |
| Frameworks | `anchor-lang`, `anchor-lang-error`, `anchor-spl`, `pinocchio` and its `system`, `token`, `token-2022`, `associated-token-account` and `log` companions |
| Tokens | `spl-token`, `spl-token-2022`, their interface crates, associated token account, token metadata, transfer hook, `spl-memo`, `spl-pod` |
| Serialization | `borsh`, `bytemuck` |
| Oracles | `pyth-solana-receiver-sdk`, `pythnet-sdk`, `switchboard-on-demand` |
| Solana SDK | 29 `solana-*` crates, including `solana-program`, `solana-account-info`, `solana-cpi`, `solana-instruction`, `solana-pubkey`, `solana-sysvar`, `solana-system-interface` and `solana-stake-interface` |

Each crate root covers a listed subset of its crate, not every function. The [library catalog](packages/solanalib-specs/LIBRARIES.md) names the modeled functions, and [version compatibility](packages/solanalib-specs/VERSION_COMPATIBILITY.md) records the releases each contract was reviewed against.

### `Solanalib.Contracts`: the contract vocabulary

The library-neutral definitions the crate models are written in: preconditions, outcomes, callbacks, capabilities and versioning. Use it to write contracts for crates that are not covered yet. See the [contracts guide](packages/solanalib-contracts/README.md).

## A first proof

The [worked example](examples/SolanalibTest/Examples/CheckedTransfer.lean) connects an SDK contract to runtime execution. Take any instruction that satisfies the `solana-system-interface` transfer contract for seven lamports. Running the System program of the runtime on it succeeds, debits and credits the right accounts, and conserves lamports:

```lean
theorem checked_transfer (prims : Prims) (instruction : CpiInstruction)
    (constructed : transfer_contract.ensures () args instruction ()) :
    systemProcess mainnet prims before (frameOf instruction) = some (.ok after) ∧
    (after.acct 0).lamports = 93 ∧ (after.acct 1).lamports = 27 ∧
    after.lamportSum = before.lamportSum
```

A second theorem removes the signer flag and proves that the runtime answers `MissingRequiredSignature`. Both proofs are checked by the Lean kernel, and CI builds the file with warnings as errors. The [getting-started guide](docs/getting-started.md) walks through it line by line.

## Use it in your project

Add the package to your `lakefile.lean` at a fixed commit:

```lean
require solanalib from git
  "https://github.com/solana-foundation/leanprover-solanalib" @ "<commit>"
```

Then import what you need:

```lean
import Solanalib.Runtime
import Solanalib.Contracts
import Solanalib.Specs.PinocchioToken
```

## What the models are checked against

A model is only useful if it matches the code it describes. Each one comes with evidence you can rerun:

- **Recorded native results.** The runtime model replays 79 cases recorded from native Agave. The crate models replay 12,276 records from the real Rust crates, with 2,673 negative controls that must fail.
- **Scenario tests.** Fourteen runtime scenarios and a scenario library for each crate, all built with warnings as errors.
- **Source notes.** Every model module is tied to the pinned Rust source it was reviewed against, by file hash and line anchor.
- **Axiom audit.** The runtime and crate model proofs depend only on `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`.

The boundary is stated plainly. The contracts are mathematical models of pinned releases. The evidence above supports their correspondence with the Rust code; it is not a proof about the Rust implementations or the compiled program. The runtime [trust boundary](packages/solanalib-runtime/TRUST.md) lists what the bank is assumed to supply, [BINDINGS.md](packages/solanalib-specs/BINDINGS.md) lists what a binding to real Rust must establish, and the [gap index](docs/model-gaps.md) lists every known gap.

## Who uses it

- **[Harmonic](https://harmonic.fun)** contributed the runtime and library models and uses Solanalib under the hood to verify Solana programs.
- **[Lusterna](https://lusterna.sh)**, by Certora, has AI agents translate Rust to Lean 4 and prove properties that the Lean kernel checks. It uses Solanalib under the hood for Solana programs.

## Build and check

Install [`elan`](https://github.com/leanprover/elan), [`just`](https://github.com/casey/just) and [`uv`](https://docs.astral.sh/uv/getting-started/installation/), then run from the repository root:

```sh
just setup             # fetch committed dependencies, Mathlib cache and Python tools
just build             # runtime and contract libraries
just test-examples     # the worked example, with warnings as errors
just test-runtime      # runtime scenarios and offline controls
just test-specs        # contracts and every crate library
just test-conformance  # replay both native recordings with negative controls
just audit             # proof, source, generator, ownership and loading checks
just docs              # the documentation site
just check-all         # every suite above
```

The [test index](docs/tests.md) lists every scenario and checker, and the [CI guide](docs/ci.md) describes the jobs that run on pull requests. Use `just --list` for all targets.

## Contributing

Missing a crate or a function? [Extending Solanalib](docs/extending.md) walks through adding a runtime rule or an SDK contract with its tests and native evidence. Read [CONTRIBUTING.md](CONTRIBUTING.md) for model boundaries, source review, style and signed commits, and the [model standard](docs/model-standard.md) for what a model must record.

## License

Apache-2.0. See [`LICENSE`](LICENSE).

---

<p align="center">
  <a href="https://solana-foundation.github.io/leanprover-solanalib/">Docs</a> ·
  <a href="docs/getting-started.md">Getting started</a> ·
  <a href="packages/solanalib-specs/LIBRARIES.md">Library catalog</a> ·
  <a href="https://harmonic.fun">Harmonic</a> ·
  <a href="https://lusterna.sh">Lusterna</a> ·
  <a href="https://lean-lang.org/">Lean</a> ·
  <a href="https://solana.org">Solana Foundation</a>
</p>
