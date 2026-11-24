# Getting started

This guide is for a Lean user who knows Solana. You will build a small proof that connects an SDK instruction contract to the checked System transfer of the runtime. The [complete example](../examples/SolanalibTest/Examples/CheckedTransfer.lean) is a real Lean module. CI builds it with warnings treated as errors.

## Set up a checkout

Install [elan](https://github.com/leanprover/elan), [just](https://github.com/casey/just) and [uv](https://docs.astral.sh/uv/getting-started/installation/). You also need Git, a C compiler and an internet connection for the initial dependencies. Start at the root of a checkout containing this guide. Keep its `lean-toolchain` and `lake-manifest.json`: they select Lean 4.34.0 and matching dependency revisions.

```sh
just setup
just test-examples
```

Setup fetches the committed dependencies and the small Mathlib cache used by the root library. It also prepares Python 3.12 through uv. It does not run a dependency update. The first build downloads more than a warm build needs.

All libraries belong to one Lake package, `solanalib`, and share one build directory. The package includes Mathlib. Choose a library target for the work you need:

| Need | Import | Build target |
| --- | --- | --- |
| Accounts, runtime checks and execution | `Solanalib.Runtime` | `Solanalib.Runtime` |
| Contract and outcome vocabulary | `Solanalib.Contracts` | `Solanalib.Contracts` |
| System instruction constructors | `Solanalib.Specs.SolanaSystemInterface` | `Solanalib.Specs.SolanaSystemInterface` |
| Pinocchio token operations | `Solanalib.Specs.PinocchioToken` | `Solanalib.Specs.PinocchioToken` |
| The sBPF machine model | `Solanalib` | `Solanalib` |

For example, build the System interface and its scenarios:

```sh
lake --wfail build Solanalib.Specs.SolanaSystemInterface SolanalibTest.Specs.SolanaSystemInterface
```

The [library catalog](../packages/solanalib-specs/LIBRARIES.md) describes each modeled subset. A crate root does not claim to model every function in that crate. For a separate project, use the [root Git dependency instructions](../packages/solanalib-specs/README.md#package-consumption) with an available immutable commit. Use the shared `Solanalib.Runtime.Pubkey`, `Account` and `CpiInstruction` types throughout. Runtime balances are `Nat` values; `Account.WF` supplies their `u64` bound, the account data limit and the rent-epoch bound.

## Follow the transfer proof

Open [CheckedTransfer.lean](../examples/SolanalibTest/Examples/CheckedTransfer.lean). Its imports select the runtime System processor and the SDK constructor contract directly:

```lean
public import Solanalib.Runtime.System
public import Solanalib.Specs.SolanaSystemInterface.Instruction
```

The file has four parts:

1. `args` requests a transfer of seven lamports between two distinct runtime public keys. `before` gives the sender 100 lamports, the recipient 20, and the System program its own account. `frameOf` resolves the keys of the instruction in that fixed account list and preserves its signer and writable flags.
2. `constructor_satisfies_contract` applies the existing `transfer_reference` theorem of the SDK. It proves that the mathematical constructor supplies a value satisfying `transfer_contract`; the example does not assume that the mathematical model meets its own contract.
3. `checked_transfer` accepts any instruction value satisfying that contract. The contract fixes its program ID, account order, flags and bytes. The proof then evaluates the actual runtime `systemProcess`, including `checkedSubLamports` and `checkedAddLamports`. The result has balances 93 and 27, both mutation markers, and the same total lamports as before. The theorem works for arbitrary `Prims`; this transfer does not call cryptographic providers.
4. `missing_signature_rejected` removes the signer flag of the sender and proves the actual `MissingRequiredSignature` result. A signature flag here is runtime input, not a proof that a cryptographic signature was verified.

The proof uses `cbv` and `decide`, which produce kernel-checked proofs. It does not use `native_decide`, an assumed successful runtime result or a Rust oracle. To check the exact file with ordinary Lean loading after the build:

```sh
lake env lean -DwarningAsError=true examples/SolanalibTest/Examples/CheckedTransfer.lean
```

`--wfail` applies to Lake builds; `-DwarningAsError=true` applies to this direct Lean invocation. A successful exit checks the statements and their proofs. There is no deployed program to run.

## Understand the boundary

This worked example proves one modeled instruction in a fixed account context. The general theorem [`Solanalib.Runtime.transfer_preserves_total`](../packages/solanalib-runtime/Solanalib/Runtime/Transfer.lean) separately proves conservation for every successful `sysTransfer`, including aliased transaction account indices. Its success premise includes the signature, data, ownership, writability, account-index and arithmetic checks. The [transfer scenarios](../packages/solanalib-runtime/SolanalibTest/Runtime/Transfer.lean) exercise that theorem and these rejection conditions; `just test-runtime` runs them. The SDK premise uses the **returned-value observation** contract. The separate [operational constructor family](../packages/solanalib-specs/Solanalib/Specs/SolanaSystemInterface/Operational.lean) also models allocation, serialization, cleanup and non-returning outcomes. The observation alone does not establish that a Rust constructor returns successfully.

The example does not cover transaction admission, fees, account loading, commit or rollback. It does not prove Rust bodies, compiler bindings, deployed sBPF execution or a general instruction-to-frame translation. See the runtime [trust boundary](../packages/solanalib-runtime/TRUST.md), SDK [binding obligations](../packages/solanalib-specs/BINDINGS.md), and [gap index](model-gaps.md). The existing [transaction success scenario](../packages/solanalib-runtime/SolanalibTest/Runtime/TransactionSuccess.lean) shows how the wider modeled transaction pipeline fits together.

For the next step, follow [Extending Solanalib](extending.md). The [test index](tests.md) links every scenario and checker, with the Just target that runs its suite.
