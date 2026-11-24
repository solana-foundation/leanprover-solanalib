# Solana execution model

A Lean model of account state, memory visible to programs, runtime
checks and transaction commit. The `Solanalib.Runtime` library belongs to the root
`solanalib` package, which pins Lean 4.34.0 and Mathlib. Select this library with
`lake build Solanalib.Runtime`; downstream clients require the repository root.

The reference runtime is Agave 4.3.2. [TRUST.md](TRUST.md) records the selected
profile and external assumptions; [source notes](source-notes/README.md)
explain the correspondence with the runtime sources.

The [model and test standard](../../docs/model-standard.md) explains how to document source correspondence, test runtime changes and record open obligations. The [gap index](../../docs/model-gaps.md) follows the source-correspondence records.

## Use the model

Import `Solanalib.Runtime`, or a specific module such as `Solanalib.Runtime.Transaction`,
`Solanalib.Runtime.Memory` or `Solanalib.Runtime.AccountState`.
SDK contracts use these definitions alongside the library-neutral contract vocabulary. A separate binding to the Rust implementation must establish execution and memory correspondence.

A syscall here takes and returns mathematical values. Program-memory reads and
writes belong to that separate interpretation.

## Memory configurations and account operations

`MemConfig` has three choices. `L` represents one writable input buffer, with account data copied in and checked at read-back. `S` gives each account a separate data region whose length tracks the account data length. `D` maps those regions directly to transaction-account storage, so a store changes the account immediately. The selected Agave source argument uses `L`; the [memory analysis](source-notes/agave-4.3.2.md#memory) records the remaining correspondence obligations for `S` and `D`.

`Solanalib.Runtime.StoreOps` defines in-place operations over the abstract account store: reads, writes and borrow-state transitions. These operations model library-visible state; a Rust binding must justify the concrete representation and legal memory accesses.

## Tests

From the repository root:

```sh
just test-runtime
just test-conformance
```

The [Agave suite](../../tools/runtime-conformance/README.md) checks account
operations, serialization/read-back and nonempty CPI calls against pinned native
results. Its guide gives the archive, toolchain and command to reproduce them.

The [scenario-test root](SolanalibTest/Runtime.lean) includes all fourteen files:

| Test | Behavior |
| --- | --- |
| [Examples](SolanalibTest/Runtime/Examples.lean) | Evaluated examples of runtime definitions and checked operations. |
| [Regression](SolanalibTest/Runtime/Regression.lean) | Borrow limits, resize error order, touched accounts and no-ops, nonce handling and transaction storage regressions. |
| [Transfer](SolanalibTest/Runtime/Transfer.lean) | System transfer conservation, zero and draining transfers, aliased accounts, and the signature, data, ownership, writability, index and arithmetic rejections. |
| [TransactionSuccess](SolanalibTest/Runtime/TransactionSuccess.lean) | Complete checked System transfer, including admission, fees, loading and commit. |
| [TransactionRollback](SolanalibTest/Runtime/TransactionRollback.lean) | A successful transfer followed by failure rolls back the transfer and retains the fee. |
| [CpiSuccess](SolanalibTest/Runtime/CpiSuccess.lean) | Caller synchronization, checked callee execution and a continuation observing the returned state. |
| [ProgramCache](SolanalibTest/Runtime/ProgramCache.lean) | Loader cache updates, visibility, close-then-invoke rejection and commit/rollback. |
| [NativeReturnData](SolanalibTest/Runtime/NativeReturnData.lean) | Native-builtin and SBF return-data size rules. |
| [ReadBackCoverage](SolanalibTest/Runtime/ReadBackCoverage.lean) | Data, owner and balance changes, duplicates and ABI variants. |
| [RuntimeBoundaries](SolanalibTest/Runtime/RuntimeBoundaries.lean) | Allocation limits, cumulative growth, shrink accounting and balance rejection. |
| [CpiOrdering](SolanalibTest/Runtime/CpiOrdering.lean) | Account lookup, duplicate merging, caller privileges and callee lookup preserve their error order before invocation. |
| [NonceAdmission](SolanalibTest/Runtime/NonceAdmission.lean) | Pre-fee nonce checks, authority and writability, static indices, forged-record rejection and rollback. |
| [SerializationAccounts](SolanalibTest/Runtime/SerializationAccounts.lean) | The 255/256 account-reference boundary precedes ABI selection and stays distinct from the CPI account-count limit. |
| [SiblingOutputs](SolanalibTest/Runtime/SiblingOutputs.lean) | Sibling header sizes, output overlap, zero-length buffers and related return-data/memory-copy boundaries. |

The `SolanalibTest.Runtime` target includes these tests. General
[flag-consistency lemmas](Solanalib/Runtime/FlagConsistency.lean) also relate message
and CPI frames to the runtime privilege checks.

The [complete test index](../../docs/tests.md) also links every root/SDK scenario and conformance checker. The [getting-started example](../../docs/getting-started.md) connects an SDK constructor contract to checked runtime execution; the [runtime extension walkthrough](../../docs/extending.md#runtime-walkthrough) covers model, source, fixture and gap updates together.

## Source and proof audits

[source-map/sources.json](source-map/sources.json) connects the reviewed Lean hashes to the runtime source arguments. [source-map/modules.json](source-map/modules.json) describes every production module. Run the module, source-correspondence and proof-dependency audit from the repository root:

```sh
just audit-runtime
```

The [source guide](source-map/README.md) explains how to check all upstream file bytes and line anchors as well. The audit distinguishes those byte checks from the manual semantic argument and the Lean proofs.
