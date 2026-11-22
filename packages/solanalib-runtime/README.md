# Solana execution model

A Lean model of account state, memory visible to programs, runtime
checks and transaction commit. The `Solanalib.Runtime` library belongs to the root
`solanalib` package, which pins Lean 4.34.0 and Mathlib. Select this library with
`lake build Solanalib.Runtime`; downstream clients require the repository root.

The reference runtime is Agave 4.3.2. [TRUST.md](TRUST.md) records the selected
profile and external assumptions; [source notes](source-notes/README.md)
explain the correspondence with the runtime sources.

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
lake build Solanalib.Runtime SolanalibTest.Runtime
python3.12 -B -m unittest discover -s tools/runtime-conformance -p 'test_*.py'
python3.12 -B tools/runtime-conformance/run.py --model-only \
  --evidence-dir /tmp/solana-runtime-check
```

The [Agave suite](../../tools/runtime-conformance/README.md) checks account
operations, serialization/read-back and nonempty CPI calls against pinned native
results. Its guide gives the archive, toolchain and command to reproduce them.

The [scenario-test root](SolanalibTest/Runtime.lean) includes:

| Test | Behavior |
| --- | --- |
| [TransactionSuccess](SolanalibTest/Runtime/TransactionSuccess.lean) | Complete checked System transfer, including admission, fees, loading and commit. |
| [TransactionRollback](SolanalibTest/Runtime/TransactionRollback.lean) | A successful transfer followed by failure rolls back the transfer and retains the fee. |
| [CpiSuccess](SolanalibTest/Runtime/CpiSuccess.lean) | Caller synchronization, checked callee execution and a continuation observing the returned state. |
| [ProgramCache](SolanalibTest/Runtime/ProgramCache.lean) | Loader cache updates, visibility, close-then-invoke rejection and commit/rollback. |
| [NativeReturnData](SolanalibTest/Runtime/NativeReturnData.lean) | Native-builtin and SBF return-data size rules. |
| [ReadBackCoverage](SolanalibTest/Runtime/ReadBackCoverage.lean) | Data, owner and balance changes, duplicates and ABI variants. |
| [RuntimeBoundaries](SolanalibTest/Runtime/RuntimeBoundaries.lean) | Allocation limits, cumulative growth, shrink accounting and balance rejection. |

The `SolanalibTest.Runtime` target includes these tests. General
[flag-consistency lemmas](Solanalib/Runtime/FlagConsistency.lean) also relate message
and CPI frames to the runtime privilege checks.

## Source and proof audits

[source-map/sources.json](source-map/sources.json) connects the reviewed Lean hashes to the runtime source arguments. [source-map/modules.json](source-map/modules.json) describes every production module. Run the module, source-correspondence and proof-dependency audit from the repository root:

```sh
uv run --no-project --python 3.12 python tools/model-audit/check_runtime.py
```

The [source guide](source-map/README.md) explains how to check all upstream file bytes and line anchors as well. The audit distinguishes those byte checks from the manual semantic argument and the Lean proofs.
