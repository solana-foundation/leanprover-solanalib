# Runtime source analysis index

The current argument is [Agave 4.3.2 source correspondence](agave-4.3.2.md).
It records the actual functions re-read at commit
`a203300045b405f86c9c84308b2eae76af69ac3b`, the selected profile,
the comparison conditions and known differences.

| Area | Current analysis |
| --- | --- |
| Feature configuration and machine limits | [Profile and limits](agave-4.3.2.md#profile-and-limits) |
| Stored accounts and the implemented rent transition | [Accounts and rent](agave-4.3.2.md#accounts-and-rent) |
| Setter ordering and touch metadata | [Account mutation](agave-4.3.2.md#account-mutation) |
| Bank inputs, fees and loading | [Admission and loading](agave-4.3.2.md#transaction-admission-and-loading) |
| Selected nonce, validation and computed advance | [Nonce admission](agave-4.3.2.md#nonce-admission) |
| Invocation, final checks, saving and rollback | [Execution and commit](agave-4.3.2.md#execution-and-commit) |
| Loader effects, nested cache visibility and successful cache commit | [Transaction-local program cache](agave-4.3.2.md#transaction-local-program-cache) |
| Message authority and instruction metadata | [Message privileges](agave-4.3.2.md#message-privileges-and-instructions-sysvar) |
| Both input ABIs and ordered synchronization | [Serialization and read-back](agave-4.3.2.md#serialization-and-read-back) |
| Represented memory and additional configurations | [Memory](agave-4.3.2.md#memory) |
| CPI preparation, synchronization and error order | [CPI](agave-4.3.2.md#cpi) |
| Runtime services and primitive contracts | [Syscalls and primitives](agave-4.3.2.md#syscalls-and-primitives) |
| Interpreted and opaque System instructions | [System instructions](agave-4.3.2.md#system-instructions) |
| Model state interfaces and proved consequences | [Library state and derived proofs](agave-4.3.2.md#library-state-and-derived-proofs) |

The current argument uses the actual Agave 4.3.2 implementations and the 4.4.0 rent dependency.
Historical release selectors remain in the Lean model without extending the
scope of this current-source review to those releases.
