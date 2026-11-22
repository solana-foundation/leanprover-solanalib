# Runtime definition and trust boundary

`Solanalib.Runtime` is the authoritative runtime definition used by this development.
Its reference is [Agave 4.3.2](https://github.com/anza-xyz/agave/tree/a203300045b405f86c9c84308b2eae76af69ac3b).
The [source analysis](source-notes/agave-4.3.2.md) identifies the checked runtime
functions, the conditions of the comparison and the release-sensitive rules.
Every model module is associated with that argument and its exact reviewed hash
in [the source map](source-map/sources.json). Hash and reference checks detect
stale evidence; they are not a semantic refinement proof.

The mainnet profile fixes the feature state and rent parameters. The observed
rent multiplier is 5,080 lamports per byte with exemption threshold 1.0; the
minimum is `(128 + data_length) * 5080`. This value is a profile parameter,
shared by runtime checks and their clients. A history spanning a change of
profile is a separate modeling obligation.

The profile excludes the inactive NoOp fee-payer feature. The modular
exponentiation syscall is also inactive in this profile; its enabled behavior
and primitive interface are selected by release. Unknown or unsupported profile
combinations are not additional claims about mainnet behavior.

Nonce admission is checked before fee-payer validation. A transaction supplies
the bank-selected nonce index; the model checks its selection, address, stored
current state, authority, blockhash and ability to advance. It computes the
advanced account from the stored account and the bank context. No transaction
can supply an arbitrary advanced account. An admission failure leaves the bank
unchanged and charges no fee.

System nonce instructions execute as opaque builtins through `Havoc`, which
permits a successful return without changing any account. The advanced account
computed during admission is used by `commitRollback` for fees-only outcomes and
execution failures after nonce and fee-payer validation. Execution starts from
the stored nonce data, and `commitSuccess` does not require nonce advancement.
A successful durable-nonce transaction therefore has no nonce-advancement
guarantee in this model. Reasoning about that effect requires a separate
contract for System nonce execution and any later instructions that modify the
nonce account. Admission and fee-payer rejections commit no nonce advancement.

The bank still supplies its actual recent-blockhash queue decision, fee and
limits, signature and status-cache checks, stored accounts and program-cache
state at entry. Their correspondence with execution is a boundary assumption. The
well-formedness predicates in Lean are partial: the source analysis also states
the required header, index, integer, rent and loaded-data conditions. They must
not be inferred merely from construction of a model record.

Transaction-local program-cache changes are explicit in `TxState.modifiedPrograms`
and flow through instructions and CPI. Successful loader-v3 ProgramData closure
writes `Closed`; deployment, upgrade and extension write `Unloaded` with the
execution Clock slot. These entries override the initial cache and reject
invocation in the current batch. Loader authority, funding, account effects and
code verification remain opaque source contracts. The cache classification and
its mandatory write do not prove those success conditions.

`ProcTxWithCache` returns account effects and cache changes from the same execution.
It exports changes only after complete transaction success; every other outcome
retains the initial cache. `ProcTx` is its proved existential projection, which
forgets the cache result. `BankEnv.withCommittedPrograms` supplies the resulting
dispatch view for subsequent transactions in the batch. The Clock and cache slots
must agree with the actual execution context; the dated snapshot of the profile is
not that clock. A fresh batch or bank cache load requires a new binding to its
actual entries and executable code, beyond this dispatch projection.

Opaque native builtins may set return data directly with an explicit program tag
and no instruction accounts. The native API has no 1,024-byte limit; that limit
belongs to the SBF syscall. The native capability witness uses a hypothetical
registered builtin and does not claim a current mainnet builtin exercises it.

Cryptographic functions are symbolic parameters. The digest widths of the four
hash syscalls are laws of `Prims`; other interface conditions, and security
assumptions used by applications, remain explicit.
Proofs do not evaluate a concrete hashing algorithm. Executable tests may supply
concrete primitive implementations for concrete inputs.

External programs supply their own behavioral contracts. The runtime defines
invocation preparation, account synchronization, checks, saving and rollback.
A contract about a callee effect does not establish that a deployed callee
implementation satisfies it. Source memory and argument bindings are checked
separately from these external effects.

Lean checks the stated mathematical results. Correspondence of the runtime
definition with Agave is justified by the versioned source analysis; this
development does not contain a refinement proof of the complete validator
implementation. Using a model to reason about a program requires the additional execution and
representation assumptions for that program.
