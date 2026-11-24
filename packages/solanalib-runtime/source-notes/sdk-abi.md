# SDK interfaces used by the model

This analysis concerns the library state and entrypoint observations represented
by the current model. Runtime admission, privileges and synchronization use the
[Agave 4.3.2 argument](agave-4.3.2.md). That review defines the scope of the runtime behavior described here.

## Selected interfaces

| Interface | Exact source | Modeled connection |
| --- | --- | --- |
| Stored account | [solana-account 4.5.0][account] | Balance, data, owner, executable flag and rent epoch |
| Message authority | [solana-message 4.5.0][message] and [loaded messages][message-loaded] | Signer/writable header interpretation, loaded-key segments and program demotion |
| Account view | [solana-account-view 2.0.0][account-view] | Entry metadata, direct balance/owner observation and data lease convention |
| Entrypoint | [Pinocchio 0.11.1][sdk-entrypoint] | Initial account views and duplicate account references |
| Safe resizing | [Pinocchio 0.11.1 resize implementation][sdk-account-resize] | Authenticated entry-length bound, absence of existing leases and zero-fill behavior |
| SDK account interface | [solana-account-info 3.1.1][sdk-account-info] | A separate balance/data access interface; not a complete interpretation supplied by StoreOps |

The runtime dependency versions are selected by the pinned Agave lockfile.
AccountView, AccountInfo and Pinocchio are explicitly selected interface versions;
they are not asserted to be runtime dependencies merely because the source map
records them. Source files, crate VCS metadata and immutable archives were
checked. The source map retains their exact revisions and SHA-256 values.

## Account state and operations

`Cell` contains abstract account observations, entry length and lease state;
`Store` assigns cells to account identities. A binding must show that identities
refer to the actual account locations, duplicates preserve their aliases, and
entry lengths come from the original input metadata. Constructing a cell with
particular metadata does not establish instruction authority.

For the selected AccountView interface, the data lease byte is 255 when free,
zero when exclusive, and `255 - shared_count` for shared access. Thus at most
254 shared holders are representable. `Lease.addShared`, `Lease.release` and
`leaseStep` use those limits on reachable lease states. Their mathematical
results do not establish that an arbitrary starting lease count is reachable.

`stepInPlace` represents local balance/owner changes and data operations.
Source AccountView setters update their existing fields; the runtime checks
those changes only at the relevant synchronization point. In particular,
`setLamports` at this interface does not grant permission to debit a foreign
account or write a read-only account. Those conditions belong to
[the runtime setters](agave-4.3.2.md#account-mutation).

Resize in the store factors an exclusive data update, length change and zero
fill into an abstract operation. The safe source method checks that no lease
already exists. Relating the abstract factorization to a source call requires
an appropriate entry/exit lease interpretation and the same original length.
The bound is 10 KiB of growth beyond entry, as well as the subsequent runtime
account and transaction limits.

AccountInfo 3.1.1 has separately checked balance and data accessors. A single
data-lease state and a direct balance write do not describe every operation of
that interface. No generic equivalence of these SDK interfaces follows from
the library store definitions.

## Partial observations

`PartialCell`, `Completes` and `PartialCell.ofCell` formalize observations that
remain available during an exclusive lease. Hidden data need not be empty.
The corresponding lemma permits hidden bytes to vary only at the preserved
length. Owner, balance, metadata and alias interpretation remain constrained
by the actual statement.

`initialStore` derives the initial observations from the runtime entry state.
Its source connection requires the admitted input layout and authenticated
account identities described in
[serialization and read-back](agave-4.3.2.md#serialization-and-read-back).
The mathematical derivation does not decode arbitrary source memory.

## Conditional copy-back theorem

`releaseCopy` and `stepCopyBack` define an alternative mathematical store.
No selected SDK method implements delayed copying. `copyBack_step` proves
agreement of the two stores under `CopyRel` and `WellBracketed`; `copyBack_run`
requires `CopyRel` and `WellBracketedRun`. These conditions prevent observation
of an account while its exclusive data view is hidden. Applying the theorem
to a program requires that condition at every
runtime observation, together with a trace interpretation and preserved aliases.
It does not prove equivalence of the L, S and D runtime configurations.

## Invocation bindings

The model operates on values and abstract stores. A source binding must establish
the actual entry layout, account identity, admitted memory accesses, request
encoding and output writes. The runtime uses its saved privileges, regardless
of edited visible header flags. CPI updates and shared output locations require
the explicit observation argument in [the CPI analysis](agave-4.3.2.md#cpi).
These premises belong to the source connection; model theorems do not silently
discharge them.

[account]: https://github.com/anza-xyz/solana-sdk/blob/a541f77a1d482fdbcf420084d27fac42880d78bf/account/src/lib.rs#L61
[message]: https://github.com/anza-xyz/solana-sdk/blob/cd508efc69f65c3900d60a2f4c65212a037f4e98/message/src/legacy.rs#L571
[message-loaded]: https://github.com/anza-xyz/solana-sdk/blob/cd508efc69f65c3900d60a2f4c65212a037f4e98/message/src/versions/v0/loaded.rs#L160
[account-view]: https://github.com/anza-xyz/solana-sdk/blob/1666707490c6c29e6e2edf69e2122b7cae3c9dbb/account-view/src/lib.rs#L180
[sdk-entrypoint]: https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/entrypoint/mod.rs#L307
[sdk-account-info]: https://github.com/anza-xyz/solana-sdk/blob/9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23/account-info/src/lib.rs#L28
[sdk-account-resize]: https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/lib.rs#L457
