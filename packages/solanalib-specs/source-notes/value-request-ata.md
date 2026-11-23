# Associated Token Account 0.4.0 helper request

`CreateIdempotent::invoke` constructs a request for the ATA program address
`ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL` with the single data byte `[1]`.
The account order is funding, associated account, wallet, mint, System program,
Token program. Their `(signer, writable)` flags are `(1, 1)`, `(0, 1)`, followed
by four `(0, 0)` entries. The unsigned wrapper passes an empty signer list.

The model preserves caller-provided System and Token program addresses; it does
not validate or replace them. It also preserves duplicate account identities
and positions. The common canonical program address is the exact 32-byte base58
decoding of the declaration, not a shortened numeric identifier.

The local wrapper derives each metadata key from the current account pool and
calls the InstructionView 2.1.0 checked array entry with the same six handles.
The first two positions request writable access and reject live data leases;
the four readonly positions perform no borrow check in this revision. The
shared checked model retains address/check order, aliases and the actual
initialized descriptors. The two arrays have equal fixed size six and satisfy
the compile-time capacity bound.

The v2 descriptor copies the current raw flag bytes and header padding exactly.
These bytes are an explicit current-state observation alongside the account
pool. The model imposes no 0/1 restriction or zero-padding assumption.

Checked errors propagate unchanged before opaque invocation. The remaining
opaque boundary returns Unit: normal completion becomes `Ok(())`, while unwind
and terminal effects are preserved. A freely chosen ordinary invocation error
is not part of this source signature. The name does not imply account creation,
existing-account acceptance, authentication or rollback. The local fixed arrays
and borrowed references introduce no owned-vector or account-guard cleanup.

Reviewed pinned sources are
[src/lib.rs line 5](https://github.com/anza-xyz/pinocchio/blob/3a3a1a65984ffd0b6debe460276c0a6ebb685dcb/programs/associated-token-account/src/lib.rs#L5)
for the program address and
[create_idempotent.rs line 38](https://github.com/anza-xyz/pinocchio/blob/3a3a1a65984ffd0b6debe460276c0a6ebb685dcb/programs/associated-token-account/src/instructions/create_idempotent.rs#L38)
for the unsigned wrapper. Local signed preparation starts at 43 and stops at
the actual invocation call at 65. The wrapper source slice stops at that checked call. Shared checked-entry
semantics are documented in the [InstructionView note](value-request-instruction-view.md);
actual unchecked invocation bodies remain opaque. The pinned dependencies are InstructionView 2.1.0, AccountView 2.0.0
and Address 2.6.0. The published crate lockfile instead selects Address 2.5.0;
the review profile is an explicit compatible selection, not a claim about every
client resolution. The Lean model imports shared request and checked-preparation
vocabulary.

Tests check exact order, flags, data, empty signers, current supplied program
addresses, duplicate identities, normal state effects and unwind state. A real
exclusive acquisition on the second writable account rejects with no possible
invocation outcome. A separate live exclusive lease on a readonly wallet still
reaches invocation, distinguishing the selected v2 behavior from v1. These are
mathematical executions; legal source handles, `AsRef`, Rust implementation,
byte storage and representation correspondence remain open bindings. The raw
header observation must agree with the actual source bytes and their Boolean
getters at each legal current handle.
