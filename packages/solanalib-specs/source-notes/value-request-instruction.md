# Instruction 3.4.0 supporting constructors

`Solanalib.Specs.Core.Instruction.make` constructs the canonical
`Solanalib.Runtime.CpiInstruction` from a program address, an ordered metadata list and data
bytes. It preserves duplicate addresses, separate flags on duplicate entries,
empty lists and every byte. It is shared mathematical vocabulary, not a claim
that an SDK `Vec` constructor has run or allocated storage.

The versioned `Solanalib.Specs.SolanaInstruction.AccountMeta` models provide the two
supporting SDK constructors used by modeled builders. `new` retains the supplied
signer flag and sets writable to 1. `new_readonly` retains the signer flag and
sets writable to 0. These are complete value constructors without allocation.
Their closed references and satisfiable preconditions are checked separately.

`Instruction::new_with_bincode` and `new_with_wincode` are also supporting
requirements: the two required System interface 3.2.0 builders consume these
feature-selected constructors. Their primary models are complete operational
families above explicit dependency providers. They call the selected serializer
with the data value and retain its actual state. An `Ok` byte-vector handle
moves into the result alongside the same caller-owned metadata handle. A
serializer `Err` goes through a non-returning `Result::unwrap` failure provider;
it cannot become a normal constructor return or a returned error result.

`Solanalib.Specs.Core.InstructionBuilder` models those dependencies at their call
sites, using the shared `Owned.VectorOps` and ordered cleanup vocabulary.
Serialization or unwrap unwinding drops the retained metadata resource in the
current state. A terminal exit skips cleanup. A second unwind during destruction
uses an explicit terminal-only policy with the actual state of the destructor. The
serializer provider owns cleanup of its internal partial allocations, while the
unwrap-failure provider includes formatting, panic and owned-error cleanup.
Neither provider includes the retained metadata-vector cleanup of the caller.

`TokenInstructionAllocated` uses the same `Instruction.OwnedValue`, callback
composition and ordered cleanup mechanisms, but models a different source
path. It packs bytes through `Vec::with_capacity`, push and extend calls, with
the allocation order of each token constructor and ordinary token errors.
`InstructionBuilder` instead invokes the selected serializer and handles its
`Err` through `unwrap`. These transitions stay separate to preserve their
different calls, order and exits.

`Instruction.OwnedValue` carries the exact metadata and byte resource handles.
Its value observer reads both provider tables in the actual final state. Local
primitive vector laws, serializer byte correctness and resource frames can
establish stronger returned-value facts through `observe_of_current`; those
facts do not follow merely from operational trace composition. The model does
not assume callback success, rollback, a complete SDK postcondition, or proved
core/alloc/std implementations. Its positive closed execution witnesses allocate
nonempty mathematical vectors; they are consistency witnesses, not Rust runs.

All four constructors support the registered library builders. They do not
imply models for the other Instruction constructors: `new_with_bytes` and
`new_with_borsh` remain outside this subset.

The reviewed [account_meta.rs](https://github.com/anza-xyz/solana-sdk/blob/1d4d322b9eac89e6c8069464e0c184d72584106c/instruction/src/account_meta.rs#L62)
anchors are `new` at line 62 and `new_readonly` at line 98. The reviewed
[instruction/src/lib.rs](https://github.com/anza-xyz/solana-sdk/blob/1d4d322b9eac89e6c8069464e0c184d72584106c/instruction/src/lib.rs#L198)
anchors are `new_with_bincode` at line 198 and `new_with_wincode` at line 249.
Crate source bytes match the pinned 3.4.0 archive.

Tests include writable non-signers, readonly signers, duplicate metadata,
embedded zero bytes, actual resource transfer, serializer errors, cleanup using
partial serializer effects, terminal exits with impossible drop callbacks, and
double unwind. A negative control excludes a returned instruction after a
serializer error. Rust storage, dependency-provider, feature, compiler and
implementation correspondence remain open.
