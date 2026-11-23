# SDK aligned entrypoint deserialization

The native and exact source reference for `solana-program-entrypoint::deserialize`
is 2.3.0 at [revision 5d0a784](https://github.com/anza-xyz/solana-sdk/blob/5d0a784ca69704a3eb6728d494f5c4d4b35ceecf/program-entrypoint/src/lib.rs#L457),
with resolved `solana-account-info` 2.3.0. The inspected 2.2.1 and 2.3.0
implementations support `2.2.1 ≤ v < 3.0.0` under the recorded allocation,
layout, dependency and loader-format conditions. The [source registry](../source-map.json)
retains exact bindings separately. This unsafe library interface does not
establish loader, startup or application correctness.

## Input format

The selected format has 64-bit pointers and little-endian integers. A leading
`u64` gives the account count. A unique account uses these relative offsets:

| Offset | Width | Contents |
| --- | --- | --- |
| 0 | 1 | Nonduplicate marker 255 |
| 1, 2, 3 | 1 each | Signer, writable, executable |
| 4 | 4 | Original data length, written by this function |
| 8 | 32 | Key |
| 40 | 32 | Owner |
| 72 | 8 | Lamports |
| 80 | 8 | Serialized data length |
| 88 | data length | Data |
| after data | 10,240 | Reallocation reserve |
| after reserve | 0 to 7 | Padding to an eight-byte boundary |
| after padding | 8 | Rent epoch |

A duplicate is an earlier account **slot** index followed by seven padding
bytes. It consumes no account body. A duplicate of a duplicate retains the
original identity; unique records with equal keys remain distinct. After the
records come a `u64` instruction length, its bytes and a 32-byte program ID.
Trailing allocation bytes are retained. Reserve and padding need not be zero.

`parse = none` excludes an input from the contract; it does not describe a
Rust error return. The loader-format profile requires backward duplicate
indices and account data lengths at most 10,485,760 bytes. These are input
restrictions, not checks in `deserialize`. There is no 254-account cap in this
SDK model: its selected 48-byte element profile requires
`count * 48 < 2^63`.

The source input must be one live, nonnull, eight-byte-aligned allocation
covering every read, reserve and view, with its actual provenance. Additions
and alignment rounding must fit `usize`; slices and pointer differences must
fit the selected signed pointer bound. Source access is exclusive for
lamports, data and original-length words, with valid shared key, owner,
instruction and program views for the returned Rust lifetime. Duplicate Rc
handles share one original mutable borrow; they do not create independent
mutable owners. Solana cfg selection does not prove SBF layout equivalence.

## Allocation, state and finite exits

The model reserves an account vector when the count is nonzero and processes
records in source order. A unique record allocates the lamports Rc, writes the
current data length as a `u32` at offset 4, then allocates the data Rc. Failure
of that second allocation therefore occurs after the header write. The
allocator provider sees its actual allocation site and the then-current input
bytes. This source profile has no allocator unwind; terminal exits have no
invented after-state, and an allocator need not have a finite outcome.

The returned AccountInfo vector preserves order, nonzero-to-Boolean flag
conversion and rent epoch. Duplicate entries share both borrow-cell handles,
owner-reference identity and original header offset, incrementing both strong
counts. Unique equal-key entries keep distinct storage. Buffer state retains
original length, serialized length and the entire reserve. The shape and
origin lemmas derive these identities and the result length from the actual
parsed records.

The [binding obligations](../BINDINGS.md) require the selected allocator,
Rc/RefCell lifecycle, layouts, reference lifetimes and physical access rights.
A satisfying mathematical input or finite reference execution does not prove
the unsafe Rust body, allocator, loader or compiler correct.

## Pinocchio bounded output

The same loader-format parser supports the Pinocchio 0.9.2
`entrypoint::deserialize`, with a separate bounded AccountInfo output-array
contract. It initializes `min(account_count, MAX_ACCOUNTS)` slots, preserves
the untouched suffix and advances past skipped accounts before locating the
instruction slice and program ID. It preserves duplicate header identity and
raw flag bytes and does not write the original-length field of the SDK.

The inspected Pinocchio 0.9.2 and 0.9.3 deserializers support
`0.9.2 ≤ v < 0.10.0` under these same input, alias, output-capacity and
source-ABI obligations. Native observations and the existing exact binding
remain at 0.9.2. SDK 3.x changes the unique-account allocation sequence and
is outside the SDK range above.

Pinocchio writes slot zero before checking capacity. A nonempty input with
`MAX_ACCOUNTS = 0` is therefore outside its unsafe precondition; the native
driver never calls Rust on that case. Empty input remains admissible at zero
capacity. The exact const argument of the output array is part of the source ABI,
so a different capacity is not a substitute for a selected source binding. The existing
`EntryDeserialize` conformance family and mathematical tests check both paths
without inferring loader or sBPF correctness from the shared byte parser.
