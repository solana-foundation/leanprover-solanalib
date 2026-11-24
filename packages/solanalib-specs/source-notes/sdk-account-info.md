# SDK AccountInfo operations

The [source registry](../source-map/solana-account-info.json) retains exact trait
and inherent-method identities, source anchors and profiles for this subset.
The table lists exact inspected references. The 3.1.1 profiles declare
`[3.1.1, 4.0.0)` only under their method-specific current-cell, borrow, owner-write
and resize assumptions. Actual source layouts and source selection checks remain exact.

| Published crate | Registered AccountInfo operations covered here |
| --- | --- |
| `solana-program` 1.15.2 | `assign`, `clone`, `data_len`, `lamports`, `realloc`, `try_borrow_data`, `try_borrow_mut_data`, `try_borrow_mut_lamports`, `try_data_len` |
| `solana-program` 1.18.26 | `assign`, `clone`, `data_is_empty`, `data_len`, `lamports`, `realloc`, `try_borrow_data`, `try_borrow_lamports`, `try_borrow_mut_data`, `try_data_len` |
| `solana-account-info` 2.3.0 | `as_ref`, `assign`, `try_borrow_lamports`, `try_data_len`, `data_is_empty`, `realloc`, `resize` |
| `solana-account-info` 3.1.1 | `as_ref`, `assign`, `try_borrow_mut_lamports`, `try_data_len`, `data_is_empty`, `resize` |

The 1.15.2 `src/account_info.rs` is at revision
`dea65f48e9920a71edd7c12c305c5ebadd192afa`, SHA-256
`1e8cca42d368803cd0529a5a25860a31afb0d3abf526e98a0ecc0389f8adc3f6`.
The 1.18.26 file is at revision
`c2b350023ba849d1b33142592264aaa51fcb7f1e`, SHA-256
`dc0096411ce48bed4ec21e0b0ba45f39de5e3c72d69db2594ac12a65acb62413`.
Its operation profiles declare `[1.18.26, 2.0.0)` under their recorded
source and provider assumptions.

The inherited profiles use the inspected 2.3.0 reference and declare
`[2.3.0, 3.0.0)` under their own operation and provider assumptions,
with the separate `data_is_empty` range below. The 2.3.0 `src/lib.rs` is at revision
`985c90595dda6fe2bc1026f0b1c942c75a266b6f`, SHA-256
`6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a`.
The 3.1.1 file is at revision
`9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23`, SHA-256
`f7aeb75e2f891502f8c3dd06650e86d57539528ad92f5e67372640ded0a194b7`.

For `data_is_empty`, AccountInfo 2.1.0, 2.2.1 and 2.3.0 retain the same
current data-cell read, temporary shared loan and panic-on-conflict behavior.
Its declared range is `2.1.0 ≤ v < 3.0.0`; the exact 2.3.0 record, layout
and provider binding remains separate. The other methods retain their own
compatibility profiles.

## References, borrowing and owner writes

Reflexive `AsRef` returns the same existing shared reference and preserves the
world. It creates neither an AccountInfo value nor another Rc owner.
Lamports and data use independent cells in the common borrow protocol, with
stable guards, generations and the selected shared-counter policy. A checked
lamports borrow requires a valid protocol and the actual typed cell. The
1.18.26 and 2.3.0 operations acquire a shared guard; the selected 1.15.2
and 3.1.1 operations acquire an exclusive guard. Success returns that live
guard; conflict returns `AccountBorrowFailed`. There is no
signer, writable or unrelated-data check. Aliases refer to the same cell.
The selected 1.15.2 and 1.18.26 data methods return the actual shared or
exclusive data guard under the corresponding protocol, with the same ordinary
conflict error.

`try_data_len` temporarily acquires a shared data guard, reads the current
length and releases it; acquisition failure returns `AccountBorrowFailed`.
`data_is_empty` follows the same temporary lifecycle but panics on conflict
according to the selected panic strategy. The selected 1.15.2 and 1.18.26
`lamports` and `data_len` similarly read under temporary shared guards and
panic on conflict. Typed-cell conditions exclude
malformed mathematical reads. Actual counter bounds, lifetimes and object
geometry remain source representation obligations.

The 1.15.2 and 1.18.26 derived clones copy the record metadata and references,
cloning the lamports Rc before the data Rc. They add owner occurrences for those same
cells without copying balances or data bytes. Actual Rc count updates, partial
cleanup and primitive exit behavior belong to the selected source contract;
record equality does not deduplicate those owners.

`OwnerRef` identifies current owner storage; the saved owner observation of an AccountInfo is not a replacement for it. `assign` performs the volatile write in the source through that shared owner reference. The storage bound supports
the new current value through every alias. This operation acquires no RefCell
guard and performs no runtime authority check. The source interpretation must
justify the storage and the legal write through that reference.

## Reallocation order and backing bytes

The 1.15.2, 1.18.26 and 2.3.0 `realloc` and the 3.1.1 `resize` perform these
operations in order:

1. Acquire an exclusive data guard; conflict returns `AccountBorrowFailed`.
2. Read the current slice length. An equal-length request releases the guard
   and succeeds without reading the original-length header.
3. Read the original length of the loader. Saturating subtraction checks growth
   against 10,240 bytes from that original length. Excess growth returns
   `InvalidRealloc` and releases the guard.
4. Write the serialized length and replace the shared data slice. If requested,
   zero only the newly exposed tail, then release the guard.

`Buffer.originalLen` is immutable. The serialized length, current bytes and
spare bytes describe the actual backing. Shrinking moves truncated bytes into
the spare region; a later 1.15.2, 1.18.26 or 2.3.0 `realloc(_, false)` exposes them
again. In 2.3.0, `resize` delegates to `realloc(_, true)`. Release 3.1.1 removes
`realloc` and inlines the always-zeroing behavior. Its wrapper fixes the zeroing flag of the
shared model to true.

`ResizeReady` requires the actual typed data cell and a valid borrow world.
A buffer is needed only after successful acquisition and a changed length;
capacity is needed only after the growth check permits that change. These
conditions prove the resulting slice length. An early borrow error or
equal-length return needs no original header or spare region. The source
interpretation separately relates the original `u32` at `key - 4`, serialized
`u64` at `data - 8`, slice descriptor, complete allocation, integer widths,
alignment, provenance and legal pointer operations.

At a reached zeroing syscall the new lengths are already written and the
exclusive guard remains live. The model retains a terminal exit there without
an after-state. A normal return uses the explicit memory contract that zeroes
the reached tail and then releases the guard. There is no added unwind across
the C ABI or rollback of the preceding writes.

## Source profile and interpretation

The 1.15.2 reallocation profile also requires `target_os = "solana"`
and its internal `solana_program::program_memory` branch, forwarding the
actual destination, zero byte and tail length to `sol_memset_`.

The 1.18.26 reallocation profile requires `target_os = "solana"` and its
internal `solana_program::program_memory` branch, forwarding the actual
destination, zero byte and tail length to `sol_memset_`.

The 2.3.0 resize profiles require `target_os = "solana"` and the
`solana-program-memory` operation profile: inspected references 2.2.1 and
2.3.1, declared range `[2.2.1, 3.0.0)`. The complete `sol_memset` functions
agree at those references. Compatibility assumes that the selected branch
continues to forward the actual destination, zero byte and tail length to
`sol_memset_` with the recorded normal and terminal effects. The 3.1.1 resize
profiles require the same Solana target and keep `solana-program-memory`
3.0.0 and 3.1.0 as inspected references, with declared range `[3.0.0, 4.0.0)`
under the same reached-memory-operation assumption. A replaceable host
stub may have other effects or unwind and is outside that profile. Selecting
Solana cfg does not establish native/SBF layout equivalence.

Release 3.1.1 uses Address for the key and owner and retains the actual
`_unused` metadata word; 1.15.2, 1.18.26 and 2.3.0 retain `rent_epoch`.
The 1.15.2 record lacks the later `repr(C)` declaration and has a distinct
compiled field order. Shared mathematical bytes do not identify these source
types or establish equal physical layouts.

The registry retains both the named lifetimes in Rust source and alternative
spellings with erased lifetimes for these exact methods. This does not
relax package or ABI selection. The [binding obligations](../BINDINGS.md)
cover physical guards, source storage, dependencies and target correspondence.
Borrow and resize laws concern the mathematical state; they are not SDK body,
allocator, compiler or runtime implementation proofs.

The [AccountInfo scenarios](../SolanalibTest/Specs/Core/AccountInfoSdk.lean)
exercise borrow conflicts and cleanup, owner aliases, resize error order,
stale-byte regrowth and reached zeroing exits. The library [reallocation tests](../SolanalibTest/Specs/SolanaAccountInfo/Realloc.lean) retain the
source-facing contract. A separate binding to the Rust implementation must establish the physical header, counter and resource checks.
The existing `SdkAccounts` family replays the selected records of the
`sdk-accounts-2` native driver; the
[conformance guide](../../../tools/library-conformance/README.md)
describes selected replay and fresh recording. Extra recorded helper methods
do not become registered model coverage merely by sharing this driver.

The Program 1.15 compatibility interval in the applicability registry assumes
these operations preserve the 1.15.2 reference contracts. It ends before 1.16.0,
whose `AccountInfo` adds `repr(C)` and changes field order. A compatible catalog
selection does not supply the concrete record layout, Rc/RefCell identities or
source-call proof; those remain the separately bound source inputs. The
inspected/native versions in the tables above are unchanged.
