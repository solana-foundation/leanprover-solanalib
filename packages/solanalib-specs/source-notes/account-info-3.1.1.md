# AccountInfo 3.1.1 mathematical models

The reviewed source is `solana-account-info` 3.1.1, revision
`9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23`,
[`account-info/src/lib.rs`](https://github.com/anza-xyz/solana-sdk/blob/9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23/account-info/src/lib.rs),
SHA-256 `f7aeb75e2f891502f8c3dd06650e86d57539528ad92f5e67372640ded0a194b7`.
The [source registry](../source-map.json) records the exact Rust names and
source anchors. Models cover `lamports`, `data_len`, `try_borrow_data`,
`try_borrow_mut_data` and derived `clone`, with drop behavior used in composition.

The shared Borrow model represents two distinct typed cells: UInt64 lamports
and data bytes. Aliases preserve these identities; stable guard IDs and
generations prevent using a released or consumed token again. The shared count
limit is the selected RefCell bound `2^(wordBits - 1) - 1`, not the bound of 254 for AccountView. The target profile is explicit. Logical IDs are not source addresses,
provenance or ownership permissions.

Getters perform temporary shared borrows and release them after observing
current contents. A conflict panics, with unwind or terminal abort selected by
the profile. Checked data borrowing returns a live guard or the exact SDK
AccountBorrowFailed error. Mutable borrowing has no writable-metadata check.

The checked-borrow contracts require only a protocol-valid guard world and a
present data cell. Those premises prove final protocol validity and current
typed data through every successfully returned guard. Getter admission requires
only a present, typed selected cell; `observe_reference_exists` uses it to rule
out a malformed-model path and provide a finite value or borrow panic. Neither
operation requires bounds on the target width or data length, or validity of
the unused cell, for these mathematical results. The broader `AccountInfo.Valid`
predicate remains available to source interpretations and other composed models.
Rust field widths, the selected RefCell policy, distinct source cells and
physical reference validity still require their own binding.

`Value.owner` is an entry observation; `OwnerRef` identifies the pointed owner
and `OwnerAt Aux` reads its current contents. Keeping or cloning an AccountInfo
does not imply immutable owner contents. Constructor and codec controls change
that owner between reads.

The primary clone family calls lamports Rc clone then data Rc clone in actual
state order. Success returns the same aliases and owner reference; overflow
may terminate. A corresponding drop binding must preserve the same field order. The selected
`Rc<RefCell<&mut u64>, Global>` and `Rc<RefCell<&mut [u8]>, Global>` have no user
destructor or allocator-clone callback that can unwind. This source capability
is explicit, while terminal exits remain possible. The registry pins supporting
Rc excerpts; no Rc implementation correctness is assumed or proved here.

`clone_observation_contract` forgets the Rc lifecycle and is supporting only.
Its identity operation has an unconditional mathematical precondition.
Concrete event traces witness dependency scheduling, not real allocation or
reference counts. Source binding must supply actual Rc operations and relate
logical live resources to source owners. Closed witnesses and model clients
cover conflicts, saturation, independent cells, mutation/release, consumed
guards, panic and exact Rc sequencing. Rust representation, dependency and body
proofs remain open.
