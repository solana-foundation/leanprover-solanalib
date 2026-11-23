# SPL instruction builders

The [source registry](../source-map.json) selects these exact construction and
constant operations. Source hashes, anchors and resolved dependencies remain
per API in its [profiles](../applicability.json).

| Native/source reference crate | Registered operations covered here |
| --- | --- |
| `spl-token` 8.0.0 | `close_account`, `mint_to`, `burn_checked`, `set_authority`, `native_mint::check_id` |
| `spl-token-2022` 8.0.1 | `id`, `close_account`, `mint_to`, `burn_checked`, `set_authority`, `freeze_account`, `thaw_account`, `initialize_account3`, `transfer_checked`, `initialize_mint2`, `initialize_immutable_owner`, `initialize_mint_close_authority`, `initialize_non_transferable_mint`, metadata-pointer `initialize`, `native_mint::check_id` |
| `spl-token-2022-interface` 3.1.1 | `id`, `close_account`, `initialize_account3`, `transfer_checked` |
| `spl-token-metadata-interface` 0.7.0 | `instruction::initialize` |
| `spl-memo` 6.0.0 | `id` |

The five legacy Token operations in the table declare `8.0.0 ≤ v < 9.0.0`
from the inspected 8.0.0 source. The newly recorded Token-2022 constructors
(`close_account`, `mint_to`, `burn_checked`, `set_authority`, `freeze_account`,
`thaw_account`, `initialize_account3`, `transfer_checked`, `initialize_mint2`,
`initialize_immutable_owner`, `initialize_non_transferable_mint`) and
`native_mint::check_id` were inspected at 8.0.0 and 8.0.1 and declare the
same 8.x range. Exact keys, enum/layout indices, program checks, dependency
sources, allocation order and cleanup conditions remain per operation.
Existing ID, mint-close, metadata and interface profiles are preserved.
The `mint_to` change between 8.0.0 and 8.0.1 renames an authority parameter
without changing the ordered construction; it does not authorize a pin update.

The 3.1.1 source and shared constructor families are described in the existing
[constructor note](token-instructions.md#constructor-semantics). The reviewed
8.0.1 close, account3 and checked-transfer implementations reuse their complete
contracts, including checks, packing, capacities, metadata and lifetime order.
They keep the actual compiled `enumSize` index; neither a later enum layout nor
the sample size of a mathematical witness is substituted.

## Bytes, metadata and allocation order

| Builder | Data prefix and fields | Ordered metadata |
| --- | --- | --- |
| `mint_to` | 7, u64 amount | Writable mint, writable destination, authority and signers |
| `burn_checked` | 15, u64 amount, u8 decimals | Writable source, writable mint, authority and signers |
| `close_account` | 9 | Writable source, writable destination, authority and signers |
| `set_authority` | 6, authority-type byte, optional key | Writable account, authority and signers |
| `freeze_account` / `thaw_account` | 10 / 11 | Writable account, readonly mint, authority and signers |
| `initialize_account3` | 18, owner key | Writable account, readonly mint |
| `transfer_checked` | 12, u64 amount, u8 decimals | Writable source, readonly mint, writable destination, authority and signers |
| `initialize_mint2` | 20, decimals, mint authority, optional freeze authority | Writable mint |
| `initialize_immutable_owner` | 22 | Writable account |
| `initialize_mint_close_authority` | 25, optional close authority | Writable mint |
| `initialize_non_transferable_mint` | 32 | Writable mint |
| Metadata-pointer `initialize` | 39, 0, authority key, metadata-address key | Writable mint |

Amounts use little-endian bytes. Authority and explicit signer metas are
readonly. The authority is a signer exactly when the supplied signer list is
empty; explicit signers retain order and duplicates. No extra signer-count
gate is imposed. `set_authority` reserves `3 + N` slots but fills `2 + N`.
Legacy builders require the legacy token ID. Ordinary Token-2022 builders and
immutable-owner initialization accept either token ID; mint-close authority,
nontransferable mint and metadata-pointer initialization require Token-2022.
Program checks precede allocation.

An ordinary optional key uses a one-byte tag and 32 bytes for `Some`;
`Some(zero)` is accepted and differs from `None`. The selected AuthorityType
has four variants in legacy 8.0.0 and seventeen in Token-2022 8.0.1.
The `OptionalNonZeroPubkey` of Metadata-pointer instead rejects `Some(zero)`. Its
metadata allocation precedes authority validation and then metadata-address
validation, so either key error drops an allocated owner. A program-ID error
has no such allocation.

Ordinary builders construct bytes before metadata. Immutable-owner,
mint-close-authority and nontransferable-mint constructors allocate metadata
first. The full allocated families retain both current vector identities,
partial states, cleanup of later owners before earlier ones, double unwind
and terminal stopping. No provider termination is assumed.

## Metadata serialization and constants

Metadata-interface initialization accepts any program ID and orders four metas
as metadata (writable), update authority, mint and mint authority (readonly
signer). After metadata allocation it constructs output bytes, appends the
eight-byte discriminator `d2e11ea258b84d8d`, serializes the three moved String
owners, appends the temporary serialization vector and drops it. Input strings
are destroyed after the return place has been constructed.

The reached Borsh 1.5.7 and 1.6.0 encoders agree on name, symbol and URI:
little-endian `u32` UTF-8 byte lengths followed by those bytes. Oversized
lengths produce `InvalidData`; the error provider denotes the whole consuming
`unwrap`, with its actual panic outcome. Serialization reads current String
owners at the reached state. Intervening vector operations must preserve
their ownership and contents, rather than supplying an earlier text snapshot.

The registered Token-2022 `id` functions return their fixed program key.
Native-mint `check_id` compares all 32 bytes: legacy declares
`So11111111111111111111111111111111111111112`, while Token-2022 declares
`9pan9bMn5HatX4EJdBwg9VgCa7Uz5HL8N1m5D3NdXejP`. Memo returns the declared
`MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr` key without a syscall.

The metadata-pointer, mint-close-authority and Token-2022 ID entries also
retain the explicitly reviewed Pubkey 2.4.0 profile with Instruction 2.3.3;
the initializers use spl-pod 0.5.1 and bytemuck 1.24.0 there. Other selected
8.0.1 builders keep their reviewed Pubkey 2.2.1 profile. These are source
comparisons, not additional native recordings. The
[binding obligations](../BINDINGS.md) retain real vector/String providers,
source widths, layouts and callback frames. Constructing an instruction
establishes no callee execution, authorization or transaction success.
