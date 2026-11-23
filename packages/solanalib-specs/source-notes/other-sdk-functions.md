# Additional shared SDK functions

These are mathematical function models. The argument below compares their
definitions with the pinned source; the Lean theorems concern those models.
No compiled Rust implementation, standard-library implementation or deployed
program is proved correct here. All implementation bindings remain open.

## Selected sources

| Crate | Exact source revision | Selected source |
| --- | --- | --- |
| `solana-curve25519` 3.1.12 | `6c1ba34691f17ac902ae3d2e1147eed5723b9cef` | [edwards.rs](https://github.com/anza-xyz/agave/blob/6c1ba34691f17ac902ae3d2e1147eed5723b9cef/curves/curve25519/src/edwards.rs#L148) |
| `solana-sdk-ids` 3.1.0 | `1bb184f0646173544c0b44d45342d6d66d54b9ce` | [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/1bb184f0646173544c0b44d45342d6d66d54b9ce/sdk-ids/src/lib.rs#L67) |
| `solana-program-option` 3.1.0 | `229ec99c991df1db516c0645b8a6ecf3df5a55cc` | [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/229ec99c991df1db516c0645b8a6ecf3df5a55cc/program-option/src/lib.rs#L50) |
| `solana-zero-copy` 1.2.0 | `5d3cfe493b77f916cb6f73cf034558065cae554f` | [unaligned.rs](https://github.com/anza-xyz/solana-sdk/blob/5d3cfe493b77f916cb6f73cf034558065cae554f/zero-copy/src/unaligned.rs#L150) |
| `pyth-solana-receiver-sdk` 2.0.0 | `4099cb15d0943e603bdc6ad12aecbd2b6eb0f2c0` | [price_update.rs](https://github.com/pyth-network/pyth-crosschain/blob/4099cb15d0943e603bdc6ad12aecbd2b6eb0f2c0/target_chains/solana/pyth_solana_receiver_sdk/src/price_update.rs#L235) |
| `switchboard-on-demand` 0.12.1 | `f75b1ef63e10eda35d046b1838810ec2935d7f39` | [pull_feed.rs](https://github.com/switchboard-xyz/switchboard-sdk/blob/f75b1ef63e10eda35d046b1838810ec2935d7f39/solana/rust/switchboard-on-demand/src/on_demand/accounts/pull_feed.rs#L270) |

The [source registry](../source-map.json) records the exact repository, revision, file hash and Rust symbols for each model. The Pyth references are the checksum-verified crates.io releases receiver SDK 2.0.0 and Pythnet SDK 3.0.0, both published from upstream revision `4099cb15d0943e603bdc6ad12aecbd2b6eb0f2c0`. The applicability catalog retains the reviewed published release ranges and their dependency conditions. Macro expansion locations do not change the defining crate version of a function. The source audit checks these pinned files and anchors.

## Curve, ID and value functions

`Curve.validateEdwards` models the selected `target_os = "solana"` branch.
The request contains curve ID 0, the supplied 32 point bytes and an output
byte initialized to 0. The source returns `result == 0`; it does not read that
output byte when deciding validity. The callback relation preserves its actual
state on return or unwind and its terminal reason. The model tests deliberately
use status 0 with scratch 255, and nonzero status with scratch 0.

`Curve.primitiveReply_status` relates an admitted canonical Edwards primitive
reply to the existing `Prims.validatePoint_edwards` theorem. Syscall admission,
feature gates, metering, point/output memory and the correctness of the cryptographic primitive remain separate bindings. A host decompression implementation is
not substituted for this source branch.

The system-program ID macro supplies the address consisting of 32 zero bytes.
The model returns the same canonical `Solanalib.Runtime.Ids.systemProgram`; its test checks
all 32 bytes. The supporting declaration span is in the `declare_id` of `solana-address` 2.6.1 macro, while the defined function belongs to `solana-sdk-ids` 3.1.0.

`COption::is_some` examines only the variant, through a family quantified over
every payload type. It neither moves nor clones the payload. An uninhabited
payload type still admits `None`; no type-inhabitation assumption is needed.
The model does not assert the physical C layout of the enum.

`From<U64> for u64` uses the macro instantiated for the eight-byte `U64` at
lines 449–450. The conversion of the macro at line 150 calls `from_le_bytes`, so
the mathematical decoder is little endian regardless of native u64 alignment.
Its input has exactly eight bytes. The bound and all-value encode/decode
round-trip theorems use the canonical byte codec; they are not proofs about
the core integer methods of Rust.

## Pyth price getter

The model keeps the authority, verification level, complete price
message of the update and posted slot. The source reads only the verification level and the feed, price, confidence, exponent and publication time of the
message. The full
verification level dominates every partial level; partial levels compare their
byte-sized signature counts. A level field is data, not a proof of signatures.

The family has no clock precondition: its mathematical operation and exact
outcome postcondition are defined on all canonical clocks, whose fields use
unbounded `Nat` and `Int`. This getter reads only `unix_timestamp`. Relating
an argument to a Rust `Clock` still requires every field to fit its source
`u64` or `i64` range, as expressed by `Sysvar.clockValid`. That representation
obligation is separate from the mathematical family; the getter performs no
runtime clock-width validation.

The source first rejects insufficient verification, then calls
`get_price_unchecked`, which rejects a mismatched feed and copies the four
returned price fields. Only afterwards does it evaluate
`maximum_age.try_into().unwrap()`. Conversion to i64 panics above `2^63 - 1`;
neither an ordinary stale-price error nor clamping models that branch.
The subsequent signed addition saturates at the upper bound of i64. Because the
converted age is nonnegative, lower saturation is impossible. Acceptance is
inclusive at `publish_time + age = clock.unix_timestamp`, and future publication
times are accepted. Both panic strategies are explicit family choices.

The tests cover all three ordinary error priorities, the panic threshold,
upper saturation, negative timestamps, the maximum accepted age and equality
at the freshness boundary. Two exact-family controls also retain the outcomes
for abstract clocks with an out-of-range unused slot or timestamp. Those
controls exercise the extended mathematical domain, not Rust inputs.
The return contains exactly the `Price` fields of the source. The `GetPriceError` variants are modeled directly; no Anchor numeric
conversion or deserialization is claimed. Account ownership and the validity
of the authority or signatures of the update are outside this getter.

## Switchboard feed parsing

The applicability catalog records the published releases and Git revision
`f75b1ef63e10eda35d046b1838810ec2935d7f39` as separate source origins. The Git
revision is already the pinned source of this model and its Rust conformance
corpus. Its complete `pull_feed.rs` and `error.rs` files match both the recorded
source hashes and the checksum-verified crates.io 0.12.1 archive. The manifest
differences concern host secp256k1 features and Solana dependency defaults;
neither affects the reached operations of the parser. The existing parser, bytemuck
and layout interpretation below therefore applies to this exact Git source.

The Git profile admits only version 0.12.1 at this exact revision; the registry
compatibility intervals do not apply to this source origin.

The source argument is already `Ref<&mut [u8]>`. The model starts with a live
guard in the common AccountInfo cell world. Binding that guard to the source
argument requires shared mode; the mathematical parser also operates on other
live modes. It performs no second acquisition, owner check or key check.
It reads current bytes, tests the eight-byte discriminator, checks enough
bytes for the payload, repeats the
sliced-length check and then checks the alignment of the payload address.

The pinned `repr(C)` fields give the following layout under both supported
64-bit choices for i128 alignment. The overall alignment of the payload is 8 or 16,
respectively; its size is 3200 in either case.

| Field or component | Offset or size in bytes |
| --- | --- |
| `OracleSubmission` / array of 32 | 64 / 2048 |
| authority / queue / feed hash | 2048 / 2080 / 2112 |
| initialized time / permissions / variance | 2144 / 2152 / 2160 |
| minimum responses / name | 2168 / 2172 |
| four one-byte fields, including padding | 2204 through 2207 |
| last-update time / lookup-table slot / reserved bytes | 2208 / 2216 / 2224 |
| `CurrentResult` | offset 2256, size 128 |
| maximum staleness / padding | 2384 / 2388 |
| 32 `CompactResult` values | offset 2400, 16 bytes each |
| two reserved arrays | 2912 / 2920 |
| 32 submission timestamps | 2944 through 3199 |

Selecting a Solana cfg on a host target does not establish Solana layout
equivalence. The model supports i128 alignment 8 and 16 explicitly, including
successful and failed controls for both. A Rust binding must select the actual
layout and justify the supplied slice address.
The same bytes and address can pass the 8-byte profile and fail the 16-byte one.

Mathematical `Ready` requires protocol validity and a live readable byte view.
These premises provide progress, final protocol validity and retirement of the
input token. Shared mode, a positive 64-bit slice address, an isize-bounded
length and a nonoverflowing complete extent remain source-argument binding
obligations. The natural-number arithmetic is also defined outside those
physical bounds; they are not unused hypotheses of the mathematical family.

The fields are Pod byte arrays, integers and floats, with explicit padding;
there is no additional payload bit-validity predicate. Once `try_from_bytes`
has accepted the checked size and alignment, the following pure mapping closure
repeats the same slice and `from_bytes` check without intervening mutation.
It therefore has no new panic branch on an admitted input. The model retains
the three possible `OnDemandError` variants as an explicit result subset.

The reviewed parser dependency is bytemuck 1.25.0, at source revision
`164cedda0eae131bc6cb67902599f4ec253642ca`. Another dependency resolution needs
its own source correspondence. Its
[`try_from_bytes`](https://github.com/Lokathor/bytemuck/blob/164cedda0eae131bc6cb67902599f4ec253642ca/src/internal.rs#L157)
checks exact size before alignment, then forms the reference. `from_bytes`
uses the same helper. The alignment primitive has modulo and `align_offset`
feature branches; the interpretation must justify the chosen branch on the
valid byte pointer. The mathematical 8/16 alignment predicate is not a proof
of that Rust pointer operation.

Every ordinary error drops exactly the input guard. Success transfers
its token to the 3200-byte range after the discriminator, retains the same lease
and invalidates the input generation. Trailing bytes are accepted but are not
part of the returned view. `parse_exists` proves a finite model exit for every
admitted input, and `parse_cells` proves that all backing cells are unchanged.
`parse_valid_consumes` uses `Ready` to prove that every result preserves the
borrow-state invariant and retires the input token; both guarantees are part
of the postcondition of the versioned contract. This supports subsequent borrowing
without allowing reuse of the consumed guard generation.
The returned `FeedRef` represents a typed live byte view, not a copied decoded
record. Physical references, Pod layout and typed field projections still need
their Rust interpretation; no std Ref or bytemuck implementation proof is added.

## Pyth PriceUpdateV2 decoding

`PriceUpdateV2` (price_update.rs line 51) carries the Anchor `#[account]`
attribute at line 49. Anchor-attribute-account 1.0.2 expands it, outside the
zero-copy branch, into `#[derive(AnchorSerialize, AnchorDeserialize, Clone)]`,
`AccountSerialize`, `AccountDeserialize`, `Discriminator` and `Owner`
implementations. Anchor-derive-serde 1.0.2 turns `AnchorDeserialize` into
the `BorshDeserialize` of Borsh-derive 1.6.1 with
`borsh(crate = "anchor_lang::prelude::borsh")`. All of these generated
functions are code in the pyth crate, so the decoders modeled below belong to
this root.
`VerificationLevel` (line 19) derives `AnchorDeserialize` at line 18 in the
same way.

The derived `PriceUpdateV2::deserialize_reader` decodes the four fields in
declaration order. They are `write_authority`, `verification_level`,
`price_message` and `posted_slot`. The first failing field returns its error
at once. As with every Borsh decoder here, the contract leaves the remaining
slice after an error unconstrained, and the reference follows the `Read for &[u8]` of std.
`write_authority` is the `Pubkey` of Anchor. anchor-lang 1.0.2 takes it from
solana-pubkey 3.0.0, which re-exports `Address` from solana-address 1.1.0, and
that crate re-exports solana-address 2.x; under a resolution to
`solana_address::Address` 2.6.0, its decoder is the derived Address model.
This is a reference resolution, not an additional patch-version requirement
on Pyth callers. The declared Pyth compatibility ranges assume that the used
authority decoder preserves its 32-byte encoding and error behavior.
`posted_slot` uses the Borsh 1.6.1 little-endian `u64` decoder.

For the crates.io receiver 2.0.0 reference, the manifest permits Anchor
`^1.0.2`, Borsh `^1.5.3` and Pythnet `^3.0.0`. The applicability profiles
separate these compatibility assumptions from the exact reviewed/tested
resolutions. Only the used field decoders, enum-tag expansion and error
delegation must preserve the modeled behavior; unrelated dependency features
and operations are not constrained.

`VerificationLevel::deserialize_reader` first reads one `u8` tag, then calls
the derived `EnumExt::deserialize_variant`. The enum has no explicit
discriminants and no `use_discriminant` attribute, so the tags are 0 and 1.
Tag 0 reads one more `u8` as `Partial { num_signatures }`, and tag 1 is
`Full` with no payload. Any other tag returns `InvalidData` with the message
`Unexpected variant tag: {tag:?}`, after the tag byte has been consumed. A
`u8` prints in decimal, for example "Unexpected variant tag: 2". The model
writes the at most three digits out explicitly (`decimalU8`), so that proofs
can evaluate the message; the `Nat.repr` of core does not unfold in these modules.

`PriceFeedMessage` is defined in pythnet-sdk 3.0.0 (messages.rs line 91).
pyth-solana-receiver-sdk enables the `solana-program` feature of pythnet-sdk, which
selects the Anchor derives at line 86. The derived decoder reads `feed_id` as
`[u8; 32]`, then `price: i64`, `conf: u64`, `exponent: i32`,
`publish_time: i64`, `prev_publish_time: i64`, `ema_price: i64` and
`ema_conf: u64`, all little-endian. This decoder is pythnet-sdk code, so its
model is in `Solanalib.Specs.PythnetSdk`. The `PriceUpdateV2` model
calls that model, just as it calls the Address and Borsh models. A decoding
error inside the message keeps the error of that model. A complete Full update has
125 bytes and a Partial one 126 bytes.
Together with the 8-byte discriminator, this matches `LEN = 134` (line 59) for
the larger form.

`#[account]` also generates the `Discriminator::DISCRIMINATOR` constant, the
first eight bytes of SHA-256 over `account:PriceUpdateV2` (anchor-syn 1.0.2
`sighash`), which is `[34, 241, 35, 99, 157, 126, 244, 205]`, and
`AccountDeserialize::try_deserialize`. Neither is modeled: the constant is
inlined by compiler constant evaluation, and a client that compares the first eight
bytes itself and then calls the default `deserialize` of Borsh on the remaining
bytes needs only the decoder. Such a comparison and its error belong to the
client. The theorem `deserialize_forwards` shows that
the Borsh 1.6.1 default `deserialize`, at this decoder, returns exactly the outcome of the
decoder.

Decoding checks only the encoding. It does not check the account owner, the
write authority, the guardian signatures or freshness, and a decoded
verification level is only data. Tests cover every proper prefix of an
update and of a message, a wrong tag (with the exact message for tags 2 and
255), both verification forms, field order (swapping the authority and feed
identifier, or the price and confidence, changes the result), trailing bytes
left unread, and a decoded update passed to the price getter.

| Package | Immutable source | Anchors |
| --- | --- | --- |
| pyth-solana-receiver-sdk 2.0.0 | [price_update.rs](https://github.com/pyth-network/pyth-crosschain/blob/4099cb15d0943e603bdc6ad12aecbd2b6eb0f2c0/target_chains/solana/pyth_solana_receiver_sdk/src/price_update.rs#L49) | Enum derive 18; enum 19; `#[account]` 49; struct 51; `LEN` 59 |
| pythnet-sdk 3.0.0 | [messages.rs](https://github.com/pyth-network/pyth-crosschain/blob/4099cb15d0943e603bdc6ad12aecbd2b6eb0f2c0/pythnet/pythnet_sdk/src/messages.rs#L84) | Anchor derive 86; struct 91; fields 93–113 |
| Borsh-derive 1.6.1 | [enums (de)](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh-derive/src/internals/deserialize/enums/mod.rs#L39) | Tag read 39–40; variant chain 21–23; unknown tag 52–55 |
