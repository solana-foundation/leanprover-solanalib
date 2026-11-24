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

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:a1872d017fc9df3f -->
<a id="review-a1872d017fc9df3f"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The published Pyth receiver 2.0.0 reference first checks verification dominance, then feed identity, then the maximum-age conversion that panics beyond i64 MAX. It performs signed saturating addition and an inclusive freshness comparison, and returns exactly the source Price fields. Both panic strategies and the framed state are explicit. The verification field is data, not a signature-validity assumption. The generated Borsh decoders read write_authority (Address 2.6.0 model), verification_level (u8 tag 0 with a u8 count, tag 1, other tags InvalidData "Unexpected variant tag: n" after the tag), price_message (pythnet-sdk 3.0.0 model) and posted_slot (u64) in declaration order; the Borsh 1.6.1 default deserialize forwards the outcome of that decoder.
<!-- /registry -->

<!-- registry:review:7af989a61b051e6d -->
<a id="review-7af989a61b051e6d"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

pythnet-sdk 3.0.0 with feature solana-program derives AnchorDeserialize, which anchor-derive-serde 1.0.2 re-emits as Borsh-derive 1.6.1 BorshDeserialize, for PriceFeedMessage. The decoder reads feed_id ([u8; 32]), price (i64), conf (u64), exponent (i32), publish_time, prev_publish_time, ema_price (i64) and ema_conf (u64) in declaration order with the Borsh 1.6.1 decoders; the first error is returned unchanged.
<!-- /registry -->

<!-- registry:review:568403ef2efa5912 -->
<a id="review-568403ef2efa5912"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The model for the Solana source branch submits curve ID 0, exactly 32 point bytes and an output byte initialized to 0. It returns the Boolean test status = 0, independently of the output scratch byte. The callback mapper retains each returned/unwound state and terminal reason. primitiveReply_status relates the status to the existing canonical Edwards primitive predicate; no host decompression path is substituted.
<!-- /registry -->

<!-- registry:review:c7417a1e9610d378 -->
<a id="review-c7417a1e9610d378"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Select target_os=solana or the distinct host override and forward the complete bytes with the u64 length cast of the Solana branch. The raw family has precondition True and preserves all provider outcomes. length_exact separately proves cast exactness under its bound; canonical runtime size and program-tag behavior remain separately interpreted.

Versioned public aggregate of the reviewed mathematical models.

Instantiate the shared mathematical operations for this exact SDK version; keep closed reference, precondition and execution witnesses in the public version namespace.

The signature families retain concrete source preparation and canonical Agave CPI stages. Borrowed and owned stable-instruction contracts are separate; checked signatures use the first matching AccountInfo and the shared lease world. C and Rust raw declarations share the runtime family but require distinct pointer-layout interpretations. Closed consistency witnesses use declared mock callee results only.

The selected AccountInfo functions reuse the identified Borrow/AccountInfo/Rc world. Reflexive AsRef preserves the existing source reference; lamports acquisition returns typed current guards; scalar/boolean getters preserve temporary lifecycle and errors. Owner assignment updates shared owner storage. Resize/realloc preserve original-length accounting, complete backing bytes, shared serialized/local lengths, source error order and guard cleanup, with termination at a reached zeroing syscall. Generic preservation/progress and exact output-length lemmas and closed reference witnesses are mathematical evidence under their stated premises. Exact versions and defining Rust identities, including legacy solana_program paths, are reviewed individually.

The shared families preserve exact value bytes, source guard and seed order, destination initialization, profile-specific error conversion, and actual callback state and exits. Version wrappers retain their complete family and source-dependent reader error kind. The source review is detailed in source-notes/address-profiles.md.

This source module instantiates the shared SDK value family and closed witnesses at the exact source identities registered here. Imports do not add whole-crate coverage.

The legacy SDK log function forwards UTF-8 bytes and byte length to sol_log_ on Solana; on the host it calls the installed program_stubs implementation, which is replaceable and is not identified with stdout. The compute-unit logger calls sol_log_compute_units_ with no integer return or the corresponding host stub. Exact sink effects and finite abnormal exits are retained.

Consumes a Copy Hash value and returns exactly its stored 32-byte array. The mathematical value-copy contract is unchanged; source ownership differs from the borrowed newer receiver.

The macro initializes the actual typed destination with Default, calls the Solana typed syscall or the selected replaceable host stub and returns that current value for status 0. It converts each nonzero status with ProgramError::from(u64), preserving exact builtin matching and unknown-status low-word truncation. Borsh tag 15 returns BorshIoError("Unknown"). The 1.15.2 table ends at tag 21; 1.18.26 at tag 24; program-error 2.2.2 at tag 26. No nonzero status is folded to UnsupportedSysvar in these profiles. The exact Borsh tag reaches an explicit literal-copy provider after the typed read. Its returned OwnedError retains a live String resource; StringReady for reached normal copies proves freshness at the post-read state and exact current contents "Unknown". ownedPost and the nonempty closed witness retain ordinary allocation effects. fromStatus remains a separate value facet; no error-buffer ownership is inferred from it.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Legacy stake values share the exact field vocabulary without the later StakeFlags variant. Instruction plans and resource lifetimes follow the selected constructor source. Pack is a callback family and WriteCounter is a serializer state machine, preserving generic effects and cleanup rather than treating them as pure decoders. Lookup decoding models the complete fixed bincode boundary and exact borrowed suffix. Closed references and witnesses are mathematical facts under the stated source interfaces. ALT normal error paths retain bincode Box<ErrorKind> allocation and map_err destruction in the indexed state; its pure decoder remains a value facet.

The added source-owned Program function families preserve the entire corresponding mathematical contracts and references. Exact source API/profile redirects retain the original runtime, provider, representation, arithmetic and panic conditions; all inherited foreign-library API/profile rows remain unchanged. Raw CPI stays opaque and retains its separate runtime and source-memory obligations.

The reviewed derived Instruction Clone fields have program ID, Vec<AccountMeta>, Vec<u8> in that order. Primitive clones preserve exact order/duplicates and data; failure while cloning bytes drops only newly cloned accounts. Original vectors are borrowed, not consumed. Vec source layouts and allocator/cleanup correspondence remain separate; complete provider outcomes and useful exact-current laws are retained.

The complete query uses arbitrary public schedule fields. firstSlot selects epoch <= first_normal_epoch, truncates epoch to u32 before saturating_pow, then saturating-subtracts 1 and multiplies by 32. Its other branch subtracts first_normal_epoch, multiplies slots_per_epoch and adds first_normal_slot with saturation. lastSlot calls firstSlot, adds get_slots_in_epoch with saturation and subtracts 1; warmup slots use a separate strict < test and saturating u32 exponent addition by 5. No schedule invariant or warmup-flag premise is imposed.
<!-- /registry -->

<!-- registry:review:63d53cfa0f1566df -->
<a id="review-63d53cfa0f1566df"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

COption::is_some matches only the enum variant. A closed Family quantifies every payload type, including uninhabited types, without payload movement, cloning or an inhabitance premise. The model makes no C-layout claim.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

This source module instantiates the shared SDK value family and closed witnesses at the exact source identities registered here. Imports do not add whole-crate coverage.
<!-- /registry -->

<!-- registry:review:13e3e9536693e1bc -->
<a id="review-13e3e9536693e1bc"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The SDK declaration invokes the pinned address macro with the Base58 system key. The macro yields the same canonical 32-zero-byte Solanalib.Runtime.Ids.systemProgram. The returned value and state frame are computed, with an exact byte-level test. The compiler macro-provider span is not treated as the defining crate version.

This source module instantiates the shared SDK value family and closed witnesses at the exact source identities registered here. Imports do not add whole-crate coverage.
<!-- /registry -->

<!-- registry:review:e2728ac84eea4607 -->
<a id="review-e2728ac84eea4607"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The eight-byte U64 macro instantiation converts with u64::from_le_bytes. The model uses an exact-length byte input, the canonical little-endian decoder and UInt64 bounds. Its general bound and encode/decode round-trip proofs establish mathematical value correspondence, without assuming native u64 alignment.

In every listed release, U64 is repr(transparent) over [u8; 8], and impl_int_conversion!(U64, u64) implements From<U64> for u64 with u64::from_le_bytes(unaligned.0). The type, conversion body and little-endian interpretation are unchanged. Added arithmetic methods and derives are not used by this conversion. All versions share the entire original bounded-value contract; Rust core conversion and legal read correspondence remain separate obligations. Release 1.1.0 is yanked, but its published source was also checked. Other unaligned operations and versions outside this window have not been assessed.

This source module instantiates the shared SDK value family and closed witnesses at the exact source identities registered here. Imports do not add whole-crate coverage.
<!-- /registry -->

<!-- registry:review:3a86962caedde554 -->
<a id="review-3a86962caedde554"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The parser consumes an existing AccountInfo guard; its Rust argument interpretation supplies shared mode. It checks discriminator length, discriminator bytes, complete payload extent, sliced extent and actual payload alignment in source order. Both 8-byte and 16-byte i128 layout choices have size 3200. The selected bytemuck1.25.0 helper checks size before alignment; its repeated successful cast has no intervening mutation. Error releases exactly the input lease; success transfers its generation to the payload range without adding a lease or changing cells. General progress and cell-frame lemmas cover every admitted input. The contract additionally guarantees the final borrow-state invariant and retirement of the input guard generation, using the Ready premise in its reference proof.
<!-- /registry -->

<!-- registry:review:548e308d9bfc9219 -->
<a id="review-548e308d9bfc9219"></a>

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Exact Base58 literals were decoded to 32-byte constants and compared with direct native id/check_id calls. Each mathematical function is a state-preserving constant copy or full equality; no allocation, hashing or syscall is introduced.
<!-- /registry -->

<!-- registry:review:b7fe6d3dfab05a86 -->
<a id="review-b7fe6d3dfab05a86"></a>

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Account::is_frozen compares only its valid AccountState enum against Frozen. It neither invokes Pack nor requires initialization; Uninitialized is a valid receiver and returns false. Other account fields and the receiver remain unchanged. The concrete derived Default calls the default constructors for OptionalNonZeroPubkey, Pubkey, three String fields and Vec<(String,String)>. Both keys are zero and all containers are empty with zero capacity; constructing them needs no heap allocation or user callback. The mathematical value postcondition contains the six actual fields without imposing the documented additional-key uniqueness convention. A Rust binding must supply real owned empty container representations separately.

For any program ID, retain four metas in source order: writable metadata, readonly update authority, readonly mint and readonly signer mint authority. Allocate metadata first; build discriminator-prefixed bytes, serialize the three actual current String owners, append then destroy the temporary vector, and finally destroy input strings after constructing the return place. UTF-8 byte lengths are u32 little endian. Returned output is Instruction directly; unwrap, allocation and destructor unwind/terminal outcomes are retained. The closed witness executes every allocation/append/drop and leaves only the constructed Instruction owners. Serialization reads live owners at its actual callback state, rather than a saved pre-allocation text snapshot.
<!-- /registry -->

<!-- registry:review:90ece16362c5466e -->
<a id="review-90ece16362c5466e"></a>

This source module instantiates the shared SDK value family and closed witnesses at the exact source identities registered here. Imports do not add whole-crate coverage.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.
<!-- /registry -->

<!-- registry:review:29c3df036102ffee -->
<a id="review-29c3df036102ffee"></a>

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

The shared families preserve exact value bytes, source guard and seed order, destination initialization, profile-specific error conversion, and actual callback state and exits. Version wrappers retain their complete family and source-dependent reader error kind. The source review is detailed in source-notes/address-profiles.md.
<!-- /registry -->

<!-- registry:review:eb99249d6ff6ae2a -->
<a id="review-eb99249d6ff6ae2a"></a>

The complete query uses arbitrary public schedule fields. firstSlot selects epoch <= first_normal_epoch, truncates epoch to u32 before saturating_pow, then saturating-subtracts 1 and multiplies by 32. Its other branch subtracts first_normal_epoch, multiplies slots_per_epoch and adds first_normal_slot with saturation. lastSlot calls firstSlot, adds get_slots_in_epoch with saturation and subtracts 1; warmup slots use a separate strict < test and saturating u32 exponent addition by 5. No schedule invariant or warmup-flag premise is imposed.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.
<!-- /registry -->

<!-- registry:review:15f03ca788d4712c -->
<a id="review-15f03ca788d4712c"></a>

In every listed release, U64 is repr(transparent) over [u8; 8], and impl_int_conversion!(U64, u64) implements From<U64> for u64 with u64::from_le_bytes(unaligned.0). The type, conversion body and little-endian interpretation are unchanged. Added arithmetic methods and derives are not used by this conversion. All versions share the entire original bounded-value contract; Rust core conversion and legal read correspondence remain separate obligations. Release 1.1.0 is yanked, but its published source was also checked. Other unaligned operations and versions outside this window have not been assessed.
<!-- /registry -->

<!-- registry:review:6f9ccd58c30b3efe -->
<a id="review-6f9ccd58c30b3efe"></a>

Reference: receiver 2.0.0, Anchor and macros 1.0.2, Borsh and derive 1.6.1, Pythnet 3.0.0. The declared registry ranges assume preservation of this decoder contract at the used field types, including exact errors; SemVer is compatibility evidence, not a proof of those details. Receiver Cargo requirements allow Anchor ^1.0.2, Borsh ^1.5.3 and Pythnet ^3.0.0. Pyth PriceUpdateV2 decodes write_authority [u8; 32], VerificationLevel (one or two bytes), the complete 84-byte PriceFeedMessage and posted_slot u64 in order. It returns all fields and the exact suffix, stops at the first field error, and neither consumes nor checks an account discriminator. The published 2.0.0 reference provides the current InvalidData and variant-tag diagnostics; the complete Pyth operation includes the behavior of its reached field readers. Published 1.2.0 uses an Anchor 0.32/Borsh 0.10 dependency graph that produces observably different errors. Older published 1.x pins Anchor 0.x; 0.x has BorshSchema coupling to the Pythnet 0.10 schema despite its broad Anchor constraint. All malformed-input and error-order behavior is retained. Diagnostic error allocations fall under the shared scope boundary and impose no extra Pyth caller premise. Pyth-generated VerificationLevel and PriceUpdateV2 readers; AnchorDeserialize re-emits BorshDeserialize through Anchor 1.0.2 with derive/account macros 1.0.2 and Borsh/derive 1.6.1.
<!-- /registry -->

<!-- registry:review:b27a9726da79cdd4 -->
<a id="review-b27a9726da79cdd4"></a>

All 14 published versions have the same getter, verification ordering, unchecked feed lookup, output fields and relevant integer expressions. The order is insufficient verification, mismatched feed, fallible u64-to-i64 age conversion (panic at age >= 2^63), then signed saturating publish_time + age with an inclusive freshness comparison. Full dominates every level; Partial compares signature counts and cannot satisfy Full. Future publication times are accepted. Added unused error variants and formatting/attributes do not change these branches, and all unreturned update/message/clock observations are framed. This source correspondence does not create a registered callable binding for a different published version.
<!-- /registry -->

<!-- registry:review:44d5d11edded22b9 -->
<a id="review-44d5d11edded22b9"></a>

Reference: receiver 2.0.0, Anchor and macros 1.0.2, Borsh and derive 1.6.1, Pythnet 3.0.0. The declared registry ranges assume preservation of this decoder contract at the used field types, including exact errors; SemVer is compatibility evidence, not a proof of those details. Receiver Cargo requirements allow Anchor ^1.0.2, Borsh ^1.5.3 and Pythnet ^3.0.0. Pyth VerificationLevel reads a u8 tag: 0 reads a further u8 signature count and returns Partial; 1 returns Full without reading a count; all other tags return InvalidData with Unexpected variant tag: N, rendering N in decimal. Truncation returns InvalidData / Unexpected length of input. The published 2.0.0 reference has exactly this Pyth behavior through its reviewed Anchor/Borsh derives, including field/error order and success remainder. Every tag byte was exercised by the retained ordinary tests. The 13 older publications have the 0.10-based Pyth profile: InvalidInput on truncation and Unexpected variant index: N for an unknown tag. Receiver 0.x retains BorshSchema coupling to the 0.10 schema of Pythnet despite a broad Anchor bound, and published 1.x pins Anchor 0.x. The source distinctions determine the released-version partition; diagnostic-allocation failure remains outside the shared model boundary. Pyth-generated VerificationLevel and PriceUpdateV2 readers; AnchorDeserialize re-emits BorshDeserialize through Anchor 1.0.2 with derive/account macros 1.0.2 and Borsh/derive 1.6.1.
<!-- /registry -->

<!-- registry:review:dce2d2cc949e6cf7 -->
<a id="review-dce2d2cc949e6cf7"></a>

All six published Pythnet messages have the same ordered fields and 84-byte encoding: feed ID [u8; 32], price i64, confidence u64, exponent i32, publish time i64, previous publish time i64, EMA price i64 and EMA confidence u64. The reviewed Pyth implementations read those fields in order, stop at the first error and return the exact suffix on success. Under the shared error-construction boundary, the 2.3.0/2.3.1 solana-program profiles and 3.0.0 direct/matched-Anchor profiles provide the modeled InvalidData / Unexpected length of input diagnostics. The Anchor derive routes explicitly to anchor_lang::prelude::borsh, so the independent 0.10 schema dependency does not determine the selected reader. The default 2.3.x reader and the 2.0.0 reader instead return InvalidInput; this is an observable Pyth API difference. Versions 2.1.0/2.2.0 add optional Anchor but pin proc-macro2 = 1.0.79, preventing the reviewed Anchor 1.0.2 profile; 2.1.0 records the exact attempted resolver conflict. Their older buildable profile remains incompatible. Diagnostic-allocation failure lies outside the shared model boundary and does not exclude a version from this partition. Pyth PriceFeedMessage uses AnchorDeserialize; effective Anchor is 1.0.2, anchor-derive-serde is 1.2.2, and the emitted reader uses the Borsh/derive 1.8.1 of Anchor. Direct Borsh 0.10.4 supplies the independent schema trait, not this reader.
<!-- /registry -->

<!-- registry:review:32c21966f5d1da6e -->
<a id="review-32c21966f5d1da6e"></a>

Reference: Pythnet 3.0.0, with the recorded direct/Anchor derive selections. Declared registry ranges assume preservation of the 84-byte field encoding, success suffix and exact Borsh 1 errors. The solana-program branch remains explicit. All six published Pythnet messages have the same ordered fields and 84-byte encoding: feed ID [u8; 32], price i64, confidence u64, exponent i32, publish time i64, previous publish time i64, EMA price i64 and EMA confidence u64. The reviewed Pyth implementations read those fields in order, stop at the first error and return the exact suffix on success. Under the shared error-construction boundary, the 2.3.0/2.3.1 solana-program profiles and 3.0.0 direct/matched-Anchor profiles provide the modeled InvalidData / Unexpected length of input diagnostics. The Anchor derive routes explicitly to anchor_lang::prelude::borsh, so the independent 0.10 schema dependency does not determine the selected reader. The default 2.3.x reader and the 2.0.0 reader instead return InvalidInput; this is an observable Pyth API difference. Versions 2.1.0/2.2.0 add optional Anchor but pin proc-macro2 = 1.0.79, preventing the reviewed Anchor 1.0.2 profile; 2.1.0 records the exact attempted resolver conflict. Their older buildable profile remains incompatible. Diagnostic-allocation failure lies outside the shared model boundary and does not exclude a version from this partition. Pyth PriceFeedMessage derives its direct Borsh/derive 1.6.1 reader; solana-program is disabled.
<!-- /registry -->

<!-- registry:review:2a2cef78c5b5051e -->
<a id="review-2a2cef78c5b5051e"></a>

Reference: Pythnet 3.0.0, with the recorded direct/Anchor derive selections. Declared registry ranges assume preservation of the 84-byte field encoding, success suffix and exact Borsh 1 errors. The solana-program branch remains explicit. All six published Pythnet messages have the same ordered fields and 84-byte encoding: feed ID [u8; 32], price i64, confidence u64, exponent i32, publish time i64, previous publish time i64, EMA price i64 and EMA confidence u64. The reviewed Pyth implementations read those fields in order, stop at the first error and return the exact suffix on success. Under the shared error-construction boundary, the 2.3.0/2.3.1 solana-program profiles and 3.0.0 direct/matched-Anchor profiles provide the modeled InvalidData / Unexpected length of input diagnostics. The Anchor derive routes explicitly to anchor_lang::prelude::borsh, so the independent 0.10 schema dependency does not determine the selected reader. The default 2.3.x reader and the 2.0.0 reader instead return InvalidInput; this is an observable Pyth API difference. Versions 2.1.0/2.2.0 add optional Anchor but pin proc-macro2 = 1.0.79, preventing the reviewed Anchor 1.0.2 profile; 2.1.0 records the exact attempted resolver conflict. Their older buildable profile remains incompatible. Diagnostic-allocation failure lies outside the shared model boundary and does not exclude a version from this partition. Pyth PriceFeedMessage uses the receiver 2.0.0 dependency graph: Anchor and derive/account macros 1.0.2, Borsh/derive 1.6.1. This is the exact retained native-to-Lean profile.
<!-- /registry -->

<!-- registry:review:40d75bf97cd7d988 -->
<a id="review-40d75bf97cd7d988"></a>

All 110 real stable releases use transparent PodEdwardsPoint([u8;32]), selector CURVE25519_EDWARDS=0, a non-null one-byte scratch initialized to zero, and return whether the syscall register equals zero while ignoring final scratch. 2.0/2.1 reach exact matching solana-program versions; every one of these 45 dependency archives has the same selected declaration/cfg closure within its generation. 2.2+ reach solana-define-syscall; all admitted 2.x/3.x/5.x declarations and macro generations preserve the argument/result transport, with dynamic versus static dispatch remaining the provider binding. No callback effects or finite exits are replaced by host curve validity. 0.0.0 is a placeholder without this API.
<!-- /registry -->

<!-- registry:review:62ddac5388ea8b4e -->
<a id="review-62ddac5388ea8b4e"></a>

Every one of the 26 nonplaceholder releases has the same impl<T> method taking &self and matching Some(_) versus None. There is no Copy, Clone or Drop constraint on T and the wildcard pattern does not move, clone or drop the payload. The indexed logical representation covers every source payload type, including an uninhabited payload in None. Native checks execute all 26 releases with the existing four-type value corpus and additional String-owning, non-Copy drop-counted payload checks. This establishes source correspondence and native samples; it does not assert a physical COption layout theorem.
<!-- /registry -->

<!-- registry:review:d622a3916362dca2 -->
<a id="review-d622a3916362dca2"></a>

The API is absent in the same 91 early solana-program releases as set_return_data. The same 92 releases use target_arch=bpf and disagree with the existing OS-based target binding. The 183 compatible releases have one byte-identical top-level body: target_os=solana passes the nested slice descriptor pointer and field count to crate::syscalls::sol_log_data; other targets pass the borrowed nested slice to the actual host stub. The reached re-exports, syscall declarations and macro selection were reviewed, including local program definitions, the split define-syscall macro and later direct re-exports. Empty fields, repeated fields and field boundaries are preserved. Rendering, base64, memory translation, resource costs and provider exits remain in the supplied sink; flattening is only a coarse projection.
<!-- /registry -->

<!-- registry:review:2a102b773c791d69 -->
<a id="review-2a102b773c791d69"></a>

The 91 releases through 1.8.0 have no public helper. The 92 published releases in 1.8.1 through 1.10.41 and in 1.13.0 through 1.13.7 select by target_arch=bpf, which disagrees with the existing target_os=solana binding. The ten published 1.11.x releases and all published 1.14.0 through 5.2.0 releases, 183 in total, select by target_os=solana. The first 154 compatible releases directly pass the slice pointer and length-as-u64 to the syscall; the remaining 29, starting at 2.1.0, call solana_cpi::set_return_data on Solana. Every real reviewed solana-cpi release retains that same pointer/length forwarding helper. The non-Solana branch retains the separately overridable solana-program host stub. No compatible wrapper truncates, validates, or limits length to 1024. The source includes a genuine 1.13.x cfg regression, so an endpoint interval would be wrong. Pointer representation and all actual provider finite outcomes and state effects remain explicit source/provider obligations.
<!-- /registry -->

<!-- registry:review:6dd40202dd300385 -->
<a id="review-6dd40202dd300385"></a>

Each of the six real SDK IDs releases declares the system program using exactly 32 base58 ones. Through 3.0.0 the invocation uses solana_pubkey::declare_id!; 3.1.0 uses solana_address::declare_id!. The review follows the Pubkey 2.x macros and const decoder, Pubkey 3.0.0 re-exports through Address 1.x, Address 1.1.0 re-exports through 2.x, and all relevant Address 2.x macros and constant decoders. The decode closure maps each base58 one to digit zero, all accumulation stays zero, and the 32 leading-zero characters produce exactly 32 zero bytes. Host id returns ID; the Address BPF branch re-evaluates the same constant literal and yields the same value. The changes in wrapper type, const versus static ID and macro expansion do not change the interpreted canonical address. Physical Rust type identity and compiled macro correspondence remain separate.
<!-- /registry -->

<!-- registry:review:d97b65f4ae11d782 -->
<a id="review-d97b65f4ae11d782"></a>

All six archives declare transparent U64([u8;8]) and expand the same From<U64> for u64 body, Self::from_le_bytes(unaligned.0). Macro additions in 1.1.0/1.1.1 affect other operations and compile-time layout assertions, not this call closure. Optional serialization/bytemuck/wincode derives do not branch the conversion. The mathematical contract does not require a physical alignment hypothesis.
<!-- /registry -->

<!-- registry:review:bc4114fe79581f5d -->
<a id="review-bc4114fe79581f5d"></a>

The checked Ref<&mut [u8]> parser appears in 0.7.0 and its body is identical through 0.13.0 (26 stable releases). It rejects missing or wrong discriminator [196, 27, 108, 196, 10, 215, 219, 40] before short total length, then checks a 3200-byte payload with bytemuck::try_from_bytes before Ref::map/from_bytes. Exact failure order is discriminator, size, alignment. Successful mapping returns the original payload address + 8 and bytes without allocation while transferring the existing shared lease; errors retire the input lease and preserve an independent sibling. All 26 payload layouts are 3200 bytes for both supported i128 alignments; the 0.11.2 padding-byte-to-permit_write_by_authority change preserves every parser-observed byte and offset. 0.1.0-0.1.2 instead accept AccountInfo and acquire a borrow, 0.1.3 accepts Ref<[u8]>, and the later pre-0.7.0 parser panics after a valid discriminator on short or misaligned data. 0.1.11 has no PullFeedAccountData::parse at all. No precondition is strengthened to discard the old panic cases.
<!-- /registry -->

<!-- registry:review:2fdf544ec5043063 -->
<a id="review-2fdf544ec5043063"></a>

This exact Git source has the same pull_feed.rs and error.rs as crates.io 0.12.1. Its Cargo differences do not affect parse or its bytemuck helpers. The existing parser contract and separate representation obligations apply; see source-notes/other-sdk-functions.md#switchboard-feed-parsing.
<!-- /registry -->

<!-- registry:review:a927e286624546c2 -->
<a id="review-a927e286624546c2"></a>

Reference: solana-address-lookup-table-interface 2.2.2. Compatibility in [2.2.2, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the complete reached bincode decoder, owned-error cleanup and bytemuck/Pubkey representation: decode ProgramState first, destroy the owned error before InvalidAccountData, retain Uninitialized precedence, None/Some serialized metadata lengths 24/56 and trailing-byte/padding behavior, then borrow the entire suffix at byte offset 56 as complete 32-byte alignment-1 Pubkeys. Retain the original allocation/provenance/lifetime and Cow::Borrowed representation, without an address-storage allocation, 256-address limit or liveness check. Reached Box<ErrorKind>/diagnostic allocation and destruction, source-normal cleanup, external effects and the recorded allocation-failure boundary must remain the same; generic destructor-unwind witnesses do not claim that GlobalAlloc unwinds.
<!-- /registry -->

<!-- registry:review:7044a4f56239cb54 -->
<a id="review-7044a4f56239cb54"></a>

Reference: solana-program 2.3.0. The declared [2.3.0, 3.0.0) range assumes preservation of the ordered first-match RefCell preflight and Solana-target delegation of the checked wrapper to solana-cpi::invoke_signed_unchecked. Its storage provider clones the complete Instruction into a fresh owner, transfers its vectors into StableInstruction and destroys that owner after successful opaque CPI. Clone order, allocator state, ownership transfer, cleanup effects and terminal outcomes remain explicit; allocation success is not assumed. Borrowed-buffer invocation and replaceable host stubs retain separate contracts/profiles.
<!-- /registry -->

<!-- registry:review:485c27a125510883 -->
<a id="review-485c27a125510883"></a>

The inspected 2.2.1/2.3.0 wrappers delegate to the owned-clone CPI path. This incoming range assumes first-match lamports/data preflight, ordered signer forwarding, Instruction clone/StableInstruction ownership and post-success destruction. Local borrow failure remains an ordinary error; runtime failure remains terminal and CPI opaque. Existing 2.3.0 invoke_signed profiles retain their own ranges.
<!-- /registry -->

<!-- registry:review:8c11113beacf3b60 -->
<a id="review-8c11113beacf3b60"></a>

Reference source: solana-program 1.18.26. Probe the first matching AccountInfo for each meta, lamports before data, and release each temporary guard. Then clone Instruction into an owned StableInstruction before opaque signed invocation and destroy it after success. Retain local borrow errors, allocator state, source decoding/copyback and terminal outcomes. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:23e53b8d2ab57366 -->
<a id="review-23e53b8d2ab57366"></a>

Return None or the payload reference of the same parent, without a new owner or guard. The 2.1.0, 2.2.0 and 2.2.1 files are identical. Compatibility within 2.x assumes the same discriminants, callbacks and reached cleanup; concrete key/bool variants retain their gates.
<!-- /registry -->

<!-- registry:review:c3beeee4518fed92 -->
<a id="review-c3beeee4518fed92"></a>

Negate is_some without moving or destroying the payload. The 2.1.0, 2.2.0 and 2.2.1 files are identical. Compatibility within 2.x assumes the same discriminants, callbacks and reached cleanup; concrete key/bool variants retain their gates.
<!-- /registry -->

<!-- registry:review:ee8cbe7e3eff7393 -->
<a id="review-ee8cbe7e3eff7393"></a>

Some moves closure and payload into FnOnce and forwards every exit; None drops the unused closure before returning None. The 2.1.0, 2.2.0 and 2.2.1 files are identical. Compatibility within 2.x assumes the same discriminants, callbacks and reached cleanup; concrete key/bool variants retain their gates.
<!-- /registry -->

<!-- registry:review:ee3ee1f7ecae914c -->
<a id="review-ee3ee1f7ecae914c"></a>

None moves the evaluated fallback; Some drops that fallback before returning the original payload. Preserve unwind/terminal outcomes and the selected moved-return cleanup policy. The 2.1.0, 2.2.0 and 2.2.1 files are identical. Compatibility within 2.x assumes the same discriminants, callbacks and reached cleanup; concrete key/bool variants retain their gates.
<!-- /registry -->

<!-- registry:review:5d1f888e8622a468 -->
<a id="review-5d1f888e8622a468"></a>

The 6.0.0 reference returns the declared Memo program key without allocation, derivation or state change. Compatibility within 6.x assumes the same macro-generated value operation and selected defining Pubkey representation. The two exact Pubkey dependency variants and production target gates remain distinct.
<!-- /registry -->

<!-- registry:review:0aa95830ee2443fb -->
<a id="review-0aa95830ee2443fb"></a>

The 0.7.0 reference allocates four ordered metas before discriminator-prefixed Borsh data, serializes the three current UTF-8 String owners, then appends/destroys the temporary and input owners. Compatibility within 0.7 assumes these bytes, field order and all reached unwrap/cleanup exits remain unchanged under the exact dependency variants.
<!-- /registry -->

<!-- registry:review:37bd4f6f60522e35 -->
<a id="review-37bd4f6f60522e35"></a>

The 0.7.0 derived default contains two zero keys, three empty Strings and an empty Vec of pairs, without allocation or a uniqueness precondition. Compatibility within 0.7 assumes these six fields and empty-container representations remain unchanged under the selected dependencies.
<!-- /registry -->

<!-- registry:review:95da390aa988b6c1 -->
<a id="review-95da390aa988b6c1"></a>

The inspected 0.5.0/0.5.1 integer-conversion macro is identical. The declared 0.5 range assumes unsigned little-endian decoding of the complete eight stored bytes, unchanged source state and the same primitive result; later reexported defining items are not inferred.
<!-- /registry -->

<!-- registry:review:2387a17d47ea4ad5 -->
<a id="review-2387a17d47ea4ad5"></a>

The inspected 0.5.0/0.5.1 integer-conversion macro is identical. The declared 0.5 range assumes unsigned little-endian decoding of the complete two stored bytes, unchanged source state and the same primitive result; later reexported defining items are not inferred.
<!-- /registry -->

<!-- registry:review:d635aa0cd598fa81 -->
<a id="review-d635aa0cd598fa81"></a>

The declared compatible range assumes consumption of the two stored bytes and little-endian u16 decoding, with unchanged ambient state and no alignment, allocation or callback requirement.
<!-- /registry -->

<!-- registry:review:a2d067cf51f89b01 -->
<a id="review-a2d067cf51f89b01"></a>

Decode the exact two bytes as little-endian u16; every byte pattern is admitted, independent of source pointer alignment. Keep the exact source item and provider gates. The source reference remains 1.0.1; the interval is a separate preservation assumption. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:f0dceb56dc5ecb35 -->
<a id="review-f0dceb56dc5ecb35"></a>

The declared compatible range assumes discriminant comparison before invoking payload PartialEq only for two Some values. Preserve the original left/right borrowed payloads, callback state and every finite exit.
<!-- /registry -->

<!-- registry:review:949fed1e1d300395 -->
<a id="review-949fed1e1d300395"></a>

The declared compatible range assumes discriminant comparison before invoking payload PartialEq only for two Some values. Preserve the original left/right borrowed payloads, callback state and every finite exit. The concrete key interpretation retains the exact Address identities of the selected concrete payload profile; generic-family applicability is unchanged.
<!-- /registry -->

<!-- registry:review:f55cba8211b26530 -->
<a id="review-f55cba8211b26530"></a>

The declared compatible range assumes movement of a Some payload unchanged and invocation of the nonreturning panic provider with the exact None diagnostic. None remains admitted; its actual unwind or terminal behavior is not hidden by a precondition.
<!-- /registry -->

<!-- registry:review:670bd1fbc57b0a42 -->
<a id="review-670bd1fbc57b0a42"></a>

The declared compatible range assumes movement of a Some payload unchanged and invocation of the nonreturning panic provider with the exact None diagnostic. None remains admitted; its actual unwind or terminal behavior is not hidden by a precondition. The concrete key interpretation retains the exact Address identities of the selected concrete payload profile; generic-family applicability is unchanged. This concrete index selects panic=abort; unwinding panic remains a general-family choice.
<!-- /registry -->

<!-- registry:review:809ad2def3c50bc7 -->
<a id="review-809ad2def3c50bc7"></a>

The declared compatible range assumes return of the exact canonical 32-byte ed25519_program key from its declare_id invocation, with unchanged state; host and BPF macro branches return the same constant.
<!-- /registry -->

<!-- registry:review:104ee369e04cc255 -->
<a id="review-104ee369e04cc255"></a>

The declared compatible range assumes one PDA seed containing the complete program address and the fixed upgradeable-loader ID, the actual dependency PDA search and discarding only its returned bump. Keep MaybeUninit output obligations, reached panic state and all abnormal exits.
<!-- /registry -->

<!-- registry:review:5e7aca45b8b50771 -->
<a id="review-5e7aca45b8b50771"></a>

The declared compatible range assumes return of the exact canonical 32-byte bpf_loader_upgradeable key from its declare_id invocation, with unchanged state; host and BPF macro branches return the same constant.
<!-- /registry -->

<!-- registry:review:1a3f81796ccb2475 -->
<a id="review-1a3f81796ccb2475"></a>

Preserve the <= first-normal-epoch branch, truncating u32 cast, saturating power/subtraction/multiplication and the saturating normal-epoch formula for arbitrary public schedule fields. No schedule-consistency, warmup-flag or nonzero-length precondition is introduced. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:d153b6c8ee481a36 -->
<a id="review-d153b6c8ee481a36"></a>

Preserve the exact declared 32-byte constant, by-value result and solana-address macro-provider gate. The 3.0 source invokes the solana-pubkey provider; it is a separate nominal-source case even though the key bytes agree. Inspected provider references remain exact. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:31c138400add8692 -->
<a id="review-31c138400add8692"></a>

Preserve the infallible move: zero key becomes None and every nonzero key becomes Some unchanged. This is not TryFrom<Option<Pubkey>>, which rejects Some(zero). Keep the exact nominal Pubkey/Address provider chain and original dependency gates. Release 0.7.2 was not inspected; its inclusion in the interval relies solely on this preservation assumption. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:265452bd1e35a6f3 -->
<a id="review-265452bd1e35a6f3"></a>

Reference source: solana-program 1.18.26. Copy all owner bytes through the existing owner reference with the source volatile write, preserving the record identity and caller storage. This unsafe setter adds no owner, signer or writable validation. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:7d41cffcc64d7354 -->
<a id="review-7d41cffcc64d7354"></a>

Volatile current owner update at shared storage identity, preserving every borrow and buffer. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:07cc44d0d3f7bc9a -->
<a id="review-07cc44d0d3f7bc9a"></a>

Reference source: solana-program 1.18.26. Clone the two Rc owners in declaration order and copy the remaining metadata/references. Preserve actual alias counters, reached clone failures, first-field cleanup and distinct source-record identities. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:f5e3f073b1dcd8d7 -->
<a id="review-f5e3f073b1dcd8d7"></a>

Derived Clone retains both Rc operations, source order, aliases and dependency terminal exits. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:dc1a8b7a23704272 -->
<a id="review-dc1a8b7a23704272"></a>

Reference source: solana-program 1.18.26. Acquire the current shared data borrow, observe whether its length is zero and release that same guard. A conflicting borrow follows the selected panic policy; it is not a returned ProgramError. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:364cd5d25f68799a -->
<a id="review-364cd5d25f68799a"></a>

Reference source: solana-program 1.18.26. Acquire the current shared data borrow, return the full current slice length and release the same guard. Preserve a conflicting borrow panic and the actual data-cell identity. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:4766c4fd735ba6b3 -->
<a id="review-4766c4fd735ba6b3"></a>

Current data length with temporary shared borrow, panic and release. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:ef6ebdd460ebfc64 -->
<a id="review-ef6ebdd460ebfc64"></a>

Reference source: solana-program 1.18.26. Read the current lamports through its shared RefCell guard and release that guard before returning. Preserve alias counters and the selected panic behavior on a conflicting borrow. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:1c18d4d5a47a62b7 -->
<a id="review-1c18d4d5a47a62b7"></a>

Current lamports with temporary shared borrow, panic and release. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:da67106e78c3cbf0 -->
<a id="review-da67106e78c3cbf0"></a>

Reference source: solana-program 1.18.26. Borrow data and return early for equal length before reading the original serialized length or checking growth. Otherwise update the prefix and slice descriptor, then zero only an admitted growing suffix when requested. Preserve stale bytes and allocation geometry; replaceable host memset is excluded. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:a96a054d4842b39a -->
<a id="review-a96a054d4842b39a"></a>

Source-ordered borrow/equality/growth checks, optional zero-tail syscall, retained spare bytes and guard cleanup. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:d9b9503c647314cf -->
<a id="review-d9b9503c647314cf"></a>

Reference source: solana-program 1.18.26. Acquire one shared guard for the actual data cell, or return AccountBorrowFailed without replacing that cell. The returned guard retains its exact current range, counter and repayment obligation. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:148250830823ab57 -->
<a id="review-148250830823ab57"></a>

Checked current data guard with shared leases, aliasing and source error. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:e17ceeaf5bfff689 -->
<a id="review-e17ceeaf5bfff689"></a>

Reference source: solana-program 1.18.26. Acquire one shared guard for the actual lamports cell, or return AccountBorrowFailed without changing the cell. Preserve actual aliases, counter limits, value type and guard repayment. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:8f974308d7dcf9dc -->
<a id="review-8f974308d7dcf9dc"></a>

Reference source: solana-program 1.18.26. Acquire an exclusive guard for the actual data slice only when its borrow counter permits it. Preserve conflicts as AccountBorrowFailed and retain the current range, aliases and exclusive repayment. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:9b921faacb15d815 -->
<a id="review-9b921faacb15d815"></a>

Checked current mutable data guard with exclusive leases, aliasing and source error. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:80e2a78c17486848 -->
<a id="review-80e2a78c17486848"></a>

Reference source: solana-program 1.18.26. Use the fallible current-data borrow, return AccountBorrowFailed on conflict and otherwise read the length before releasing that same shared guard. No writable or owner check is added. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:d4562ae66bb69b10 -->
<a id="review-d4562ae66bb69b10"></a>

Checked current length with temporary shared acquisition/release and AccountBorrowFailed. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:d17dc37a2aeb489c -->
<a id="review-d17dc37a2aeb489c"></a>

Reference source: solana-program 1.18.26. Decode ProgramState first and destroy a reached owned decoder error before InvalidAccountData. Uninitialized precedes the 56-byte suffix check. Borrow the full aligned suffix as 32-byte keys; retain padding/trailing metadata and impose no 256-key or liveness check. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:41215ac316a859be -->
<a id="review-41215ac316a859be"></a>

Reference source: solana-program 1.18.26. Run the actual Borsh serializer against a fresh zero WriteCounter. Full-buffer writes count bytes, flush is inert, and only serializer success returns the count. Preserve checked-overflow panic before mutation, unchecked wrapping, error ownership and all callback effects. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:033a205164c1f1b2 -->
<a id="review-033a205164c1f1b2"></a>

Reference source: solana-program 1.18.26. Copy the entire 32-byte Hash array in order without allocation or state change. The source codec still supplies the actual complete Hash layout and initialized bytes. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:9486fba92553201c -->
<a id="review-9486fba92553201c"></a>

Reference source: solana-program 1.18.26. Pass the single input slice through hashv to the Solana SHA-256 syscall with a zero-initialized 32-byte destination. Preserve the actual reply bytes and effects; the wrapper ignores the integer return. Host hashing remains a separate path. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:c69154f996a007e8 -->
<a id="review-c69154f996a007e8"></a>

Reference source: solana-program 1.18.26. Copy the complete key and signer/writable flags without cloning an owned buffer or allocating. Preserve the actual field order and current input record. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:68d6787aa6f09fb7 -->
<a id="review-68d6787aa6f09fb7"></a>

Reference source: solana-program 1.18.26. Construct the supplied key and signer bit with writable set to true, without allocation or validation. The complete source AccountMeta layout and nominal key remain separate ABI obligations. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:cb382e4e99d6d8e6 -->
<a id="review-cb382e4e99d6d8e6"></a>

Reference source: solana-program 1.18.26. Construct the supplied key and signer bit with writable set to false, without allocation or validation. Retain the complete source AccountMeta layout and nominal key obligations. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:2c9ef26fd927cb35 -->
<a id="review-2c9ef26fd927cb35"></a>

Reference source: solana-program 1.15.2, 1.18.26. Forward the current UTF-8 bytes and byte length to sol_log_ on Solana or the installed replaceable host logging stub. Preserve actual sink effects and abnormal exits; the host stub is not identified with stdout. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:494c26d45f93635a -->
<a id="review-494c26d45f93635a"></a>

Reference source: solana-program 1.18.26. Change only the outer enum and move a Some payload unchanged. No Clone, Default, comparison or Drop callback is invoked. Preserve the C representation and the exact nominal payload obligation of the concrete-key companion separately from this generic value fact. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:e76d35325b059dc6 -->
<a id="review-e76d35325b059dc6"></a>

Reference source: solana-program 1.15.2, 1.18.26. Return the same initialized 32-byte key array as a borrowed byte slice, retaining its actual provenance and lifetime. No copy, allocation or new owner is implied by the value observation. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:91de7bdfd81b75bb -->
<a id="review-91de7bdfd81b75bb"></a>

Reference source: solana-program 1.15.2, 1.18.26. Copy all 32 Pubkey bytes without allocation, callback or state change. Exact nominal source identity and the complete emitted key layout remain separate from byte equality. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:2e6e69c1dd5d63e1 -->
<a id="review-2e6e69c1dd5d63e1"></a>

Reference source: solana-program 1.15.2, 1.18.26. Check seed count and each seed length before the Solana syscall. Start with a zero key destination; retain the syscall status conversion, bytes and effects. The host curve/hash implementation is a distinct source path. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:5867dd1282508744 -->
<a id="review-5867dd1282508744"></a>

Reference source: solana-program 1.15.2, 1.18.26. Check the UTF-8 seed byte bound and illegal owner suffix in source order, then hash the ordered base, seed and owner bytes. Retain the selected Solana hashing protocol and its zeroed destination and effects. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:3d0347c475b214fa -->
<a id="review-3d0347c475b214fa"></a>

Reference source: solana-program 1.15.2, 1.18.26. Return exactly the all-zero 32-byte Pubkey without allocation or a runtime callback. The value fact does not identify another same-layout nominal key type. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:69233a91545f5a24 -->
<a id="review-69233a91545f5a24"></a>

Reference source: solana-program 1.18.26. Use the Borsh 0.10 reader operation for the entire 32-byte key. Retain the partial consumption, EOF replacement error construction/destruction and abnormal effects of the selected reader; this is not the older slice-deserialize method. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:df3e3dbd6048201c -->
<a id="review-df3e3dbd6048201c"></a>

Reference source: solana-program 1.15.2, 1.18.26. Compare every byte of both 32-byte Pubkeys and return exact array equality, preserving both source borrows. No numeric-status or pointer-equality surrogate is used. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:5fefd807a2da9194 -->
<a id="review-5fefd807a2da9194"></a>

Reference source: solana-program 1.15.2, 1.18.26. Use the Solana try-find syscall protocol with zero-initialized key and bump destinations, preserve status conversion, and retain the reached failure behavior of the wrapper. Host retry/curve arithmetic stays outside this selected branch. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:7310e2c573df7c3c -->
<a id="review-7310e2c573df7c3c"></a>

Reference source: solana-program 1.18.26. Forward the complete current 32-byte array to the selected Borsh 0.10 Write interface. Preserve partial writes, errors, callback state and cleanup; no total-writer or allocation-success assumption is added. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:b915f3aced3855ee -->
<a id="review-b915f3aced3855ee"></a>

The reached Borsh implementation serializes the single nonempty [u8; 32] field through one actual W::write_all. Its result, partial writer state, error, unwind and terminal outcome are retained. No successful-writer or rollback assumption is introduced. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:0ee48651689e7b5b -->
<a id="review-0ee48651689e7b5b"></a>

Reference source: solana-program 1.15.2, 1.18.26. Return all 32 current key bytes in their original order without allocation or state change. The nominal Pubkey and its full source representation remain explicit. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:4222a6ac2aff5c94 -->
<a id="review-4222a6ac2aff5c94"></a>

Reference source: solana-program 1.15.2, 1.18.26. Compare balance against minimum_balance using the same account-storage overhead, u64 arithmetic and binary64 threshold conversion. Retain the actual checked/wrapping overflow profile and 64-bit length interpretation, including unusual float bit patterns. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:9b74e0169f3ab857 -->
<a id="review-9b74e0169f3ab857"></a>

Reference source: solana-program 1.15.2, 1.18.26. Add account-storage overhead, multiply the selected rate and length, convert to binary64, apply the threshold and use the saturating float-to-u64 result of Rust. Preserve checked versus wrapping integer behavior and all threshold bits. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:180d2550abadeacf -->
<a id="review-180d2550abadeacf"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C seed/address pointer and length order and integer status. The provider interprets only the admitted runtime memory and status contract, with actual returned key bytes and effects. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:de89d1b5debfccce -->
<a id="review-de89d1b5debfccce"></a>

Preserve this checksum-pinned Program extern-C declaration, including its exact argument order, result type and dynamic syscall gates. Macro expansion does not change the defining crate or supply a runtime implementation. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:a00befd8bf62ec73 -->
<a id="review-a00befd8bf62ec73"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C destination pointer and u64 status, actual initialized writes and finite runtime effects. This raw boundary neither manufactures a Clock value nor folds failures into a typed getter result. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:65c7bd752e62933b -->
<a id="review-65c7bd752e62933b"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C destination pointer and u64 status, actual initialized writes and finite runtime effects. The typed Rent initialization and status conversion belong to the separate wrapper. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:f9c14441768b7ed8 -->
<a id="review-f9c14441768b7ed8"></a>

Reference source: solana-program 1.18.26. Preserve the complete Rust instruction, account-info array and nested signer-tree ABI. The selected canonical provider returns only on successful invocation; decode, copyback, privilege/error order and terminal effects remain explicit. Invocation and callee execution stay opaque. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:85288a3a6ceb6b14 -->
<a id="review-85288a3a6ceb6b14"></a>

Preserve the dynamic unsafe extern-C declaration (*const u8, *const u8, u64, *const u8, u64) -> u64 and its actual Program defining identity. C/Rust pointer layout and opaque runtime behavior remain separate. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:7343934ac16a5f5a -->
<a id="review-7343934ac16a5f5a"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C destination/source/count order and nonoverlapping initialized memory-copy contract. Retain the complete selected write effects and runtime failures; overlapping regions require their separate source obligations. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:a27b08fb0e9ae533 -->
<a id="review-a27b08fb0e9ae533"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C destination, byte value and count order and the exact admitted destination writes. Runtime failures and source memory/provenance conditions remain explicit. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:e1a79dad4d2f21d3 -->
<a id="review-e1a79dad4d2f21d3"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C ordered slice descriptors, count and result pointer with the u64 status. The provider supplies the admitted cryptographic result and writes; no SDK or validator hash implementation is proved. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:529b4b375adfcfba -->
<a id="review-529b4b375adfcfba"></a>

Reference source: solana-program 1.18.26. Preserve the extern-C seed descriptors, program key, address destination and bump destination in order. Retain actual status, writes and runtime effects; no host search or uniqueness theorem is substituted. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:1e34106b662e38da -->
<a id="review-1e34106b662e38da"></a>

Reference source: solana-program 1.15.2, 1.18.26. Build three ordered metas: writable signing funder, writable nonsigning new account, and readonly signing base, retaining duplicates. Then serialize the SystemInstruction fields with bincode. Preserve seed String bytes, metadata/data allocation order and reached error, unwind and cleanup effects. Compatibility in [1.15.2, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:d6d716cab93d4543 -->
<a id="review-d6d716cab93d4543"></a>

Reference source: solana-program 1.18.26. Initialize the actual Clock destination with Default before the selected syscall or host stub. Status zero returns its current initialized value; nonzero uses the legacy ProgramError table, including owned BorshIoError("Unknown") and unknown-status low-word truncation. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:ffcaebc46840ac1b -->
<a id="review-ffcaebc46840ac1b"></a>

Reference source: solana-program 1.18.26. Initialize the actual Rent destination with its rate, threshold and burn defaults before the selected syscall or host stub. Status zero returns its current value; nonzero retains the legacy ProgramError table and owned diagnostic behavior. Compatibility in [1.18.26, 2.0.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:88189e5deea155db -->
<a id="review-88189e5deea155db"></a>

Checked exclusive lamports guard, typed current value, aliases and RefCell failure. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:d88ec2be3c670c5e -->
<a id="review-d88ec2be3c670c5e"></a>

The complete query uses arbitrary public schedule fields. firstSlot selects epoch <= first_normal_epoch, truncates epoch to u32 before saturating_pow, then saturating-subtracts 1 and multiplies by 32. Its other branch subtracts first_normal_epoch, multiplies slots_per_epoch and adds first_normal_slot with saturation. lastSlot calls firstSlot, adds get_slots_in_epoch with saturation and subtracts 1; warmup slots use a separate strict < test and saturating u32 exponent addition by 5. No schedule invariant or warmup-flag premise is imposed. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:74ccb7faae3e508c -->
<a id="review-74ccb7faae3e508c"></a>

The reviewed derived Instruction Clone fields have program ID, Vec<AccountMeta>, Vec<u8> in that order. Primitive clones preserve exact order/duplicates and data; failure while cloning bytes drops only newly cloned accounts. Original vectors are borrowed, not consumed. Vec source layouts and allocator/cleanup correspondence remain separate; complete provider outcomes and useful exact-current laws are retained. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:12ffa0620dfd4a4f -->
<a id="review-12ffa0620dfd4a4f"></a>

The legacy SDK log function forwards UTF-8 bytes and byte length to sol_log_ on Solana; on the host it calls the installed program_stubs implementation, which is replaceable and is not identified with stdout. The compute-unit logger calls sol_log_compute_units_ with no integer return or the corresponding host stub. Exact sink effects and finite abnormal exits are retained. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:f4e7b6034dcae400 -->
<a id="review-f4e7b6034dcae400"></a>

None returns false without a callback. Some calls U::eq(query, payload), in this exact order, with callback effects and exits intact. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:e97babf2059ddc09 -->
<a id="review-e97babf2059ddc09"></a>

Exact 1.15.2 only: instantiate the complete COption family at the nominal Program Pubkey/Boolean behavior fixed by the selected concrete payload profile, retaining the emitted layout, shared references, byte equality, zero Default and trivial payload drop. The generic profile has a separate compatibility assumption; it does not extend this concrete source or its ABI.
<!-- /registry -->

<!-- registry:review:8829fc8900548fcb -->
<a id="review-8829fc8900548fcb"></a>

Return the negation of is_some, without payload movement, callbacks or destruction. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:3c3a390a565f9889 -->
<a id="review-3c3a390a565f9889"></a>

Some returns its payload and never calls Default. None delegates to the actual Default callback and forwards its effects and every exit. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:44235a8eab28858a -->
<a id="review-44235a8eab28858a"></a>

Call the selected overridable unpack_unchecked; propagate a decode error before initialization; query a decoded value once; return it if initialized or drop it before UninitializedAccount. A query unwind drops the value, and a drop unwind during unwinding follows the double-unwind callback. Resolve Self::unpack_unchecked, Self::is_initialized and Self drop for the actual type, with its complete state, error (including owned BorshIoError payload), unwind and terminal representations. Use defaultUnchecked only if source resolution selects that provided method; the generic Pack method does not impose LEN itself. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:e8a81fa8a4ee7d03 -->
<a id="review-e8a81fa8a4ee7d03"></a>

Borsh 0.9.3 copies the first 32 bytes and advances the mutable slice by 32 on success. A short input returns InvalidInput/Unexpected length of input before changing the slice. Fixed-array and const-generics paths have the same byte specialization. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:10391b5959f2b349 -->
<a id="review-10391b5959f2b349"></a>

Construct authorize with the exact instruction discriminant, ordered account metadata, signer/writable flags and optional fields. Split returns allocate(200), assign(stake program), split in order; merge allocates its metadata before its outer array. Temporary ownership and unwind/terminal cleanup follow the generic owned providers. Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition. Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:700c3a53053bc12d -->
<a id="review-700c3a53053bc12d"></a>

Construct delegate_stake with the exact instruction discriminant, ordered account metadata, signer/writable flags and optional fields. Split returns allocate(200), assign(stake program), split in order; merge allocates its metadata before its outer array. Temporary ownership and unwind/terminal cleanup follow the generic owned providers. Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition. Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:3c0a68d9b209079f -->
<a id="review-3c0a68d9b209079f"></a>

Construct initialize with the exact instruction discriminant, ordered account metadata, signer/writable flags and optional fields. Split returns allocate(200), assign(stake program), split in order; merge allocates its metadata before its outer array. Temporary ownership and unwind/terminal cleanup follow the generic owned providers. Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition. Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:430cf6bdfa9a9b46 -->
<a id="review-430cf6bdfa9a9b46"></a>

Construct merge with the exact instruction discriminant, ordered account metadata, signer/writable flags and optional fields. Split returns allocate(200), assign(stake program), split in order; merge allocates its metadata before its outer array. Temporary ownership and unwind/terminal cleanup follow the generic owned providers. Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition. Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:d9bbeda9c7871eb0 -->
<a id="review-d9bbeda9c7871eb0"></a>

Construct set_lockup with the exact instruction discriminant, ordered account metadata, signer/writable flags and optional fields. Split returns allocate(200), assign(stake program), split in order; merge allocates its metadata before its outer array. Temporary ownership and unwind/terminal cleanup follow the generic owned providers. Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition. Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:0372ee9fe1f3d50c -->
<a id="review-0372ee9fe1f3d50c"></a>

Construct split with the exact instruction discriminant, ordered account metadata, signer/writable flags and optional fields. Split returns allocate(200), assign(stake program), split in order; merge allocates its metadata before its outer array. Temporary ownership and unwind/terminal cleanup follow the generic owned providers. Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition. Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:6dacec6cfb817207 -->
<a id="review-6dacec6cfb817207"></a>

Derived Default returns zero timestamp, zero epoch and the zero Pubkey. Preserve the legacy four-variant StakeState representation and every copied integer, key and binary64 bit. No decoder, float validation or allocation is performed. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:776b0bb2e7d150c2 -->
<a id="review-776b0bb2e7d150c2"></a>

Equal custodian bypasses the lockup; otherwise compare strict future timestamp or epoch with short-circuiting, retaining source signedness. Preserve the legacy four-variant StakeState representation and every copied integer, key and binary64 bit. No decoder, float validation or allocation is performed. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:8383f82b363ac8de -->
<a id="review-8383f82b363ac8de"></a>

Copy the selected optional delegation from legacy StakeState, preserving all fields and returning None in the source variants. Preserve the legacy four-variant StakeState representation and every copied integer, key and binary64 bit. No decoder, float validation or allocation is performed. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:9eb0c57ab04320ed -->
<a id="review-9eb0c57ab04320ed"></a>

Copy the selected optional lockup from legacy StakeState, preserving all fields and returning None in the source variants. Preserve the legacy four-variant StakeState representation and every copied integer, key and binary64 bit. No decoder, float validation or allocation is performed. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:40e6b0b03ae230f5 -->
<a id="review-40e6b0b03ae230f5"></a>

Copy the selected optional meta from legacy StakeState, preserving all fields and returning None in the source variants. Preserve the legacy four-variant StakeState representation and every copied integer, key and binary64 bit. No decoder, float validation or allocation is performed. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:5055d7e974a0290b -->
<a id="review-5055d7e974a0290b"></a>

Default-initialize the typed destination, call the selected typed syscall or replaceable host stub, and return its current value on status zero. Nonzero statuses use the exact ProgramError conversion: the 1.15.2 builtin table ends at tag 21, tag 15 owns BorshIoError("Unknown"), and unknown codes retain low-word truncation. Compatibility in [1.15.2, 1.16.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->
