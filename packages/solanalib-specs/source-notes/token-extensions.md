# Token-2022 extensions, unpacking and account length

The shared definitions in `Solanalib.Specs.Core.TokenExtension`,
`TokenExtensionState`, `TokenExtensionSize` and `TokenExtensionFee` describe the
byte and value semantics used by `spl-token-2022-interface` 3.1.1.
`TokenExtensionGetter` adds the resolved generic getter and its actual exits.
`TokenExtensionScan`, `TokenExtensionListCurrent`,
`TokenExtensionListFrame` and `TokenExtensionListReference` supply operational
type listing, ownership, cleanup, an explicit read-frame theorem and a concrete
reference. The versioned contracts are in
`Solanalib.Specs.SplToken2022Interface.Extensions`; their independent controls are in
`SolanalibTest.Specs.SplToken2022Interface.Extensions`.
`TokenExtensionUnpack` and `TokenExtensionUnpackFacts` add generic owned-base
destruction, current-state layout checks and retained source-region identity.

These are mathematical models with source correspondence arguments, closed
reference witnesses and concrete executions. They are not proofs of compiled
Rust bodies. The contracts do not establish Rust reference permissions, pointer
provenance, allocator behavior, compiler correctness, token-processor execution
or CPI effects. Generic source methods and parsers must be bound to their actual
implementations before a Rust caller can use these contracts.

## Source identity

The token interface is pinned to
[`e18f9c6f9bf6044b934f48e3090e8e59e4820f02`](https://github.com/solana-program/token-2022/tree/e18f9c6f9bf6044b934f48e3090e8e59e4820f02/interface).
The principal source files are `src/extension/mod.rs`,
`src/extension/account_len.rs`, `src/state.rs`, `src/pod.rs` and
`src/extension/transfer_fee/mod.rs`. Every fixed extension size is justified by
the production enum and its corresponding structure declaration, including the
group and encrypted-value dependencies. Test-only enum variants are excluded.

The [source registry](../source-map.json) records exact file hashes, immutable
repository paths and revisions, and line anchors. The source audit checks those
files against their pinned upstream versions. Interface IDs for the shared base
decoders are `spl-token-2022-interface-3.1.1-state`,
`spl-token-2022-interface-3.1.1-pod` and `solana-program-pack-3.1.0-lib`.

## Lookup and iteration have different admission rules

`get_extension_indices` at `extension/mod.rs:152` inspects a complete four-byte
header before comparing the raw tag. A matching tag wins before the zero-tag
sentinel check. A nonmatching zero tag produces `ExtensionNotFound`, encoded as
custom error 48. Other raw tags are skipped using their declared length, even
when the tag does not decode to a known production extension. Exhaustion or a
short header yields `InvalidAccountData`. The selected value must fit the TLV
slice. The first matching entry is returned; later duplicate entries and later
malformed bytes are not inspected.

`getExtension` first checks the account association of the extension against
`S::ACCOUNT_TYPE`, then performs this raw lookup, then checks the selected Pod
size and alignment. Wrong base association is `InvalidAccountData`; wrong Pod
size or alignment is `InvalidArgument`. The alignment address includes the offset of the
selected value, rather than just the start of the TLV slice. The
logical reference retains that offset, the exact selected bytes and their
typed observation.

The default `get_extension` of the trait calls `Self::get_extension_bytes`, which
can be overridden. The primary `get_extension_operational_contract` takes the
actual resolved method as an outcome provider. It propagates the error of that method, changed state, unwind or terminal exit. On success it casts the bytes
observed through the returned reference in the actual returned state, checks
size before alignment, and retains the same reference identity. A method with
no finite exit cannot produce an enclosing finite execution.

The default lookup is a concrete provider. `getDefaultExtension_agrees` proves
that forgetting only its base-address wrapper yields exactly the supporting
`get_extension_contract` observation for every Pod representation and input.
No theorem equates an arbitrary override to this default. A Rust binding must
identify the resolved methods, their state and slice interpretations, and
their actual finite exits. The `ExtensionRepresentation` observation function
describes how a source Pod value is represented in Lean; it is not an additional
Rust callback executed by `get_extension`.

Type iteration instead decodes every visited tag. An unknown tag is
`InvalidAccountData`; a zero tag stops iteration without requiring a length
field. An empty or one-byte tail is accepted, including a realloc byte. A known
nonzero tag requires the entire header and declared value. The list retains
source order and duplicates. Neither listing nor sizing invents a requirement
that a value have the standard fixed size or that every visited tag belong to
the base account kind.

## Listing allocation and cleanup

The primary `get_extension_types_operational_contract` calls the actual
`Self::get_tlv_data` provider first. After a returning accessor, it creates the
empty vector and visits entries in source order. Each complete nonzero entry
causes one actual vector push. A successful scan moves that same vector out.
A malformed entry drops the accumulated vector before returning the parse
error. A push unwind passes its actual changed state to that destructor. A
second unwind during cleanup uses an explicit terminal-only provider carrying
both reasons and the actual state. Terminal exits bypass further reads and
cleanup. An accessor unwind or terminal exit happens before vector creation.

The vector provider is a shared `Owned` dependency. Its optional primitive laws
track a stable logical resource and its current contents. They allow
partial contents changes before unwind and impose no general frame condition
on other state. The model therefore reads each successive entry through the
same source reference and fixed length metadata in the state actually returned
by the preceding push. It never silently substitutes an earlier byte snapshot
or an earlier vector-content snapshot during cleanup.

`ExtensionReadFrame` explicitly states immutability of the source bytes across
normally returning pushes. `collectCurrentExtensionTypes_success` uses that
law and the `push_current` guarantee of the vector to prove, directly from the live
loop, that every successful execution returns the pure ordered list in the same
live resource. The proof follows each push and the bytes observed in its returned
state; cleanup of an error or unwind cannot manufacture success. It starts at
the actual input state of the collector after empty-vector construction. A Rust
correspondence must also frame that construction and bind the accessor, source
reference and read permissions. The primary operational contract has no entry
restriction; these two laws are premises of this separate
success-value theorem.

The separately registered `get_extension_types_contract` is the pure-list
observation. It does not itself represent vector allocation or lifetime. The
primary operational sample uses a concrete ledger, creates a fresh vector,
performs two pushes, and returns a nonempty live result.
Further controls prove late-error cleanup, impossibility of success on a
malformed tail, cleanup of a partially modified vector, absence of a destructor
exit on the discarded old snapshot, double-unwind behavior and terminal bypass.
Every abnormal vector provider used by those controls also has a primitive-law
proof. Another control changes the next source tag after a successful push:
the live reader rejects it, and a theorem proves that provider interpretation
fails the explicit read-frame condition.

Source slice lengths, Pod layouts and pointer ranges belong to the Rust
representation binding. The mathematical getters, unpackers and size
observations accept arbitrary lists and natural-number offsets.
`tlvU16_le` bounds every decoded two-byte length; `extensionTlvIndexFits`
proves that a cursor below `2^63`, plus a four-byte header and any decoded
16-bit length, remains below `2^64`. That theorem consumes its explicit cursor
bound. Relating the slice and cursor representation of the source to this arithmetic
fact remains part of the source binding.

## Base decoding and generic parser exits

`StateWithExtensions::unpack` first rejects the 355-byte multisig length and
lengths below `S::SIZE_OF`. It then calls the base parser on exactly that many
bytes. Base errors precede extension-layout errors. A bare base has no TLV
tail. Otherwise the model checks zero padding up to byte 165 and the matching
account marker, then returns the unchanged TLV tail without validating its
entries.

The primary `unpack_operational_contract` takes an `ExtensionUnpacker`: the
source size and account kind, logical types, live input reference and length,
current byte reader, actual parser exits and the destructor of its owned base
value. It propagates parser errors, changed states, unwinds and terminal exits.
Tail checks occur only after a successful base parse and read the actual state
returned by that parser.

`BaseState + Pack` does not imply `Copy` or forbid `Drop`. At source lines
538–539, parsing creates an owned `S` before the fallible tail check. A layout
error therefore calls the actual destructor of that value. A normal destructor
return preserves the pending layout error and its changed state; an unwind or
terminal exit replaces the pending error. If the destructor has no finite
exit, the enclosing error path has none. Success moves the exact parsed base
into the result and calls no destructor. Internal cleanup of a generic `S`
belongs to its supplied destructor dependency.

The result retains a logical range of the original input with its exact origin,
offset and length. Generic theorems prove the range is bounded and reaches the end of the
same input. The bare-base path returns the static `&[]` literal in the source;
an extended input with no TLV bytes returns an empty range of the original
input, and the model keeps those origins distinct. Another theorem shows every
successful outer result comes from the actual parser returning that same base
and state; cleanup cannot manufacture success.

The earlier `unpack_contract` remains a supporting value observation for
immutable bytes and trivial base destruction. It uses an explicit
`ExtensionBaseParser` and retains its actual exits. The pure, trivial-destructor
instantiations of the operational model are proved to recover this exact
byte-level result when their retained references are observed. This bridge
makes no frame claim for arbitrary effectful parsers. The Rust binding must
establish the actual parser, destructor, ownership and shared-slice permissions;
an assumed desired parser result does not supply these obligations.

The concrete Mint and Account instances use the shared packed codecs and their
complete COption, state and Boolean checks. Initialized and frozen token
accounts are both admitted. The sizing helper uses `PodMint`, not packed Mint:
its initialization byte need only be nonzero, and COption tags are not
validated. Controls demonstrate bytes accepted for sizing that packed Mint
unpacking rejects. The successful unpack-family witness uses an actual
initialized 82-byte Mint, not an arbitrary successful parser premise. Controls
add a nontrivial generic destructor, destructor unwind and terminal exits,
nonreturning cleanup, source bytes changed by the parser, successful ownership
transfer and both empty-tail reference origins.

## Production extension sizes

The source uses 16-bit tags and two-byte length fields. These are the value
sizes before adding the four-byte TLV header; all listed production fixed
layouts have alignment one. The numeric table does not impose extra payload
validation on raw type iteration.

| Tag | Production extension | Value bytes |
| --- | --- | ---: |
| 0 | Uninitialized | 0 |
| 1 | TransferFeeConfig | 108 |
| 2 | TransferFeeAmount | 8 |
| 3 | MintCloseAuthority | 32 |
| 4 | ConfidentialTransferMint | 65 |
| 5 | ConfidentialTransferAccount | 295 |
| 6 | DefaultAccountState | 1 |
| 7 | ImmutableOwner | 0 |
| 8 | MemoTransfer | 1 |
| 9 | NonTransferable | 0 |
| 10 | InterestBearingConfig | 52 |
| 11 | CpiGuard | 1 |
| 12 | PermanentDelegate | 32 |
| 13 | NonTransferableAccount | 0 |
| 14 | TransferHook | 64 |
| 15 | TransferHookAccount | 1 |
| 16 | ConfidentialTransferFeeConfig | 129 |
| 17 | ConfidentialTransferFeeAmount | 64 |
| 18 | MetadataPointer | 64 |
| 19 | TokenMetadata | Variable; fixed-size request is InvalidArgument |
| 20 | GroupPointer | 64 |
| 21 | TokenGroup | 80 |
| 22 | GroupMemberPointer | 64 |
| 23 | TokenGroupMember | 72 |
| 24 | ConfidentialMintBurn | 196 |
| 25 | ScaledUiAmount | 56 |
| 26 | Pausable | 33 |
| 27 | PausableAccount | 0 |
| 28 | PermissionedBurn | 32 |

`try_calculate_account_len_from_mint_data` checks the account kind of every requested additional extension before parsing the mint. A bad requested kind yields
custom error 20. A PodMint or base-layout error maps to custom error 2
(`InvalidMint`); a later malformed TLV error is preserved as
`InvalidAccountData`.

The required account extensions are `TransferFeeAmount` for a fee mint,
`NonTransferableAccount` followed by `ImmutableOwner` for a nontransferable mint,
`TransferHookAccount` for a hook mint, and `PausableAccount` for a pausable mint.
The shared accumulator removes duplicate types across required and additional
extensions. No extensions gives 165 bytes; otherwise the result starts at 166
and adds the value of each unique extension plus its header. A computed length of
355 is increased to 357. The generic fixed-size helper also preserves the lack of the
source of account-kind checks and its variable-metadata error.

The source accumulator sets a local `seen` bit before attempting a fixed-size
lookup. The pure accumulator returns only `Except` and therefore discards that
local state on failure. Both contracted sizing callers also discard their local
accumulator on failure, so the difference is unobservable for these functions.
The helper is not a contract for an externally retained mutable accumulator.

The 3.1.1 sizing path uses `TlvLenAccumulator` with a stack `u64` bitset and a
`usize` total. Required extension groups are static slices. This path allocates
no vectors: the lists in the mathematical accumulator and its fold are logical
representations, not omitted source allocation calls. The deprecated helper
that collects a vector is not called by this sizing function.

## Fee bytes, controls and remaining bindings

`TokenExtensionFee` joins checked TLV retrieval to the shared fee arithmetic.
A `TransferFee` is exactly 18 bytes: epoch at offset 0, maximum fee at 8 and the
full unsigned 16-bit rate at 16. A `TransferFeeConfig` is exactly 108 bytes:
two raw nullable authorities at 0 and 32, withheld amount at 64, older fee at
72 and newer fee at 90. No rate clamp or additional option-tag check is
invented. The extension sample is a real, complete fee-config TLV. A control
retrieves nonzero fee bytes, chooses the fee of the epoch and calculates different
net amounts on the two sides of activation. The arithmetic source argument is
in [token-fees.md](token-fees.md).

The finite controls distinguish truncated headers, unknown tags, zero
sentinels, duplicate ordering, declared-value bounds, Pod-size errors, alignment,
padding, base-error order, packed versus Pod admission, required-extension
deduplication, variable-size errors and the multisig collision. Generic controls
also show stateful parser errors and unwinds, absence of invented exits, and
consequences for arbitrary interpretations satisfying the registered contract.

Every exposed contract has a closed reference proof and satisfiable
precondition. The five indexed families also have closed sample execution
witnesses, while reference correctness quantifies over every family index.
Fresh isolated Lean builds treat warnings as errors and enable documentation
checks for all owned modules. The audit checks every owned declaration,
including generated and private declarations, for unexpected axioms and checks
that witness conclusions name the registered contract, reference and sample.

Those results prove properties of the mathematical models. Establishing a Rust
binding still requires the concrete trait resolutions, parser and Pod laws,
source integer/layout representation, actual vector dependency implementations,
source reference identity, lifetime and read permissions, and compiler execution
correspondence. Allocation control flow and cleanup above those dependencies
are modeled here; the allocator and standard-library bodies remain separate.
The copied result of `get_epoch_fee` is a supporting observation. Its primary
model retains the parent and selected field, as described in
[the fee reference note](token-fees.md#borrowed-fee-selection); physical lifetime
and access correspondence remain separate obligations. No CPI body is included.
