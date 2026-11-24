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

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:c3ab832f3bc32e62 -->
<a id="review-c3ab832f3bc32e62"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Import-only versioned roots collect the separately reviewed leaf modules. The listed module hashes seal their exact imports; each leaf retains its own source-facing contract and interpretation obligations.

The primary Family composes owned instruction construction, the ordered clone/move literal trace, current-owner multisig checks, mint/validation/collected data guards, interface-3.0 padding, TLV and seed helpers, and final opaque CPI. Its one selected collection protocol joins primitive guard/data admission, current-resource retention and the five reached source borrow domains. family_mint_primitive_retain derives actual read/release continuation from that family input; checked errors and early rejection do not require success-only invariants. Literal work/count and finite-prefix cleanup-order admission prevent local protocol checks from discarding actual downstream exits. Both actual PDA sites require bounded successful replies to initialize output. The full non-hook witness allocates, clones, acquires/releases mint data, invokes and cleans temporary owners. Exact current-array and collection-length results retain their used CurrentLaw and finish-current premises. No callback termination, inverse to one-way Conforms, complete hook-call derivation or Rust implementation correctness is inferred.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

The concrete StateWithExtensions trait implementation returns its stored borrowed TLV slice directly. It performs no parsing, initialization test, allocation or extension validation. The family retains the base value, the parent reference and exact tail range; an empty literal tail remains distinct from a borrowed tail. The source checks minimum length and the multisig collision before splitting the input and calling the actual generic Pack::unpack. On success it obtains the tail and drops the owned base if the tail stage fails or unwinds. A nonempty remainder first checks the version-specific minimum, then creates a zero-filled temporary Vec, compares padding, destroys that temporary, and only then decodes/checks the account marker. The comparison is captured before destruction, while the marker reads current input afterward. Token 8.0.1 rejects a remainder ending exactly at the marker; interfaces 2.1.0 and 3.0.1 admit that empty borrowed tail. The returned tail is not validated as a TLV stream. The old get_tlv_data_info allocates an empty vector after the resolved accessor returns. It decodes each type, stops at the sentinel or a final single spare byte, checks the length header, then pushes the type BEFORE checking that the payload fits. Thus a push failure may precede malformed-payload rejection. Reached errors destroy the temporary owner; success transfers the live ordered vector. This is deliberately distinct from the later interface scan that checks payload bounds before pushing. For nonempty input the old source constructs and fully deduplicates a temporary Vec before attempting any fixed-width calculation. A variable-length kind can therefore be preceded by allocation or push failure. It sums each successful distinct type length including the four-byte header, then destroys the temporary and applies the base/marker and multisig adjustment. TokenExtensionLegacyBounds derives at most 28 distinct ordinary kinds from actual empty/current/push laws and proves each fixed length at most 299, so the ordinary usize sum cannot overflow at the reviewed 64-bit target. No overflow or rate-domain hypothesis is added to the mathematical contract. The required-init function starts an empty Vec and performs ordered pushes for each input kind. It preserves duplicates; NonTransferable contributes NonTransferableAccount followed by ImmutableOwner. It does not read the existing result elements before a push. The family preserves each reached allocation/push exit and owned-vector cleanup, returning the same live vector identity on success. Rust evaluates get_tlv_data before the fallible new-extension get_packed_len callback, then scans the TLV bytes into an owned temporary. Measurement errors occur before that scan/allocation. The calculation uses the scanned used prefix rather than backing capacity, performs a fresh current-slice lookup for an existing extension, masks only that lookup ordinary error to length zero, applies saturating usize arithmetic and the multisig adjustment, then destroys the vector. Callback mutation, unwind, terminal exits and cleanup remain at those exact stages. The provided get_extension first invokes the actual get_extension_bytes implementation, then interprets its returned slice as the selected Pod V. Default byte lookup is supplied separately: requested/base type compatibility is checked before scanning; encountered types are decoded and their account association checked in source order; sentinel, unknown type, reached length errors and Pod size/alignment errors remain distinct. The result is a reference to the same source bytes, not a copied arbitrary V. The helper calls the resolved typed extension getter once. A returned extension maps its concrete nullable 32-byte field to Option<Pubkey>, where all-zero is None; the hook selects the second key after its authority. Result::ok consumes an ordinary getter error before returning None. A legacy BorshIoError may own a String, so the explicit reached error-destructor dependency preserves its deallocation effects, unwind or terminal exit; only a normal drop permits None. The error variant may abstract the message while its actual owner remains in the shared state. Neither helper invokes CPI.

The Pod fields are decoded as unsigned little-endian 64/16-bit values. Checked u128 multiplication and ceiling division are followed by u64 narrowing BEFORE maximum-fee capping. The inverse helper retains the zero amount/rate branches, the full-rate cap branch and checked denominator/subtraction/addition behavior, then calculates the fee of the derived gross amount. No basis-points-at-most-10000 precondition is imposed: invalid raw rates are admitted and may return None. Epoch wrappers select newer at equality, retain the receiver and apply the same checked arithmetic. The source returns an existing reference to newer_transfer_fee when epoch is at least its epoch, otherwise older_transfer_fee. The complete shared reference family retains parent identity and selected field; later observation reads that field from the current parent. It is not a snapshot or a new allocated fee record.

These complete families select the source-specific program check, enum domain and ordered plan. All native callback/state/resource indices remain explicit, and each family has a closed real execution at the two-ledger sample. Three unchanged Token-2022 constructors use the pre-existing complete families via explicit applicability profiles, with their own released source layout index.

Require the Token-2022 program before allocating the writable mint metadata vector. Validate authority before metadata address: None encodes zeros, Some(zero) returns InvalidArgument and destroys the actual allocated metadata owner. Success packs outer tag 39, subtag 0 and the two key32 POD fields. Complete byte allocation, partial-state cleanup, double unwind and terminal stopping remain explicit.

The id function defined by spl-token-2022 8.0.1 has its own library member and the two exact reviewed Pubkey dependency profiles. Its complete contract and reference are definitionally equal to the existing interface constant; source identity and build admission remain distinct.

The source-owned spl-token-2022::instruction::initialize_account3 facade uses the same complete mathematical contract and reference as the inherited spl-token-2022-interface::instruction::initialize_account3 family. Its exact defining source profile is kept separately. Check either token program before allocation; pack tag 18 and owner key32 before constructing the literal metadata vector. Account is writable and mint readonly, neither signer. The complete existing allocated family is reused at the actual released enumSize/provider index, retaining allocation and cleanup order.

The source-owned spl-token-2022::instruction::close_account facade uses the same complete mathematical contract and reference as the inherited spl-token-2022-interface::instruction::close_account family. Its exact defining source profile is kept separately. Check the selected token program before allocation; pack tag 9, then reserve 3 + signer count metadata entries. Source and destination are writable; authority is readonly and a signer iff no explicit signers. Explicit readonly signers retain their order and duplicates. Data-first construction and actual partial-owner cleanup are preserved.

The source-owned spl-token-2022::instruction::transfer_checked facade uses the same complete mathematical contract and reference as the inherited spl-token-2022-interface::instruction::transfer_checked family. Its exact defining source profile is kept separately. Accept either token program before allocation; pack tag 12, little-endian amount and decimals, then reserve 4 + signer count. Source and destination writable, mint readonly, readonly authority signer iff no explicit signers, followed by ordered readonly signer metas. Reuse the complete existing family at the actual released enumSize/provider index; aliases and all allocation/cleanup effects remain explicit.

Account::is_frozen compares only its valid AccountState enum against Frozen. It neither invokes Pack nor requires initialization; Uninitialized is a valid receiver and returns false. Other account fields and the receiver remain unchanged. The concrete derived Default calls the default constructors for OptionalNonZeroPubkey, Pubkey, three String fields and Vec<(String,String)>. Both keys are zero and all containers are empty with zero capacity; constructing them needs no heap allocation or user callback. The mathematical value postcondition contains the six actual fields without imposing the documented additional-key uniqueness convention. A Rust binding must supply real owned empty container representations separately.

Exact Base58 literals were decoded to 32-byte constants and compared with direct native id/check_id calls. Each mathematical function is a state-preserving constant copy or full equality; no allocation, hashing or syscall is introduced.
<!-- /registry -->

<!-- registry:review:d61b5fb23b12511a -->
<a id="review-d61b5fb23b12511a"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The declared Token-2022 key and both-token check are pure. InitializeAccount3, CloseAccount and TransferChecked instantiate both-token admission; WithdrawExcessLamports admits only Token-2022. Withdraw constructs a literal three-meta prefix, pushes signers, and only then packs its byte tag; the other selected constructors pack first. The owned builders preserve exact data, metadata, source allocation order and exceptional cleanup. Each separate value observation and primary operational Family has exact closed source-facing witnesses.

Import-only versioned roots collect the separately reviewed leaf modules. The listed module hashes seal their exact imports; each leaf retains its own source-facing contract and interpretation obligations.

Thin version contracts register primary operational getter, listing and unpack families over their actual dependencies, plus exact allocation-free sizing. Default lookup, pure listing and dropless immutable unpack remain separately inventoried supporting observations. Every family reference quantifies over all indices and has a closed sample with an actual execution; every contract has a closed satisfiable-precondition witness. References, samples and all generated declarations are covered by the exact compiled module hashes. All these extension contracts have precondition True; the successful current-vector result separately uses the direct push_current capability and read-frame law. Source slice, pointer and layout validity remain interpretation obligations, while actual branch checks determine returned geometry.

Checked u128 ceiling arithmetic keeps the source operation order. Forward fees convert the raw result to u64 before capping; inverse fees compare the cap before conversion. All u16 rates, zero/10000/over-10000 cases, checked deduction, overflow and epoch equality branches are modeled. get_epoch_fee is an immutable copied-field observation; its source field reference is not modeled. The four frozen fee models and their original evidence bytes remain unchanged.

The pinned get_epoch_fee body reads the current newer activation epoch and compares the copied requested epoch. Equality selects newer; an earlier epoch selects older without inspecting the older activation epoch. The result retains the same parent and chosen field, and the ambient state is unchanged. Later admitted reads use the current contents of that fixed field without reselecting. Immediate dereference is proved to agree with the frozen copied-value getEpochFee observation. The closed indexed contract, universal reference proof, satisfiability sample and nonempty execution witness cover generic state and parent-identity interpretations.

The published 3.1.1 state.rs derives Clone and Copy for the concrete five-field repr(C) Mint. Its COption<Address> fields use solana-program-option 3.1.0 and solana-address 2.6.1; the latter is Copy through the required bytemuck feature. COption::clone preserves its discriminant and only clones the concrete 32-byte Address payload. Thus the reached operations copy all five fields, retain the receiver, allocate nothing and call no user-supplied callback. Neither Pack nor IsInitialized is called. The registered reference copies the entire Mint, including false initialization and all source u64 supplies. A separate binding to the Rust implementation must prove exact 88-byte layout, loadability, unchanged owned input and coverage; the 82-byte persistent account representation is used only to record logical fields in native conformance.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

The concrete StateWithExtensions trait implementation returns its stored borrowed TLV slice directly. It performs no parsing, initialization test, allocation or extension validation. The family retains the base value, the parent reference and exact tail range; an empty literal tail remains distinct from a borrowed tail. The source checks minimum length and the multisig collision before splitting the input and calling the actual generic Pack::unpack. On success it obtains the tail and drops the owned base if the tail stage fails or unwinds. A nonempty remainder first checks the version-specific minimum, then creates a zero-filled temporary Vec, compares padding, destroys that temporary, and only then decodes/checks the account marker. The comparison is captured before destruction, while the marker reads current input afterward. Token 8.0.1 rejects a remainder ending exactly at the marker; interfaces 2.1.0 and 3.0.1 admit that empty borrowed tail. The returned tail is not validated as a TLV stream. The old get_tlv_data_info allocates an empty vector after the resolved accessor returns. It decodes each type, stops at the sentinel or a final single spare byte, checks the length header, then pushes the type BEFORE checking that the payload fits. Thus a push failure may precede malformed-payload rejection. Reached errors destroy the temporary owner; success transfers the live ordered vector. This is deliberately distinct from the later interface scan that checks payload bounds before pushing. For nonempty input the old source constructs and fully deduplicates a temporary Vec<&ExtensionType> before attempting any fixed-width calculation. Equality compares referent values, while each stored reference retains the exact reached operand at the first encountered source occurrence, including its actual tag. A variable-length kind can therefore be preceded by allocation or push failure. It sums each successful distinct type length including the four-byte header, then destroys the temporary and applies the base/marker and multisig adjustment. TokenExtensionLegacyBounds derives at most 28 distinct ordinary kinds from actual empty/current/push laws and proves each fixed length at most 299, so the ordinary usize sum cannot overflow at the reviewed 64-bit target. No overflow or rate-domain hypothesis is added to the mathematical contract. The required-init function starts an empty Vec and performs ordered pushes for each input kind. It preserves duplicates; NonTransferable contributes NonTransferableAccount followed by ImmutableOwner. It does not read the existing result elements before a push. The family preserves each reached allocation/push exit and owned-vector cleanup, returning the same live vector identity on success. Rust evaluates get_tlv_data before the fallible new-extension get_packed_len callback, then scans the TLV bytes into an owned temporary. Measurement errors occur before that scan/allocation. The calculation uses the scanned used prefix rather than backing capacity, performs a fresh current-slice lookup for an existing extension, masks only that lookup ordinary error to length zero, applies saturating usize arithmetic and the multisig adjustment, then destroys the vector. Callback mutation, unwind, terminal exits and cleanup remain at those exact stages. The provided get_extension first invokes the actual get_extension_bytes implementation, then interprets its returned slice as the selected Pod V. Default byte lookup is supplied separately: requested/base type compatibility is checked before scanning; encountered types are decoded and their account association checked in source order; sentinel, unknown type, reached length errors and Pod size/alignment errors remain distinct. The result is a reference to the same source bytes, not a copied arbitrary V. The helper calls the resolved typed extension getter once. A returned extension maps its concrete nullable 32-byte field to Option<Pubkey>, where all-zero is None; the hook selects the second key after its authority. Result::ok consumes an ordinary getter error before returning None. A legacy BorshIoError may own a String, so the explicit reached error-destructor dependency preserves its deallocation effects, unwind or terminal exit; only a normal drop permits None. The error variant may abstract the message while its actual owner remains in the shared state. Neither helper invokes CPI.

The Pod fields are decoded as unsigned little-endian 64/16-bit values. Checked u128 multiplication and ceiling division are followed by u64 narrowing BEFORE maximum-fee capping. The inverse helper retains the zero amount/rate branches, the full-rate cap branch and checked denominator/subtraction/addition behavior, then calculates the fee of the derived gross amount. No basis-points-at-most-10000 precondition is imposed: invalid raw rates are admitted and may return None. Epoch wrappers select newer at equality, retain the receiver and apply the same checked arithmetic. The source returns an existing reference to newer_transfer_fee when epoch is at least its epoch, otherwise older_transfer_fee. The complete shared reference family retains parent identity and selected field; later observation reads that field from the current parent. It is not a snapshot or a new allocated fee record.
<!-- /registry -->

<!-- registry:review:a83a7769b739bc26 -->
<a id="review-a83a7769b739bc26"></a>

The exact source-call binding remains registered at 3.1.1. Complete-contract source review admits 3.1.0, 3.1.1, 3.1.2 and 4.0.0 through the per-function applicability profiles. Their reached parser checks payload bounds before invoking the vector push callback. Releases 1.0.0 through 3.0.1 instead push before that bounds check, changing allocation and abnormal-exit behavior; 1.0.0, 2.0.0 and 2.1.0 additionally reject tag 28. Release 0.0.0 has no API. Every listed release is assessed; source correspondence does not provide a Rust implementation proof.
<!-- /registry -->

<!-- registry:review:6e81da70805af4a8 -->
<a id="review-6e81da70805af4a8"></a>

Every API-bearing release checks Token-2022 first and then inline legacy Token by short-circuit key equality, returning IncorrectProgramId exactly when both differ. Equality is derived on the 32 bytes in the reviewed Pubkey/Address dependencies; there is no account-executable check, allocation or invocation. The only source changes in the selected function are Pubkey-to-Address type names. The 0.0.0 package is a placeholder with add, not this API.
<!-- /registry -->

<!-- registry:review:33c48da31756a928 -->
<a id="review-33c48da31756a928"></a>

The concrete default lookup closure remains raw-tag based with account association first, first matching header before zero sentinel, unknown-tag skipping, selected-value bounds, then Pod size/alignment validation. Old spl-pod wrappers are source-equivalent to the direct bytemuck calls introduced in 3.0.0. Actual older V::TYPE values map into the existing generic representation index; no claim is made that later PermissionedBurn types existed earlier. The supporting observation remains narrower than arbitrary provider overrides.
<!-- /registry -->

<!-- registry:review:d0aaf77dfffc2e12 -->
<a id="review-d0aaf77dfffc2e12"></a>

Every API-bearing release invokes the resolved get_extension_bytes provider and then performs the same Pod cast. All actual finite provider outcomes and returned state/reference identity remain parameters. The spl-pod pod_from_bytes wrapper maps exactly the same Bytemuck size/alignment failures to InvalidArgument and adds no allocation or callback. No generic type or provider is specialized or strengthened.
<!-- /registry -->

<!-- registry:review:eaff83cf08cbd191 -->
<a id="review-eaff83cf08cbd191"></a>

This explicitly pure ordered-list observation omits vector allocation/ownership and abnormal exits. Its whole value behavior first matches3.0.0, when PermissionedBurn tag28 is added. The later push-versus-bounds reordering does not change the pure result on immutable bytes. Ordered duplicates, zero sentinel, short-tail acceptance, unknown tags, short headers and bounds errors have been reviewed at every release.
<!-- /registry -->

<!-- registry:review:e29949ce4b4d6eb6 -->
<a id="review-e29949ce4b4d6eb6"></a>

Versions before 3.0.0 also reject tag28. More broadly every release through 3.0.1 pushes a recognized tag before reading/checking payload length, while the existing full family validates the entry before push. Native allocation/reallocation counts and allocator-failure terminal probes distinguish the paths. Starting with 3.1.0 the visitor callback runs only after complete bounds checks; accessor effects, current reads, vector identity, pushes, cleanup and abnormal exits match the existing family.
<!-- /registry -->

<!-- registry:review:cc9d56c6bc60348f -->
<a id="review-cc9d56c6bc60348f"></a>

Although every tested ordinary packed-Mint/Account result matches all releases, this supporting contract is still a family preserving actual parser exits and returned state, with immutable bytes and trivial base destruction. It has no post-parser allocation provider or allocation-success condition. The old padding allocation creates an extra terminal outcome after a successful parser; all pre-3.1 native allocation-failure probes abort. Full-family correspondence therefore starts at 3.1.0 without weakening it to ordinary returns only.
<!-- /registry -->

<!-- registry:review:f12e1e06895461b8 -->
<a id="review-f12e1e06895461b8"></a>

The top-level unpack is identical at all API-bearing releases, but through 3.0.1 type_and_tlv_indices allocates vec![0; padding] after successful parsing. The existing operational family has parser/destructor providers and no padding allocator; the old global allocator state effects and terminal abort cannot be assigned to the earlier completed parser. Starting with 3.1.0 iter().any removes this allocation. Exact generic parser calls, base destruction, error precedence and static-versus-borrowed tail origins remain unchanged.
<!-- /registry -->

<!-- registry:review:9ce560439eb6425c -->
<a id="review-9ce560439eb6425c"></a>

The API is first published in3.1.0. Its full account_len.rs file is identical through4.0.0, as are reached enum, type map, padding and scan helper bodies. PodMint initialization and InvalidMint conversion, requested-kind-before-mint error order, production fixed layouts, required-extension groups, local bitset deduplication and allocation-free accumulation remain unchanged. All modern released dependencies retain those layouts; unrelated4.0.0 AccountView resize APIs are not reached.
<!-- /registry -->

<!-- registry:review:28e31dbe04246159 -->
<a id="review-28e31dbe04246159"></a>

All nine sources decode the full u16 rate, short-circuit only zero rate/amount, checked-multiply in u128, invoke the identical checked-add/subtract/divide ceil_div helper, narrow the uncapped result to u64, then apply cmp::min with the decoded cap. In particular a raw fee exceeding u64::MAX yields None even with cap zero. The record is immutable. The old Pod wrappers and later zero-copy wrappers have reviewed unconditional little-endian conversions. Source declaration/representation, constant and reached-helper review supplements the equal body hashes and native cases.
<!-- /registry -->

<!-- registry:review:ccb6c1643a16ec25 -->
<a id="review-ccb6c1643a16ec25"></a>

All nine sources first execute calculate_fee, including its checked u128 helper and narrowing-before-cap failure, then checked_sub the resulting u64 fee from the requested amount. They preserve the full record and permit None both from fee calculation and subtraction. The relevant source closure includes calculate_fee, ceil_div, both constants and the old/new exact field conversions, not merely this one-line body.
<!-- /registry -->

<!-- registry:review:7b78712629aac6e6 -->
<a id="review-7b78712629aac6e6"></a>

All nine sources read the decoded cap/rate and preserve ordered branches: zero rate, zero requested output, exactly 10000 basis points with checked cap-plus-output, then checked u128 multiplication, checked scale-minus-rate, ceil_div, checked raw-minus-output, cap comparison and either checked output-plus-cap or narrowing of raw input. Positive outputs above 10000 fail even at cap zero; zero output still succeeds. Zero cap can recover u64::MAX before an uncapped narrowing would fail. These operations, conversions, helper and constants match the existing total model without restricting the decoded u16 domain.
<!-- /registry -->

<!-- registry:review:166cd5aa480c5d0f -->
<a id="review-166cd5aa480c5d0f"></a>

All nine sources compare the requested epoch to the currently decoded newer epoch and return a reference to newer on >=, otherwise older. The copied-value observation preserves the entire configuration and does not claim returned-reference identity. Source review includes the old/new integer representations; the older activation epoch, authority bytes and withheld amount are not inspected or changed. This observation has no independently registered Rust callable identity.
<!-- /registry -->

<!-- registry:review:8d03aede94ab48b1 -->
<a id="review-8d03aede94ab48b1"></a>

All nine sources return the actual shared field reference of the existing receiver, newer on epoch >= current newer epoch and older otherwise, with unchanged state. There is no callback, allocation, borrow-guard acquisition or consumption in the reached closure. Reviewed PodU64/U64 conversions are ordinary little-endian reads; field location and live parent permissions remain the existing source interpretation obligations. Native pointer comparisons distinguish both fields and two equal-valued parent configurations. The generic family is preserved; these samples do not prove arbitrary lifetimes or a Rust memory interpretation.
<!-- /registry -->

<!-- registry:review:7e2afbfd5094ed77 -->
<a id="review-7e2afbfd5094ed77"></a>

The declared base58 literal is unchanged in every API-bearing release. The reached declare_id macro returns the exact 32-byte constant. Pubkey 2.4.0 is a transparent [u8; 32]; Pubkey 3 and 4 reexport Address through the recorded dependency profiles. Address macros distinguish a bpf static ID from a non-bpf const ID, but id() returns the same constant bytes in both branches and performs no allocation. The 0.0.0 release lacks the selected root-level API.
<!-- /registry -->

<!-- registry:review:b0c9ae64c62db2c8 -->
<a id="review-b0c9ae64c62db2c8"></a>

Every API-bearing release accepts either program before allocation, packs tag 9 with one push, then calls Vec::with_capacity(3 + signer count) and pushes source/destination/authority/signers in source order. Authority is a signer iff no explicit signers, duplicates are preserved and no execution-state check is performed. Selected source bodies are identical modulo Pubkey/Address, with unchanged reached check, pack arm and metadata constructors. The full family preserves data-first resource lifetime and partial-metadata-before-data cleanup. The 0.0.0 API is absent.
<!-- /registry -->

<!-- registry:review:48bd7be8d2264f0a -->
<a id="review-48bd7be8d2264f0a"></a>

Every API-bearing release accepts either program before allocation, packs tag 9 with one push, then calls Vec::with_capacity(3 + signer count) and pushes source/destination/authority/signers in source order. Authority is a signer iff no explicit signers, duplicates are preserved and no execution-state check is performed. Selected source bodies are identical modulo Pubkey/Address, with unchanged reached check, pack arm and metadata constructors. The full family preserves data-first resource lifetime and partial-metadata-before-data cleanup. The 0.0.0 API is absent. This entry is only the existing value observation; compatible releases share admission and returned values, while allocation, owned-resource lifecycle and abnormal exits remain covered by the separately registered full family.
<!-- /registry -->

<!-- registry:review:12548e5b65371c7e -->
<a id="review-12548e5b65371c7e"></a>

The crate-specific program check runs first: legacy-only for spl-token-interface, either token program for spl-token-2022-interface. The builder packs tag 18 by a single push followed by one owner-byte extend, then constructs a two-entry metadata literal (writable nonsigner account, readonly nonsigner mint); owner appears only in the data. The body and selected packing branch match in all API-bearing releases modulo key-type spelling. The full family retains data-before-metadata allocation, target enumSize reservation, actual vector identities, dependency outcomes and cleanup. The 0.0.0 API is absent.
<!-- /registry -->

<!-- registry:review:356fa700da31921e -->
<a id="review-356fa700da31921e"></a>

The crate-specific program check runs first: legacy-only for spl-token-interface, either token program for spl-token-2022-interface. The builder packs tag 18 by a single push followed by one owner-byte extend, then constructs a two-entry metadata literal (writable nonsigner account, readonly nonsigner mint); owner appears only in the data. The body and selected packing branch match in all API-bearing releases modulo key-type spelling. The full family retains data-before-metadata allocation, target enumSize reservation, actual vector identities, dependency outcomes and cleanup. The 0.0.0 API is absent. This entry is only the existing value observation; compatible releases share admission and returned values, while allocation, owned-resource lifecycle and abnormal exits remain covered by the separately registered full family.
<!-- /registry -->

<!-- registry:review:c2df0ff347ff2ea2 -->
<a id="review-c2df0ff347ff2ea2"></a>

Every API-bearing release accepts either token program before allocation; pack reserves size_of<TokenInstruction>, pushes tag 12, extends the eight little-endian amount bytes, then separately pushes the decimals byte. The builder reserves 4 + signer count metadata and pushes writable source, readonly mint, writable destination, readonly authority and every readonly signer in order. It imposes no mint-decimal, balance or signer-limit validation. Reached bodies and arm match modulo key type. Full family allocation calls, resource identities, exceptional dependency exits and cleanup remain intact; 0.0.0 lacks the API.
<!-- /registry -->

<!-- registry:review:f9e706a74ab30fc2 -->
<a id="review-f9e706a74ab30fc2"></a>

Every API-bearing release accepts either token program before allocation; pack reserves size_of<TokenInstruction>, pushes tag 12, extends the eight little-endian amount bytes, then separately pushes the decimals byte. The builder reserves 4 + signer count metadata and pushes writable source, readonly mint, writable destination, readonly authority and every readonly signer in order. It imposes no mint-decimal, balance or signer-limit validation. Reached bodies and arm match modulo key type. Full family allocation calls, resource identities, exceptional dependency exits and cleanup remain intact; 0.0.0 lacks the API. This entry is only the existing value observation; compatible releases share admission and returned values, while allocation, owned-resource lifecycle and abnormal exits remain covered by the separately registered full family.
<!-- /registry -->

<!-- registry:review:8688c973210fad86 -->
<a id="review-8688c973210fad86"></a>

Every API-bearing release rejects the legacy and all other programs before allocation. It first constructs a three-entry metadata literal, then pushes all signer keys, and only then evaluates TokenInstruction::WithdrawExcessLamports.pack in the returned Instruction data field (reserve enumSize, push tag 38). This differs from the other builders, and exactly matches the existing metasThenData/fromListThenPush family. Signer-push unwind drops partial metadata without starting pack; packing unwind drops partial bytes before the already-moved metadata. Completed Instruction drop still retires metadata before bytes. All selected bodies/arms match modulo key type; 0.0.0 is absent.
<!-- /registry -->

<!-- registry:review:ad1d9bef8e06d13f -->
<a id="review-ad1d9bef8e06d13f"></a>

Every API-bearing release rejects the legacy and all other programs before allocation. It first constructs a three-entry metadata literal, then pushes all signer keys, and only then evaluates TokenInstruction::WithdrawExcessLamports.pack in the returned Instruction data field (reserve enumSize, push tag 38). This differs from the other builders, and exactly matches the existing metasThenData/fromListThenPush family. Signer-push unwind drops partial metadata without starting pack; packing unwind drops partial bytes before the already-moved metadata. Completed Instruction drop still retires metadata before bytes. All selected bodies/arms match modulo key type; 0.0.0 is absent. This entry is only the existing value observation; compatible releases share admission and returned values, while allocation, owned-resource lifecycle and abnormal exits remain covered by the separately registered full family.
<!-- /registry -->

<!-- registry:review:d883d470f0a21ad8 -->
<a id="review-d883d470f0a21ad8"></a>

No onchain module/API exists through 0.6.1. Versions 0.7.0–7.0.0 append every additional signer and do not perform the current multisig owner/size/key filter or clear authority signer status. Versions 8.0.0/8.0.1/9.0.0 have the modern local multisig wrapper, but their hook 0.10/resolver 0.10 profile preserves the signer flag of a new extra account; the model always clears it. Version 10.0.0 is compatible under the executed allowed hook 2.1/resolver 0.11.1 profile: its PodMultisig pod_from_bytes helper is exactly try_from_bytes.map_err(InvalidArgument), and its interface 2.1.0 Mint parsing/getter and instruction closures correspond. Version 11.0.0 has the same full ordinary preparation under the baseline interface 3.0.0 profile. Version 11.1.0 requires interface>=3.1.0, which removes the 83-byte repeated-zero padding allocation from extended Mint parsing. The full family includes that allocation, its possible exits and retirement; the native 4-case padding probes expose 1/1 events at 10.0/11.0 versus 0/0 at 11.1. Thus 11.1.0 and 12.0.0 do not fit the complete family despite identical top-level wrapper source and passing ordinary corpus samples. Version 12.0.0 also makes pinocchio-transfer-hook-interface 0.1.0 mandatory, forcing resolver>=0.11.4. That resolver retains one collected data-Ref vector, accumulates pending AccountInfos and borrows each resolved extra, including the last. A final extra account with exclusively held data succeeds in resolver 0.11.1 preparation but fails AccountBorrowFailed in 0.11.4 before CPI. The old profile is rejected by Cargo; this is an incompatibility for both facets, not an optional dependency choice.
<!-- /registry -->

<!-- registry:review:c1bbb4a0a16744c0 -->
<a id="review-c1bbb4a0a16744c0"></a>

No onchain module/API exists through 0.6.1. Versions 0.7.0–7.0.0 append every additional signer and do not perform the current multisig owner/size/key filter or clear authority signer status. Versions 8.0.0/8.0.1/9.0.0 have the modern local multisig wrapper, but their hook 0.10/resolver 0.10 profile preserves the signer flag of a new extra account; the model always clears it. Version 10.0.0 is compatible under the executed allowed hook 2.1/resolver 0.11.1 profile: its PodMultisig pod_from_bytes helper is exactly try_from_bytes.map_err(InvalidArgument), and its interface 2.1.0 Mint parsing/getter and instruction closures correspond. Version 11.0.0 has the same full ordinary preparation under the baseline interface 3.0.0 profile. Version 11.1.0 requires interface>=3.1.0; removing the temporary padding vector is within the explicitly omitted allocation effects, so the value/borrow/error preparation still corresponds under resolver 0.11.1. Version 12.0.0 also makes pinocchio-transfer-hook-interface 0.1.0 mandatory, forcing resolver>=0.11.4. That resolver retains one collected data-Ref vector, accumulates pending AccountInfos and borrows each resolved extra, including the last. A final extra account with exclusively held data succeeds in resolver 0.11.1 preparation but fails AccountBorrowFailed in 0.11.4 before CPI. The old profile is rejected by Cargo; this is an incompatibility for both facets, not an optional dependency choice.
<!-- /registry -->

<!-- registry:review:ef79aabb38ac584c -->
<a id="review-ef79aabb38ac584c"></a>

The reviewed 3.1.1 and 3.1.2 state.rs files are byte-identical. Derived Clone copies all five fields of the concrete repr(C) Mint, retaining the receiver without allocation or user callbacks; neither Pack nor IsInitialized is called. COption<Address> preserves None versus Some and all 32 payload bytes. The declared compatible range assumes preservation of that complete copy and the selected field providers. A separate Rust binding must check the actual 88-byte host layout; native recordings serialize 82 logical account bytes and do not prove target-layout equivalence.
<!-- /registry -->

<!-- registry:review:8307f2be6ed8edfb -->
<a id="review-8307f2be6ed8edfb"></a>

The provided getter first calls the actual get_extension_bytes implementation, then performs the selected Pod view of that same borrowed slice. Preserve provider effects and size/alignment errors; default scanning is supplied separately. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:31339c49ec573e1f -->
<a id="review-31339c49ec573e1f"></a>

Allocate after the accessor, decode types and stop at sentinel/spare byte. Push each type before checking payload bounds, and destroy the vector on a reached error; retain ordered first-class ownership on success. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:612275de10c23d40 -->
<a id="review-612275de10c23d40"></a>

Evaluate the accessor before packed length, then scan into an owned vector. Use the current used prefix, mask only ordinary existing-extension lookup errors, apply saturating arithmetic/multisig adjustment and retain cleanup at those stages. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:b3abe0f8ed417e33 -->
<a id="review-b3abe0f8ed417e33"></a>

Deduplicate source references before fixed-length calculation, preserving each first occurrence and all allocation/push failures before variable-length rejection. Retain header/base/multisig arithmetic and destruction; the existing bound theorem needs no added precondition. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:c0076cfcdac79236 -->
<a id="review-c0076cfcdac79236"></a>

Check base size/multisig, call Pack::unpack, then validate the tail using a zero-vector padding comparison and current marker read. Preserve base/temporary destruction and reject the exact marker-only tail; 9.0.0 changes that boundary and is excluded. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:c68e958a595eb369 -->
<a id="review-c68e958a595eb369"></a>

Check Token-2022 before metadata allocation; validate authority before metadata address. Preserve tags 39/0, reject Some(zero), and retain reached owners and allocation/error cleanup. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:44243189cac7d10f -->
<a id="review-44243189cac7d10f"></a>

Call the selected typed getter once; decode its zero-or-key field, or destroy an ordinary owned error before returning None. Retain Borsh String destruction, unwind and terminal effects; no CPI is invoked. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:5174fd0a7bbaedd9 -->
<a id="review-5174fd0a7bbaedd9"></a>

Select the newer fee at epoch equality. Decode POD fields and retain checked arithmetic and u64 narrowing before capping, including None for invalid raw rates/overflow; do not assume a rate bound. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:bd85ea367e2fbc37 -->
<a id="review-bd85ea367e2fbc37"></a>

Select the newer fee at epoch equality. Retain zero/full/excess-rate branches, checked inverse subtraction/addition and the fee of the derived gross amount, including None; do not assume a rate bound. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:28cc3ea33c68497c -->
<a id="review-28cc3ea33c68497c"></a>

Check Token-2022, allocate the writable mint meta, then encode tag 25 and the one-byte COption/key fields. Some(zero) stays valid; preserve metadata-before-data allocation and partial cleanup. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:a0291dcd7dd0de3a -->
<a id="review-a0291dcd7dd0de3a"></a>

Return the declared Token-2022 program key by value without allocation or syscall; preserve the actual defining crate and the exact Pubkey dependency variants. The inspected 8.0.0/8.0.1 references agree. Compatibility within 8.x assumes this operation and its selected dependencies preserve the complete contract.
<!-- /registry -->

<!-- registry:review:c6262f5c8828c172 -->
<a id="review-c6262f5c8828c172"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes the reached extension lookup and errors, all-byte optional-key sentinel and unchanged borrowed state; missing or invalid extensions keep their existing result. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:9402441d10fff9b6 -->
<a id="review-9402441d10fff9b6"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes little-endian POD decoding, checked u128 multiplication and ceiling division, u64 narrowing before maximum-fee capping, and all raw basis-point values including rates above 10000. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:c64a0e02627f9b07 -->
<a id="review-c64a0e02627f9b07"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes the zero amount/rate and full-rate cap branches, checked denominator/subtraction/addition, then the fee of the derived gross amount; invalid raw rates may return None and narrowing precedes capping. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:c44f0f273a790d8f -->
<a id="review-c44f0f273a790d8f"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes the exact AccountState equality test, including initialized and uninitialized values, with unchanged receiver. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:ef05754abb0f5ce1 -->
<a id="review-ef05754abb0f5ce1"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes selecting the newer fee at epoch equality and the older fee below it, while preserving the borrowed field identity and receiver. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:6c9202e23c839cb6 -->
<a id="review-6c9202e23c839cb6"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes the current borrowed TLV slice, including its exact extent/reference identity, without parsing, allocation or mutation. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:657edf1c7337d204 -->
<a id="review-657edf1c7337d204"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 11 and account/mint/authority/signers in order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:b376731ee5466374 -->
<a id="review-b376731ee5466374"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes metadata-before-data allocation, tag 22 and one writable account, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:c22be15772d4f046 -->
<a id="review-c22be15772d4f046"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 15, amount and decimals bytes, source/mint/authority/signers in order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:cca78589eecf0740 -->
<a id="review-cca78589eecf0740"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 20, decimals, mint authority and optional freeze authority, followed by one writable mint, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:31b98ce174d6ce21 -->
<a id="review-31b98ce174d6ce21"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes metadata-before-data allocation, tag 32 and one writable mint, checking Token-2022 only before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:e4f89e847c853a39 -->
<a id="review-e4f89e847c853a39"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 6, the exact authority enum byte and optional key, 3 + N reserved but 2 + N initialized metadata slots, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order, including seventeen authority variants and distinct None/Some(zero). Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:ea5404ed6cc70e5d -->
<a id="review-ea5404ed6cc70e5d"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 7, little-endian amount and mint/destination/authority/signers in order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:eae9c1b5dd863903 -->
<a id="review-eae9c1b5dd863903"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 10 and account/mint/authority/signers in order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:d767ce8a622e18aa -->
<a id="review-d767ce8a622e18aa"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes comparison of every key byte with the fixed Token-2022 native-mint ID, without allocation or state change. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->

<!-- registry:review:b0b30c903babfce9 -->
<a id="review-b0b30c903babfce9"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 18, owner key bytes and account/mint metadata order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:46c1147a4b0fb846 -->
<a id="review-46c1147a4b0fb846"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 9 and source/destination/authority/signers in order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:d548401b6c9db70e -->
<a id="review-d548401b6c9db70e"></a>

The inspected 8.0.0/8.0.1 operation and reached helpers agree. The declared 8.x range assumes tag 12, amount/decimals bytes and source/mint/destination/authority/signers in order, checking either token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:66db908697abe7d4 -->
<a id="review-66db908697abe7d4"></a>

The declared compatible range assumes minimum-length and multisig-collision checks before the actual generic Pack::unpack; tail failure/unwind destroys the owned base. A nonempty remainder allocates a zero-filled padding Vec, captures the comparison, drops that temporary, and only then reads/checks the current account marker. Ending exactly at the marker returns an empty borrowed tail, not a validated TLV stream. The allocation-removing 3.1.0 tail implementation is excluded.
<!-- /registry -->

<!-- registry:review:b0cc2e711caa8716 -->
<a id="review-b0cc2e711caa8716"></a>

Preserve accessor-before-allocation and type/length-header checks followed by push BEFORE payload bounds validation, with source-order cleanup and actual vector ownership. A failing push can precede malformed-payload rejection; the later bounds-before-push scan differs. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:de622f5f7245f288 -->
<a id="review-de622f5f7245f288"></a>

Preserve the empty Vec and ordered per-input pushes, including duplicates and NonTransferableAccount then ImmutableOwner. Do not replace the reached allocation/push protocol by a flat_map/collect protocol merely because successful lists agree. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:472bb224cb93d2bb -->
<a id="review-472bb224cb93d2bb"></a>

Preserve full temporary-reference deduplication before type-size calculation, actual first-occurrence references, cleanup, base/marker and multisig adjustment. The 28-kind/299-byte bounds are derived, not caller assumptions. The later PermissionedBurn enum and sizing/iterator families are outside this profile. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:daa1cf890c808f2d -->
<a id="review-daa1cf890c808f2d"></a>

Preserve unsigned little-endian Pod decoding, newer-fee selection at epoch equality, checked ceiling arithmetic, u64 narrowing BEFORE maximum-fee capping and None for applicable invalid raw rates. No basis-point-domain precondition is added. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->
