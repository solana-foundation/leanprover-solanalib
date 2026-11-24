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

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:6e7648dc76cd2eac -->
<a id="review-6e7648dc76cd2eac"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Exact versioned mathematical API with closed reference, precondition and (where relation-based) execution witnesses. Source anchors support the value/request interpretation; they do not establish a Rust body or ABI proof.

Manual archive review of the derived Clone fields and reached canonical key clone: pubkey/Address bytes and both Boolean fields are copied without allocation, mutation, validation or guard acquisition. Legacy repr(C) and modern layouts require separate ABI interpretations; the value/lifetime contract is shared.
<!-- /registry -->

<!-- registry:review:368a351053a95def -->
<a id="review-368a351053a95def"></a>

0.0.1 is a placeholder without the API. Every direct implementation from 0.0.2 through 4.0.0 has byte-identical relevant AccountMeta fields and constructor body: preserve pubkey and is_signer, set is_writable to true. 3.5.1 reexports solana-instruction-v4 ^4.0; its only published target 4.0.0 was reviewed and natively executed. Renamed key wrappers/reexports preserve the canonical value observation. No deduplication, address validation or allocation occurs.
<!-- /registry -->

<!-- registry:review:69e9e25daa077bb4 -->
<a id="review-69e9e25daa077bb4"></a>

0.0.1 is a placeholder without the API. Every direct implementation from 0.0.2 through 4.0.0 has byte-identical relevant AccountMeta fields and constructor body: preserve pubkey and is_signer, set is_writable to false. 3.5.1 reexports solana-instruction-v4 ^4.0; its only published target 4.0.0 was reviewed and natively executed. Renamed key wrappers/reexports preserve the canonical value observation. No deduplication, address validation or allocation occurs.
<!-- /registry -->

<!-- registry:review:2fb770428902189d -->
<a id="review-2fb770428902189d"></a>

Only placeholder 0.0.1 lacks the API. All direct implementations with the API have identical Instruction fields, generic bounds and body: call the selected serializer on &T, unwrap, then move program_id, the supplied accounts Vec and returned data Vec into Instruction. Serializer error therefore unwinds through unwrap rather than becoming an ordinary Result error; the retained accounts Vec is dropped at the actual reached state. Internal partial-data cleanup belongs to the serializer dependency, and terminal exits skip subsequent cleanup. 3.5.1 forwards the feature and public item to reviewed 4.0.0. Generic stateful/panicking serializers remain in scope; tests include them.
<!-- /registry -->

<!-- registry:review:634c69b9e5eb1999 -->
<a id="review-634c69b9e5eb1999"></a>

The API first appears in 3.2.0; every earlier stable release lacks it. All direct implementations with the API have identical Instruction fields, generic bounds and body: call the selected serializer on &T, unwrap, then move program_id, the supplied accounts Vec and returned data Vec into Instruction. Serializer error therefore unwinds through unwrap rather than becoming an ordinary Result error; the retained accounts Vec is dropped at the actual reached state. Internal partial-data cleanup belongs to the serializer dependency, and terminal exits skip subsequent cleanup. 3.5.1 forwards the feature and public item to reviewed 4.0.0. Generic stateful/panicking serializers remain in scope; tests include them.
<!-- /registry -->

<!-- registry:review:42ae8b05e4f83a04 -->
<a id="review-42ae8b05e4f83a04"></a>

Reference: solana-instruction 2.3.3. Compatibility in [2.3.3, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve derived field cloning and the reached canonical key clone: copy all key bytes and both Boolean fields from the live current shared borrow, preserve the existing source state and borrow, and add no allocation, mutation, validation or borrow guard. Bind the selected release to its actual legal source representation separately; the frozen 2.3.3 physical clone/ABI fixture is not generalized by a catalog range.
<!-- /registry -->
