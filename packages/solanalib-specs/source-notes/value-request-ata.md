# Associated Token Account 0.4.0 helper request

`CreateIdempotent::invoke` constructs a request for the ATA program address
`ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL` with the single data byte `[1]`.
The account order is funding, associated account, wallet, mint, System program,
Token program. Their `(signer, writable)` flags are `(1, 1)`, `(0, 1)`, followed
by four `(0, 0)` entries. The unsigned wrapper passes an empty signer list.

The model preserves caller-provided System and Token program addresses; it does
not validate or replace them. It also preserves duplicate account identities
and positions. The common canonical program address is the exact 32-byte base58
decoding of the declaration, not a shortened numeric identifier.

The local wrapper derives each metadata key from the current account pool and
calls the InstructionView 2.1.0 checked array entry with the same six handles.
The first two positions request writable access and reject live data leases;
the four readonly positions perform no borrow check in this revision. The
shared checked model retains address/check order, aliases and the actual
initialized descriptors. The two arrays have equal fixed size six and satisfy
the compile-time capacity bound.

The v2 descriptor copies the current raw flag bytes and header padding exactly.
These bytes are an explicit current-state observation alongside the account
pool. The model imposes no 0/1 restriction or zero-padding assumption.

Checked errors propagate unchanged before opaque invocation. The remaining
opaque boundary returns Unit: normal completion becomes `Ok(())`, while unwind
and terminal effects are preserved. A freely chosen ordinary invocation error
is not part of this source signature. The name does not imply account creation,
existing-account acceptance, authentication or rollback. The local fixed arrays
and borrowed references introduce no owned-vector or account-guard cleanup.

Reviewed pinned sources are
[src/lib.rs line 5](https://github.com/anza-xyz/pinocchio/blob/3a3a1a65984ffd0b6debe460276c0a6ebb685dcb/programs/associated-token-account/src/lib.rs#L5)
for the program address and
[create_idempotent.rs line 38](https://github.com/anza-xyz/pinocchio/blob/3a3a1a65984ffd0b6debe460276c0a6ebb685dcb/programs/associated-token-account/src/instructions/create_idempotent.rs#L38)
for the unsigned wrapper. Local signed preparation starts at 43 and stops at
the actual invocation call at 65. The wrapper source slice stops at that checked call. Shared checked-entry
semantics are documented in the [InstructionView note](value-request-instruction-view.md);
actual unchecked invocation bodies remain opaque. The pinned dependencies are InstructionView 2.1.0, AccountView 2.0.0
and Address 2.6.0. The published crate lockfile instead selects Address 2.5.0;
the review profile is an explicit compatible selection, not a claim about every
client resolution. The Lean model imports shared request and checked-preparation
vocabulary.

Tests check exact order, flags, data, empty signers, current supplied program
addresses, duplicate identities, normal state effects and unwind state. A real
exclusive acquisition on the second writable account rejects with no possible
invocation outcome. A separate live exclusive lease on a readonly wallet still
reaches invocation, distinguishing the selected v2 behavior from v1. These are
mathematical executions; legal source handles, `AsRef`, Rust implementation,
byte storage and representation correspondence remain open bindings. The raw
header observation must agree with the actual source bytes and their Boolean
getters at each legal current handle.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:4626f6ec58659e66 -->
<a id="review-4626f6ec58659e66"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

CreateIdempotent constructs the exact six-account request from current pool keys, retaining flags, aliases and supplied program identities. Its proved fixed cardinality fits InstructionView 2.1.0; checked directV2 preparation runs before the actual opaque unit-returning invocation.
<!-- /registry -->

<!-- registry:review:87cfbc9f0a7c2c53 -->
<a id="review-87cfbc9f0a7c2c53"></a>

The shared families preserve exact value bytes, source guard and seed order, destination initialization, profile-specific error conversion, and actual callback state and exits. Version wrappers retain their complete family and source-dependent reader error kind. The source review is detailed in source-notes/address-profiles.md.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.
<!-- /registry -->

<!-- registry:review:3f1548ef8a8836c7 -->
<a id="review-3f1548ef8a8836c7"></a>

CreateIdempotent::invoke delegates with an empty signer tree; preserves the six ordered funding/account/wallet/mint/System/Token identities including aliases; uses writable signer/writable/readonly/readonly/readonly/readonly metadata, the associated-token program ID and data [1]. Supplied System/Token account keys are used directly, without replacement or validation. Only the first two positions are borrow checked. The wrapper file is byte-identical in 0.4.0 and 0.5.0. The latter changes AccountView ^2.0 / InstructionView ^2.1 to AccountView ^3.0 / InstructionView ^3.0. InstructionView 2.1.0 and 3.0.0 cpi.rs and lib.rs are byte-identical; the AccountView 3 owner() return-by-value change is bypassed by direct raw-header/owner-field-pointer initialization. The named wrapper exists in every release. Releases 0.1.0/0.1.1/0.2.0 reach old Pinocchio AccountInfo helpers, and 0.3.0 reaches InstructionView 1.0.0. They normalize descriptor flags and reject readonly exclusive borrows. Both differences violate the existing full v2 relation; no extra canonical-header or no-borrow premise is added.
<!-- /registry -->

<!-- registry:review:f568791c6e6e856d -->
<a id="review-f568791c6e6e856d"></a>

The 2.0.0 reference searches the fixed ATA program with wallet, token-program and mint byte seeds in that order, then discards only the bump. Compatibility within 2.x assumes this seed order, zero-initialized Pubkey search output and all reached failure effects remain unchanged under the selected dependency profile.
<!-- /registry -->

<!-- registry:review:e4575ab7dc5f1d40 -->
<a id="review-e4575ab7dc5f1d40"></a>

The declared compatible range assumes ordered wallet/token-program/mint seeds, the fixed ATA ID, the actual dependency PDA search and discarding only its returned bump. The selected facade reaches MaybeUninit Address search; a zero-initialized output profile is not interchangeable.
<!-- /registry -->
