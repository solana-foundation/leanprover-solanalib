# System instruction values and local helpers

The common request vocabulary preserves ordered accounts and nested signer
seeds. The System program address is 32 zero bytes, the base58 value
`11111111111111111111111111111111`. Amount and space are mathematical naturals
encoded by the existing u64 little-endian helpers. Their correspondence to Rust
u64 arguments is a source-binding obligation, not a family entry restriction.

| Operation | Metadata flags `(signer, writable)` | Data |
| --- | --- | --- |
| Create account | From `(1, 1)`, to `(1, 1)` | u32 little-endian tag 0, u64 lamports, u64 space, 32 owner bytes |
| Transfer | From `(1, 1)`, to `(0, 1)` | u32 little-endian tag 2, u64 lamports |
| Allocate | Account `(1, 1)` | u32 little-endian tag 8, u64 space |
| Assign | Account `(1, 1)` | u32 little-endian tag 1, 32 owner bytes |

The `solana_system_interface.instruction::{create_account,transfer}`
value contracts remain **instruction value observations**. They describe the returned program address,
metadata and bytes, including duplicate keys with different flags. The source
allocates metadata and serializes the System instruction, selecting bincode or
wincode through features. Allocation, serialization errors and non-returning
behavior are not part of these two models, so they are not full operational
constructor coverage. They neither call nor prove the System program.

The primary source-facing models use
`create_account_operational_contract` and `transfer_operational_contract`.
These closed families model the complete constructor control flow above
explicit allocation, serialization, unwrap-failure and destruction providers.
The value models remain separate observations in the registry and
serve as model dependencies, without weakening or replacing the stated coverage of the operational
families.

The source first constructs `vec![...]` containing the two ordered metadata
values, including separate flags when the keys coincide. The `fromList`
dependency must return an owned metadata resource before serialization starts.
An allocation unwind or terminal exit cannot call the serializer or drop a
resource that was never returned. On allocation success, the model passes the
actual resulting state and handle to the matching Instruction 3.4.0 constructor.
Its serializer receives the tagged System data. Serialization success moves
the exact metadata and byte handles into the returned instruction; a serializer
error follows the non-returning unwrap path. Serialization or unwrap unwinding
drops retained metadata using the current state. Terminal exits skip later
cleanup, and double unwind follows the explicit terminal policy.

The operational argument explicitly chooses bincode or wincode. In the source,
wincode takes precedence when that feature is enabled; bincode is the other
enabled branch. Binding the features of a recorded binary remains a separate
obligation. The mathematical provider trace does not itself prove serialized
bytes or vector framing: those observations require the local primitive vector
laws, codec correctness and resource frames. No allocator success, callback
rollback, complete SDK postcondition, or std implementation proof is assumed.
The source owns partial-construction cleanup inside the allocation/serializer
dependencies, and error formatting/panic cleanup inside the unwrap dependency.

The Pinocchio System 0.6.0 helper models cover `Allocate::invoke_signed`,
`Assign::invoke_signed` and `Transfer::invoke`. Their account and metadata
arrays have exact sizes one, one and two. The selected profile resolves
`pinocchio::cpi::invoke_signed` through Pinocchio 0.11.1 to the InstructionView 2.1.0 checked array entry over AccountView 2.0.0. Unsigned transfer calls its
own signed wrapper with an empty signer slice. Signed helpers retain the full
nested seed tree, and account aliases retain every source position.

The request keys are read from the current shared account pool at wrapper
entry. They cannot be chosen independently from the supplied account handles.
The shared checked model performs the count check and ordered address/borrow
checks, initializes the actual descriptor prefix and only then reaches the
opaque unit-returning invocation. All System positions request writable access,
so any live data lease causes a local `AccountBorrowFailed`. Identity `AsRef`
conversion neither changes the pool nor acquires a new guard. The exact source
array sizes discharge the compile-time limit of 64.

The v2 initializer copies the current raw signer, writable, executable and
padding bytes. The family therefore receives a current raw-header observation
in addition to the account pool; it does not normalize nonzero flags to one or
discard padding. Canonical bytes are a choice of the closed sample only.

A checked error is returned unchanged, in the checking state. Normal opaque
completion returns `Ok(())` with its actual state; the Unit signature cannot
inject a new ordinary SDK error. Opaque unwind and terminal exits retain their
actual effects. These wrappers own only fixed stack arrays and borrowed
references, so they add no vector or account-guard cleanup callback. No funding,
allocation, owner change, authorization, rollback or callee-success property is
supplied by these contracts.

The local builder source slices stop at their checked invocation calls. The
checked-entry definitions and their source review are shared with the
[InstructionView model](value-request-instruction-view.md); unchecked invocation
bodies and invoked programs remain opaque. Legal live handles, concrete
`AsRef` identity, source storage/layout and local byte initialization remain
implementation-binding obligations. In particular, the source binding must
relate the supplied raw bytes to the Boolean getters of the pool at each legal current
handle. The mathematical family witnesses execute
nonempty checked paths; they are not Rust execution proofs.

| Version | Source | Anchors |
| --- | --- | --- |
| System interface 3.2.0 | [system-interface/src/instruction.rs](https://github.com/anza-xyz/solana-sdk/blob/c36b228d023aa6c1869565768b225b685d7dc7c1/system-interface/src/instruction.rs#L487) | Serialization helper alternatives 305/315; create account 487; transfer 902 |
| System interface 3.2.0 | [system-interface/src/lib.rs](https://github.com/anza-xyz/solana-sdk/blob/c36b228d023aa6c1869565768b225b685d7dc7c1/system-interface/src/lib.rs#L34) | System program ID 34 |
| Pinocchio System 0.6.0 | [programs/system/src/instructions/allocate.rs](https://github.com/anza-xyz/pinocchio/blob/ef16a3a3e134c44d1a5fcd49cc35d04246006bf4/programs/system/src/instructions/allocate.rs#L26) | Local builder 26; invocation stop 44 |
| Pinocchio System 0.6.0 | [programs/system/src/instructions/assign.rs](https://github.com/anza-xyz/pinocchio/blob/ef16a3a3e134c44d1a5fcd49cc35d04246006bf4/programs/system/src/instructions/assign.rs#L26) | Local builder 26; invocation stop 44 |
| Pinocchio System 0.6.0 | [programs/system/src/instructions/transfer.rs](https://github.com/anza-xyz/pinocchio/blob/ef16a3a3e134c44d1a5fcd49cc35d04246006bf4/programs/system/src/instructions/transfer.rs#L25) | Unsigned wrapper 25; local signed preparation 30; invocation stop 50 |

Tests check exact little-endian value observations, unsigned calls, aliases,
metadata flags and normal/terminal callback effects. Concrete successful
AccountView acquisitions supply live-lease rejection controls for allocate,
assign and the second position of the transfer, with an impossible invocation provider.
Operational System-interface constructor controls also check
allocation-before-serialization order, both serializer choices, fresh handles,
allocation failures and cleanup that retires only newly owned metadata.
Source/archive identity and these mathematical facts remain separate from
Rust implementation correctness.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:65cb96dc162fd1b5 -->
<a id="review-65cb96dc162fd1b5"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Allocate, Assign and Transfer construct their exact fixed requests from current pool keys and retain aliases, flags, scalar bytes and signed/unsigned seed shape. Their mathematical families require True, with Rust u64 scalar representation separate from the existing byte encoding. Their fixed cardinalities discharge the InstructionView 2.1.0 source const bound; checked directV2 preparation runs before the actual opaque unit-returning invocation.
<!-- /registry -->

<!-- registry:review:27fd35c41a9b380b -->
<a id="review-27fd35c41a9b380b"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Exact versioned mathematical API with closed reference, precondition and (where relation-based) execution witnesses. Source anchors support the value/request interpretation; they do not establish a Rust body or ABI proof.

Each reviewed constructor always supplies [funding signer+writable, destination writable+nonsigner, base signer+readonly], including aliases; no seed/derived-key validation. It constructs metadata before seed.to_string, then calls bincode on variant 3/base/String/u64 lamports/u64 space/owner and drops the temporary String. Bincode 1.3.3 uses fixed little-endian u32/u64 and String byte length; normal output resources move and every admitted allocation/serialization/unwrap/cleanup exit is retained. The pinned String/Vec deallocator is lawful GlobalAlloc and has no unwound outcome; generalized destructor-unwind cleanup in the mathematical provider graph is not a claim about a compiler return-place. System interface 3.2.0 conditionally omits a duplicate base and is not admitted by this model. The reviewed 3.2.0 implementation allocates one new-account signer+writable metadata entry, then pushes the supplied optional payer regardless of lamports or key equality. It encodes variant 13/u64 lamports/u64 space/owner at the zero System program key. Bincode and wincode branches are separately selected; with both features wincode wins. Source ownership moves and cleanup/failure outcomes are modeled through actual-site providers, with no invocation or runtime effect claim.
<!-- /registry -->

<!-- registry:review:5209b1533c4f1f3b -->
<a id="review-5209b1533c4f1f3b"></a>

Allocate retains one writable signer account, System program ID, discriminator 8 encoded as u32 little endian, space encoded as u64 little endian, and every nested signer group/seed in order. Only the local borrow error can return ordinarily before the opaque call. 0.6.0 follows Pinocchio 0.11.x reexports to InstructionView 2.1.0. 0.6.1 and 0.7.0 replace generic checked preparation with equivalent local is_borrowed checks, fully initialized MaybeUninit arrays and the same raw CpiAccount initializer. The self-key/count checks removed in 0.6.1 are tautologies for these fixed arrays; omitted AsRef calls are the existing pure identity binding. Transfer eagerly reads both borrow bytes, but both are pure legal reads, the failure is the same AccountBorrowFailed and no stateful initialization/callback intervenes. 0.7.0 changes the dependency to Pinocchio 0.12.0 / InstructionView 3.0.0 / AccountView 3.0.0, whose reached local closure remains equivalent. Earlier 0.0.0–0.4.0 use Pinocchio AccountInfo and normalize descriptor flags; 0.5.0 uses AccountView/InstructionView 1.0.0 and also normalizes. The current full contract explicitly preserves arbitrary source flag bytes and copied padding, so these releases are incompatible even where canonical-header samples agree. Every release has the named wrapper; API absence is not the reason. Yanked 0.0.0 is included; its broad ^0 dependency also admits source-incompatible API resolutions.
<!-- /registry -->

<!-- registry:review:c7565d84fc60a9a5 -->
<a id="review-c7565d84fc60a9a5"></a>

Assign retains one writable signer account, System program ID, discriminator 1 as u32 little endian, the exact 32 owner bytes and all ordered nested signer groups. It does not validate the proposed owner or caller authorization. 0.6.0 follows Pinocchio 0.11.x reexports to InstructionView 2.1.0. 0.6.1 and 0.7.0 replace generic checked preparation with equivalent local is_borrowed checks, fully initialized MaybeUninit arrays and the same raw CpiAccount initializer. The self-key/count checks removed in 0.6.1 are tautologies for these fixed arrays; omitted AsRef calls are the existing pure identity binding. Transfer eagerly reads both borrow bytes, but both are pure legal reads, the failure is the same AccountBorrowFailed and no stateful initialization/callback intervenes. 0.7.0 changes the dependency to Pinocchio 0.12.0 / InstructionView 3.0.0 / AccountView 3.0.0, whose reached local closure remains equivalent. Earlier 0.0.0–0.4.0 use Pinocchio AccountInfo and normalize descriptor flags; 0.5.0 uses AccountView/InstructionView 1.0.0 and also normalizes. The current full contract explicitly preserves arbitrary source flag bytes and copied padding, so these releases are incompatible even where canonical-header samples agree. Every release has the named wrapper; API absence is not the reason. Yanked 0.0.0 is included; its broad ^0 dependency also admits source-incompatible API resolutions.
<!-- /registry -->

<!-- registry:review:6566cb12033f4daf -->
<a id="review-6566cb12033f4daf"></a>

Transfer::invoke delegates with an empty signer tree. It retains ordered funding/destination identities (including aliases), writable signer/writable metadata, discriminator 2 as u32 little endian and the exact u64 little-endian lamports. It performs no balance, owner, source-data, signer-flag or writable-flag validation beyond the writable borrow checks. 0.6.0 follows Pinocchio 0.11.x reexports to InstructionView 2.1.0. 0.6.1 and 0.7.0 replace generic checked preparation with equivalent local is_borrowed checks, fully initialized MaybeUninit arrays and the same raw CpiAccount initializer. The self-key/count checks removed in 0.6.1 are tautologies for these fixed arrays; omitted AsRef calls are the existing pure identity binding. Transfer eagerly reads both borrow bytes, but both are pure legal reads, the failure is the same AccountBorrowFailed and no stateful initialization/callback intervenes. 0.7.0 changes the dependency to Pinocchio 0.12.0 / InstructionView 3.0.0 / AccountView 3.0.0, whose reached local closure remains equivalent. Earlier 0.0.0–0.4.0 use Pinocchio AccountInfo and normalize descriptor flags; 0.5.0 uses AccountView/InstructionView 1.0.0 and also normalizes. The current full contract explicitly preserves arbitrary source flag bytes and copied padding, so these releases are incompatible even where canonical-header samples agree. Every release has the named wrapper; API absence is not the reason. Yanked 0.0.0 is included; its broad ^0 dependency also admits source-incompatible API resolutions.
<!-- /registry -->

<!-- registry:review:eb933ec0c3d1825a -->
<a id="review-eb933ec0c3d1825a"></a>

create_account retains [from signer+writable, to signer+writable] and serializes tag 0, lamports, space, owner in that order (52 bytes). The program ID is 32 zero bytes, duplicate from/to keys remain two ordered entries, and full source u64 values including maxima are accepted by construction. System 1.0/2.0 uses Pubkey; 3.x uses Address with the same canonical 32-byte observation. Appending CreateAccountAllowPrefund in 3.0 does not alter variant tags 0 and 2. Versions through 3.0 call bincode directly; 3.1+ reaches create_instruction, choosing wincode if enabled. The serializer defaults and derive field order preserve fixed-width little-endian tags/u64 and the owner bytes across the reviewed codec patches. This registered entry is the narrower returned-value observation. It specifies constructed fields/bytes after successful construction and does not establish allocation order, unwind cleanup or termination; those belong to the separately classified operational entry.
<!-- /registry -->

<!-- registry:review:1dc90cf64696a31e -->
<a id="review-1dc90cf64696a31e"></a>

create_account retains [from signer+writable, to signer+writable] and serializes tag 0, lamports, space, owner in that order (52 bytes). The program ID is 32 zero bytes, duplicate from/to keys remain two ordered entries, and full source u64 values including maxima are accepted by construction. System 1.0/2.0 uses Pubkey; 3.x uses Address with the same canonical 32-byte observation. Appending CreateAccountAllowPrefund in 3.0 does not alter variant tags 0 and 2. Versions through 3.0 call bincode directly; 3.1+ reaches create_instruction, choosing wincode if enabled. The serializer defaults and derive field order preserve fixed-width little-endian tags/u64 and the owner bytes across the reviewed codec patches. The operational family retains the actual Vec construction before serializer invocation, successful resource-handle moves, unwrap failure, stateful dependency outcomes, current-table observations, retained-accounts destruction and terminal/double-unwind policy. It assumes no successful allocation/serialization or rollback. It is not replaced by the value observation.
<!-- /registry -->

<!-- registry:review:226697e9a0aa4d75 -->
<a id="review-226697e9a0aa4d75"></a>

transfer retains [from signer+writable, to nonsigner+writable] and serializes tag 2, lamports (12 bytes). The program ID is 32 zero bytes, duplicate from/to keys remain two ordered entries, and full source u64 values including maxima are accepted by construction. System 1.0/2.0 uses Pubkey; 3.x uses Address with the same canonical 32-byte observation. Appending CreateAccountAllowPrefund in 3.0 does not alter variant tags 0 and 2. Versions through 3.0 call bincode directly; 3.1+ reaches create_instruction, choosing wincode if enabled. The serializer defaults and derive field order preserve fixed-width little-endian tags/u64 and the owner bytes across the reviewed codec patches. This registered entry is the narrower returned-value observation. It specifies constructed fields/bytes after successful construction and does not establish allocation order, unwind cleanup or termination; those belong to the separately classified operational entry.
<!-- /registry -->

<!-- registry:review:cef426fd77a2d448 -->
<a id="review-cef426fd77a2d448"></a>

transfer retains [from signer+writable, to nonsigner+writable] and serializes tag 2, lamports (12 bytes). The program ID is 32 zero bytes, duplicate from/to keys remain two ordered entries, and full source u64 values including maxima are accepted by construction. System 1.0/2.0 uses Pubkey; 3.x uses Address with the same canonical 32-byte observation. Appending CreateAccountAllowPrefund in 3.0 does not alter variant tags 0 and 2. Versions through 3.0 call bincode directly; 3.1+ reaches create_instruction, choosing wincode if enabled. The serializer defaults and derive field order preserve fixed-width little-endian tags/u64 and the owner bytes across the reviewed codec patches. The operational family retains the actual Vec construction before serializer invocation, successful resource-handle moves, unwrap failure, stateful dependency outcomes, current-table observations, retained-accounts destruction and terminal/double-unwind policy. It assumes no successful allocation/serialization or rollback. It is not replaced by the value observation.
<!-- /registry -->

<!-- registry:review:822d943b46b3ac87 -->
<a id="review-822d943b46b3ac87"></a>

Reference: solana-system-interface 1.0.0. Compatibility in [1.0.0, 2.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the full operational constructor and reached String/Vec/Instruction/bincode providers, not only the successful bytes: always keep three ordered metadata positions, including key aliases, with funding signer+writable, destination writable+nonsigner and base signer+readonly. Allocate metadata before copying the entire UTF-8 seed into a temporary String, serialize fixed little-endian variant 3/base/String/u64 lamports/u64 space/owner, transfer returned owners, and drop the temporary at the recorded point. Retain allocation, partial initialization, serialization, unwrap, cleanup and abnormal-exit order, lawful GlobalAlloc no-unwind behavior, and terminal exits without later cleanup. Do not introduce seed-length or derived-key checks. System 3.2.0 duplicate-base omission remains excluded.
<!-- /registry -->

<!-- registry:review:151b2ada1b769d7d -->
<a id="review-151b2ada1b769d7d"></a>

The declared compatible range assumes allocation of one new-account signer/writable metadata entry, then insertion of an optional payer even at zero lamports or an equal key, and variant-13/u64-lamports/u64-space/owner encoding at the zero System key. Wincode takes precedence over Bincode; actual moves, serializer failures and cleanup are retained without a CPI claim.
<!-- /registry -->
