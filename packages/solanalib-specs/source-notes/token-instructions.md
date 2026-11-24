# Token instruction construction and local CPI preparation

The versioned instruction contracts instantiate common instruction, account,
borrow, owned-resource and outcome models. Their arguments are library values
and explicit dependency interpretations. Their scope is the library functions
registered in the source map.

The selected source APIs are:

| Published crate | Selected ordinary SDK functions |
| --- | --- |
| `spl-token-interface` 2.0.0 | `id`, `initialize_account3`, `transfer` |
| `spl-token-2022-interface` 3.1.1 | `id`, `check_spl_token_program_account`, `initialize_account3`, `close_account`, `transfer_checked`, `withdraw_excess_lamports` |
| `pinocchio-token-2022` 0.3.1 | `CloseAccount::invoke_signed`, `TransferChecked::invoke`, `TransferChecked::invoke_signed` |
| `spl-token-2022` 11.0.0 | `onchain::invoke_transfer_checked`, including its ordinary multisig and transfer-hook preparation |

The separate [batch note](token-batch.md) covers the `pinocchio-token` 0.6.0
`TransferChecked::new`, `IntoBatch::into_batch`, `Batch::new` and
`Batch::invoke_signed`. Its two `AsRef` passes and retained account/address
references are not replaced with the direct-account wrappers described here.

## Source identity and boundary

The [source registry](../source-map.json) records exact Rust names, package
versions, immutable file hashes and source anchors. The source audit checks
the corresponding ordinary library files. The main sources use these revisions:

| Published crate | Repository revision |
| --- | --- |
| `spl-token-interface` 2.0.0 | `beeb441b449555311a6a88fffe7aa6499a2f6266` |
| `spl-token-2022-interface` 3.1.1 | `e18f9c6f9bf6044b934f48e3090e8e59e4820f02` |
| `pinocchio-token-2022` 0.3.1 | `d713b2d0baf9bb406eea34cd020c963078b8c56a` |
| `spl-token-2022` 11.0.0 | `d9a5ce37c018981b6823746856ff9fe1268837cf` |
| its `spl-token-2022-interface` 3.0.0 dependency | `e0ad14742f4df0e111b8fa81da1e7163525be76c` |
| `spl-transfer-hook-interface` 2.1.0 | `b14c7c375cdc013123b8b042e331497016439f93` |
| `spl-tlv-account-resolution` 0.11.1 | `e05bf3a438d9bcc4b71a8f3c53897543b62f6fb9` |
| `spl-type-length-value` 0.9.1 | `9339df941e71459485cd6f50a4df1a001d018621` |
| `spl-pod` 0.7.3 | `1b60dd54705070f862dad4f8337cbb2d2f19ddb5` |

The reviewed 11.0.0 dependency profile uses interface 3.0.0 and hook 2.1.0,
with resolution 0.11.1, TLV 0.9.1 and POD 0.7.3. Its PDA source path follows
the `solana-pubkey` 3.0.0 to `solana-address` 1.1.0 to 2.6.0 re-exports.
These exact profiles do not imply correspondence for every resolution of the dependency ranges of the crates.

The Pinocchio token wrappers and SPL multisig/hook helpers are modeled through
their local preparation up to explicit invocation contracts. The selected Pinocchio wrappers use InstructionView 2.1.0 checked array
preparation before an explicit opaque unit-returning invocation. The SPL
`solana_cpi::invoke_signed` boundary remains a separate explicit opaque relation. Their implementations and invoked programs are outside this
source review. An opaque relation supplies no success, unchanged-state or
termination guarantee.

## Constructor semantics

`TokenInstruction` supplies shared wire and account-metadata operations.
`TokenInstructionConstructors` adds transfer admission and value observations;
`TokenInstructionValues` adds the remaining pure constructor observations.
`TokenInstructionPlan` records source call order for transfer and checked transfer;
`TokenInstructionVariants` adds initialization, close and excess-lamport
withdrawal plans. `TokenInstructionAllocated` executes these plans over
outcome-carrying vector dependencies. `TokenInstructionAllocatedFamily` supplies
the primary versioned constructor contracts. The `_value_contract` declarations
are supporting observations of the constructed values; they omit allocation
and ownership exits and are not registered as full operational models.

Program admission precedes allocation. Legacy constructors accept only the
legacy Token ID. The selected 3.1.1 initialization, close and checked-transfer
constructors accept either Token program; `withdraw_excess_lamports` accepts
Token-2022 only. ID/check functions are pure full models. None of these
constructors validates execution balances, signatures or the deployed program.

The byte tags are 18 for InitializeAccount3, 3 for Transfer, 12 for
TransferChecked, 9 for CloseAccount and 38 for WithdrawExcessLamports. Amounts
are eight little-endian bytes, decimals are one byte, and InitializeAccount3
serializes the 32 bytes of the owner in data. That owner is absent from its account
list. Other constructors retain the exact source/mint/destination/authority
order. The authority is a signer exactly when no multisig signer keys were
supplied; every supplied signer is retained, including duplicates.

`TokenInstruction::pack` calls
`Vec::with_capacity(size_of::<TokenInstruction>())`, then the individual push/extend operations of the source. InitializeAccount3 packs before its
metadata literal; Transfer, TransferChecked and CloseAccount pack before a
metadata capacity call and ordered pushes. WithdrawExcessLamports follows a
different source order at interface 3.1.1 `instruction.rs:2177`: after program
admission it constructs the source/destination/authority metadata literal,
pushes each signer, and only then packs tag 38 in the data field of the returned Instruction. `Plan.order` and `MetaPlan.fromListThenPush` retain this order and
the actual literal constructor rather than replacing it with a reservation.
The enum size is an explicit target-layout parameter. A sample value of 128
demonstrates consistency; it is not a measurement of a Rust layout. Relating
natural-number model arguments and capacity expressions to Rust requires the
selected scalar and usize bounds. These representation obligations are
separate from primitive provider laws.

A successful constructor returns both actual vector identities in
`Instruction.OwnedValue`. Its observation reads both resources in the current
state. In the data-first constructors, a metadata-construction unwind cleans
partial metadata before the earlier packed bytes. WithdrawExcessLamports
already owns its metadata when packing begins: packing unwind cleans its
partial byte vector inside `pack`, then the metadata moved into the partially
initialized return value. A signer-push unwind cleans the partial metadata
without beginning byte construction. Partial vector contents are read in the
actual cleanup state. Terminal exits bypass remaining cleanup; a second
unwind invokes the explicit terminal policy before any later destructor.
A successfully returned Instruction still drops its metadata field before its
data field, regardless of construction order.

## Allocation-free Pinocchio wrappers

The three selected 0.3.1 wrappers call the InstructionView 2.1.0 checked
`invoke_signed` array entry, with AccountView 2.0.0. Close constructs three
account entries; checked transfer constructs four. The unsigned transfer entry
calls its own signed wrapper with an empty signer slice. Both account and
metadata lengths are fixed and equal, below the compile-time limit of 64.
`TokenRequest` retains source/mint/destination/authority order, asymmetric flags,
nested seeds and duplicate account handles. It reads metadata keys from the
actual current pool rather than separate freely supplied address observations.

The shared checked path performs count admission and positional address checks,
checks a requested writable account for any live data lease, and captures the
actual descriptor list before opaque invocation. In this selected v2 revision,
readonly metadata performs no borrow check, including readonly signer authority
metadata. The wrapper itself adds no program-ID authentication, callee execution
property, or new account guard. The plain borrowed AccountView instance uses
identity `AsRef`; arbitrary generic conversion callbacks are modeled separately
by the InstructionView entry and by batching where applicable.

Checked `ProgramError` values return unchanged. Normal opaque Unit completion
becomes `Ok(())` with the actual callback state; it cannot invent a new ordinary
SDK error. Unwind and terminal effects remain explicit. These local stack arrays
and borrowed references require no owned-vector or account-guard cleanup.
Concrete controls include successful acquisition followed by preflight rejection,
exclusive leases on both readonly positions followed by successful invocation,
and recording the complete prepared descriptor list in callback state, with
nonempty source bytes and repeated account identities. The recording control
preserves raw flag bytes 2 and 1 with the same true Boolean observation and
nonzero header padding. Captured flag bytes, padding and data lengths come from
current accounts; instruction flags do not replace them. The shared family
requires a current raw-header observation and imposes no canonical-byte
restriction.

The transfer relations admit every mathematical natural amount and decimal
value. Their results do not use a separate scalar-width restriction: the
existing encoder performs its explicit byte conversions and the checked path
still applies its current-account tests. Controls with amounts/decimals outside
u64/u8 retain the actual writable-borrow error before an impossible invocation.
These inputs do not represent Rust arguments. The source binding must establish
the actual u64/u8 widths; no target overflow behavior follows from the wider
mathematical domain.

Source handle validity, the concrete `AsRef` instance, fixed stack layout and
local `MaybeUninit` byte initialization remain implementation obligations.
The source binding must relate the raw-header observation to the actual bytes
and the Boolean getters of the pool at every legal current handle.
The checked entry has its separate [source note](value-request-instruction-view.md).
Unchecked invocation bodies and invoked programs remain opaque; these
mathematical paths do not supply a Rust or validator correspondence proof.

## Token-2022 11.0.0 preparation

`TokenRequestAllocatedOnchain` composes the common instruction builder, current
AccountInfo borrow world, explicit Rc operations, ordinary hook/TLV/seed
helpers and the final opaque CPI relation. `fee` is fixed to `None`, as in the
selected public entry point. The earlier `TokenRequestOnchain` family remains
a supporting value-level observation and omits vector/Rc effects.

The source order matters at several points:

1. The checked-transfer instruction is built before the four-element literal
   constructor. Its expressions clone source, mint, destination and authority
   in order; constructor work may occur before or between those expressions.
   Multisig ownership is read
   through `ownerAt` after those dependency calls. Non-token owners bypass
   the temporary data-length borrow.
2. A recognized multisig clears authority metadata slot three before taking
   the unchecked authority-data borrow. The POD reader checks size and the
   eleven-key range; it does not validate initialization, threshold or the
   additional AccountInfo signer flags. The filter retains source order and
   duplicates, reads the held signer slice at each iteration, pushes metadata,
   then clones and pushes the matching AccountInfo.
3. A shared mint guard begins after multisig preparation. Total-length and
   initialized packed-Mint checks precede extension padding. The guard remains
   live throughout hook preparation and ends before CPI.
4. Interface **3.0.0**, used here, compares padding with `vec![0; 83]` for an
   extended Mint. `AllocatedTlv.mintTail` preserves that constructor and drops
   its temporary before reading the account marker. Bare mints and short
   tails bypass it. Interface **3.1.1** checks padding with an iterator and has
   no such allocation. A separate provider field binds the repeated-zero
   constructor; no equivalence with a different vector constructor is assumed.
5. Hook retrieval treats an extension lookup error or a zero hook program ID
   as absence. With a hook, the validation PDA is derived before mandatory
   first-match program lookup. Both this derivation and seed resolution use
   the stateful `Address.Syscall.findRun` wrapper over the actual PDA syscall.
   A viable mathematical PDA does not suppress metering, unwind or terminal
   failures. Nonzero returned status reaches the local panic in the actual
   returned state. The validation account is optional.
6. With validation, Execute bytes and metadata are allocated, the validation
   meta is pushed, and the Execute AccountInfo array is constructed before
   borrowing validation data. Full TLV validation precedes the first Execute
   lookup and ListView admission. The admitted payload range and iterator
   count are retained; later record reads follow the same live data Ref.
7. Each extra entry collects current account keys and shared data Refs through
   the actual higher-order `collect::<Result<Vec<_>, ProgramError>>()`
   dependency, supplied the exact key-before-borrow closure. Its ordered
   prefix, early-exit, current-resource and element-cleanup obligations are
   stated by `AllocatedCollect.Protocol`, `Provider.Conforms` and
   `ResourceLaws`. These are not an invented SDK-level reserve/push schedule.
   Provider binding must also preserve the held iterator and reference
   lifetimes across its internal effects; a length theorem alone does not
   establish that frame.
8. `AllocatedSeeds.resolve` retains owned literal buffers, unpacked seeds and
   live borrowed seed views through their individual allocation sites. External
   PDA program lookup precedes seed unpacking. Ref-vector cleanup, copied flag
   timing and owned-seed cleanup follow the source, including abnormal exits
   from the stateful PDA dependency. The collected account-data vector drops
   before de-escalation and additional-account lookup.
9. Every resolved extra is made a nonsigner. Existing duplicate accounts limit
   requested writability according to earlier metadata. The selected
   AccountInfo is cloned before its metadata push; a push unwind drops that
   local clone. A successful metadata push is followed by the info push,
   which consumes the cloned owner.
10. The validation guard ends before copying the current Execute suffix after
    its five standard entries into the transfer vectors. Metadata extension
    precedes the concrete AccountInfo clone-extension dependency. Validation
    is then appended; Execute locals drop; the hook program is appended last.

AccountInfo ownership follows the actual moves. Before the hook call, the
function retains all four arguments. With a hook, source, destination,
authority and a new mint clone move into the helper. If an Execute array is
successfully constructed, it consumes those four owners; its vector destructor
owns their drops. The caller retains its original mint owner until the mint guard ends.
Without a hook all four original arguments drop in reverse declaration order.
At the eventual invocation, the account and instruction vectors are still
owned. They drop after ordinary CPI success/error or unwind, with current info
elements first, then instruction metadata and bytes.

`TokenRequestAllocatedLiteral` uses `Owned.Array` for both AccountInfo literals.
The constructor receives an exact indexed expression callback. Its internal
work may allocate or change state before or between evaluations; the SDK
model does not prescribe a macro expansion. The actual array trace records
ordered evaluation, completion at the exact count and cleanup of every
evaluated occurrence. There is no unused proof-valued field on `Types` for
constructor conformance. Equal AccountInfo values still represent distinct
positions and owners. The composed provider uses the ordinary
`AccountInfoRc.dropCall` and the surrounding double-unwind policy directly.

The initial literal evaluates four clones while its original arguments remain
owned by the outer function. The literal of Execute first moves four arguments and
then clones validation. `executeInfoAt_no_unwind` proves that these expressions
cannot unwind: a pure move returns and the selected Rc clone can return or
terminate. On a surviving constructor unwind, the completed expression count
therefore identifies exactly which originals remain unmoved. Cleanup destroys
the evaluated array elements and temporary storage, then the earlier Execute
instruction inside the block, then the remaining function arguments in reverse
declaration order. The latter two phases form one cleanup list, so a second
unwind during instruction destruction terminates before argument cleanup.
This progress argument does not extend silently to arbitrary consuming
callbacks that can unwind. Constructor completion/temporary-storage ownership,
live references and primitive frame laws still need their source bindings.

`Types.findPda` requires `PdaInputs.Bounded` at each actual call. The two slices of the fixed
hook prelude satisfy the bound by `hookPdaInputs_bounded` for
every mint key. `TokenRequestAllocatedPdaAdmission.Ready` additionally requires
an initialized address only for actual status-zero replies to those bounded
requests. Its continuation theorem returns the exact address, bump and syscall
state. Nonzero replies retain each actual downstream panic exit; direct unwind
and terminal replies pass through without an output-initialization premise.
The unchanged raw decoder remains partial for an unadmitted status-zero reply
with no address. It fabricates neither a key nor a panic.

For seed resolution, the machine-slice bound applies to the actual retained
views. Their current contents, captured lengths and resource lifetimes are
separate local admission obligations. These are representation bounds, not
extra runtime PDA seed-count/length checks. The earlier pure `Args.crypto`
observation is used only by supporting value models; operational outcomes come
from the explicit syscall interpretation. A Rust binding must justify both the
input representation and the actual output initialization of the syscall.

## Evidence and remaining bindings

The full allocated family admits the capabilities needed at its local reads
and checked cleanup. This corrects two distinct empty-relation risks: a finite
callback can destroy a held data guard, or it can retain account guards while
erasing a vector or output that the next local read requires. Admission is
checked at actual primitive exits and forward cleanup prefixes, independently
of whether the complete SDK function later has an outcome. The raw operations,
error precedence, unwind cleanup and terminal bypass remain unchanged.

`TokenRequestAllocatedAdmission` supplies live-guard frames, typed data after
ordinary returns, the retained collected-Ref ledger, PDA reply initialization
and literal-control admission. Guard destruction is allowed only for elements
actually owned by the current Ref-vector destructor. The two fixed AccountInfo
literals admit evaluate/finish commands at their exact four/five-element
counts and require cleanup to include each completed occurrence. Each actual
source expression, constructor or cleanup exit then passes the existing local
check; no constructor, Rc operation, destructor or panic is assumed to finish.

`TokenRequestAllocatedResourceAdmission` separately covers current constructor
results, used vector updates, exact authority-slot writes, captured lengths,
indexed views and retention of other live locals. The footprint distinguishes
the mutated/consumed owner from separately retained owners, including the
shared identity type of instruction bytes, padding and seed literals. The
actual discriminator operations retain those locals, but no unused
`discriminators.current` or generic destructor-retirement law is required.
The three prepared vectors remain owned during the opaque CPI, so each returned
or unwound invocation exit must retain them for local cleanup; account-state effects and
all invocation exit kinds remain explicit.

The collection obligations use one selected protocol for conformance,
finish-current linkage, guard/data frames, ordinary-resource frames and
forward-prefix cleanup-order admission. `token-collect.md` explains those
separate checks. The final-exit premise of a complete body cannot replace any of
these earlier primitive or cleanup-site obligations. No frame conjunction is
inserted into `withData`, `inspect`, `DataRef.drop` or the raw array/collection
trace relations.

`TokenRequestAllocatedBorrowAdmission` supplies the input domain at the actual
authority getter, unchecked authority borrow, mint borrow, validation borrow
and collected-element borrow. Its prefixes stop before that read, including
the current callback prefix of the same collection protocol. Successful retained
Ref acquisitions supply the protocol validity and current data used by their
later read/cleanup lemmas. Checked borrow errors remain admitted without those
success conditions. The temporary authority getter instead needs only its
selected current data or an actual conflict/shared-limit panic branch; it
requires no whole-store validity. Non-token owners bypass that getter, and
initial program rejection bypasses every borrow-site condition.

There is no blanket
scalar, profile, initial-account or constructor-capacity restriction. Minimal
selected-cell and protocol conditions are supplied at the reads that consume
them; concrete Rust scalar/slice/layout and ownership representation remain
source-binding obligations. An early-error control still uses an amount outside the
Rust u64 domain and a rejected program ID: the admitted sample returns
`IncorrectProgramId` after four real argument drops, before vector allocation
or CPI. This is a mathematical-domain control, not a Rust input witness.

The supporting value-family uses `PreparationReady` at its reached borrow,
read and release sites. `prepare_not_malformed` proves that these local steps
retain their result; `run_retains` preserves every actual reached invocation
exit. `run_hasOutcome_iff` makes any remaining need for a finite invocation
outcome explicit. Early errors bypass later read conditions, and an invocation
provider with no finite outcome remains permitted. There is no whole-input
`Args.Valid` gate; that predicate remains available to the separate input-frame
preservation lemma. The actual constructor, the size and alignment checks of
extension lookup, and the early length checks of the base parser remain explicit.
The descriptors still need exact size, alignment and target-width bindings
when related to a Rust type; deleting an unused mathematical bound does not
establish those bindings.

The retained primitive capabilities yield local continuation theorems for
multisig, mint-padding, TLV pushes, seed/reference operations and collection.
They compose an actual finite callback exit with the next current read and
checked release, retaining its real state and reason. Typed-data return laws
also yield the next checked borrow before a first guard exists. An unwind
requires the existing guard/resource cleanup frames and has no unused
next-borrow typing obligation.

The registered family rejects the concrete guard-destroying and pre-borrow
type-corrupting providers. Raw controls still show exactly where their later
read or drop has no outcome, and separate controls cover lost vector contents,
invalid literal commands, omitted cleanup elements and uninitialized PDA
success. Permitted auxiliary mutations, normal/error returns, unwind effects
and terminal bypass remain observable. Logical data cells and an observed
vector slot do not by themselves grant physical Rc ownership; those source
permissions remain separate from the callback continuation claims.

Closed reference theorems cover every Family index. Closed sample executions
and satisfiability theorems prevent an empty reference from being the sole
evidence. Constructor samples retain live output resources; the full Onchain
sample carries initialized mint data, actual guard acquisition/release, Rc
ownership counts, a successful CPI and final owned-resource cleanup. Separate
controls exercise program/error precedence, byte order, duplicates, authority
flags, hook validation, collection failure, live seed reads, partial writes,
unwind cleanup, terminal bypass and double unwind. They are mathematical
executions; they do not assert production allocation success.

Using these models to verify Rust still requires body proofs and bindings for
memory layout, reference identities, pointer permissions, retained slice lifetimes, concrete
trait/primitive implementations, target panic behavior and the actual opaque
CPI interface. Vector `current`/freshness/retirement laws do not supply a
general frame law. A vector drop that owns AccountInfos, seed literals or data
Refs must implement their actual element cleanup. The model keeps those
obligations explicit and never treats a supplied successful SDK result as a
replacement for local control flow. Tools interpreting compiled Rust and runtime
correspondences are separate work; no such correctness claim is made by this package.
The finite-continuation results establish only their stated local reads and
cleanup under the admitted source-provider and input premises. They do not
establish arbitrary initial representation, allocation success or opaque
callback termination. Those facts do not follow from the relational reference
theorem or its one closed sample.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:6e7fd6d28e34a9e1 -->
<a id="review-6e7fd6d28e34a9e1"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The models retain both AsRef passes, source error order, partial buffer writes and final-only counters. InvocationReady requires exactly three bounded, fully initialized committed prefixes. request_domain proves this is precisely request the domain of the construction; initializedPrefix_exact and request_exact preserve the order of every slot and committed length. Admitted requests retain every actual finite provider exit, without a termination assumption. Rust private-state invariants, source widths, retained-reference validity and buffer separation remain separate bindings, as described in source-notes/token-batch.md.

Thin exact-version instantiations of the common owner/length/borrow/layout policies and live reference getter contracts, with separately named closed reference/nonvacuity witnesses.

Import-only versioned roots collect the separately reviewed leaf modules. The listed module hashes seal their exact imports; each leaf retains its own source-facing contract and interpretation obligations.
<!-- /registry -->

<!-- registry:review:3b70a7c946979705 -->
<a id="review-3b70a7c946979705"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The allocation-free CloseAccount and TransferChecked wrappers construct exact fixed arrays and data from current pool keys, retaining the supplied program, repeated handles, flags and nested signer order. Unsigned transfer supplies empty signers. Their cardinality proofs discharge the checked v2 array bound; source-local writable borrow checks run before the unit-returning unchecked invocation. Only normal unit completion becomes Ok(()), while actual unwind and terminal effects survive. HeaderTypes carries mandatory exact raw header bytes, not a canonical-byte restriction.

Thin exact-version instantiations of the common owner/length/borrow/layout policies and live reference getter contracts, with separately named closed reference/nonvacuity witnesses.

Import-only versioned roots collect the separately reviewed leaf modules. The listed module hashes seal their exact imports; each leaf retains its own source-facing contract and interpretation obligations.
<!-- /registry -->

<!-- registry:review:15248e4612e34a8a -->
<a id="review-15248e4612e34a8a"></a>

0.3.0 and 0.3.1 have byte-identical local wrapper files and the same InstructionView ^2.1 dependency. Close constructs three ordered metas with byte 9; transfer constructs four ordered metas with byte 12, little-endian u64 amount and u8 decimals. Unsigned transfer delegates with an empty signer list. All retain the caller-selected token_program address. DirectV2 checks writable borrow flags, retains readonly exclusive borrows, initializes exact raw four-byte headers, preserves account multiplicity and forwards the complete request to the opaque unit boundary. 0.1.0 reaches Pinocchio ^0.9 AccountInfo preparation with separate seven-reference borrow categories and normalized CPI fields; 0.2.0 reaches InstructionView 1.0, whose readonly borrow checks and normalized three flag bytes differ, while fourth-byte padding is uninitialized. 0.4.0/0.5.0 replace local structs by TokenProgram-generic implementations reexported from pinocchio-token 0.7.0/0.8.0 as Token2022Program aliases, with multisig fields and no runtime token_program field. Their default-ID empty-multisig paths pass 22 native cases each, but the full former arbitrary-program API contract cannot be assigned to those methods. The 0.0.0 placeholder has no API.
<!-- /registry -->

<!-- registry:review:e41e1332385fe3b7 -->
<a id="review-e41e1332385fe3b7"></a>

The payload bytes 64..72 are read without changing storage, borrow state, or guard identity. Token 0.1.0 uses an owned pointer wrapper; 0.2.0–0.3.0 use repr(C) raw views but still read a native-endian unaligned u64. On the intended little-endian Solana target these match the existing little-endian amount projection; big-endian behavior is not admitted for those releases. Token 0.4.0 onward uses u64::from_le_bytes. Token-2022 uses u64::from_le_bytes in every non-placeholder release. A valid pointer/guard-to-payload interpretation remains separate from the mathematical value result; the broken direct checked cast in Token 0.1.0 is not evidence for such a binding.
<!-- /registry -->

<!-- registry:review:7d16f4f0c9434b3f -->
<a id="review-7d16f4f0c9434b3f"></a>

The complete extensible parser checks fixed Token-2022 ownership, acquires a shared guard, then validates layout: exact 165-byte base, or length > 165 excluding 355 with type byte 2 at offset 165. Layout failure releases the temporary guard; success maps it. Existing unrelated guards and all bytes are preserved. No initialization, option-tag, padding or TLV validation is added. 0.2.0 TokenAccount instead checks minimum length before owner/borrow and accepts arbitrary tails without type or multisig validation. 0.3.0 introduces the modeled layout/order; 0.4.0 leaves this closure unchanged. 0.5.0 changes wrong-owner error to IncorrectProgramId. 0.1.0 only has the AccountInfo receiver predecessor; 0.0.0 is empty.
<!-- /registry -->

<!-- registry:review:b6b7a827293762e1 -->
<a id="review-b6b7a827293762e1"></a>

The complete contract returns a borrowed field descriptor at offset 0, retaining the parent guard and all state. Token 0.1.0 returns an owned Pubkey copy and is incompatible. Token 0.2.0 onward and every non-placeholder Token-2022 release return &Pubkey / &Address into the original payload; changing the name TokenAccount to Account and changing [u8; 32] to transparent Address do not change the borrowed range, lifetime dependency or allocation behavior.
<!-- /registry -->

<!-- registry:review:1a9fd693392646d6 -->
<a id="review-1a9fd693392646d6"></a>

The complete contract returns a borrowed field descriptor at offset 32, retaining the parent guard and all state. The predecessor Token 0.1.0 method is named authority and returns an owned Pubkey; it is incompatible with this descriptor contract. Token 0.2.0 onward and every non-placeholder Token-2022 release return &Pubkey / &Address into the current original payload. The explicit predecessor names are recorded separately from exact callable bindings.
<!-- /registry -->

<!-- registry:review:2f9a6710ed3062dd -->
<a id="review-2f9a6710ed3062dd"></a>

Token 0.2.0–0.7.0 and Token-2022 0.1.0–0.3.1 use the same From<u8> match: 0/1/2 return enum values; every other byte panics with the byte in its diagnostic. The existing arbitrary target panic provider retains every finite unwind/terminal effect and has no normal result. Token 0.1.0 instead loads AccountState directly through a pointer, with no repr(u8) declaration and undefined behavior for invalid enum bytes; the model admits those raw bytes and demands a panic, so it does not apply. Token 0.8.0 and Token-2022 0.4.0/0.5.0 change the return type to Result and return InvalidAccountData on invalid bytes. Restricting to valid enum bytes would not preserve the complete existing contract.
<!-- /registry -->

<!-- registry:review:399a45958c2ff606 -->
<a id="review-399a45958c2ff606"></a>

The current payload byte at offset 44 is returned without validation, allocation or mutation. Every non-placeholder release has this projection. Token 0.1.0 stores a pointer rather than a direct 82-byte repr(C) view; correspondence requires that its pointer denote the same live guarded payload under the existing source representation obligation. It does not justify the 0.1.0 checked parser, which casts the data bytes to the pointer wrapper. Token 0.2.0 onward and all Token-2022 releases use direct alignment-1 82-byte raw mint fields.
<!-- /registry -->

<!-- registry:review:09d8ea98bb4f48e4 -->
<a id="review-09d8ea98bb4f48e4"></a>

The full mint parser checks fixed Token-2022 owner (InvalidAccountOwner), acquires a shared guard, then accepts exact 82 bytes or the extensible account layout (length > 165, not 355, type byte 1 at offset 165). Invalid layout drops only the temporary guard. Nonzero mint padding and arbitrary tails remain admitted. 0.2.0 uses minimum-length/owner/borrow checks and no extension-type validation. 0.3.0 adds layout validation but omits the owner check entirely and rejects short data before borrowing. 0.3.1 replaces that early length check with the modeled owner check; 0.4.0 preserves it. 0.5.0 changes wrong-owner error to IncorrectProgramId. Earlier AccountInfo APIs and the empty 0.0.0 placeholder are distinct.
<!-- /registry -->

<!-- registry:review:0b08ae694a6d99d1 -->
<a id="review-0b08ae694a6d99d1"></a>

0.6.0 forwards the fixed legacy Token ID, exactly the three committed prefixes in order/multiplicity and the complete nested signer tree to the opaque unit-returning invoke_signed_unchecked. Ordinary completion becomes Ok(()); provider unwind/terminal effects are preserved and no ProgramError can be injected by normal unit completion. 0.7.0 forwards through invoke_signed_with_unverified_program with Program::ID; its public alias fixes that ID to legacy Token, preserving the complete existing contract at that instance. Its newly public push does not discharge InvocationReady. 0.8.0 removes invoke_signed and exposes unsafe invoke_signed_unchecked with an explicit no-outstanding-borrows safety obligation; that distinct successor is documented, not registered or silently admitted.
<!-- /registry -->

<!-- registry:review:a5e134a2cf66a49a -->
<a id="review-a5e134a2cf66a49a"></a>

All three releases reject an empty data buffer with InvalidArgument before mutation. Otherwise only data[0] becomes 255 and returned committed lengths are (1,0,0), retaining all three buffers and suffixes. 0.7.0 introduces a zero-sized Program phantom and moves constants; neither affects the full constructor observation. The public Batch alias selects TokenProgram. Allocation-enabled BatchState constructors are not this method.
<!-- /registry -->

<!-- registry:review:2f940ec0181d7f35 -->
<a id="review-2f940ec0181d7f35"></a>

0.6.0/0.7.0 have the same full write closure: check two-byte header room, write the ten-byte payload, check CPI capacity then source/destination borrow flags, initialize fixed and signer descriptors in one callback pass, then check metadata capacity and initialize metadata in a separate callback pass. Every earlier write and actual callback effect survives later failure/unwind. Lengths and the two u8 header casts commit only after full success; aliases and duplicate signers are retained. The mint, authority and signer borrows are not checked. 0.7.0 only introduces Program phantom/contextual aliases here. 0.8.0 adds an early multisig length > 11 rejection, before all writes/callbacks. The existing model intentionally admits 12/255/256 signers and wraps only the header byte; the four new failing limit controls demonstrate the incompatible outcomes. The trait becomes unsafe in 0.8.0 as an additional source-interface change.
<!-- /registry -->

<!-- registry:review:ab8e2b1dcd43e32a -->
<a id="review-ab8e2b1dcd43e32a"></a>

The specialized constructor delegates to with_multisig_signers with an empty slice and retains the four account references, u64 amount and u8 decimals without reading account state or allocating. 0.7.0/0.8.0 add a Program phantom; the public alias selects TokenProgram, and no verifier/callback is invoked by this constructor. The earlier releases expose struct fields and invoke methods but no new constructor.
<!-- /registry -->

<!-- registry:review:9ac46a1fb1763b5d -->
<a id="review-9ac46a1fb1763b5d"></a>

The complete legacy parser checks exact base length first, then the fixed legacy token owner, then shared borrow; success maps the same lease to the base range. Wrong length is InvalidAccountData; wrong owner is InvalidAccountData. TokenAccount was renamed Account in 0.6.0. AccountView dependencies 1.0 and 2.x preserve the reached owner/length/borrow/map behavior; offset-4 resize-delta versus padding is untouched. In 0.8.0 the owner failure becomes IncorrectProgramId. Before 0.5.0 the from_account_view API is absent: the different from_account_info predecessor uses Pinocchio AccountInfo and separate seven-reference data/lamports borrow accounting; this report does not silently substitute that receiver protocol.
<!-- /registry -->

<!-- registry:review:479fe83689102fcf -->
<a id="review-479fe83689102fcf"></a>

The complete legacy parser checks exact base length first, then the fixed legacy token owner, then shared borrow; success maps the same lease to the base range. Wrong length is InvalidAccountData; wrong owner is InvalidAccountOwner. TokenAccount was renamed Account in 0.6.0. AccountView dependencies 1.0 and 2.x preserve the reached owner/length/borrow/map behavior; offset-4 resize-delta versus padding is untouched. In 0.8.0 the owner failure becomes IncorrectProgramId. Before 0.5.0 the from_account_view API is absent: the different from_account_info predecessor uses Pinocchio AccountInfo and separate seven-reference data/lamports borrow accounting; this report does not silently substitute that receiver protocol.
<!-- /registry -->
