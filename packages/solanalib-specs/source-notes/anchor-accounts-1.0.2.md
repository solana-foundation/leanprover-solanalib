# Anchor 1.0.2 account composition

The reviewed `anchor-lang` 1.0.2 files belong to revision
`1314a6b83b16e6a31947b372d57988fd0e81559c` of
[`solana-foundation/anchor`](https://github.com/solana-foundation/anchor/tree/1314a6b83b16e6a31947b372d57988fd0e81559c/lang/src).
The [source registry](../source-map.json) pins complete files and source anchors. Models
bind AccountInfo 3.1.1 and ProgramError 3.0.1 explicitly, without cross-version
equivalence claims.

Six dereference/key operations project fields with arbitrary payload/tag types.
The Rust returned-reference lifetime remains a binding obligation. Account and
Loader constructors store a borrowed AccountInfo and do not clone its Rc
fields. ToAccountInfo separately runs AsRef, then clones the actual returned
AccountInfo through both Rc dependency operations.

Primary constructor families preserve source check order. Account and
InterfaceAccount check uninitialized system-owned accounts before their
owner/codec paths; Loader checks its owner before the data discriminator.
Checked borrow errors are boxed ProgramErrors. Fixed ErrorCode construction
runs name literal copying, message formatting and Box allocation in order,
retaining dependency effects and terminal outcomes.

Account and InterfaceAccount admission first requires `InitReady`: only when
the current owner is the system program, the actual lamports observation must
not be malformed. A non-system owner skips this condition with the source
short circuit. The condition admits zero and nonzero balances, checked borrow
failure, unwind and configured abort. It requires no whole `AccountInfo.Valid`,
distinct field handles, target policy equality or integer widths. For the
observation initializer, it is exactly equivalent to existence of its raw
finite outcome. The owned initializer retains every actual error-factory exit
on the zero-balance branch; this supplies no allocator termination assumption.
Loader does not call initialization and has no `InitReady` condition.

Owner, CheckOwner and deserialization are explicit callbacks with actual
normal/error/unwind/terminal behavior. The raw decoder and local guard scope do
not filter these exits by a frame. Constructor family posts retain these raw
finite outcomes. Their preconditions require admission at every data scope
reached through an actual successful initialization and Owner or CheckOwner
prefix, before cleanup. Admission covers every finite codec exit at that input,
including an exit whose invalidated guard would prevent a complete constructor
result. It assumes no callback termination or law at an unreachable input.

The constructor continuation lemmas consume this admission and an actual codec
exit to derive a complete constructor exit with exact cleanup. At the codec
input, every state-bearing exit preserves the held cell and lease while
allowing other cells and auxiliary state to change. The typed contents of the selected data cell supply the actual codec input; the frame supplies exact guard
cleanup. At this reached data scope, the lemmas need no additional lamports
condition, distinct field handles, target policy equality or source integer
bounds. The broader representation
facts remain source-binding obligations. The conclusion preserves the actual
success, ordinary error, unwind or terminal exit rather than assuming a desired
complete-constructor postcondition.

Guard cleanup uses the actual callback state. It remains checked and partial
for an invalid or already consumed token; that path is outside the admitted
representation and does not fabricate a successful destructor. The shared
`AccountInfo.GuardCallback` laws prove that every actual finite exit of an
admitted callback at a live guard has exact cleanup. Returned errors and unwinds
retain their effects, and terminal exits have no invented state or cleanup.
A footprint-violating callback whose guard remains live still has its raw
returned or unwound constructor exit. It fails the reached-call admission of the registered family. An invalid or consumed guard can leave the raw relation
without a finite outcome, but its actual finite invalidating callback exit also
fails admission before cleanup. No totality or successful allocation is inferred.

Conditional cleanup proofs for error factories under a Loader guard use
`AnchorGuardEffects.BuildCodeAdmissible` primitive laws: the name allocation at
the reached factory input, the message allocation after each actual name
return, and the Box allocation after each actual message return. This rules out
an invalidating early allocation even if a later dependency has no finite
outcome. String/Box heap laws alone do not establish these guard obligations.
The compositional frame proof derives whole-factory admission from those
primitive premises; it does not assume the desired postcondition of the factory.
The owned Loader readiness premise includes common borrow-protocol validity:
the successful discriminator branch uses it to frame the unchanged state and
derive cleanup without an error allocation. It does not require the whole
AccountInfo representation bundle. At every successful Owner prefix, the
observation Loader constructor requires selected-data typing; the owned Loader
constructor requires that typing together with the existing local `LoaderReady`
premise. Both posts retain the raw checked behavior. The owned continuation
lemma consumes an actual guarded-check exit and derives the full constructor
result, including exceptional outcomes.

Each owner read occurs at the source point. Comparison reads after the first
Owner callback. On mismatch, the ErrorCode factory completes before copying
the current owner for diagnostics; that copy precedes the second Owner call.
An unwind of that second call drops the live boxed error. InterfaceAccount
captures owner after deserialization. Tests mutate owner during Owner, name
construction and decoding and check the separate observations.

The owned Account and Loader families also require `OwnerCheckReady` at each
reached Owner check. After an actual first-call mismatch, name return, message
return and Box return, the Box must contain the exact newly allocated payload.
Every actual returned or unwinding second Owner exit preserves that current
payload; each return also admits the exact diagnostic payload store. A terminal
exit has no further read, store or cleanup condition. These premises precede a
completed owner-check result and do not assume callback termination or laws for
uncalled factories. The return continuation derives the actual empty compared
field cleanup and `withPubkeys` store. The unwind continuation obtains the real
`dropError` input and composes actual ordered String cleanup and Box-free exits,
including cleanup terminals without requiring a later free. The raw operations
and their partial missing-resource paths remain unchanged.

Mutable loading checks writable metadata before borrowing. Discriminator errors
allocate with the guard held and then release it. Successful mapping consumes
the old guard generation and returns a live projection. Discriminator length
does not establish payload length. Payload size/alignment, data address, usize
width and overflow mode are explicit parameters; the model does not manufacture
a Pod interpretation. Slice/alignment panic, configured abort and error
allocation terminals remain distinct.

The `load` and `load_mut` families require typed current data only after a
successful checked acquisition. The shared `AccountInfo.DataBorrow.Ready`
condition supplies that actual read. Their supporting observation families use
`AnchorAccount.LoadReady`; `load_complete` proves a local result for every
admitted input. Successful mapping additionally exposes the complete current
byte range and consumption of the old guard generation.

The owned families require `AnchorLoadingOwned.Admission`. A reached
discriminator-error factory must retain the held token at every actual name,
message and Box allocation return. `local_continuations` proves current-data
availability, checked cleanup at each primitive prefix, and the exact outer
continuation of every finite factory exit. Terminal allocations skip cleanup;
the generic cleanup result also preserves state-bearing unwind. These conditions
assume no callback termination, unrelated account validity or decoded payload.
Physical reference permissions, Rust layout, source integer bounds and returned
String/Box ownership remain separate binding obligations.

The map-unwind release rule follows the frozen Ref::map and RefMut::map source:
callback evaluation precedes moving the owned borrow field. The registry pins
the exact snippets from core cell.rs, hash
`751d7301e865f9557103f9ddfeaa770ef7d0e12b63a4406db8747e874dcec4d8`.
This is a source sequencing argument, not a std implementation proof.

Anchor sol_log_data forwards nested binary fields to an explicit syscall sink
on Solana. Its host branch is black_box(data), preserving state without a sink
call; it is not the separate solana-program host stub. No base64/display output
is invented.

Earlier allocation-free functions are explicitly named `_observation_contract`.
Primary contracts include owned error/Rc sequencing. The GuardCallbacks controls
include an exact raw constructor result with an unframed return and failure of
its registered family admission, raw unwinds, and a single admitted provider
whose success, ordinary error, unwind and terminal exits each continue through
the full constructor. A killed-guard callback has a real finite exit and failed
registered admission in both observation and owned families; neither raw cleanup
relation fabricates a release. An invalidating allocation prefix followed by an
empty dependency is also rejected by the registered Loader constructor.
Additional controls retain an Owner unwind with an abstract
unsupported width and an allocated writable error before a zero abstract address
is used. Selected-data controls reach the decoder and Loader cleanup with no
lamports cell at the designated handle and an unsupported abstract profile.
Their registered precondition witnesses use the weak selected-data facts,
together with `LoaderReady` for the owned Loader. The owner-changing observation
and owned interface controls use the full constructor continuation lemmas and
capture the actual post-decoder owner.
Initialization controls reject a system-owned malformed lamports projection in
both constructor families, retain a non-system bypass, and admit actual borrow
failure before that projection under either panic strategy. The owned zero
balance control runs its actual String/String/Box factory. Owner-resource
controls start with an initialized Box and distinct String fields, then reject
real second-Owner returns and unwinds that erase it. The raw `withPubkeys` and
`dropError` relations do not fabricate the missing read. Positive normal and
unwinding diagnostic controls consume the generic continuation proofs and retain
the actual owner mutations and ordered destructor effects in the full Loader.
These inputs witness the mathematical domain, not a Rust representation.
Closed reference and execution witnesses cover the mathematical models only. Rust types, trait implementations, ownership, allocator behavior,
panic strategy and implementation correctness remain binding obligations.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:6a25e416937b4592 -->
<a id="review-6a25e416937b4592"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The AccountInfo 3.1.1, Anchor 1.0.2 and Anchor SPL 1.0.2 functions compose identified borrows, current owner reads, explicit trait callbacks, owned resources and source-ordered cleanup. AccountInfo borrow/getter conditions support their actual typed-current and progress conclusions. Constructor admission covers only reached initialization reads, diagnostic Error resources and guarded decoder/discriminator continuations. Loading and amount admit earlier checked errors but require current data after successful acquisition; reached owned loading factories retain their held tokens. Their continuation results preserve actual finite exits without assuming dependency termination. Owned-error families retain their three boxing or four comparison capabilities; comparisons additionally require reached assignment availability, and with_values protects resources on continuing unwind/destructor paths through CallReady. Pure error observation facets retain their stated omissions. Context uses actual empty-provider current/fresh facts. Primary transfer requires current instruction vectors on each successful builder return; invocation remains opaque. Pinned edition-2021 cleanup destroys instruction metadata and bytes, the tail-expression account array, then the remaining vector. Conditional destructor non-unwind claims and concrete resource/reference/target interpretations remain explicit source bindings.

The reviewed wrapper methods are represented by current source-object cells and live source loans, separate from AccountInfo RefCell storage. Shared and mutable references retain exact source identity and cannot outlive their parent token. Key copies retain ambient state. Clone and Drop receive the actual source field reference and its readable value; shared references retain external AccountInfo identity, whereas owned fields have distinct object identity and source-ordered Rc clone/drop effects. Sysvar clone decodes from the original AccountInfo reference after retaining info, with complete owned error unwrap and unwind cleanup. set_inner installs its replacement on normal and destructor-unwind paths. The proof witnesses are closed mathematical models; Rust bindings and native checks have the narrower scopes documented separately.

The root modules reexport the reviewed function facades. Capability catalogs are generated from the exact model, source-identity and applicability records in this shard and the selected shared shards; they preserve every complete family and its closed witnesses.

The selected function models compose explicit primitive operations at actual current states. Context constructors/mutators preserve fields, references and Vec owners; old program AccountInfo and modern copied Pubkey are distinct interpretations. Error callbacks retain unwind, terminal outcomes and source cleanup; log temporaries are cleaned on host unwind. Exact finite code tables select each released macro expansion. Codec bodies retain partial write/cursor mutations and diagnostic resources. Families with True mathematical preconditions still require the separate Rust binding to establish initialized current resources and representations; no source-output premise is inferred from finite witnesses.

System allocate, assign, create_account and transfer use the 0.32.1 reference family. Their per-function profiles record inspected 0.32.0–0.32.3 sources, the declared 0.32 compatibility range and constructor/error dependencies. Invocation remains opaque; detailed resource and source assumptions stay in the binding obligations.

This shard registers thirteen Anchor 0.32.1 methods. Shared lifecycle families compose source-order record consumption, initialization, owner/ID observations, error resources, guarded codecs, focused payload replacement, conditional serialization and close mutation/cleanup. Their retained helper branches and source evidence also distinguish other reviewed releases; those supporting definitions add no registrations here. Each selected facade fixes its information-field storage, error storage and operation mode. Readiness applies only at reached prefixes and supports typed current data, actual error stores, guard release and continuation of every admitted finite dependency exit. Exact file/package seals remain in this registry. The selected methods and their interpretation are described in source-notes/anchor-lifecycle.md.

AccountLoader identity, unchecked and account-slice construction, zero-copy initialization and discriminator persistence reuse actual shared AccountInfo/Borrow and owned Anchor diagnostic operations. Prefix admission gives the consumed local read/cleanup continuations. Reference indices keep record identity distinct from cells and guard generations. Close reuses source-ordered current lamports/owner/resize and destination Rc cleanup, including sequential self-aliasing.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Named source families have closed references, satisfiable samples and concrete executions. Exact reviewed defining packages and dynamic-dispatch build profiles select those same families; macros do not transfer ownership. Wrapper families select only the Solana64 forwarding branches. The mathematical buffer is a fixed initial request snapshot. A physical memory interpretation must retain that snapshot for model indexing and compose ordered output stores into the actual returned invocation state.

Error.log_modern is defined by anchor-lang 1.0.2. It retains the complete boxed modern ProgramError logger family and run while keeping the inherited anchor-lang-error registration and legacy Anchor logger distinct.
<!-- /registry -->

<!-- registry:review:61ed80b0c51ea69f -->
<a id="review-61ed80b0c51ea69f"></a>

For this concrete AccountInfo receiver, 0.14.0-0.20.1 and 0.23.0-1.2.2 copy *self.key directly. 0.21.0-0.22.1 use the AsRef blanket Key implementation; the reached concrete AccountInfo::as_ref is identity, so no callback effect, borrow or Rc operation is introduced. The old 0.10.0-0.13.2 blanket Key instead calls the AccountInfo-specific ToAccountInfo, cloning lamports Rc then data Rc and dropping the temporary. Its possible Rc-overflow abort and lifecycle operations are absent from the current pure, always-returning projection contract; equal ordinary returned keys do not establish that full contract. The Key API is absent through 0.9.0. Pubkey/Address aliases and rent_epoch/_unused metadata changes do not change this projection under the existing reference/value binding.
<!-- /registry -->

<!-- registry:review:41ae2f7754391683 -->
<a id="review-41ae2f7754391683"></a>

The exact generic blanket implementation for arbitrary T: AsRef<AccountInfo> first calls self.as_ref() at the current state, then performs derived AccountInfo::clone. It is byte-identical in every stable release from 0.21.0 through 1.2.2. The reached clone performs lamports Rc then data Rc, preserves key/owner references, scalar flags and the existing metadata field, and acquires no RefCell borrow. AsRef unwind skips both clones; a terminal Rc exit skips later work. Earlier releases have the trait and some concrete implementations but not this generic AsRef blanket source operation; admitting them would narrow or replace the modeled generic API. The supporting observation records the callback exit and copied value while deliberately forgetting the Rc ownership lifecycle of the primary model.
<!-- /registry -->

<!-- registry:review:fc3b6324be5291cf -->
<a id="review-fc3b6324be5291cf"></a>

Account first exists in 0.15.0. Every released implementation returns a shared reference to its stored account field; the 0.26.0 removal of redundant (*self) syntax does not invoke a payload operation. The owned-to-borrowed AccountInfo representation change in 0.29.0 does not clone, borrow, or drop anything during deref. Earlier ProgramAccount is a distinct overlapping API, not an alias.
<!-- /registry -->

<!-- registry:review:b354e3d1d7938174 -->
<a id="review-b354e3d1d7938174"></a>

The full owned constructor corresponds from 0.29.0: short-circuit system-owner/lamports initialization, first Owner then comparison, wrong-owner name/message/Box creation before actual-owner copy and the second Owner callback, exact error cleanup if that callback unwinds, checked shared data borrow, arbitrary decoder exits and release, and a wrapper retaining the input AccountInfo reference. 0.15.0–0.18.2 lack the initialization check; older errors also differ. All 0.15.0–0.28.0 clone AccountInfo before decoding and store it by value; before 0.29.0 Anchor errors are unboxed. A decoder can observe the extra two Rc references. From 0.29.0 the primary family forwards arbitrary decoder error resource identities without destructuring or destroying their payloads; its only internally constructed ProgramError is AccountBorrowFailed. Therefore legacy String-bearing BorshIoError callback payloads do not impose the 1.0.0 bound of the separate observation facet. This argument does not restrict arbitrary callbacks.
<!-- /registry -->

<!-- registry:review:247cd20594a958bb -->
<a id="review-247cd20594a958bb"></a>

This supporting observation keeps the existing ConstructorReady callback/guard contract and its recorded omission of owned error/dependency lifecycle. Unlike the primary family, AnchorAccount.Error is the concrete AnchorError.Value ProgramError.Value, including a unit borshIoError. Arbitrary decoder errors (and arbitrary CheckOwner errors for InterfaceAccount) in every pre-1.0 release can carry ProgramError::BorshIoError(String); source and native witnesses preserve the String. Erasing it or restricting callback errors would change the existing contract. The compatible source set therefore starts at 1.0.0. Initialization, callback sequencing, data guard cleanup and current-owner capture follow the primary source closure; no resource-lifecycle completeness is claimed for this facet.
<!-- /registry -->

<!-- registry:review:b7488b6b812b6f1b -->
<a id="review-b7488b6b812b6f1b"></a>

AccountLoader first exists in 0.18.0. The module moves from loader_account to accounts::loader_account to accounts::account_loader. Direct key implementations copy the stored key; 0.21.0, 0.22.0, and 0.22.1 reach the same field through the blanket Key implementation and the concrete identity-field AsRef. They invoke neither Owner nor Discriminator nor a checked borrow. The older Loader type remains a distinct contemporaneous API and is not silently substituted.
<!-- /registry -->

<!-- registry:review:abdc4724f4d2b4dc -->
<a id="review-abdc4724f4d2b4dc"></a>

The complete load correspondence is 0.31.0–1.1.2. Loading borrows current data without rechecking Owner, validates the immutable arbitrary-length discriminator, and transfers the live guard through Ref::map after exact payload slicing and bytemuck size/alignment checks. Reached discriminator errors allocate name/message/Box while the guard is live, then release it. 0.18.0–0.20.1 map the entire trailing slice, so excess payload bytes differ; later old releases still invoke an effectful, overridable discriminator method and retain older discriminator error messages. From 1.2.0 check_size returns AccountDidNotDeserialize (3003) on short payload or size addition overflow before mapping, whereas the existing contract retains bounds/overflow panic and configured abort. No extra payload-length precondition is added.
<!-- /registry -->

<!-- registry:review:c336cb354bda5a3d -->
<a id="review-c336cb354bda5a3d"></a>

The complete load_mut correspondence is 0.31.0–1.1.2. Writable metadata is checked before attempting the exclusive data borrow; the non-writable error takes precedence over a borrow conflict. The remaining path uses current bytes, an immutable arbitrary-length discriminator, held-guard error factories, and RefMut::map, transferring the original guard and exposing the actual mutable payload range without Owner recheck. Older releases have overridable discriminator callbacks, older error messages, and (through 0.20.1) whole-trailing-slice mapping. 1.2.0–1.2.2 add check_size, replacing admitted short-payload/overflow panic or abort paths with a newly allocated AccountDidNotDeserialize error. The existing full contract is retained, including its failure paths.
<!-- /registry -->

<!-- registry:review:9c15be46c1b63bdb -->
<a id="review-9c15be46c1b63bdb"></a>

This supporting observation retains its recorded omission of owned error/dependency lifecycle. It reviews the same underlying operation, including callback, live-data, guard-transfer and panic/error distinctions; it cannot bypass a changed discriminator or short-payload branch. The complete load_mut correspondence is 0.31.0–1.1.2. Writable metadata is checked before attempting the exclusive data borrow; the non-writable error takes precedence over a borrow conflict. The remaining path uses current bytes, an immutable arbitrary-length discriminator, held-guard error factories, and RefMut::map, transferring the original guard and exposing the actual mutable payload range without Owner recheck. Older releases have overridable discriminator callbacks, older error messages, and (through 0.20.1) whole-trailing-slice mapping. 1.2.0–1.2.2 add check_size, replacing admitted short-payload/overflow panic or abort paths with a newly allocated AccountDidNotDeserialize error. The existing full contract is retained, including its failure paths.
<!-- /registry -->

<!-- registry:review:ff2b8374a60596ea -->
<a id="review-ff2b8374a60596ea"></a>

This supporting observation retains its recorded omission of owned error/dependency lifecycle. It reviews the same underlying operation, including callback, live-data, guard-transfer and panic/error distinctions; it cannot bypass a changed discriminator or short-payload branch. The complete load correspondence is 0.31.0–1.1.2. Loading borrows current data without rechecking Owner, validates the immutable arbitrary-length discriminator, and transfers the live guard through Ref::map after exact payload slicing and bytemuck size/alignment checks. Reached discriminator errors allocate name/message/Box while the guard is live, then release it. 0.18.0–0.20.1 map the entire trailing slice, so excess payload bytes differ; later old releases still invoke an effectful, overridable discriminator method and retain older discriminator error messages. From 1.2.0 check_size returns AccountDidNotDeserialize (3003) on short payload or size addition overflow before mapping, whereas the existing contract retains bounds/overflow panic and configured abort. No extra payload-length precondition is added.
<!-- /registry -->

<!-- registry:review:e3f07e07375b6142 -->
<a id="review-e3f07e07375b6142"></a>

The full constructor corresponds from 0.31.0 through 1.2.2: first Owner/comparison, conditional diagnostic factory and second Owner, checked shared borrow, immutable arbitrary-length discriminator validation, exact guard release, and borrowed input reference. Earlier implementations clone AccountInfo through 0.28.0, use unboxed errors through 0.28.0, and call the overridable Discriminator::discriminator method through 0.30.3. That method can mutate state or unwind, which the current immutable discriminator parameter does not model; native counterexamples do so. Short discriminator data panics before 0.24.0; 0.24.0–0.30.3 return older discriminator messages. The 1.2.0 new→new_unchecked helper rename preserves the behavior of this constructor; its new check_size helper is not called here. AccountBorrowFailed is the only reached ProgramError variant, so an unrelated legacy BorshIoError payload does not narrow this operation.
<!-- /registry -->

<!-- registry:review:03d7b4193e7cbdeb -->
<a id="review-03d7b4193e7cbdeb"></a>

This supporting observation retains its recorded omission of owned error/dependency lifecycle. It reviews the same underlying operation, including callback, live-data, guard-transfer and panic/error distinctions; it cannot bypass a changed discriminator or short-payload branch. The full constructor corresponds from 0.31.0 through 1.2.2: first Owner/comparison, conditional diagnostic factory and second Owner, checked shared borrow, immutable arbitrary-length discriminator validation, exact guard release, and borrowed input reference. Earlier implementations clone AccountInfo through 0.28.0, use unboxed errors through 0.28.0, and call the overridable Discriminator::discriminator method through 0.30.3. That method can mutate state or unwind, which the current immutable discriminator parameter does not model; native counterexamples do so. Short discriminator data panics before 0.24.0; 0.24.0–0.30.3 return older discriminator messages. The 1.2.0 new→new_unchecked helper rename preserves the behavior of this constructor; its new check_size helper is not called here. AccountBorrowFailed is the only reached ProgramError variant, so an unrelated legacy BorshIoError payload does not narrow this operation.
<!-- /registry -->

<!-- registry:review:069c5428358c0885 -->
<a id="review-069c5428358c0885"></a>

Interface first exists in 0.27.0. Every body delegates to the contained concrete Program deref, which projects its stored AccountInfo. The owned-to-borrowed Program representation change in 0.29.0 changes the stored reference interpretation, not the effects of this operation. No generic program ID check or callback runs during the projection.
<!-- /registry -->

<!-- registry:review:1774f48157e2775c -->
<a id="review-1774f48157e2775c"></a>

InterfaceAccount first exists in 0.27.0. Every body delegates to the contained concrete Account deref and returns the payload field reference. The captured owner is not read or checked. No payload deref/clone, decoder, owner callback, borrow, or destructor runs.
<!-- /registry -->

<!-- registry:review:65583ae38693b642 -->
<a id="review-65583ae38693b642"></a>

The full owned constructor corresponds from 0.29.0: initialization, actual-owner reference passed to arbitrary CheckOwner, checked shared data borrow and arbitrary decoder exits with release, then capture of the current owner after successful decoding. 0.27.0 and 0.28.0 instead clone AccountInfo before decoding and store it by value, and their internally created errors are unboxed. From 0.29.0 callback Error values remain opaque forwarded resources; no callback error payload is inspected or destroyed by this constructor. Only the reached AccountBorrowFailed conversion needs the fixed ProgramError interpretation. This preserves generic callbacks including old String-bearing BorshIoError values without extending the distinct concrete observation facet.
<!-- /registry -->

<!-- registry:review:ba5966e16ad81f69 -->
<a id="review-ba5966e16ad81f69"></a>

Signer first exists in 0.16.0. Direct implementations copy the stored 32-byte key. In 0.21.0, 0.22.0, and 0.22.1 the blanket Key for T: AsRef<AccountInfo> reaches the fixed identity-field AsRef of Signer; it makes the same copy without Rc operations. The change to borrowed AccountInfo storage in 0.29.0 preserves this selected operation.
<!-- /registry -->

<!-- registry:review:8d454b2d87ae11b9 -->
<a id="review-8d454b2d87ae11b9"></a>

The current constructor is unchanged from 1.0.0 through 1.2.2: move arbitrary T, copy/move the supplied Pubkey program_id, preserve the borrowed nested signer-seed slice and invoke Vec::new once. It does not call ToAccountInfos/ToAccountMetas, validate seeds or invoke CPI. The fresh empty-vector owner of the full model is logical ownership identity, not an allocation or a fresh backing pointer. Releases 0.1.0-0.4.4 lack remaining_accounts entirely; 0.4.5-0.32.3 store an owned program AccountInfo instead of a Pubkey program_id, retaining its Rc resources. Both the primary and copied-value observation use the current program-ID input/output shape. Replacing the old AccountInfo by its key would add a projection and discard fields not part of the existing binding, so the older constructor is incompatible even for this observation.
<!-- /registry -->

<!-- registry:review:72fd80e24b8a21a5 -->
<a id="review-72fd80e24b8a21a5"></a>

From<AnchorError> is absent through 0.21.0. Releases 0.22.0/0.22.1 use separate source and account_name options, which can coexist, and have no compared_values; their full payload cannot be identified with the current origin sum and comparison field. From 0.23.0 the complete Anchor payload shape is stable. However, 0.22.0-0.28.0 store Error variants inline and do not allocate the Box required by the primary contract. At 0.29.0 exactly one Box::new is introduced, moving all existing Strings and preserving their identities, with no extra String allocation. That implementation and full payload closure persist through 1.2.2. The existing BoxingLaws supply current payload, fresh identity and preservation of String observations without assuming allocation success. The ProgramError branch is unreachable in this conversion and does not narrow its range.
<!-- /registry -->

<!-- registry:review:0bedddbc7c0c7d06 -->
<a id="review-0bedddbc7c0c7d06"></a>

From<AnchorError> is absent through 0.21.0. Releases 0.22.0/0.22.1 use separate source and account_name options, which can coexist, and have no compared_values; their full payload cannot be identified with the current origin sum and comparison field. From 0.23.0 the complete Anchor payload shape is stable. However, 0.22.0-0.28.0 store Error variants inline and do not allocate the Box required by the primary contract. At 0.29.0 exactly one Box::new is introduced, moving all existing Strings and preserving their identities, with no extra String allocation. That implementation and full payload closure persist through 1.2.2. The existing BoxingLaws supply current payload, fresh identity and preservation of String observations without assuming allocation success. The ProgramError branch is unreachable in this conversion and does not narrow its range. Anchor 1.0.0 through 1.0.3 still define Error locally; the facade begins at 1.1.1.
<!-- /registry -->

<!-- registry:review:a76da9cda3cce162 -->
<a id="review-a76da9cda3cce162"></a>

All six stable standalone anchor-lang-error releases preserve the current boxed Error, AnchorError, ProgramErrorWithOrigin, Source, ErrorOrigin and ComparedValues closure and the reached method. ProgramError is the 3.0.x payload domain. The v3/v4 Pubkey aliases in 1.2.1/1.2.2 preserve the copied key values. Anchor-lang reexports this crate starting at 1.1.1; standalone 1.0.1 is source-only evidence and does not mean anchor-lang 1.0.1 used that package. The same operation-specific boxing, replacement, callback sequencing and cleanup argument in the anchor-lang review applies without changing the listed existing conditions.
<!-- /registry -->

<!-- registry:review:d18e6504297f919d -->
<a id="review-d18e6504297f919d"></a>

The supporting value observation explicitly omits Box/String lifecycle. The complete Anchor payload is therefore compatible already at 0.23.0, including the inline Error variants of 0.23.0-0.28.0; it embeds the exact name, u32 code, message, origin and comparison. The 0.22.0/0.22.1 payload has separate source/account_name options and no comparison, so it is incompatible. The API is absent through 0.21.0. ProgramError is not an input or reached branch of this operation.
<!-- /registry -->

<!-- registry:review:0904c47ed30f52fe -->
<a id="review-0904c47ed30f52fe"></a>

The supporting value observation explicitly omits Box/String lifecycle. The complete Anchor payload is therefore compatible already at 0.23.0, including the inline Error variants of 0.23.0-0.28.0; it embeds the exact name, u32 code, message, origin and comparison. The 0.22.0/0.22.1 payload has separate source/account_name options and no comparison, so it is incompatible. The API is absent through 0.21.0. ProgramError is not an input or reached branch of this operation. Anchor 1.0.0 through 1.0.3 still define Error locally; the facade begins at 1.1.1.
<!-- /registry -->

<!-- registry:review:6d347b589b7c33bd -->
<a id="review-6d347b589b7c33bd"></a>

The top-level method body is byte-identical from 0.23.0 through 1.2.2, but the complete contract is not. Inline Error variants before 0.29.0 lack the retained Box identity of the full model. Throughout 0.23.0-0.32.3 the reached ProgramError has BorshIoError(String), and some historical versions also lack later variants. The current fixed ProgramError.Value contains unit borshIoError and no owned message; an arbitrary old message cannot be silently forgotten in the stated complete payload, and its ownership/retirement is absent from the current primary resources. The observation also retains this concrete payload domain; restricting to common variants or adding message erasure would be a new contract/binding. From 1.0.0 all payloads fit: preserve the receiver variant, Box identity, error/origin fields, retire old compared-value Strings left then right, and install the supplied key pair. The exact existing ComparisonLaws and reached ComparisonStoreReady remain the admission conditions. This API is absent through 0.22.1.
<!-- /registry -->

<!-- registry:review:8660342c3bedbb7e -->
<a id="review-8660342c3bedbb7e"></a>

The top-level method body is byte-identical from 0.23.0 through 1.2.2, but the complete contract is not. Inline Error variants before 0.29.0 lack the retained Box identity of the full model. Throughout 0.23.0-0.32.3 the reached ProgramError has BorshIoError(String), and some historical versions also lack later variants. The current fixed ProgramError.Value contains unit borshIoError and no owned message; an arbitrary old message cannot be silently forgotten in the stated complete payload, and its ownership/retirement is absent from the current primary resources. The observation also retains this concrete payload domain; restricting to common variants or adding message erasure would be a new contract/binding. From 1.0.0 all payloads fit: preserve the receiver variant, Box identity, error/origin fields, retire old compared-value Strings left then right, and install the supplied key pair. The exact existing ComparisonLaws and reached ComparisonStoreReady remain the admission conditions. This API is absent through 0.22.1. Anchor 1.0.0 through 1.0.3 still define Error locally; the facade begins at 1.1.1.
<!-- /registry -->

<!-- registry:review:868bcb39d3442bc2 -->
<a id="review-868bcb39d3442bc2"></a>

The method body is byte-identical from 0.23.0 through 1.2.2. It accepts two independent impl ToString types, calls the left conversion before the right at their actual states, replaces the old comparison only after both return, and drops operands left then right. Conversion unwind cleans any first returned String, then operands and the current receiver; a second unwind terminates. The existing callback readiness/store premises retain needed current resources without assuming callback success or termination. On a destructor panic after moving self into the return place, the fixed compiler exhibits the leak described in rustc#47949; the existing primary model explicitly admits both the release and leak choices. Pre-0.29.0 inline variants violate Box identity; all 0.23.0-0.32.3 arbitrary ProgramError payloads include BorshIoError(String), incompatible with the current concrete unit variant in both the primary and observation models. No new no-panic, common-variant or message-erasure restriction is introduced. The API is absent through 0.22.1; both facets are compatible from 1.0.0.
<!-- /registry -->

<!-- registry:review:0fb18df3c3041d5f -->
<a id="review-0fb18df3c3041d5f"></a>

The method body is byte-identical from 0.23.0 through 1.2.2. It accepts two independent impl ToString types, calls the left conversion before the right at their actual states, replaces the old comparison only after both return, and drops operands left then right. Conversion unwind cleans any first returned String, then operands and the current receiver; a second unwind terminates. The existing callback readiness/store premises retain needed current resources without assuming callback success or termination. On a destructor panic after moving self into the return place, the fixed compiler exhibits the leak described in rustc#47949; the existing primary model explicitly admits both the release and leak choices. Pre-0.29.0 inline variants violate Box identity; all 0.23.0-0.32.3 arbitrary ProgramError payloads include BorshIoError(String), incompatible with the current concrete unit variant in both the primary and observation models. No new no-panic, common-variant or message-erasure restriction is introduced. The API is absent through 0.22.1; both facets are compatible from 1.0.0. Anchor 1.0.0 through 1.0.3 still define Error locally; the facade begins at 1.1.1.
<!-- /registry -->

<!-- registry:review:9a092aafbafd7039 -->
<a id="review-9a092aafbafd7039"></a>

From 0.32.0 the Anchor-owned wrapper implements both existing target branches: Solana forwards the original outer slice pointer and field count once to the declared sink; other targets evaluate black_box(data) with no sink call. The 1.2.1/1.2.2 compat-module indirection selects equivalent v3/v4 declarations. Prior releases reexport solana-program::log::sol_log_data where present. Every reviewed API-bearing historical wrapper calls a mutable host stub on the host, rather than the required host no-op, so the whole two-target contract is incompatible. solana-program 1.8.0 and earlier inspected pins have no such API; 1.8.1 first introduces it. Anchor releases exactly pinning 1.5.0, 1.7.8 or 1.7.11 are classified API-absent. Earlier caret dependencies can select an API-absent version or an available-but-incompatible wrapper; the incompatible array means no compatible executable resolution, with this absence nuance retained. No native SBF/static-syscall execution, display encoding or runtime logging success is claimed.
<!-- /registry -->

<!-- registry:review:5bcf5abbe8f1d09b -->
<a id="review-5bcf5abbe8f1d09b"></a>

References: 0.32.1, 0.32.2 and 0.32.3, whose complete Account/wrapper sources and relevant dependency requirements agree. The declared [0.32.1, 0.33.0) range assumes preservation of the ordinary Clone derive: clone T through its actual decoded-field source reference, then copy the borrowed AccountInfo reference. Callback identity, current value, interior effects, payload ownership and every finite exit remain in the indexed contract. The result has a fresh logical wrapper identity; retaining borrowed info neither clones Rc fields nor asserts a heap allocation. The owned-info variant stays separate.
<!-- /registry -->

<!-- registry:review:219dc3ba043168ef -->
<a id="review-219dc3ba043168ef"></a>

Reference source: anchor-lang 0.29.0. Invoke the actual payload Clone operation and retain the borrowed AccountInfo identity. Preserve callback effects and fresh wrapper/payload identities without inventing an Rc clone for the borrowed field. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:03fc209448398d95 -->
<a id="review-03fc209448398d95"></a>

References: 0.32.1, 0.32.2 and 0.32.3, with identical complete Account, Program and Signer sources and relevant dependency requirements. The declared [0.32.1, 0.33.0) range assumes that the four exact receiver/trait mappings return the same separately stored AccountInfo reference through its existing parent loan. The resolved AccountInfo provider preserves the current complete record, defining identity and emitted representation. These projections perform no clone, RefCell acquisition, allocation, owner check or cleanup. Equal lamports/data handles do not identify distinct containing records; owned-info and decoded-payload projections remain separate.
<!-- /registry -->

<!-- registry:review:ce0f2964ad4233d8 -->
<a id="review-ce0f2964ad4233d8"></a>

The declared compatible range assumes return of the same borrowed AccountInfo object with its parent lifetime and complete auxiliary state. InterfaceAccount delegates through its contained Account without replacing its saved owner; no AccountInfo clone or owned-field projection is inserted. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:436d2c7591da80f0 -->
<a id="review-436d2c7591da80f0"></a>

The exact AccountInfo object reference, preserving its parent lifetime and distinguishing an owned receiver field from an external shared object. Each listed immutable release was reviewed separately. Anchor 0.27.0 owns AccountInfo, while 0.29.0, 0.32.1, 1.0.2 and 1.1.2 store a shared reference. InterfaceAccount delegates to its contained Account and preserves the saved owner. Callback identities, source loans, owned payload transfer, current AccountInfo cells and all finite exits remain explicit at the family index; no source body, target-layout or dependency implementation proof is claimed. See source-notes/anchor-views.md. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:d44710004c562874 -->
<a id="review-d44710004c562874"></a>

Reference source: anchor-lang 0.29.0. Return the stored AccountInfo reference of the same wrapper without cloning, deserializing or reading its metadata. Equal records do not authorize swapping the actual returned pointer or loan. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:00b4c9b17a9d93ea -->
<a id="review-00b4c9b17a9d93ea"></a>

References: 0.32.1, 0.32.2 and 0.32.3, with identical complete Account source and anchor-debug definition. The declared [0.32.1, 0.33.0) range assumes preservation of the same exclusive decoded-field reference. With debug disabled there is no writability check; with debug enabled and is_writable false, the actual message provider logs 'The given Account is not mutable' before panic. Their diagnostic text, effects and all finite exits remain indexed. A source binding limited to the ordinary branch must require debug = false; the debug branch of the full family adds no blanket writable precondition.
<!-- /registry -->

<!-- registry:review:8a9f23dcd6b452ff -->
<a id="review-8a9f23dcd6b452ff"></a>

The declared compatible range assumes return of the same exclusive decoded-field reference and the anchor-debug branch that logs and panics when is_writable is false. Both feature outcomes retain actual callback effects and the borrowed AccountInfo representation. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:1854ee58f586ece5 -->
<a id="review-1854ee58f586ece5"></a>

Reference source: anchor-lang 0.29.0. Return the decoded field of the same wrapper with the original exclusive loan. Retain the 0.29 debug-only writable assertion and its selected panic effects; release-mode access does not silently acquire this check. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:2107f2488961f876 -->
<a id="review-2107f2488961f876"></a>

Return the same exclusive decoded-field reference. The separately indexed anchor-debug branch logs and panics on a non-writable account; the ordinary branch retains the same reference and state. No new feature gate is inferred. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:ac0bb934a8263fe7 -->
<a id="review-ac0bb934a8263fe7"></a>

References: 0.32.1, 0.32.2 and 0.32.3, with identical complete Key source, key-provider import and relevant dependency requirement. The declared [0.32.1, 0.33.0) range assumes that this exact implementation for solana_pubkey::Pubkey copies all 32 bytes and preserves the complete ambient world. The used nominal key provider and Copy/value interpretation must remain compatible; an Address-defined receiver is a distinct source identity. No AccountInfo clone, borrow, serialization, allocator or key-search operation is reached.
<!-- /registry -->

<!-- registry:review:17abe04ccbb538af -->
<a id="review-17abe04ccbb538af"></a>

The declared compatible range assumes copying all 32 bytes of the actual Pubkey/Address while leaving the supplied state unchanged. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:4d1141e14a67caea -->
<a id="review-4d1141e14a67caea"></a>

Copies the complete 32-byte Pubkey/Address and preserves the supplied ambient state. Each listed immutable release was reviewed separately. Anchor 0.27.0 owns AccountInfo, while 0.29.0, 0.32.1, 1.0.2 and 1.1.2 store a shared reference. InterfaceAccount delegates to its contained Account and preserves the saved owner. Callback identities, source loans, owned payload transfer, current AccountInfo cells and all finite exits remain explicit at the family index; no source body, target-layout or dependency implementation proof is claimed. See source-notes/anchor-views.md. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:d8725d58e869e38f -->
<a id="review-d8725d58e869e38f"></a>

Reference source: anchor-lang 0.29.0. Copy the complete monolithic Pubkey bytes while retaining the actual source key and nominal identity. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:2c5b2685a85f8e3b -->
<a id="review-2c5b2685a85f8e3b"></a>

Copy the complete 32-byte Pubkey and preserve the ambient state. This operation adds no callback, allocation or source-reference identity. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:cecd0cb140065c93 -->
<a id="review-cecd0cb140065c93"></a>

References: 0.32.1, 0.32.2 and 0.32.3, with identical complete Account/InterfaceAccount sources and relevant AccountInfo/Pubkey requirements. The declared [0.32.1, 0.33.0) range assumes that Account::key copies the current key through its stored AccountInfo reference, and InterfaceAccount::key delegates to its contained Account while preserving its saved owner. The actual nominal Pubkey Copy provider, current record, source loans and auxiliary world remain unchanged. Neither path adds a RefCell probe, clone, owner validation, allocation, cleanup or blanket ToAccountInfo callback.
<!-- /registry -->

<!-- registry:review:f69484d7a623d0cc -->
<a id="review-f69484d7a623d0cc"></a>

The declared compatible range assumes copying the current wrapper key while retaining the complete source loan and auxiliary state, including InterfaceAccount delegation and its saved owner. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:74ebe858db18350e -->
<a id="review-74ebe858db18350e"></a>

Copies the current wrapper key and preserves the entire source-loan and auxiliary state. Each listed immutable release was reviewed separately. Anchor 0.27.0 owns AccountInfo, while 0.29.0, 0.32.1, 1.0.2 and 1.1.2 store a shared reference. InterfaceAccount delegates to its contained Account and preserves the saved owner. Callback identities, source loans, owned payload transfer, current AccountInfo cells and all finite exits remain explicit at the family index; no source body, target-layout or dependency implementation proof is claimed. See source-notes/anchor-views.md. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:649466be651373a2 -->
<a id="review-649466be651373a2"></a>

Reference source: anchor-lang 0.29.0. Read the key through the actual AccountInfo of the current wrapper and return all key bytes. Retain the wrapper, record and reference identities without a Clone callback. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:fd22da3cb14a9407 -->
<a id="review-fd22da3cb14a9407"></a>

Copy the current wrapper key from the actual owned AccountInfo field, preserving the full source loan and auxiliary state. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:cafbae0e28188414 -->
<a id="review-cafbae0e28188414"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: call write once, perform one bounded memcpy while capacity remains, and retain the copied prefix and cursor advance when a short write returns WriteZero. There is no retry or rollback. An empty input reaches count-zero memcpy while capacity remains; an exhausted writer skips copying. The reached copy and diagnostic primitives retain their effects and abnormal exits.
<!-- /registry -->

<!-- registry:review:1387e76ba05f59df -->
<a id="review-1387e76ba05f59df"></a>

The declared compatible range assumes one write attempt: copy at most remaining capacity through the actual memcpy provider and advance by that partial count. A short write allocates WriteZero and retains the prefix mutation without retry; exhausted capacity skips copying, while empty input with remaining capacity still reaches a zero-count copy. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:9936f00c0de2e891 -->
<a id="review-9936f00c0de2e891"></a>

Reference source: anchor-lang 0.29.0. Write through the actual current cursor, advance by the copied prefix, and report WriteZero after a short write. Preserve partial destination mutation and the source 64-bit word interpretation. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:499917cfc4d760c8 -->
<a id="review-499917cfc4d760c8"></a>

BpfWriter::write_all invokes write once, copies at most the remaining capacity through the exact memcpy boundary and advances position by that partial count. A short write returns WriteZero with its allocated diagnostic after preserving the prefix mutation; it does not retry. At exhausted capacity write returns zero without copying, while an empty input with remaining capacity still reaches memcpy with count zero. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:b98115cc31b8ad7a -->
<a id="review-b98115cc31b8ad7a"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: borrow the actual error/origin/comparison variants, preserve exact formatting and log order, and retain each temporary String through its log call and subsequent cleanup. ProgramError logging clones the owned payload before consuming that clone for status conversion. Host-logger unwind and the separately indexed non-unwinding Solana logger retain their existing effects; the original error stays borrowed.
<!-- /registry -->

<!-- registry:review:67efb0c3fdf2e1a0 -->
<a id="review-67efb0c3fdf2e1a0"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: move the bumps payload and preserve the borrowed program, accounts and remaining-account references. Constructing Context does not call account traits or destroy/project the supplied generic payload; the associated Bumps representation stays part of the source binding.
<!-- /registry -->

<!-- registry:review:ba0880d64f3b9b84 -->
<a id="review-ba0880d64f3b9b84"></a>

The declared compatible range assumes movement of the actual Bumps payload and retention of the borrowed program, accounts and remaining-account references, without reaching account trait methods or adding a destructor. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:25f3294bfe14e3f5 -->
<a id="review-25f3294bfe14e3f5"></a>

The constructor moves bumps and preserves borrowed program/accounts/remaining references without reaching ToAccountInfos or other account trait methods. The older BTreeMap and newer associated Bumps payloads remain the supplied generic payload; no destructor or projection is added. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:f6a9cfd6dafd86c6 -->
<a id="review-f6a9cfd6dafd86c6"></a>

Reference source: anchor-lang 0.29.0. Store the exact program, mutable accounts, remaining-account slice and bump fields without callbacks or hidden cleanup. Retain all source-reference and lifetime obligations. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:e677aefe1f1575f6 -->
<a id="review-e677aefe1f1575f6"></a>

The constructor moves bumps and preserves borrowed program/accounts/remaining references without reaching ToAccountInfos or other account trait methods. The older BTreeMap and newer associated Bumps payloads remain the supplied generic payload; no destructor or projection is added. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:8165f65a78deb6f9 -->
<a id="review-8165f65a78deb6f9"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: call the actual ToString conversion, then replace the origin and drop its old owned account-name String. Preserve comparison fields, the full ProgramError payload and the same Error box. Destruction of the source argument and all callback/cleanup exits retain their source order.
<!-- /registry -->

<!-- registry:review:f4ce1484c670979d -->
<a id="review-f4ce1484c670979d"></a>

The generic ToString callback returns an owned new account name, then assignment drops the old origin account-name String and preserves all other fields. The source local argument is destroyed on normal/unwind exits. The moved result is the updated inline value in 0.27 and same Box owner later; callback unwind/terminal effects are preserved. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:92d8a42158610ded -->
<a id="review-92d8a42158610ded"></a>

Reference source: anchor-lang 0.29.0. Reach the actual ToString conversion before replacing the current origin and destroying its old payload. Preserve both error variants and boxed 0.29 storage, including callback failures and cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:ae0968aaaf7efc1d -->
<a id="review-ae0968aaaf7efc1d"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: convert left then right, retain the first String through the second conversion, and replace old comparisons only after both succeed. Preserve operand and temporary cleanup order, callback unwind/terminal exits and the updated boxed receiver. A destructor panic after moving the return value retains the existing release-or-leak alternative; it gains no invented cleanup.
<!-- /registry -->

<!-- registry:review:7c2013ec48389f6c -->
<a id="review-7c2013ec48389f6c"></a>

Reference source: anchor-lang 0.29.0. Evaluate the first ToString before the second, then replace the comparison payload and destroy the old value. Preserve temporary String owners, callback effects and source-ordered failure cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:710a7672cf0012a6 -->
<a id="review-710a7672cf0012a6"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: move accounts and the full owned program AccountInfo, retain the supplied borrowed nested signer slices, and obtain a fresh logical empty remaining-vector owner without Vec backing allocation. No account callback or CPI is reached; the copied-pubkey family is a different contract.
<!-- /registry -->

<!-- registry:review:410e0172e40bc02f -->
<a id="review-410e0172e40bc02f"></a>

Reference source: anchor-lang 0.29.0. Move the supplied program AccountInfo/accounts and retain the exact borrowed nested signer slices. Initialize only the remaining-account vector as empty and preserve field owners. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:5dde10ec9fd782f6 -->
<a id="review-5dde10ec9fd782f6"></a>

The older constructor keeps the full owned AccountInfo program and arbitrary moved accounts, retains the borrowed nested signer slices and obtains one fresh logical empty-vector owner. It neither allocates backing memory for the empty Vec nor reaches trait callbacks or CPI. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:e675ff4a45f5f49e -->
<a id="review-e675ff4a45f5f49e"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: replace only the borrowed signer-seed descriptor. Accounts, the full program AccountInfo and the existing remaining-vector owner/state move unchanged. The old borrowed seed descriptor has no destructor.
<!-- /registry -->

<!-- registry:review:52b056459b37f73a -->
<a id="review-52b056459b37f73a"></a>

The declared compatible range assumes replacement of only the borrowed signer-seed descriptor. The accounts, copied program_id and remaining-vector owner move unchanged; the borrowed old descriptor has no destructor. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:9c6ac7efa868fa0f -->
<a id="review-9c6ac7efa868fa0f"></a>

Replace only the borrowed signer-seed descriptor. Move the actual accounts, copied program_id and remaining-vector owner unchanged; the signer descriptor has no destructor. The old owned-AccountInfo program field is a separate interpretation of the shared family. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:bb0ec4e10fd56ffe -->
<a id="review-bb0ec4e10fd56ffe"></a>

Reference source: anchor-lang 0.29.0. Replace only the signer-seed reference tree, retaining the current program/accounts/remaining owners and their source field order. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:aa85d7a205293e23 -->
<a id="review-aa85d7a205293e23"></a>

Only the borrowed signer-seed descriptor is replaced. The full accounts/program/remaining-vector owners move unchanged, including the old AccountInfo Rc fields. Borrowed signer descriptors have no destructor. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:270a75fef77b91ef -->
<a id="review-270a75fef77b91ef"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: preserve the full 77-variant code/name/message table and zero offset, copy the name, convert the code, format the message, then allocate the Error box. The generated match and reached allocation/formatting exits must remain the same; equally sized but different tables are separate profiles.
<!-- /registry -->

<!-- registry:review:7dbd9c3d8ae2e895 -->
<a id="review-7dbd9c3d8ae2e895"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: drop replaced comparison Strings and store the two copied pubkeys in source order, preserving the origin, full ProgramError payload and Error box identity. This operation performs no ToString callback; its reached assignment/destruction effects remain explicit.
<!-- /registry -->

<!-- registry:review:8def0be8fdf8edaa -->
<a id="review-8def0be8fdf8edaa"></a>

Reference source: anchor-lang 0.29.0. Install the ordered compared Pubkeys and destroy the replaced comparison payload at the source assignment. Preserve all other current error fields and the boxed representation. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:12bcea8ccc19768e -->
<a id="review-12bcea8ccc19768e"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: select the exact variant name and construct one owned String through the reached string primitive. The 77-name match and its exits are preserved; this method does not format an error message or allocate an Error box.
<!-- /registry -->

<!-- registry:review:98ee2022e2f58de3 -->
<a id="review-98ee2022e2f58de3"></a>

The declared range [0.32.1, 0.33.0) assumes the behavior of the inspected 0.32.1–0.32.3 sources: move accounts and the full owned program AccountInfo, including its Rc fields; obtain a fresh logical empty remaining-vector owner without allocating Vec backing storage; and retain an empty borrowed signer descriptor. No account callback or CPI is reached. The AccountInfo-program family remains distinct from the copied-pubkey family.
<!-- /registry -->

<!-- registry:review:4398a8132a2cdae6 -->
<a id="review-4398a8132a2cdae6"></a>

The declared compatible range assumes movement of all accounts and the copied program_id, retention of source references and acquisition of one actual empty remaining-vector owner. The complete generic Program index and the existing EmptyReady facts are retained. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:00b8c9c32d731530 -->
<a id="review-00b8c9c32d731530"></a>

The constructor moves every accounts field and the full program field, preserves source references and obtains one empty remaining-vector owner. The source profile selects an owned AccountInfo through 0.32.1 and copied Pubkey in 1.x; these are distinct generic Program interpretations, not a key projection. EmptyReady current/fresh facts support the actual output facts. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:9b574609335f5e3c -->
<a id="review-9b574609335f5e3c"></a>

Reference source: anchor-lang 0.29.0. Move the supplied owned program AccountInfo and accounts into the context with empty remaining accounts and signer seeds. Preserve actual field owners and drop order. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:2f39e6fd1357c6b7 -->
<a id="review-2f39e6fd1357c6b7"></a>

The constructor moves every accounts field and the full program field, preserves source references and obtains one empty remaining-vector owner. The source profile selects an owned AccountInfo through 0.32.1 and copied Pubkey in 1.x; these are distinct generic Program interpretations, not a key projection. EmptyReady current/fresh facts support the actual output facts. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:f39930520dcff385 -->
<a id="review-f39930520dcff385"></a>

Anchor Lang 0.32.0–0.32.3 have identical System wrapper, context and error-conversion files. The declared 0.32 range assumes the same tag 8 and copied space, with one writable signer, moved account array, owned context program and boxed legacy error cleanup. The 0.32.0 prelude-only change is outside these calls; 1.0.0 changes the program carrier.
<!-- /registry -->

<!-- registry:review:198acae4cfd2cd5f -->
<a id="review-198acae4cfd2cd5f"></a>

Reference source: anchor-lang 0.29.0. Construct the allocate instruction before invoking with the exact ordered account and signer-seed slices. Preserve current context owners, constructor/CPI outcomes and cleanup; invocation stays opaque. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:3309aed5d71fc528 -->
<a id="review-3309aed5d71fc528"></a>

Anchor Lang 0.32.0–0.32.3 have identical System wrapper, context and error-conversion files. The declared 0.32 range assumes the same tag 0 and lamports/space/owner, with ordered from/to writable signers, moved account array, owned context program and boxed legacy error cleanup. The 0.32.0 prelude-only change is outside these calls; 1.0.0 changes the program carrier.
<!-- /registry -->

<!-- registry:review:f22122a4b6b5a2f2 -->
<a id="review-f22122a4b6b5a2f2"></a>

Reference source: anchor-lang 0.29.0. Construct the transfer/new-owner data and exact from/to metas before opaque invocation. Retain the source account order, lamports/space/owner arguments and context cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:79f2fe72cd619c05 -->
<a id="review-79f2fe72cd619c05"></a>

Anchor Lang 0.32.0–0.32.3 have identical System wrapper, context and error-conversion files. The declared 0.32 range assumes the same tag 2 and lamports, with a writable signer source and writable nonsigner destination, moved account array, owned context program and boxed legacy error cleanup. The 0.32.0 prelude-only change is outside these calls; 1.0.0 changes the program carrier.
<!-- /registry -->

<!-- registry:review:8202c264802c9ee4 -->
<a id="review-8202c264802c9ee4"></a>

Reference source: anchor-lang 0.29.0. Construct transfer with the exact lamports and from/to order before opaque invocation. Retain signer seeds, context owners and all ordinary/abnormal callback exits. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:a329e07ad025b746 -->
<a id="review-a329e07ad025b746"></a>

Anchor Lang 0.32.0–0.32.3 have identical System wrapper, context and error-conversion files. The declared 0.32 range assumes the same tag 1 and all owner bytes, with one writable signer, moved account array, owned context program and boxed legacy error cleanup. The 0.32.0 prelude-only change is outside these calls; 1.0.0 changes the program carrier.
<!-- /registry -->

<!-- registry:review:cea5c732e4195604 -->
<a id="review-cea5c732e4195604"></a>

Reference source: anchor-lang 0.29.0. Construct the assign instruction with the supplied owner before opaque invocation. Preserve exact account order, signer seeds, owned context fields and all reached cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:bfc19087781fc029 -->
<a id="review-bfc19087781fc029"></a>

The 0.32.0–0.32.3 references return Ok(()) for None and delegate Some to its current inner AccountsExit implementation. Compatibility assumes this case split and full outcome/state forwarding remain unchanged.
<!-- /registry -->

<!-- registry:review:c38820b68da88ac5 -->
<a id="review-c38820b68da88ac5"></a>

Delegate the selected exit/close to the actual current inner payload and preserve its full outcome and successor state; Option None exit returns Ok without a callback. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:b878999bd64af9fb -->
<a id="review-b878999bd64af9fb"></a>

Reference source: anchor-lang 0.29.0. Return directly for None and call only the actual inner exit for Some, retaining its exact program argument and effects. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:c8971e95a1cd0b47 -->
<a id="review-c8971e95a1cd0b47"></a>

The 0.32.0–0.32.3 references consume one record and check only its signer flag. Compatibility assumes the empty-slice error, AccountNotSigner diagnostic and borrowed-record result remain unchanged; no writable check is added.
<!-- /registry -->

<!-- registry:review:310ae4e20421be44 -->
<a id="review-310ae4e20421be44"></a>

The declared compatible range assumes empty-input AccountNotEnoughKeys without advancing the slice; otherwise consumption of the first borrowed AccountReference before the signer check. Preserve the boxed error or successful reference and every resulting slice, bumps and reallocation state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:653979b049e7b074 -->
<a id="review-653979b049e7b074"></a>

Exact simple-wrapper checks, reached Id/CheckId/Sysvar callback effects, release-specific error resources and successful AccountInfo retention. Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:8db46e02fe0100d6 -->
<a id="review-8db46e02fe0100d6"></a>

Reference source: anchor-lang 0.29.0. Consume one AccountInfo before checking the signer flag, preserving the consumed tail on validation failure and retaining the actual borrowed record on success. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:5f8578d280594623 -->
<a id="review-5f8578d280594623"></a>

The 0.32.0–0.32.3 references consume one record and clone its AccountInfo owner, or construct AccountNotEnoughKeys without consuming an empty slice. Compatibility assumes that slice update and ordered Rc clone/cleanup behavior remain unchanged.
<!-- /registry -->

<!-- registry:review:2d9b0bc928644d80 -->
<a id="review-2d9b0bc928644d80"></a>

Reference source: anchor-lang 0.29.0. Consume the head reference and clone its actual AccountInfo owners in source order. Preserve empty-input error effects, alias counters and cleanup on reached failures. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:e5bd96001488fb02 -->
<a id="review-e5bd96001488fb02"></a>

The 0.32.0–0.32.3 references consume one record, compare its key with Id, then check executable. Compatibility assumes that order, diagnostic allocation before the second Id call, and the borrowed-record result remain unchanged.
<!-- /registry -->

<!-- registry:review:c6a03a4622829098 -->
<a id="review-c6a03a4622829098"></a>

The declared compatible range assumes empty-input AccountNotEnoughKeys without advancing the slice; otherwise consume the first AccountReference, invoke the actual Id provider, then check program key and executable status in source order. Preserve boxed errors, callback effects and all remaining-slice, bumps and reallocation state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:dd1e7209a8e225b5 -->
<a id="review-dd1e7209a8e225b5"></a>

Exact simple-wrapper checks, reached Id/CheckId/Sysvar callback effects, release-specific error resources and successful AccountInfo retention. Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. Exclude 1.0.0/1.0.1: their generic T::id()==zero shortcut skips the ID check and adds a reached Id call. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:26c5efb0a530ad51 -->
<a id="review-26c5efb0a530ad51"></a>

Reference source: anchor-lang 0.29.0. Consume one AccountInfo before Program validation. Preserve Id/key comparison before executable validation and retain empty-input or callback error effects. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:acdb7923b9d8f611 -->
<a id="review-acdb7923b9d8f611"></a>

The 0.32.0–0.32.3 references consume one record before checked Account construction, leaving an empty slice untouched. Compatibility assumes that consumption, initialization/Owner ordering, checked decoder selection and borrowed-record result remain unchanged.
<!-- /registry -->

<!-- registry:review:90050e16b7b595b2 -->
<a id="review-90050e16b7b595b2"></a>

The declared compatible range assumes consumption of the first AccountReference before initialization and current-owner checks and the checked decoder, while empty input keeps its position and constructs AccountNotEnoughKeys. Preserve boxed errors, shared data-guard cleanup and the actual remaining slice, bumps and reallocations. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:d3248ad6546ead04 -->
<a id="review-d3248ad6546ead04"></a>

Reference source: anchor-lang 0.29.0. Consume the head AccountInfo before the actual checked conversion, retain owner/initialization checks and guarded deserialization, and preserve the consumed tail and all error/cleanup effects. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:51b5e6d3afdd59c1 -->
<a id="review-51b5e6d3afdd59c1"></a>

The 0.32.0–0.32.3 references call the actual current inner AccountsExit implementation. Compatibility assumes this single delegation and full outcome/state forwarding remain unchanged.
<!-- /registry -->

<!-- registry:review:252fc2084e3cd5f7 -->
<a id="review-252fc2084e3cd5f7"></a>

The declared compatible range assumes delegation to the actual current inner payload and preservation of the entire exit result and successor state without an extra allocation or projection. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:7be300aaa65fcc92 -->
<a id="review-7be300aaa65fcc92"></a>

Reference source: anchor-lang 0.29.0. Delegate to the contained exit implementation with the exact program ID and payload. Preserve callback writes, errors, unwind and terminal effects. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:d23fc95e251e7d5f -->
<a id="review-d23fc95e251e7d5f"></a>

Delegate AccountsExit to the actual current inner payload and retain its complete outcome, effects and successor state. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:bb56bafabd46bf0c -->
<a id="review-bb56bafabd46bf0c"></a>

The 0.32.0–0.32.3 references return Ok(()) without reading the receiver or program ID. Compatibility within the declared 0.32 line assumes this provided no-op and its Result representation remain unchanged.
<!-- /registry -->

<!-- registry:review:3bffdb725f97c61d -->
<a id="review-3bffdb725f97c61d"></a>

The declared compatible range assumes the provided default implementation returning Ok(()) with unchanged state. An overriding implementation has its own source identity. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:40c9ffe942ba1185 -->
<a id="review-40c9ffe942ba1185"></a>

The provided AccountsExit::exit implementation returns Ok(()) and leaves all state unchanged. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:34d3d4007e8a3287 -->
<a id="review-34d3d4007e8a3287"></a>

Reference source: anchor-lang 0.29.0. Return unit through the default exit without serializing a payload or acquiring an AccountInfo guard. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:798106631db1c4f4 -->
<a id="review-798106631db1c4f4"></a>

The provided AccountsExit::exit implementation returns Ok(()) and leaves all state unchanged. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:cc69e7463d681cfc -->
<a id="review-cc69e7463d681cfc"></a>

The 0.32.0–0.32.3 references invoke inner Accounts and box only its successful payload. Compatibility assumes this sequencing, all five operand effects, and skipping allocation on inner error, unwind or terminal exit remain unchanged.
<!-- /registry -->

<!-- registry:review:2e8e6a6a040ed329 -->
<a id="review-2e8e6a6a040ed329"></a>

The declared compatible range assumes the actual inner Accounts execution followed by Box allocation only on Ok, preserving the inner remaining slice, bumps, reallocations and every allocation, error, unwind or terminal outcome. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:e4af3f4e9a48e7df -->
<a id="review-e4af3f4e9a48e7df"></a>

Inner Accounts execution followed by actual Box allocation only on Ok, preserving inner slice/bumps/reallocations and every error or unwind. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:665da3937b974dc2 -->
<a id="review-665da3937b974dc2"></a>

Reference source: anchor-lang 0.29.0. Call the actual inner Accounts implementation before allocating the Box for a successful payload. Preserve account consumption, allocation failures and payload cleanup in that order. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:4848542eb670cf21 -->
<a id="review-4848542eb670cf21"></a>

The 0.32.0–0.32.3 references clone the source and use destination-first checked_add(...).unwrap() close. Compatibility assumes this legacy path, ordered balance/owner/resize effects, alias behavior and moved-value cleanup remain unchanged; the noncloning and checked-error 1.x paths are distinct.
<!-- /registry -->

<!-- registry:review:a6cab200d716d34c -->
<a id="review-a6cab200d716d34c"></a>

Reference source: anchor-lang 0.29.0. Use the exact current RefCell policy and Rc subfield layout through the source close phases. Retain recipient/source balance order, owner assignment, data resizing and phase-aware cleanup; no final positive borrow-count gate is introduced. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:543b99368ed16eed -->
<a id="review-543b99368ed16eed"></a>

The 0.32.0–0.32.3 references call the actual current inner AccountsClose implementation with the moved destination. Compatibility assumes this single delegation and full outcome/state forwarding remain unchanged; it does not select Account.close semantics for arbitrary T.
<!-- /registry -->

<!-- registry:review:7d0b8d8abf17385f -->
<a id="review-7d0b8d8abf17385f"></a>

Reference source: anchor-lang 0.29.0. Delegate to the contained close implementation with the exact payload and recipient. Preserve all callback results, state changes and cleanup without independently asserting close success. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:f7a5cef2422aeafc -->
<a id="review-f7a5cef2422aeafc"></a>

The 0.32.0–0.32.3 references leave an empty slice unchanged, consume a program-ID sentinel once, or delegate the original operands to inner Accounts. Compatibility assumes those branches and the allow-missing-optionals switch of the defining crate remain unchanged.
<!-- /registry -->

<!-- registry:review:045def5f633585bf -->
<a id="review-045def5f633585bf"></a>

The declared compatible range assumes the allow-missing-optionals branch on empty input, consumption of a matching program-ID sentinel into None, and otherwise the exact inner Accounts call mapped to Some. Retain all callback state and finite outcomes; the feature remains an explicit family choice. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:ab8c820a42d950b2 -->
<a id="review-ab8c820a42d950b2"></a>

Actual optional-account feature branch, program-ID sentinel consumption, unchanged empty slice and exact inner Accounts delegation. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:64e333d87b933006 -->
<a id="review-64e333d87b933006"></a>

Reference source: anchor-lang 0.29.0. Keep empty input unchanged on its error branch; otherwise test the head program-key sentinel before consuming None or delegating Some to the actual Accounts implementation. Retain source consumption and callback outcomes. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:dba422d0aa141eb4 -->
<a id="review-dba422d0aa141eb4"></a>

The 0.32.0–0.32.3 references validate initialization and Owner before invoking try_deserialize_unchecked under a shared data guard. Compatibility assumes this ordering, unchecked callback selection, finite guard cleanup and borrowed-record result remain unchanged; the pre-0.29 owned clone is distinct.
<!-- /registry -->

<!-- registry:review:dadf33d357e38c81 -->
<a id="review-dadf33d357e38c81"></a>

The declared compatible range assumes the system-owner/zero-lamports initialization check, actual current-owner check and unchecked deserializer under the real shared data guard. Preserve the borrowed AccountInfo, boxed errors, source-order callbacks and cleanup. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:862f86dcfd22d7f0 -->
<a id="review-862f86dcfd22d7f0"></a>

Reference source: anchor-lang 0.29.0. Retain initialization and Owner observations before unchecked deserialization under the actual data guard. Preserve borrowed AccountInfo identity, payload/error ownership and source cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:49264beddecbe708 -->
<a id="review-49264beddecbe708"></a>

The 0.32.0–0.32.3 references call Owner, test expected ownership and closedness, then serialize under the mutable data guard without a local AccountInfo clone. Compatibility assumes this branch order, BpfWriter behavior and finite cleanup remain unchanged; pre-0.31 clones and the 1.2.2 unowned-account branch are distinct.
<!-- /registry -->

<!-- registry:review:05aaa74cafc76917 -->
<a id="review-05aaa74cafc76917"></a>

The declared compatible range assumes the expected-owner comparison and is_closed short circuit before the mutable data borrow and actual serializer, including partial writes and guard cleanup. The later unowned-account exit path is a different operation and is not admitted here. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:2692288b6e835b14 -->
<a id="review-2692288b6e835b14"></a>

Recheck the current owner, deserialize under the data guard, then destroy and replace the current payload at the source assignment, retaining partial effects on failure. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:73ecfe98a6be1c6b -->
<a id="review-73ecfe98a6be1c6b"></a>

Consume the head before CheckId, then executable validation; keep empty input unchanged while constructing AccountNotEnoughKeys. Retain the borrowed record and actual callback exits. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:09f135b72fd55342 -->
<a id="review-09f135b72fd55342"></a>

The declared compatible range assumes empty-input AccountNotEnoughKeys without advancing the slice; otherwise consume the first AccountReference, use the actual CheckId callback and then the executable check. Preserve boxed errors, callback effects and all remaining-slice, bumps and reallocation state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:444d8b9c528c55eb -->
<a id="review-444d8b9c528c55eb"></a>

Use the saved owner for the conditional exit; after the is_closed short circuit, retain guard, serializer writes and reached cleanup, including partial writes on failure. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:6ae8f68c48343cd3 -->
<a id="review-6ae8f68c48343cd3"></a>

The declared compatible range assumes delegation to Account exit using the saved expected owner, its is_closed short circuit and actual mutable guard/serializer, including partial writes and cleanup. The later unowned-account exit path is excluded. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:fc5c1f8d1b6fbe24 -->
<a id="review-fc5c1f8d1b6fbe24"></a>

Use the saved owner and short-circuit closed-account check before reaching the actual mutable data borrow and serializer. Preserve partial writes, guard cleanup and every reached callback outcome; this profile retains borrowed AccountInfo fields. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:8ac01362820cb151 -->
<a id="review-8ac01362820cb151"></a>

Delegate to the contained Account reload, retaining owner recheck, guard lifetime, payload replacement and the saved InterfaceAccount owner. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:30bf74158f5f4a7f -->
<a id="review-30bf74158f5f4a7f"></a>

Consume the head before initialization/current-owner checks and checked deserialization. Preserve the borrowed source record, saved owner and guard cleanup on failure. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:8b5e8201412c05df -->
<a id="review-8b5e8201412c05df"></a>

The declared compatible range assumes consumption of the first AccountReference before initialization, actual CheckOwner and checked deserialization, recording the current owner in the resulting InterfaceAccount. Empty input does not advance; callback outcomes, boxed errors, guard cleanup, bumps and reallocations remain explicit. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:9622e66f277d9004 -->
<a id="review-9622e66f277d9004"></a>

Source-ordered initialization, current-owner validation, selected checked or unchecked decoder and scoped AccountInfo clone/data-guard cleanup. Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:aa3b22dd744f7844 -->
<a id="review-aa3b22dd744f7844"></a>

Reference source: anchor-lang 0.29.0. Consume the head before initialization/current-owner checks and guarded deserialization. Retain the actual borrowed AccountInfo, saved owner, consumed tail and every reached payload/error cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:b5d9d7ea8a9ca78e -->
<a id="review-b5d9d7ea8a9ca78e"></a>

Consume one source record before the Sysvar conversion and preserve its exact identity; callback errors retain the consumed tail and their effects. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:75ba61640e9711cc -->
<a id="review-75ba61640e9711cc"></a>

Empty input constructs AccountNotEnoughKeys without consumption; otherwise consume and retain the head reference without owner, signer or executable validation. The 0.32.0–0.32.3 files agree. Compatibility within 0.32 assumes the same boxed errors, borrowed fields and reached operation order.
<!-- /registry -->

<!-- registry:review:df36b83472f2988f -->
<a id="review-df36b83472f2988f"></a>

The declared compatible range assumes empty-input AccountNotEnoughKeys without advancing the slice; otherwise consume and retain the first borrowed AccountReference without validation or Rc cloning, preserving bumps and reallocation state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:297fd753aa514df6 -->
<a id="review-297fd753aa514df6"></a>

The 0.32.0–0.32.3 references distinguish variants, compare Anchor error numbers and compare the complete inner ProgramError, including BorshIoError String content. They borrow payloads without destruction. Compatibility within 0.32 assumes these comparisons and boxed representations remain unchanged; equal numeric status alone is insufficient.
<!-- /registry -->

<!-- registry:review:43191d3584fbfadd -->
<a id="review-43191d3584fbfadd"></a>

Return the stored AccountInfo reference without a read, clone or guard; equal metadata does not identify distinct records. The inspected 0.32 and 1.x references agree, including the 1.2 constructor rename. Compatibility assumes this local protocol and actual representation obligations remain unchanged.
<!-- /registry -->

<!-- registry:review:15956efb096977cf -->
<a id="review-15956efb096977cf"></a>

After Owner and is_closed short circuits, borrow data and write the discriminator. A short destination retains the partial write before unwrap unwinds; release the guard on continuing exits. Inspected 0.32 and pre-1.2 references agree. Compatibility assumes this order and cleanup; 1.2.0 introduces size checks and is excluded.
<!-- /registry -->

<!-- registry:review:c55f49e790cc7dce -->
<a id="review-c55f49e790cc7dce"></a>

Check writable, acquire data, panic on a short discriminator prefix, reject nonzero bytes, then map the same guard with source slicing/alignment failures. Write no bytes. Inspected 0.32 and pre-1.2 references agree. Compatibility assumes this order and cleanup; 1.2.0 introduces size checks and is excluded.
<!-- /registry -->

<!-- registry:review:5f5acd1eb7ec72cf -->
<a id="review-5f5acd1eb7ec72cf"></a>

This partial observation follows load_init through the same guard and mapped bytes; diagnostic allocation stays in the primary family. It has no source-call registration. Inspected 0.32 and pre-1.2 references agree. Compatibility assumes this order and cleanup; 1.2.0 introduces size checks and is excluded.
<!-- /registry -->

<!-- registry:review:c549390925c8aa2b -->
<a id="review-c549390925c8aa2b"></a>

Consume one record before checked construction, preserving the consumed tail on error or unwind; empty input constructs AccountNotEnoughKeys. Bumps and reallocations remain unchanged. The inspected 0.32 and 1.x references agree, including the 1.2 constructor rename. Compatibility assumes this local protocol and actual representation obligations remain unchanged.
<!-- /registry -->

<!-- registry:review:2fc6c963876cd396 -->
<a id="review-2fc6c963876cd396"></a>

Call Owner before comparing current owner; mismatch constructs the error and calls Owner again with the recorded cleanup. Success stores the same borrowed record without reading data or the program-ID argument. The inspected 0.32 and 1.x references agree, including the 1.2 constructor rename. Compatibility assumes this local protocol and actual representation obligations remain unchanged.
<!-- /registry -->

<!-- registry:review:21a647e89f9431bb -->
<a id="review-21a647e89f9431bb"></a>

The 0.32.0–0.32.3 references clone the Program, Interface, Signer, SystemAccount or UncheckedAccount wrapper while retaining its borrowed AccountInfo record. No payload callback or owned Rc clone is reached. Compatibility within 0.32 assumes the same borrowed fields and clone protocol; 0.27.0 owns AccountInfo and remains a different variant.
<!-- /registry -->

<!-- registry:review:e39b799783a3767c -->
<a id="review-e39b799783a3767c"></a>

The inspected 0.32.0–0.32.3 operation and reached context/error definitions agree. The declared 0.32 range assumes the complete consuming IO-to-ProgramError conversion, including user Display/Drop and its actual unwind state, followed only on normal return by boxed legacy ProgramError allocation. Actual provider, layout and finite-exit obligations remain unchanged.
<!-- /registry -->

<!-- registry:review:ee4df3b43f1f27e4 -->
<a id="review-ee4df3b43f1f27e4"></a>

The inspected 0.32.0–0.32.3 operation and reached context/error definitions agree. The declared 0.32 range assumes all 32 bytes of the fixed System ID, with no allocation, syscall or source-state change. Actual provider, layout and finite-exit obligations remain unchanged.
<!-- /registry -->

<!-- registry:review:1809d4fc8435b01b -->
<a id="review-1809d4fc8435b01b"></a>

The inspected 0.32.0–0.32.3 operation and reached context/error definitions agree. The declared 0.32 range assumes the actual AsRef loan and current lamports cell, temporary shared acquisition/release and configured panic behavior with unchanged receiver ownership. Actual provider, layout and finite-exit obligations remain unchanged.
<!-- /registry -->

<!-- registry:review:2c0a1cf16f62e91a -->
<a id="review-2c0a1cf16f62e91a"></a>

The declared compatible range assumes the system-owner/zero-lamports initialization check, actual CheckOwner and unchecked deserializer under the real shared data guard, then capture of the current owner. Preserve the borrowed AccountInfo, boxed errors and callback/cleanup effects. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:d2b59a80f7d44f6d -->
<a id="review-d2b59a80f7d44f6d"></a>

Source-ordered initialization, current-owner validation, selected checked or unchecked decoder and scoped AccountInfo clone/data-guard cleanup. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:6860409d19338f12 -->
<a id="review-6860409d19338f12"></a>

The declared compatible range assumes the current-owner recheck and actual deserializer, release of the shared data guard before set_inner, and then destruction/replacement of the old payload on the actual state. The held-guard reload family is not substituted. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:6fb1340f5555b2ca -->
<a id="review-6fb1340f5555b2ca"></a>

The declared compatible range assumes the fixed System ID, writable metadata in source order (the account-to-allocate signer) and little-endian Bincode variant 8 with the actual arguments before account moves. Remaining accounts are retained only for cleanup. Box the complete modern unit-Borsh ProgramError before Edition-2021 destruction of instruction metadata/data, the tail-expression account array and remaining accounts; copied program_id has no destructor. The invocation provider retains its full result and state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:91da534f83e0c970 -->
<a id="review-91da534f83e0c970"></a>

Construct fixed system ID, exact metadata order/flags and little-endian bincode data before moving accounts; remaining accounts are not forwarded. Edition-2021 cleanup drops instruction metadata/data, tail-expression account array, then remaining accounts; copied program_id has no destructor. ProgramError is boxed before cleanup. Review covers full context/error dependencies, not equal wrapper text alone. Projected-wrapper tests retain exact source and real context/constructors, replacing only the whole invocation signature. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:668d2059e30af99b -->
<a id="review-668d2059e30af99b"></a>

The declared compatible range assumes retention of the exact borrowed AccountReference without validation, allocation or Rc cloning. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:1ca77ddd349093ca -->
<a id="review-1ca77ddd349093ca"></a>

Direct unchecked wrapping moves the owned 0.27 input or retains the exact borrowed later AccountReference, without checks or Rc cloning. Reviewed source distinctions and continuation conditions are recorded in source-notes/anchor-lifecycle.md. Error representation is boxed; AccountInfo fields are borrowed. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:7078a0477afa2b02 -->
<a id="review-7078a0477afa2b02"></a>

The declared compatible range assumes the fixed System ID, writable metadata in source order (from signer then to nonsigner) and little-endian Bincode variant 2 with the actual arguments before account moves. Remaining accounts are retained only for cleanup. Box the complete modern unit-Borsh ProgramError before Edition-2021 destruction of instruction metadata/data, the tail-expression account array and remaining accounts; copied program_id has no destructor. The invocation provider retains its full result and state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:39e1f540dcc4f861 -->
<a id="review-39e1f540dcc4f861"></a>

The declared compatible range assumes the fixed System ID, writable metadata in source order (the account-to-assign signer) and little-endian Bincode variant 1 with the actual arguments before account moves. Remaining accounts are retained only for cleanup. Box the complete modern unit-Borsh ProgramError before Edition-2021 destruction of instruction metadata/data, the tail-expression account array and remaining accounts; copied program_id has no destructor. The invocation provider retains its full result and state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:ee0718273a829edc -->
<a id="review-ee0718273a829edc"></a>

The declared compatible range assumes the fixed little-endian bincode tag/u64/Option/Pubkey decoder for the four-arm loader-state enum, acceptance of trailing bytes and retention of the borrowed input slice. Failure boxes InvalidAccountData before dropping the actual bincode diagnostic. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:b9195e32d3f55e04 -->
<a id="review-b9195e32d3f55e04"></a>

The declared compatible range assumes source-order lamports reads and checked addition, current-cell writes, owner assignment and zero resize, including aliasing, borrow failures and moved-value cleanup. The borrowed AccountInfo is not cloned into a temporary; overflow follows the checked modern path. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:34be6adf5d4c6f3a -->
<a id="review-34be6adf5d4c6f3a"></a>

The declared compatible range assumes the fixed System ID, writable metadata in source order (from then to, both signers) and little-endian Bincode variant 0 with the actual arguments before account moves. Remaining accounts are retained only for cleanup. Box the complete modern unit-Borsh ProgramError before Edition-2021 destruction of instruction metadata/data, the tail-expression account array and remaining accounts; copied program_id has no destructor. The invocation provider retains its full result and state. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:f8ec6e1c7271909f -->
<a id="review-f8ec6e1c7271909f"></a>

The declared compatible range assumes the provided default forwarding the same mutable slice reference to the actual try_deserialize_unchecked callback, preserving every state, error, unwind and terminal result. Overrides remain different callable identities. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:6797d8b0c8331b2d -->
<a id="review-6797d8b0c8331b2d"></a>

The declared compatible range assumes the provided default forwarding the same mutable slice reference to the actual try_deserialize_unchecked callback, preserving every state, error, unwind and terminal result. Overrides remain different callable identities. This pre-cohort profile stops before the new 1.2.1 provider/feature selection. The inspected anchor-spl 1.1.2 Mint supplies only the unchecked method; the default remains defined by anchor-lang. This adds no reverse Cargo dependency and does not replace the actual provider/caller-unit join.
<!-- /registry -->

<!-- registry:review:7a1a5ff6283699b4 -->
<a id="review-7a1a5ff6283699b4"></a>

The declared compatible range assumes the provided default forwarding the same mutable slice reference to the actual try_deserialize_unchecked callback, preserving every state, error, unwind and terminal result. Overrides remain different callable identities. This pre-cohort profile stops before the new 1.2.1 provider/feature selection. The inspected anchor-spl 1.1.2 TokenAccount supplies only the unchecked method; the default remains defined by anchor-lang. This adds no reverse Cargo dependency and does not replace the actual provider/caller-unit join.
<!-- /registry -->

<!-- registry:review:531c760f2badcc6a -->
<a id="review-531c760f2badcc6a"></a>

Preserve the derived copy of the same AccountInfo reference and PhantomData. There is no Rc clone, payload read, owner check, discriminator check or borrow acquisition. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:a6c8fdcd8d564507 -->
<a id="review-a6c8fdcd8d564507"></a>

Preserve destination-then-source lamports reads, checked-add panic, ordered balance stores, system-owner assignment, resize-to-zero and destination cleanup, including aliases and late failures. The borrowed source is not cloned. Anchor 1.1 uses add_lamports with a different error/order protocol; 1.2.2 additionally rejects equal keys before those effects. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:3b92cb177a9fa090 -->
<a id="review-3b92cb177a9fa090"></a>

Preserve empty-slice error without advancement; otherwise advance the actual slice before the system-owner check and keep advancement on error. Retain the actual record, bumps, reallocations and reached error resources. The upper bound scopes this profile to the original diagnostic provider; it is not a claim that the later wrapper body differs. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:c007d729c6ce8825 -->
<a id="review-c007d729c6ce8825"></a>

Preserve the 1.0 CpiContext with its by-value program_id. Destroy the previous remaining Vec and its actual AccountInfo owners before storing the moved replacement; retain destructor outcomes. The 0.32 context instead owns a program AccountInfo, so equal assignment text alone is insufficient. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:2cfd0295b80b49a3 -->
<a id="review-2cfd0295b80b49a3"></a>

Preserve the complete migration-extended ErrorCode variant/code/name/message table and matching macro expansion. Name allocates one String; From copies the name, formats the message, then boxes the error in source order. The 0.32 table lacks these migration variants, and the 1.1 line moves the defining error module to anchor-lang-error; neither is selected by this profile. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:dd533accbc253c3e -->
<a id="review-dd533accbc253c3e"></a>

Preserve exact Error/origin/comparison branching, message bytes, formatting/logging order, temporary cleanup and all finite provider exits for the unit-Borsh ProgramError dependency. Rust string continuations do not change rendered messages. The old owned Borsh String protocol and the later defining error crate remain separate profiles. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:fd26ef5fc00c5624 -->
<a id="review-fd26ef5fc00c5624"></a>

Preserve the target_os=solana u64 syscall result cast to 64-bit usize and the fixed runtime frame-count interpretation. The inspected later change only redirects the excluded host stub; no host execution or runtime registration follows from this source range. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:61fffca873b94831 -->
<a id="review-61fffca873b94831"></a>

Reference source: anchor-lang 0.29.0. After the selected Owner and is_closed short circuits, clone the current AccountInfo, borrow its data and serialize through BpfWriter. Preserve partial writes and the old the source-ordered cleanup of the local clone on every continuing exit. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:760459d42a762e26 -->
<a id="review-760459d42a762e26"></a>

Reference source: anchor-lang 0.29.0. Move the current decoded payload out of Account and destroy only the remaining wrapper fields. Preserve payload identity and the borrowed AccountInfo representation; no payload clone or deserialization is reached. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:6513e1292d4749de -->
<a id="review-6513e1292d4749de"></a>

Reference source: anchor-lang 0.29.0. Delegate conditional exit using the saved owner, then retain the same cloned-AccountInfo serialization and cleanup protocol. Preserve the actual mutable guard, partial writer effects and saved owner rather than recomputing it. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:165707ba03dcf457 -->
<a id="review-165707ba03dcf457"></a>

Reference source: anchor-lang 0.29.0. Call the selected Id operation before comparing the current key, then check executable and return the same borrowed AccountInfo. Preserve branch-specific error construction and callback effects; equal metadata does not identify distinct records. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:5dff31ab337c7676 -->
<a id="review-5dff31ab337c7676"></a>

Reference source: anchor-lang 0.29.0. Check the current is_signer flag and either construct AccountNotSigner or retain the same borrowed AccountInfo. Add no owner, executable, key or allocation-success premise. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:efae333b3a9bccd7 -->
<a id="review-efae333b3a9bccd7"></a>

Reference source: anchor-lang 0.29.0. Use the 0.29 ErrorCode name, numeric offset and message table to construct the boxed Anchor error with no origin or compared values. Preserve actual String/Box effects; later diagnostic tables are distinct complete families. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:5eea7a103d735d3b -->
<a id="review-5eea7a103d735d3b"></a>

Reference source: anchor-lang 0.29.0. Follow the selected Anchor/Program branch and origin/compared-value logging order. Retain the old ProgramError payloads, Borsh String formatting/clone/drop and temporary cleanup. Logger effects and terminal outcomes remain explicit; later error tables are separate. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:130ccf71ae3a48da -->
<a id="review-130ccf71ae3a48da"></a>

Reference source: anchor-lang 0.29.0. Use the complete 0.29 ErrorCode variant-to-name table generated by the matching error macro. Construct the actual name String with its allocation and cleanup effects; no later table or infallible formatter is substituted. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:b523aecef88af4e2 -->
<a id="review-b523aecef88af4e2"></a>

Source-order lamports reads and writes, version-selected overflow and borrow errors, owner assignment, zero resize, aliasing and moved-value cleanup. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:8652310266f96906 -->
<a id="review-8652310266f96906"></a>

Owner-selected conditional serialization, is_closed short circuit, exact mutable guard and old local clone cleanup, with actual partial writes on failure. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:782259ccb54d76c0 -->
<a id="review-782259ccb54d76c0"></a>

Selected legacy or modern reload, exact owner-recheck and data-guard lifetime, current payload destruction and replacement on return or unwind. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:f76b195c08a5a3a0 -->
<a id="review-f76b195c08a5a3a0"></a>

Drop the old decoded field through its actual exclusive reference, then install the new owner on ordinary return and destructor unwind. The 0.27 receiver owns its AccountInfo field; preserve its record identity and source loan. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:9a81b5c2f2a29e21 -->
<a id="review-9a81b5c2f2a29e21"></a>

Source-ordered initialization, current-owner validation, selected checked or unchecked decoder and scoped AccountInfo clone/data-guard cleanup. Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:5b8724c9693e3dd0 -->
<a id="review-5b8724c9693e3dd0"></a>

Source-ordered initialization, current-owner validation, selected checked or unchecked decoder and scoped AccountInfo clone/data-guard cleanup. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:14b448c8848896ab -->
<a id="review-14b448c8848896ab"></a>

Exact simple-wrapper checks, reached Id/CheckId/Sysvar callback effects, release-specific error resources and successful AccountInfo retention. Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar. Preserve the reference non-repr(C) record, current Rc/RefCell identities and the reached borrow/drop effects; physical layouts remain separately bound. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:eb522ed8520a68a3 -->
<a id="review-eb522ed8520a68a3"></a>

Inner Accounts execution followed by actual Box allocation only on Ok, preserving inner slice/bumps/reallocations and every error or unwind. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:8ed202d9f558f6b4 -->
<a id="review-8ed202d9f558f6b4"></a>

Return the exact AccountInfo object in the owned receiver field, retaining its current cells, parent lifetime and repayment obligation. No AccountInfo or payload copy occurs. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:1c5eec70574769f0 -->
<a id="review-1c5eec70574769f0"></a>

Exact simple-wrapper checks, reached Id/CheckId/Sysvar callback effects, release-specific error resources and successful AccountInfo retention. Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:b6e3de611829fd3d -->
<a id="review-b6e3de611829fd3d"></a>

Return the same shared decoded-field reference with its parent loan and current payload location. Do not copy the payload or deserialize it. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:20cc2a7632780962 -->
<a id="review-20cc2a7632780962"></a>

Move the supplied owned AccountInfo into UncheckedAccount without checks or an Rc clone. Preserve its actual cells, owned-field layout and cleanup. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:bcc3700ba2337069 -->
<a id="review-bcc3700ba2337069"></a>

Anchor 0.27 wraps the moved AnchorError inline, preserving its String identities with no Box allocation. It does not collapse the payload to code/name observations. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:746e3d718aa5ee58 -->
<a id="review-746e3d718aa5ee58"></a>

The 0.27 reference has exactly 56 ErrorCode variants with their full numeric codes, names and messages. Convert the name, format the message and wrap the owned payload inline, preserving reached cleanup. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:a6339201be937f0b -->
<a id="review-a6339201be937f0b"></a>

Anchor 0.27 wraps the full Solana 1.15.2 ProgramError inline with empty origin/compared fields. BorshIoError retains its owned String, and source enum availability excludes later builtin variants. Numeric status is never used as the owned error representation. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:3ea5506266509e39 -->
<a id="review-3ea5506266509e39"></a>

The source matches actual Error/origin/comparison variants and performs the exact formatting/logging sequence. Old ProgramError clones its Borsh String before numeric conversion consumes that clone. The original error is only borrowed. Each temporary format String is dropped after normal logging or host logger unwind; a Solana syscall-only non-unwinding logger is a separate allowed index. Full Debug and Display arguments, including old wording, are retained. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:7b8331ae59ea933a -->
<a id="review-7b8331ae59ea933a"></a>

The generic ToString callback returns an owned new account name, then assignment drops the old origin account-name String and preserves all other fields. The source local argument is destroyed on normal/unwind exits. The moved result is the updated inline value in 0.27 and same Box owner later; callback unwind/terminal effects are preserved. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:417643673bffba6a -->
<a id="review-417643673bffba6a"></a>

Assignment drops only old owned comparison strings, writes both copied Pubkeys in order and returns the same inline payload or Box identity. Origin and underlying old/new ProgramError are preserved. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:14fc7e4e7b8a26b1 -->
<a id="review-14fc7e4e7b8a26b1"></a>

The borrowed static filename/line replaces origin; an old owned account-name String is dropped before the inline payload is updated. No new String or Box is allocated. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:ab4c30ac93c4032e -->
<a id="review-ab4c30ac93c4032e"></a>

Convert left then right with the actual user ToString callbacks, protect the first String during second-conversion unwind, then drop replaced comparison Strings and store the new pair. Source local destructors run in order. Later cleanup unwind retains the actual updated receiver/drop behavior, including the pinned edition-2021 moved-return-place alternative; terminal paths stop without invented cleanup. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:755953036fd721f0 -->
<a id="review-755953036fd721f0"></a>

The 0.27 reference has exactly 56 ErrorCode variants with their full numeric codes, names and messages. Return the exact generated owned name for each variant. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:1ff3ad11429a43ca -->
<a id="review-1ff3ad11429a43ca"></a>

The Borsh 0.9.3 derive reads one tag then the selected fields in declaration order. Scalar short reads preserve the failed field cursor; earlier consumed fields remain consumed. Write owns its decoded Vec, including an empty Vec for length zero; invalid tags and short input allocate exact InvalidInput diagnostics. This predecessor decoder is not the newer reader method. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:d0317d32fb28e53d -->
<a id="review-d0317d32fb28e53d"></a>

Construct fixed system ID, exact metadata order/flags and little-endian bincode data before moving accounts; remaining accounts are not forwarded. Edition-2021 cleanup drops instruction metadata/data, tail-expression account array, then remaining accounts and the owned context program AccountInfo. ProgramError converts inline. Review covers full context/error dependencies, not equal wrapper text alone. Projected-wrapper tests retain exact source and real context/constructors, replacing only the whole invocation signature. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->
