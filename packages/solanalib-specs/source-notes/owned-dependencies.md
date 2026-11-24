# Owned dependency and cleanup models

`Solanalib.Specs.Core.Owned` supplies the common mathematical vocabulary used by
instruction builders, token helpers and account wrappers when they call an
owned-value dependency. It does not implement `Vec`, an allocator, a destructor,
or a Rust capability model. The caller supplies each dependency relation and
sequences its actual finite return, unwind or terminal outcome.

`VectorOps` keeps a stable logical vector identity distinct from both its
machine address and its contents. `current state identity` reads the supplied
current state. The optional `Laws` express primitive partial correctness:
fresh construction, exact ordered values on a normal update, a live token after
an unwinding update, and retirement after a normally returning or unwinding drop.
They permit contents to change before an unwind. They do not imply progress,
determinism, exclusivity, separation, framing of another resource, validity of a
source pointer, or absence of identity reuse after retirement. These obligations
belong to a concrete dependency interpretation. A token alone grants no access.

`OwnedCleanup` runs retained destructors in their supplied source order. Every
next operation receives the actual state of the preceding operation. A first unwind
replaces a pending ordinary return. A second unwind can only use the explicitly
supplied terminal policy, with the actual state and both reasons. A terminal
outcome performs no later cleanup. `scope` cleans ordinary errors as well as
other ordinary returns. `protect` cleans only unwinds; its ordinary returns,
including `Result::Err`, move through unchanged. Callers that must clean an
ordinary error branch use `scope` or describe that branch explicitly.

The drop provider receives the current state and retained identity. Neither
`dropAction` nor the primitive laws derive element-by-element destructor
behavior, nested ownership transfer, or cleanup of inputs consumed by a failing
push. A vector containing guards or other owned values needs those additional
provider guarantees. Likewise, the exact `extend_current` law applies to a
dependency that preserves the supplied logical elements; it does not describe
an arbitrary effectful `Clone` callback without a separate interpretation.

`OwnedVector` gives a finite reference interpretation whose ledger never reuses
a slot. A new vector appends its values, a live update changes that same slot,
and a drop leaves a tombstone. Missing and dead identities admit no reference
operation. The proof `vectorReference_laws` discharges every primitive law for
this interpretation. It is a mathematical consistency witness, not a claim that
Rust allocation always succeeds or that the ledger is a concrete Rust layout.

`OwnedFocus` places such a dependency inside a larger mathematical state through
a lawful projection. It retains the exact inner return or unwind state and
preserves the surrounding state as specified by `set`. `OwnedFocusFacts` proves
exit inversion and preservation of every vector law. A focus is not a source
memory lens, alias proof or target-address correspondence.

`OwnedArray` records indexed expression calls, construction work and ordered
cleanup. A surviving unwind reports the completed prefix and failure site, so
an enclosing source scope can identify arguments not yet moved into a literal.
Its `CurrentLaw` relates completion to the actual current vector contents;
`construction_reference` derives the returned prefix, count and order.
The `initialInfos_success_current` of the Token helper applies this law to its
actual indexed AccountInfo clone calls and proves the exact four-account
result in source order, including duplicate identities.
These results leave the allocation schedule and the concrete ownership and
callback-frame bindings to the supplied dependencies.

The closed controls in `SolanalibTest.Specs.Core.Owned` include fresh construction
with preexisting resources, preservation of a separate slot, stale drop
rejection, an actual partial extension followed by a contents-sensitive cleanup,
order-dependent destructors, first and second unwinds, terminal short-circuiting,
ordinary errors, and a focused partial unwind. A separate failure-injection
provider satisfies the complete vector laws while changing its contents before
unwinding. This checks that those unwind obligations are usable beyond the
normal-only ledger reference.

The [package validation commands](../README.md#build-and-audit) build these
modules and audit every declaration. Source body correctness and the concrete
allocator, destructor, capability and representation bindings remain separate work.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:7802fce456a7d79d -->
<a id="review-7802fce456a7d79d"></a>

One finite Outcome relation covers returned Result values, unwinding with the actual state and terminal reasons without a fabricated state. Holds is universal partial correctness; HasExecution excludes an empty reference relation at a permitted input. RealizedBy is proved equivalent to Holds for a total returning reference. The indexed Family quantifies source types and providers, while a named sample supplies closed satisfiability and actual-execution witnesses. Tests distinguish an empty relation, uninhabited source type and real terminal execution. The common definitions live in Solanalib.Contracts.Model. The Core modules use and publicly import that contract vocabulary.
<!-- /registry -->

<!-- registry:review:07fd65078cb915e2 -->
<a id="review-07fd65078cb915e2"></a>

Explicit typed vector dependency operations observe actual current state through stable logical resource identities; primitive laws are separate from SDK postconditions and source ownership.
<!-- /registry -->

<!-- registry:review:dd55bb6df243bbae -->
<a id="review-dd55bb6df243bbae"></a>

Source-ordered cleanup threads actual callback states, preserves ordinary values, admits first-unwind cleanup and only the supplied terminal policy for double unwind; terminal exits stop cleanup.
<!-- /registry -->

<!-- registry:review:fec411198fb144de -->
<a id="review-fec411198fb144de"></a>

Lawful mathematical state focus lifts only supplied callback outcomes and their actual return/unwind states; it has no source layout or aliasing claim.
<!-- /registry -->

<!-- registry:review:54acac1468b29c10 -->
<a id="review-54acac1468b29c10"></a>

Return/unwind/terminal inversion and all vector dependency laws are proved for focused interpretations.
<!-- /registry -->

<!-- registry:review:f58d5814097e9336 -->
<a id="review-f58d5814097e9336"></a>

A finite logical ledger proves fresh construction, exact ordered current contents, stable update identities and retirement. This is a reference interpretation, not a Rust allocator implementation.
<!-- /registry -->

<!-- registry:review:1ad40f4e9cfe0bb9 -->
<a id="review-1ad40f4e9cfe0bb9"></a>

Generic finite-outcome combinators over supplied mathematical relations. Mapping changes only an ordinary return value; sequencing invokes its continuation in the actual returned state and forwards unwind and terminal exits. Except values remain ordinary callback results; each consumer supplies its own error sequencing. This module is mathematical infrastructure and has no specific Rust implementation correspondence. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.
<!-- /registry -->

<!-- registry:review:4aae0103348b7a9d -->
<a id="review-4aae0103348b7a9d"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles distinguish explicit reviewed references from declared registry compatibility ranges within one Cargo compatibility line, retaining source origins and behavior-changing build constraints. Numeric membership ignores build metadata and excludes prereleases unless explicitly reviewed; git revisions remain exact. Ranges assume preservation of the reference operation contract, including relevant dependency effects and implementation-specific results. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.
<!-- /registry -->

<!-- registry:review:2132ca4baf8a7dca -->
<a id="review-2132ca4baf8a7dca"></a>

The account observations of the primary pool model, borrow policy, current-data effects and callback cleanup order use the common Borrow registry. Its scalar observations and owner comparison require HasAccount and return values from an actual lookup cell; descriptor construction and raw acquisition require True. Successful replacement needs a present cell, close needs it only on the unborrowed branch, and release needs a live guard slot. Mapping requires the live slot, its cell, the selected mode and universal CallbackSafe, which supplies protocol admission and exit-specific validity. Projection helpers use cell presence and AccountView policy for shared acquisition, and cell presence for mutable acquisition; they establish the single-account observation postconditions without deriving the separate single-account validity preconditions. Byte-length and read-after-write helpers use data/backing containment and the selected range; header-preservation helpers use the bounds of preserved fields. Successful acquisition supplies cell presence. The single-account domains and their invariant-preservation results are specified separately. Source widths, physical references and the callback input reference remain separate bindings. closeHeader preserves resize bookkeeping while clearing the logical header.
<!-- /registry -->

<!-- registry:review:bbe607da5ac2a669 -->
<a id="review-bbe607da5ac2a669"></a>

Shared address/instruction values retain metadata address references and ordered nested requests. The generic invocation carrier supplies an explicit opaque provider interface; checked library wrappers are reviewed separately. PDA syscall families require every actual status-zero reply to initialize its address. Local decoding preserves every admitted provider exit; the find wrapper additionally follows the actual panic provider after a nonzero reply. No provider termination is assumed. The vocabulary is reviewed against Address 2.6.0, InstructionView 2.1.0 and the selected Pinocchio sources.
<!-- /registry -->

<!-- registry:review:6e4b6aca41513edd -->
<a id="review-6e4b6aca41513edd"></a>

InstructionView 2.1.0 checks the complete account count before callbacks, then checks each positional address and writable borrow before initialization. Every actual AsRef call uses the preceding returned state, and the final call selects the retained account identity and current length/raw header bytes. Nonzero flag values and padding are copied exactly. Duplicates, initialized-prefix order and nested seeds are retained; unused trailing accounts are not visited. StaticAccounts records the exact equality between its structural size and values length. The Rust const instantiation separately establishes ACCOUNTS <= 64. The exact array family has closed reference, satisfiability and nonempty execution witnesses.
<!-- /registry -->

<!-- registry:review:48e21407adf8bf90 -->
<a id="review-48e21407adf8bf90"></a>

The model for the Solana source branch submits curve ID 0, exactly 32 point bytes and an output byte initialized to 0. It returns the Boolean test status = 0, independently of the output scratch byte. The callback mapper retains each returned/unwound state and terminal reason. primitiveReply_status relates the status to the existing canonical Edwards primitive predicate; no host decompression path is substituted.
<!-- /registry -->

<!-- registry:review:ba66d22b895f89ef -->
<a id="review-ba66d22b895f89ef"></a>

The models retain both AsRef passes, source error order, partial buffer writes and final-only counters. InvocationReady requires exactly three bounded, fully initialized committed prefixes. request_domain proves this is precisely request the domain of the construction; initializedPrefix_exact and request_exact preserve the order of every slot and committed length. Admitted requests retain every actual finite provider exit, without a termination assumption. Rust private-state invariants, source widths, retained-reference validity and buffer separation remain separate bindings, as described in source-notes/token-batch.md.
<!-- /registry -->

<!-- registry:review:cae6fbc653b75319 -->
<a id="review-cae6fbc653b75319"></a>

The allocation-free CloseAccount and TransferChecked wrappers construct exact fixed arrays and data from current pool keys, retaining the supplied program, repeated handles, flags and nested signer order. Unsigned transfer supplies empty signers. Their cardinality proofs discharge the checked v2 array bound; source-local writable borrow checks run before the unit-returning unchecked invocation. Only normal unit completion becomes Ok(()), while actual unwind and terminal effects survive. HeaderTypes carries mandatory exact raw header bytes, not a canonical-byte restriction.
<!-- /registry -->

<!-- registry:review:207bfec44f28598e -->
<a id="review-207bfec44f28598e"></a>

Shared value variants and integer conversions for solana-program-error 3.0.1, including payload-free BorshIoError, custom-zero encoding, builtin upper-word tags and truncating fallback to Custom. Callers supply their own interpretation of syscall success and error admission.
<!-- /registry -->

<!-- registry:review:ae13fe7197748fbd -->
<a id="review-ae13fe7197748fbd"></a>

Supporting correspondence is to the existing canonical mathematical Lease: acquire_accountView_observation and accountView_addShared prove exact 254-policy shared acquisition; release_observation proves canonical release for either mode under valid and live premises. The mapping relation forwards every actual finite callback exit, including an inadmissible one; MapCallback.Admissible is a universal precondition of the validity and token-history preservation theorems. Other checked results establish structural validity, token retirement and current contents under their stated premises.
<!-- /registry -->

<!-- registry:review:ca5cdb03d4ef3c11 -->
<a id="review-ca5cdb03d4ef3c11"></a>

The selected byte serializer forwards one Write::write_all callback with the complete byte slice. Ordinary results and partial-write, unwind and terminal effects are exactly those of that callback.
<!-- /registry -->

<!-- registry:review:d6059dbfe2d32ac4 -->
<a id="review-d6059dbfe2d32ac4"></a>

The constructor requires a present cell and, only after matching-key successful acquisition, a contained captured slice with signed-length bounds; it retains address-before-borrow order without serialization validation. Ref-backed access contracts require the actual live shared guard and the ranges/alignment reached by each operation. Their posts now include checked decoding of the current captured bytes, excluding stale or truncated fallbacks. Only native table loads require alignment two; lookup may form a one-past pointer without validating an instruction body. Physical base placement, provenance, lifetime and read permission remain source bindings.
<!-- /registry -->

<!-- registry:review:cea4ab5cafb15798 -->
<a id="review-cea4ab5cafb15798"></a>

Admission quantifies over every actual returned Deref prefix and checks the slice, range, pointer addition and alignment needed by each reached operation. On normal completion, the unchanged raw relations use two callbacks for current-index and one or three for lookup; source-family posts additionally prove checked execution using the same current bytes and callback states. Out-of-range lookup requires no table read; early abnormal exits need no later read. Program/data observers prove actual scalar reads and complete returned regions. Signed-length and numeric address checks are explicit; physical allocation, provenance and permissions still require a Rust memory binding.
<!-- /registry -->

<!-- registry:review:a5deeeab83931dd0 -->
<a id="review-a5deeeab83931dd0"></a>

GetterReady requires every actual reply classified as success by the supplied converter to initialize its destination. The exact local forwarding condition, preservation of each finite provider exit and equivalence of provider/wrapper finite execution are proved. GetterValid is separate and supplies the value property used by get_success_valid; initialized invalid values are not filtered. Pinocchio 0.11.1 selects the generic syscall and MaybeUninit destination. Target selection, storage, representation and physical initialization correspondence remain source bindings.
<!-- /registry -->

<!-- registry:review:3a23beaba76344a2 -->
<a id="review-3a23beaba76344a2"></a>

Rent111ReadReady requires a current account and eight logical bytes only after the exclusive-lease and address checks. rent111FromAccount_read uses those conditions to produce a real-cell result with the exact earlier error or a complete eight-byte rate decode. The raw reader and its state preservation are unchanged. Physical storage, legal access and the little-endian target remain source-binding obligations; read_unaligned adds no alignment gate.
<!-- /registry -->

<!-- registry:review:e91b0898abbd0ccb -->
<a id="review-e91b0898abbd0ccb"></a>

Pinocchio 0.11.1 Rent has one u64 rate and no floating threshold. Its ordered length and rate guards precede the integer product; the accepted product is proved below the u64 limit. The encoded representation has exactly eight bytes.
<!-- /registry -->

<!-- registry:review:bfee0c153c5ae46b -->
<a id="review-bfee0c153c5ae46b"></a>

The shared token wire-value vocabulary retains the exact legacy and Token-2022 identities, instruction tags and little-endian amounts, ordered metadata and duplicate signer entries used by the selected Pinocchio wrappers and batch builder. Pure values and value contracts describe local preparation only; allocating constructor admission and lifecycle are reviewed at their consumers.
<!-- /registry -->

<!-- registry:review:a32b5e0b347d438c -->
<a id="review-a32b5e0b347d438c"></a>

Canonical token program IDs, exact byte widths and checked complete-range little-endian/key reads; AccountState conversion accepts exactly 0/1/2.
<!-- /registry -->

<!-- registry:review:0cce7c30ed79210e -->
<a id="review-0cce7c30ed79210e"></a>

Exact raw 82/165-byte records preserve malformed flags. Separate Pack decoders check complete COption tags, Boolean and enum fields in source order before initialization; PodMint uses nonzero initialization without Pack field validation. The Pinocchio2022 layout predicate preserves exact-base admission, the 355-byte exclusion and type marker at 165.
<!-- /registry -->

<!-- registry:review:e66c183efd3366da -->
<a id="review-e66c183efd3366da"></a>

The common Borrow.State Account Slice protocol computes owner/length/acquire/layout/drop/map order. Guard transfer consumes the old generation while preserving lease identity. Field descriptors retain the supplied guard and offset; current reads separately check their live view. Invalid state bytes invoke an explicit nonreturning panic provider. Unreadable guards have no raw state-getter exit and are excluded by the state family admission.
<!-- /registry -->

<!-- registry:review:0a0c246fac677b18 -->
<a id="review-0a0c246fac677b18"></a>

Contracts expose complete parser computation and guard effects, field-descriptor identities, and exact amount/decimal values under the current-readability premises they consume. The state family requires AccountReadable; stateFamily_continues supplies the actual decoded normal result or forwards every actual finite panic-provider exit with its effects. No panic-provider termination is assumed. All versioned reference and nonvacuity witnesses remain closed.
<!-- /registry -->

<!-- registry:review:217bf1f8eaa0f760 -->
<a id="review-217bf1f8eaa0f760"></a>

Derived facts establish preservation of the contents of every account, actual guard transfer/retirement, live-view field agreement and represented nonvacuity inputs; no account post-state is freely selected.
<!-- /registry -->

<!-- registry:review:b0a061492bde475d -->
<a id="review-b0a061492bde475d"></a>

The AccountInfo 3.1.1, Anchor 1.0.2 and Anchor SPL 1.0.2 functions compose identified borrows, current owner reads, explicit trait callbacks, owned resources and source-ordered cleanup. AccountInfo borrow/getter conditions support their actual typed-current and progress conclusions. Constructor admission covers only reached initialization reads, diagnostic Error resources and guarded decoder/discriminator continuations. Loading and amount admit earlier checked errors but require current data after successful acquisition; reached owned loading factories retain their held tokens. Their continuation results preserve actual finite exits without assuming dependency termination. Owned-error families retain their three boxing or four comparison capabilities; comparisons additionally require reached assignment availability, and with_values protects resources on continuing unwind/destructor paths through CallReady. Pure error observation facets retain their stated omissions. Context uses actual empty-provider current/fresh facts. Primary transfer requires current instruction vectors on each successful builder return; invocation remains opaque. Pinned edition-2021 cleanup destroys instruction metadata and bytes, the tail-expression account array, then the remaining vector. Conditional destructor non-unwind claims and concrete resource/reference/target interpretations remain explicit source bindings.
<!-- /registry -->

<!-- registry:review:8e7a02e6d145aae8 -->
<a id="review-8e7a02e6d145aae8"></a>

The published Pyth receiver 2.0.0 reference first checks verification dominance, then feed identity, then the maximum-age conversion that panics beyond i64 MAX. It performs signed saturating addition and an inclusive freshness comparison, and returns exactly the source Price fields. Both panic strategies and the framed state are explicit. The verification field is data, not a signature-validity assumption. The generated Borsh decoders read write_authority (Address 2.6.0 model), verification_level (u8 tag 0 with a u8 count, tag 1, other tags InvalidData "Unexpected variant tag: n" after the tag), price_message (pythnet-sdk 3.0.0 model) and posted_slot (u64) in declaration order; the Borsh 1.6.1 default deserialize forwards the outcome of that decoder.
<!-- /registry -->

<!-- registry:review:16b8ab7237839656 -->
<a id="review-16b8ab7237839656"></a>

The parser consumes an existing AccountInfo guard; its Rust argument interpretation supplies shared mode. It checks discriminator length, discriminator bytes, complete payload extent, sliced extent and actual payload alignment in source order. Both 8-byte and 16-byte i128 layout choices have size 3200. The selected bytemuck1.25.0 helper checks size before alignment; its repeated successful cast has no intervening mutation. Error releases exactly the input lease; success transfers its generation to the payload range without adding a lease or changing cells. General progress and cell-frame lemmas cover every admitted input. The contract additionally guarantees the final borrow-state invariant and retirement of the input guard generation, using the Ready premise in its reference proof.
<!-- /registry -->

<!-- registry:review:d5de003a6b2c3ead -->
<a id="review-d5de003a6b2c3ead"></a>

This common mathematical helper sequences an indexed evaluator with stateful work, completion, element destruction and storage retirement dependencies. Its finite trace checks expression bounds, exact completion count and cleanup-position permutations while preserving actual intermediate states and distinct equal-value occurrences. The construction Family requires True and uses CurrentLaw to expose current ordered contents on return. Bounded failure progress follows from the actual trace and is used by the literal cleanup of the SDK. The SDK also derives its exact initial four-account vector from this current-content law and the actual clone results. Closed reference and abnormal-exit controls establish mathematical consistency.
<!-- /registry -->

<!-- registry:review:14d16b02bd55ffaf -->
<a id="review-14d16b02bd55ffaf"></a>

The unchecked wrapper invokes the supplied deserializer once and discards only its returned remaining-slice value. It preserves the exact ordinary result and callback effects, including error, unwind and termination. No trailing-byte rejection, suffix law or rollback is added.
<!-- /registry -->

<!-- registry:review:08172d047fa30fc6 -->
<a id="review-08172d047fa30fc6"></a>

Define binary64 decoding, nearest-even dyadic rounding, separate integer conversion and multiplication, gradual underflow, nonfinite cases and saturating u64 conversion with integer arithmetic. NaN payloads are scoped to the final integer observation.
<!-- /registry -->

<!-- registry:review:0e1dbaff05908623 -->
<a id="review-0e1dbaff05908623"></a>

Select the actual cfg branch and retain exact UTF-8 or ordered nested fields in the callback event. The canonical flattening is a separate coarse observation and excludes host formatting.
<!-- /registry -->

<!-- registry:review:41d7b694b81c9d9e -->
<a id="review-41d7b694b81c9d9e"></a>

Solana Rent 3.0.0 retains the rate, floating-threshold bits and burn field. Its minimum-balance calculation performs integer addition and multiplication, rounded u64-to-binary64 conversion, rounded multiplication and the saturating u64 cast in source order. Integer overflow and panic exits are selected explicitly by the source build profile.
<!-- /registry -->

<!-- registry:review:d822720f764feee2 -->
<a id="review-d822720f764feee2"></a>

The typed Clock and Rent getters begin with their source Default values, call the selected typed syscall and map every nonzero returned status to UnsupportedSysvar. Their shared getter relation keeps callback state and exceptional exits; source memory validity remains an interpretation obligation. GetterReady requires initialization on each actual reply classified as success, so every finite provider exit has its unchanged forwarding continuation. Value validity uses the separate GetterValid law, and target selection remains a source binding.
<!-- /registry -->

<!-- registry:review:0ee7a6916d560ada -->
<a id="review-0ee7a6916d560ada"></a>

Explicit higher-order collection dependency and the actual source key-before-checked-borrow closure; iterator elements are read from the current state.
<!-- /registry -->

<!-- registry:review:ba99fca9a389bca3 -->
<a id="review-ba99fca9a389bca3"></a>

Successful current vector length and complete callback traversal follow from actual traces and the primitive finish-current law; errors and unwinds cannot turn into success through cleanup.
<!-- /registry -->

<!-- registry:review:4450dc166163ceb5 -->
<a id="review-4450dc166163ceb5"></a>

An explicit optional account-state frame preserves current reference reads across collector internal effects and finish; the concrete reference discharges this frame.
<!-- /registry -->

<!-- registry:review:0a45275cec1f7985 -->
<a id="review-0a45275cec1f7985"></a>

Finite callback protocol with exact index order and acquired identities, explicit internal outcomes and early stopping; partial cleanup checks the supplied actual-state order is a permutation of exactly the acquired elements before guard release and the storage callback.
<!-- /registry -->

<!-- registry:review:ae2358a58ae78ad2 -->
<a id="review-ae2358a58ae78ad2"></a>

A closed consistent collection provider transfers a fresh logical ledger vector and couples its drop to actual DataRef releases followed by storage retirement.
<!-- /registry -->

<!-- registry:review:42a32a7208cb9daf -->
<a id="review-42a32a7208cb9daf"></a>

Length and multisig rejection precede the actual base parser. Packed Mint and Account use the shared complete codecs; sizing uses the distinct nonzero-init PodMint admission. The supporting byte observation preserves parser exits, base-before-tail error ordering, padding, marker checks and deferred TLV validation. Its immutable-input/trivial-destructor scope is explicit; generic ownership and live reference behavior are in TokenExtensionUnpack.
<!-- /registry -->

<!-- registry:review:c69374e5dd0da3cd -->
<a id="review-c69374e5dd0da3cd"></a>

Production tags 0 through 28, account associations, fixed layouts, u16 TLV lengths and isize-bounded cursor geometry follow the pinned enum, dispatch and alignment-one fields. Raw lookup uses first match before sentinel and can skip unknown tags; iteration decodes every visited tag, accepts a one-byte tail and preserves duplicates. The slice-bound model requires a 64-bit target interpretation.
<!-- /registry -->

<!-- registry:review:641163d83f9c33a2 -->
<a id="review-641163d83f9c33a2"></a>

The transfer and checked-transfer value constructors retain their exact program-id admission before allocation. Their plans retain source packing capacity, ordered byte operations and literal or reserved metadata construction. The shared allocated engine returns actual resource identities, destroys a later partial owner before an earlier owner on unwind and destroys a successful Instruction as metadata then bytes. Terminal exits bypass remaining cleanup, and double unwind keeps the actual second-drop state. The finite-ledger reference proves inhabited constructors, exact observations and ownership without claiming allocator implementation correctness.
<!-- /registry -->

<!-- registry:review:1688ffe011de50d3 -->
<a id="review-1688ffe011de50d3"></a>

The primary Family composes owned instruction construction, the ordered clone/move literal trace, current-owner multisig checks, mint/validation/collected data guards, interface-3.0 padding, TLV and seed helpers, and final opaque CPI. Its one selected collection protocol joins primitive guard/data admission, current-resource retention and the five reached source borrow domains. family_mint_primitive_retain derives actual read/release continuation from that family input; checked errors and early rejection do not require success-only invariants. Literal work/count and finite-prefix cleanup-order admission prevent local protocol checks from discarding actual downstream exits. Both actual PDA sites require bounded successful replies to initialize output. The full non-hook witness allocates, clones, acquires/releases mint data, invokes and cleans temporary owners. Exact current-array and collection-length results retain their used CurrentLaw and finish-current premises. No callback termination, inverse to one-way Conforms, complete hook-call derivation or Rust implementation correctness is inferred.
<!-- /registry -->

<!-- registry:review:80aedff26aac752d -->
<a id="review-80aedff26aac752d"></a>

These supporting value models retain exact ordinary parser/error, multisig, hook, metadata and instruction observations. Their pure address search and omission of vector/Rc effects are explicit limitations; they do not represent the primary selected-Solana operational wrapper. The sole versioned value Family is registered as an observation alongside the new outcome-carrying primary Family. PreparationReady now supplies branch-sensitive selected-read and local-release admission. prepare_not_malformed and run_retains preserve the finite local/provider exits; run_hasOutcome_iff keeps opaque provider termination separate.
<!-- /registry -->

<!-- registry:review:33b566f21ea8ca75 -->
<a id="review-33b566f21ea8ca75"></a>

The source-ordered resolver retains literal owners, seed owners and live borrowed views, resolves an external PDA program before unpacking, reads retained bytes at the actual stateful PDA call, cleans reference storage before copying flags and drops seed/literal owners afterward. Primitive failures and double-unwind cleanup preserve actual states; terminal exits skip destructors. The current account observer is the selected ordinary closure, not an arbitrary effectful Fn implementation. The registry identifies the four reviewed source files. The registered modules contain primary syscall witnesses and live-view and failure controls; all their declarations are included in the axiom audit. pureFind is supporting only.
<!-- /registry -->

<!-- registry:review:78a10322f290895e -->
<a id="review-78a10322f290895e"></a>

Operational dependencies preserve the source discriminator-push/length-read order of spl-type-length-value 0.9.1 and the repeated-zero temporary allocation/comparison/drop/marker order of token-interface 3.0.0 Mint parsing. Actual returned resource identities and states flow through source-ordered cleanup on ordinary errors and unwind; terminal exits skip cleanup. Full TLV validation is completed before a caller continues to selected lookup.
<!-- /registry -->

<!-- registry:review:5bce79dc068a1249 -->
<a id="review-5bce79dc068a1249"></a>

The 1.0.0 source-facing root instantiates the shared mathematical contracts with its shared receivers, signed close/resize behavior and required reference access modes. All contracts have closed reference and satisfiability witnesses; generic families also have a named finite sample execution. The nonfallible map Family, reference and closed samples are registered here with their first SDK consumer; they retain the shared callback-admission and guard-transfer semantics.
<!-- /registry -->

<!-- registry:review:114507fe85362fc2 -->
<a id="review-114507fe85362fc2"></a>

The 1.0.0 extension supplies Revision, resize accounting, version-specific close, their contracts and lifecycle facts. Close composes the shared header update with the v1 resize-delta calculation; explicit equations recover both revision updates, and the v2 branch equals closeHeader. The branch contracts require only account presence for successful cell updates and retain the source check order. Separate pool preservation uses Ready, signed-domain preservation uses account presence and ResizeValid, and owner invalidation uses the validity of that reference. Data and arithmetic helpers take their specific containment or integer conditions. The consumed resize_data_fits lemma permits backing extension; fixed original backing length alone needs the capacity bound. Requested-length width and physical runtime storage remain source bindings, with signed conversion still an actual operation check.
<!-- /registry -->

<!-- registry:review:417fa9e60d989889 -->
<a id="review-417fa9e60d989889"></a>

A field reference contains only the original parent identity and a fixed field selector. Current value lookup follows that parent at the actual read state. Reads separately requires current admission of the existing borrow, so stale represented contents cannot license an expired or inaccessible read. The vocabulary has no allocation, acquisition, release or guard-consumption operation.
<!-- /registry -->

<!-- registry:review:3004eeecfa9bd738 -->
<a id="review-3004eeecfa9bd738"></a>

InstructionView 1.0.0 rejects more than 128 instruction accounts before allocating its temporary box; allocation precedes the supplied-account count check. Positional address validation precedes writable/shared versus readonly/exclusive borrow checks. Descriptor flags use the source Boolean getters and no source padding byte is read. Only the initialized instruction-account prefix reaches the unchecked unit-returning invocation. Actual box destruction runs after surviving returns and unwinds, using the reached state and explicit double-unwind policy; terminal exits skip cleanup. Signed and unsigned families retain exact closed reference, satisfiability and nonempty execution witnesses.
<!-- /registry -->

<!-- registry:review:61466b9fb65beb06 -->
<a id="review-61466b9fb65beb06"></a>

Instruction construction above explicit allocation, serialization, unwrap-failure and cleanup dependencies. Success transfers the exact account and byte resources; observations read their contents from the current provider state. Concrete mathematical samples establish successful nonvacuity, while resource and dependency correspondence remain binding obligations. Constructor families have precondition True. Current-vector, serializer and frame laws remain explicit premises of stronger value observations, rather than unused entry-liveness restrictions.
<!-- /registry -->

<!-- registry:review:662ed1e92cae6dcf -->
<a id="review-662ed1e92cae6dcf"></a>

COption::is_some matches only the enum variant. A closed Family quantifies every payload type, including uninhabited types, without payload movement, cloning or an inhabitance premise. The model makes no C-layout claim.
<!-- /registry -->

<!-- registry:review:b5729012462188fa -->
<a id="review-b5729012462188fa"></a>

The eight-byte U64 macro instantiation converts with u64::from_le_bytes. The model uses an exact-length byte input, the canonical little-endian decoder and UInt64 bounds. Its general bound and encode/decode round-trip proofs establish mathematical value correspondence, without assuming native u64 alignment.
<!-- /registry -->

<!-- registry:review:dfd546f11357aa1d -->
<a id="review-dfd546f11357aa1d"></a>

Represent the exact 32-byte array separately from account addresses; copying preserves every byte, with inverse and injectivity laws.
<!-- /registry -->

<!-- registry:review:f46660d940e041e7 -->
<a id="review-f46660d940e041e7"></a>

Forward the ordered slice collection and uninitialized destination. EveryReturnInitialized is the family condition that retains every normal provider return, including nonzero status, with its actual written bytes. Abnormal exits and state are preserved. The outer-count bound belongs only to the separate request_count result; canonical hash agreement and Rust slice/destination representation remain independent obligations.
<!-- /registry -->

<!-- registry:review:074718a5eea2c27f -->
<a id="review-074718a5eea2c27f"></a>

Select target_os=solana or the distinct host override and forward the complete bytes with the u64 length cast of the Solana branch. The raw family has precondition True and preserves all provider outcomes. length_exact separately proves cast exactness under its bound; canonical runtime size and program-tag behavior remain separately interpreted.
<!-- /registry -->

<!-- registry:review:b0f1d892a2c0498e -->
<a id="review-b0f1d892a2c0498e"></a>

The pure SystemInterface 3.2.0 create-account value constructor retains tag zero, little-endian lamports/space, owner bytes and the two ordered writable signer metas. The unchanged declaration is placed with its sole versioned consumer; allocation and serialization dependencies remain in the contract of that consumer.
<!-- /registry -->

<!-- registry:review:843b1d57f5e47b0e -->
<a id="review-843b1d57f5e47b0e"></a>

Pinocchio 0.10.2 retains a two-field Rent value and a 16-byte generic getter request. Minimum balance preserves the ordered length/rate checks, the one/two threshold branches and the BPF floating-branch panic. The second rate guard remains unreachable as in the source. Wrapping or checked integer arithmetic and unwind or abort are explicit source-profile choices.
<!-- /registry -->

<!-- registry:review:0b8807962123fe46 -->
<a id="review-0b8807962123fe46"></a>

TransferFee is 18 bytes at offsets 0/8/16 and TransferFeeConfig is 108 bytes with authorities 0/32, withheld amount 64, older fee 72 and newer fee 90. The typed getter retains selected bytes and uses the same Pod checks. Full unsigned rates, including values above 10000, are decoded without adding validity checks. Nonzero TLV controls join retrieval, epoch choice and arithmetic.
<!-- /registry -->

<!-- registry:review:3001f1d5ec56f3f8 -->
<a id="review-3001f1d5ec56f3f8"></a>

The default trait body calls the resolved get_extension_bytes implementation, including overrides. Its actual error, state, unwind or terminal outcome is retained. Success casts the bytes at the returned reference in the actual returned state, checks size before alignment, and preserves reference identity. The concrete default provider is proved to recover the supporting first-match observation after forgetting only its address wrapper.
<!-- /registry -->

<!-- registry:review:8c9e392a954632f6 -->
<a id="review-8c9e392a954632f6"></a>

Resolved get_tlv_data precedes empty-vector construction. Each validated entry produces one actual push before the next source read. Success transfers the same owner; parse Err drops it; push unwind cleans the actual changed vector state; terminal exits skip cleanup; a second unwind uses both actual reasons and state. Stable reference/length metadata and current-state reads avoid a hidden input snapshot. An explicit normal-push read-frame law and the direct push_current capability recover exact ordered contents from a successful live collection without unrelated vector laws. A concrete fresh/tombstone ledger supplies the nonempty execution witness.
<!-- /registry -->

<!-- registry:review:1a981692f2a146d5 -->
<a id="review-1a981692f2a146d5"></a>

BaseState + Pack does not require Copy or rule out Drop. After the exact prefix parser returns an owned base, tail validation reads the current state through the same input identity. A later layout Err sequences the actual base destructor and propagates its changed state/unwind/terminal; success moves the same base and preserves the original bounded tail range. The static empty literal differs from a borrowed empty tail. Generic theorems prove success provenance, impossibility of success from cleanup, range geometry and exact recovery of the earlier byte observation for explicit pure-codec/trivial-destructor interpretations.
<!-- /registry -->

<!-- registry:review:29a5bdd0dec945bb -->
<a id="review-29a5bdd0dec945bb"></a>

The one-entry scan preserves the termination of the TLV fold on empty input, a one-byte tail or the uninitialized sentinel. It rejects unknown tags and incomplete or out-of-bounds nonzero entries before invoking the callback. Its decomposition is proved equal to the pure fold, with exact consumed-prefix and remaining-tail geometry.
<!-- /registry -->

<!-- registry:review:8509e83632ce2ee1 -->
<a id="review-8509e83632ce2ee1"></a>

Requested account-kind checks precede PodMint parsing; base-layout failures map to InvalidMint and later TLV failures retain InvalidAccountData. Required and additional types share the deduplicating accumulator, fixed lengths, saturation and 355-to-357 adjustment. Source 3.1.1 uses a stack bitset/usize accumulator and static required-type slices, with no vector allocation. Discarded accumulator state on failure is not exposed as a mutable helper contract.
<!-- /registry -->

<!-- registry:review:4e2afbd02d2fe20e -->
<a id="review-4e2afbd02d2fe20e"></a>

Checked u128 ceiling arithmetic keeps the source operation order. Forward fees convert the raw result to u64 before capping; inverse fees compare the cap before conversion. All u16 rates, zero/10000/over-10000 cases, checked deduction, overflow and epoch equality branches are modeled. get_epoch_fee is an immutable copied-field observation; its source field reference is not modeled. The four frozen fee models and their original evidence bytes remain unchanged.
<!-- /registry -->

<!-- registry:review:fbfa63ac63ecc0c3 -->
<a id="review-fbfa63ac63ecc0c3"></a>

The pinned get_epoch_fee body reads the current newer activation epoch and compares the copied requested epoch. Equality selects newer; an earlier epoch selects older without inspecting the older activation epoch. The result retains the same parent and chosen field, and the ambient state is unchanged. Later admitted reads use the current contents of that fixed field without reselecting. Immediate dereference is proved to agree with the frozen copied-value getEpochFee observation. The closed indexed contract, universal reference proof, satisfiability sample and nonempty execution witness cover generic state and parent-identity interpretations.
<!-- /registry -->

<!-- registry:review:f64203a2a14979b0 -->
<a id="review-f64203a2a14979b0"></a>

The initialization, close and excess-lamport withdrawal extensions preserve per-entry program admission, owner-in-data encoding, metadata/signers and source allocation order. WithdrawExcessLamports builds its metadata literal and pushes signers before byte packing; a byte-pack unwind therefore drops bytes then metadata. The other selected plans pack first. The generic indexed family and closed finite-ledger samples use the shared allocated engine and explicitly instantiate its current-resource, ownership and cleanup laws. Value and operational families have precondition True. Their actual program checks remain; scalar widths, capacity arithmetic and enum layout are source bindings.
<!-- /registry -->

<!-- registry:review:4a8cdc641870bef3 -->
<a id="review-4a8cdc641870bef3"></a>

Version-independent borsh wire format at R = &[u8]: little-endian integers, binary64 bits with NaN rejection, bool and Option tags, [u8; N] in one read, the chunked reads of u8::vec_from_reader and buffer schedule, Vec<T> with hint::cautious (size truncated modulo 2^32, with the division panic before allocation at a zero divisor), the leftover check of try_from_slice, and the exact write_all chunk sequence of the selected serializers. io::Error is observed as (ErrorKind debug name, to_string()); exact source messages are fixed; the version Profile supplies the decoding error kind (InvalidInput in 0.10.4, InvalidData in 1.6.1) and the zero-sized message. Generic members are request programs over element, write_all and Vec calls with relational, executable and pure interpretations; graph lemmas connect them. The generic vector prefix selects either its request program or a division panic with the post-length slice. The unrestricted family retains panic effects and exits; pure/returning adapters require a proof that this branch is unreachable. the no-std Write::write_all in borsh is an inductive run relation over the write of the writer, the slice-index panic and the allocation of the message of the WriteZero error (WriteZero on Ok(0) once its message is allocated, retry on Interrupted, other errors unchanged), with an executable fuel form and its graph lemma; WriterIndex.ofWrite lets the serializers compose over it.
<!-- /registry -->

<!-- registry:review:d2b0e86cb1a9129c -->
<a id="review-d2b0e86cb1a9129c"></a>

Shared bytemuck vocabulary: Rust type layout (size, power-of-two alignment, size a multiple of alignment), slice and typed references with explicit pointer values, PodCastError with all four source variants, try_cast_slice with its exact branch order including the zero-sized target branch, bytes_of as the always-successful cast to u8 (alignment and slop branches proved dead, so unreachable!() is never reached), try_from_bytes checking exact length before the alignment of the slice address and returning a reference at the same address with the decoded value, and default Zeroable::zeroed as the value of size_of::<T>() zero bytes. internal.rs and zeroable.rs are byte-identical in 1.25.0 and 1.25.2.
<!-- /registry -->

<!-- registry:review:6eb11d976b802aa4 -->
<a id="review-6eb11d976b802aa4"></a>

Version-independent stake account values with every stored field and bit, including reserved flag bits, the deprecated rent reserve and the raw binary64 rate bits, and their fixed little-endian wire layout in source field order. Width lemmas give 120, 64, 48, 72, 64, 1 and 197 bytes for Meta, Authorized, Lockup, Stake, Delegation, StakeFlags and the Stake variant. Portable excludes exactly the NaN rate bit patterns.
<!-- /registry -->

<!-- registry:review:c08abffc3699b415 -->
<a id="review-c08abffc3699b415"></a>

A raw syscall call asks a syscall environment (Index.provider over Solanalib.Runtime.SysReq and Solanalib.Runtime.SysAns, with no unwind exit, since an extern "C" function cannot unwind) the request of Solanalib.Runtime.Syscall and returns its answer: sol_sha256 the answer to .hash .sha256 slices, which has the shape a u64 status and a 32-byte result carry (HashShape: one 32-byte digest on status 0, no bytes otherwise) by a law of the index (Index.hashShape), with no precondition, its arguments (Sha256Args) also saying whether vals is 8-aligned; a call with more slices than the limit of the index (Index.maxHashSlices, none for no limit) does not return and stops as the environment stops abort without asking (Sha256Args.overLimit, aborted), as Agave a203300045b405f86c9c84308b2eae76af69ac3b SyscallHash checks the count first and aborts with TooManySlices before it charges compute or translates any address (syscalls/src/lib.rs:2733-2742); where the index checks alignment, a call with a slice at an unaligned vals does not return either (Sha256Args.unaligned), as Agave aborts it with UnalignedPointer when it translates vals (2758-2764, program-runtime/src/memory.rs:113-115), after the compute and hash_result checks (2744-2756), each of which aborts as well; the call stops without asking exactly when either check fails (Sha256Args.rejected); sol_log_ () when the environment answers .log message, every message admissible, one that the environment does not answer having only its terminal exits (logPost_unanswered); sol_panic_ and abort, which return !, only the terminal exits of the environment. Terminal exits are forwarded. canonical W c is the canonical runtime as an environment: the answers of Solanalib.Runtime.Env W c and the failures of Solanalib.Runtime.sysStep, as Solanalib.Runtime.the sys, sysFail and unregistered rules of Exec have them; under it sol_sha256 returns ⟨0, [W.prims.sha256 slices.flatten]⟩, a 32-byte digest by the width law of Solanalib.Runtime.Prims (canonical_sha256_post_iff), for a call that passes the alignment check within maxHashSlices, fails beyond and fails an unaligned call with ProgramFailedToComplete (canonical_sha256_terminated_iff, canonical_sha256_unaligned_iff), sol_log_ returns for a UTF-8 message and appends it to the logs and fails otherwise (canonical_log_answered_iff, canonical_log_terminated_iff), and sol_panic_ and abort fail with ProgramFailedToComplete. An index also records whether pointer arguments must be aligned (Index.checkAligned; for sol_sha256, whether an unaligned call stops), which the sol_sha256 model reads; canonical W c takes it from check_aligned in Agave, which holds for ABI v1 (Solanalib.Runtime.Abi.checkAligned, canonical_checkAligned, canonical_unaligned_iff), and its slice limit from the maxHashSlices of the profile, the sha256_max_slices of Agave (canonical_overLimit_iff, canonical_rejected_eq_false_iff). SHA-512/MSM request families with closed references and consistency samples; canonical instances reuse the pinned runtime.
<!-- /registry -->

<!-- registry:review:f9c0caa26df2bf89 -->
<a id="review-f9c0caa26df2bf89"></a>

Both exact releases derive Ord for the sole [u8; 32] field. Rust array ordering compares unsigned bytes in increasing index order; the first difference determines Less or Greater and equal arrays produce Equal. The model retains the native state. A Rust binding must additionally preserve both shared key permissions and the same caller world.
<!-- /registry -->

<!-- registry:review:e58190d7f7177173 -->
<a id="review-e58190d7f7177173"></a>

Reusable mathematical family with explicit values, callback order, state and finite outcomes. Source-facing wrappers choose exact reviewed functions; see source-notes/error-nullable.md.
<!-- /registry -->

<!-- registry:review:5556f2335a0afb6d -->
<a id="review-5556f2335a0afb6d"></a>

The complete deterministic families reuse the existing registered request semantics over one fixed World/InvCtx and complete request-phase InvState. Memcpy adds the observed source bytes as its output; memset supplies its exact repeated-byte pending output, whose syscall registration is unconditional. No unconstrained result provider replaces the existing runtime. Separate shape theorems expose native sysvar widths, exact return-data protocol, seed checks, status and failure-only no-write behavior. The mathematical buffer is a fixed initial request snapshot. A physical memory interpretation must retain that snapshot for model indexing and compose ordered output stores into the actual returned invocation state.
<!-- /registry -->

<!-- registry:review:55a98f09bb09fae6 -->
<a id="review-55a98f09bb09fae6"></a>

The legacy SDK log function forwards UTF-8 bytes and byte length to sol_log_ on Solana; on the host it calls the installed program_stubs implementation, which is replaceable and is not identified with stdout. The compute-unit logger calls sol_log_compute_units_ with no integer return or the corresponding host stub. Exact sink effects and finite abnormal exits are retained.
<!-- /registry -->

<!-- registry:review:254f08a4d3d1c7df -->
<a id="review-254f08a4d3d1c7df"></a>

The complete query uses arbitrary public schedule fields. firstSlot selects epoch <= first_normal_epoch, truncates epoch to u32 before saturating_pow, then saturating-subtracts 1 and multiplies by 32. Its other branch subtracts first_normal_epoch, multiplies slots_per_epoch and adds first_normal_slot with saturation. lastSlot calls firstSlot, adds get_slots_in_epoch with saturation and subtracts 1; warmup slots use a separate strict < test and saturating u32 exponent addition by 5. No schedule invariant or warmup-flag premise is imposed. Default is derived by custom(432000,432000,true), giving first_normal_epoch 14 and first_normal_slot 524256; this logical Default is also used by the typed getter.
<!-- /registry -->

<!-- registry:review:6a2adf7ad9aa1762 -->
<a id="review-6a2adf7ad9aa1762"></a>

Input reindexing transports the complete source family and its precondition to a singleton list; returned bytes, state and abnormal exits are unchanged.
<!-- /registry -->

<!-- registry:review:e6e849e1b9e447fb -->
<a id="review-e6e849e1b9e447fb"></a>

The selected Solana branch creates [0;32], passes that initialized output and the exact ordered input slices and count to sol_sha256, ignores its returned integer status and wraps the actual final 32 bytes as Hash. A normal provider reply may leave some or all bytes unchanged; no all-normal full-write premise is imposed. hash(val) performs exactly hashv(&[val]), including one empty slice for empty input. Host SHA2 is a different profile and is not admitted here.
<!-- /registry -->

<!-- registry:review:ed5482b521394efa -->
<a id="review-ed5482b521394efa"></a>

The macro initializes the actual typed destination with Default, calls the Solana typed syscall or the selected replaceable host stub and returns that current value for status 0. It converts each nonzero status with ProgramError::from(u64), preserving exact builtin matching and unknown-status low-word truncation. Borsh tag 15 returns BorshIoError("Unknown"). The 1.15.2 table ends at tag 21; 1.18.26 at tag 24; program-error 2.2.2 at tag 26. No nonzero status is folded to UnsupportedSysvar in these profiles. The exact Borsh tag reaches an explicit literal-copy provider after the typed read. Its returned OwnedError retains a live String resource; StringReady for reached normal copies proves freshness at the post-read state and exact current contents "Unknown". ownedPost and the nonempty closed witness retain ordinary allocation effects. fromStatus remains a separate value facet; no error-buffer ownership is inferred from it.
<!-- /registry -->

<!-- registry:review:4e030e98221d0985 -->
<a id="review-4e030e98221d0985"></a>

The shared families preserve exact value bytes, source guard and seed order, destination initialization, profile-specific error conversion, and actual callback state and exits. Version wrappers retain their complete family and source-dependent reader error kind. The source review is detailed in source-notes/address-profiles.md.
<!-- /registry -->

<!-- registry:review:3de2f66db0a10c82 -->
<a id="review-3de2f66db0a10c82"></a>

The LegacyStake dependency supplies the complete four-variant legacy enum and its projections. SDK API bindings remain in their separate registry records; this dependency adds no Stake API registration.
<!-- /registry -->

<!-- registry:review:420c70bc5e0fc774 -->
<a id="review-420c70bc5e0fc774"></a>

Each reviewed constructor always supplies [funding signer+writable, destination writable+nonsigner, base signer+readonly], including aliases; no seed/derived-key validation. It constructs metadata before seed.to_string, then calls bincode on variant 3/base/String/u64 lamports/u64 space/owner and drops the temporary String. Bincode 1.3.3 uses fixed little-endian u32/u64 and String byte length; normal output resources move and every admitted allocation/serialization/unwrap/cleanup exit is retained. The pinned String/Vec deallocator is lawful GlobalAlloc and has no unwound outcome; generalized destructor-unwind cleanup in the mathematical provider graph is not a claim about a compiler return-place. System interface 3.2.0 conditionally omits a duplicate base and is not admitted by this model. The reviewed 3.2.0 implementation allocates one new-account signer+writable metadata entry, then pushes the supplied optional payer regardless of lamports or key equality. It encodes variant 13/u64 lamports/u64 space/owner at the zero System program key. Bincode and wincode branches are separately selected; with both features wincode wins. Source ownership moves and cleanup/failure outcomes are modeled through actual-site providers, with no invocation or runtime effect claim.
<!-- /registry -->

<!-- registry:review:7c61b66e2c36b275 -->
<a id="review-7c61b66e2c36b275"></a>

Manual archive review of the derived Clone fields and reached canonical key clone: pubkey/Address bytes and both Boolean fields are copied without allocation, mutation, validation or guard acquisition. Legacy repr(C) and modern layouts require separate ABI interpretations; the value/lifetime contract is shared.
<!-- /registry -->

<!-- registry:review:ee7ba24f0b1c6ae3 -->
<a id="review-ee7ba24f0b1c6ae3"></a>

The reviewed derived Instruction Clone fields have program ID, Vec<AccountMeta>, Vec<u8> in that order. Primitive clones preserve exact order/duplicates and data; failure while cloning bytes drops only newly cloned accounts. Original vectors are borrowed, not consumed. Vec source layouts and allocator/cleanup correspondence remain separate; complete provider outcomes and useful exact-current laws are retained.
<!-- /registry -->

<!-- registry:review:f29d0d5500d16b0f -->
<a id="review-f29d0d5500d16b0f"></a>

Legacy stake values share the exact field vocabulary without the later StakeFlags variant. Instruction plans and resource lifetimes follow the selected constructor source. Pack is a callback family and WriteCounter is a serializer state machine, preserving generic effects and cleanup rather than treating them as pure decoders. Lookup decoding models the complete fixed bincode boundary and exact borrowed suffix. Closed references and witnesses are mathematical facts under the stated source interfaces. ALT normal error paths retain bincode Box<ErrorKind> allocation and map_err destruction in the indexed state; its pure decoder remains a value facet.
<!-- /registry -->

<!-- registry:review:8ba4459d8da58983 -->
<a id="review-8ba4459d8da58983"></a>

Borrowed tuple-field and program-ID models retain complete token and legacy stake pointees. The selected TokenAccount dereference follows its existing live parent, preserves the entire ambient state and creates no allocation or snapshot. Exact version bindings and the emitted pointer, extent and lifetime obligations remain separate evidence for the Rust binding.
<!-- /registry -->

<!-- registry:review:93ea4a4f92ee5352 -->
<a id="review-93ea4a4f92ee5352"></a>

The reviewed wrapper methods are represented by current source-object cells and live source loans, separate from AccountInfo RefCell storage. Shared and mutable references retain exact source identity and cannot outlive their parent token. Key copies retain ambient state. Clone and Drop receive the actual source field reference and its readable value; shared references retain external AccountInfo identity, whereas owned fields have distinct object identity and source-ordered Rc clone/drop effects. Sysvar clone decodes from the original AccountInfo reference after retaining info, with complete owned error unwrap and unwind cleanup. set_inner installs its replacement on normal and destructor-unwind paths. The proof witnesses are closed mathematical models; Rust bindings and native checks have the narrower scopes documented separately.
<!-- /registry -->

<!-- registry:review:cbcbf177c62487f6 -->
<a id="review-cbcbf177c62487f6"></a>

One shared Borrow.State supports source-specific target views, current-content observations and lease-only observations. Mapping either view or content preserves handles, generations, tombstones, policies and lease counts; it preserves and reflects validity and commutes with acquisition and release. Content replacement and target-view issue/transfer laws remain separate. Pinocchio guards and SDK CPI preflight consume these source-neutral laws without introducing a second borrow ledger.
<!-- /registry -->

<!-- registry:review:bb2c5a347237ccd7 -->
<a id="review-bb2c5a347237ccd7"></a>

Reusable assumed invocation relations compose the existing pure Agave preparation, synchronization, external processing and copyback definitions. Ordered lease probes preserve physical counters. A proved content/view projection connects the actual typed AccountInfo borrow state to those lease probes, preserving their order, completed releases and current cells. Owned preparation is a separate scoped storage-provider contract. Closed graph references and fixtures prove consistency; source-independent input bounds prove successful copyback preserves a finite region footprint.
<!-- /registry -->

<!-- registry:review:ab164008de907922 -->
<a id="review-ab164008de907922"></a>

The selected AccountInfo functions reuse the identified Borrow/AccountInfo/Rc world. Reflexive AsRef preserves the existing source reference; lamports acquisition returns typed current guards; scalar/boolean getters preserve temporary lifecycle and errors. Owner assignment updates shared owner storage. Resize/realloc preserve original-length accounting, complete backing bytes, shared serialized/local lengths, source error order and guard cleanup, with termination at a reached zeroing syscall. Generic preservation/progress and exact output-length lemmas and closed reference witnesses are mathematical evidence under their stated premises. Exact versions and defining Rust identities, including legacy solana_program paths, are reviewed individually.
<!-- /registry -->

<!-- registry:review:303d6cdfff6b34a1 -->
<a id="review-303d6cdfff6b34a1"></a>

The selected function models compose explicit primitive operations at actual current states. Context constructors/mutators preserve fields, references and Vec owners; old program AccountInfo and modern copied Pubkey are distinct interpretations. Error callbacks retain unwind, terminal outcomes and source cleanup; log temporaries are cleaned on host unwind. Exact finite code tables select each released macro expansion. Codec bodies retain partial write/cursor mutations and diagnostic resources. Families with True mathematical preconditions still require the separate Rust binding to establish initialized current resources and representations; no source-output premise is inferred from finite witnesses.
<!-- /registry -->

<!-- registry:review:5e479024ba0d2d51 -->
<a id="review-5e479024ba0d2d51"></a>

The shared error algebra preserves inline versus boxed storage, complete old owned ProgramError Strings, modern unit Borsh errors and source-ordered replacement/destruction. Version-specific availability is a separate source-representation predicate. Numeric conversion is an observation and never destroys or replaces an owned payload. Ops.fromOwned is an exact primitive translation for the preexisting modern boxed provider, not an SDK proof.
<!-- /registry -->

<!-- registry:review:39a4b9ddaf62e22b -->
<a id="review-39a4b9ddaf62e22b"></a>

Context and CpiContext retain the actual generic fields, borrowed references and owned values. Context::new and with_signer only move the selected fields. CPI-context construction uses the explicit empty-vector operation; replacing remaining accounts invokes the actual old-vector destructor at the current state. The Program parameter is the owned AccountInfo in reviewed older releases and the copied Pubkey in 1.x. No invocation is reached.
<!-- /registry -->

<!-- registry:review:890159c9f1a99a7c -->
<a id="review-890159c9f1a99a7c"></a>

This registry admits only Anchor Lang 0.32.1 allocate, assign, create_account and transfer. The shared mathematical support contains additional source-version profiles without registering them. Full local preparation uses explicit primitive resource callbacks, opaque whole-signature invocation and selected Anchor error conversion. Retains each finite exit and source cleanup order. Nonempty closed witnesses and exact projected-wrapper conformance are separate from implementation proofs.
<!-- /registry -->

<!-- registry:review:4e073bd4cffc163f -->
<a id="review-4e073bd4cffc163f"></a>

This registry admits only Anchor SPL 0.32.1 token_2022::transfer_checked. The shared Binding index contains 27 reviewed source cases across five releases as supporting definitions, not additional registered APIs. Each Binding selects one exact wrapper and resolved constructor profile. The model composes the existing allocated instruction plans or staged extension/size builder, source-ordered array preparation, exact CpiRequest including aliases and nested signer groups, opaque invocation, versioned owned ProgramError conversion and edition-2021 cleanup. Version 0.27 clones the CPI array and uses inline ProgramErrorWithOrigin; 0.29/0.32 move operands and box the full old ProgramError, including its String; 1.x has a copied context program and modern unit Borsh variant. GetAccountDataSize releases its statement array before the getter, checks returned key before the exact eight-byte length, releases the returned Vec before conversion, then drops instruction/context. Ready checks only each reached instruction/seed read, size extension read and matching getter byte owner. The generic continuation and graph theorems retain each actual primitive finite exit without assuming termination. Closed samples execute every binding successfully. Projected-wrapper native conformance uses real Anchor contexts/account structs and real constructors while replacing only complete invocation/getter signatures.
<!-- /registry -->

<!-- registry:review:38b904f5fa73aa94 -->
<a id="review-38b904f5fa73aa94"></a>

The additive plans preserve exact enum bytes, optional-key encodings, signer order/duplicates and the source allocation sequence. SetAuthority reserves one more slot than it fills. The three inline extension constructors allocate metadata before bytes; ordinary constructors allocate bytes first. The existing InstructionAllocated engine supplies actual partial-owner cleanup, unwind and terminal behavior.
<!-- /registry -->

<!-- registry:review:8adcc7d0a266948d -->
<a id="review-8adcc7d0a266948d"></a>

Require the Token-2022 program before allocating the writable mint metadata vector. Validate authority before metadata address: None encodes zeros, Some(zero) returns InvalidArgument and destroys the actual allocated metadata owner. Success packs outer tag 39, subtag 0 and the two key32 POD fields. Complete byte allocation, partial-state cleanup, double unwind and terminal stopping remain explicit.
<!-- /registry -->

<!-- registry:review:80a4176f98915ac2 -->
<a id="review-80a4176f98915ac2"></a>

The existing callback graph algebra is shared by mathematical witnesses and conformance. Every graph theorem is an equivalence for the supplied finite callback interpretation, including partial reads, unwind cleanup, double-unwind policy and terminal exits. Existing conformance declarations are exact export aliases.
<!-- /registry -->

<!-- registry:review:e5f8d5fd55406350 -->
<a id="review-e5f8d5fd55406350"></a>

This shard registers thirteen Anchor 0.32.1 methods. Shared lifecycle families compose source-order record consumption, initialization, owner/ID observations, error resources, guarded codecs, focused payload replacement, conditional serialization and close mutation/cleanup. Their retained helper branches and source evidence also distinguish other reviewed releases; those supporting definitions add no registrations here. Each selected facade fixes its information-field storage, error storage and operation mode. Readiness applies only at reached prefixes and supports typed current data, actual error stores, guard release and continuation of every admitted finite dependency exit. Exact file/package seals remain in this registry. The selected methods and their interpretation are described in source-notes/anchor-lifecycle.md.
<!-- /registry -->

<!-- registry:review:cc6a81bdcc17465c -->
<a id="review-cc6a81bdcc17465c"></a>

AccountLoader identity, unchecked and account-slice construction, zero-copy initialization and discriminator persistence reuse actual shared AccountInfo/Borrow and owned Anchor diagnostic operations. Prefix admission gives the consumed local read/cleanup continuations. Reference indices keep record identity distinct from cells and guard generations. Close reuses source-ordered current lamports/owner/resize and destination Rc cleanup, including sequential self-aliasing.
<!-- /registry -->

<!-- registry:review:4e44ba666333c286 -->
<a id="review-4e44ba666333c286"></a>

Reusable mathematical family with explicit values, callback order, state and finite outcomes. Source-facing wrappers choose exact reviewed functions; see source-notes/sdk-values.md.
<!-- /registry -->

<!-- registry:review:7d6859774643ec81 -->
<a id="review-7d6859774643ec81"></a>

The concrete StateWithExtensions trait implementation returns its stored borrowed TLV slice directly. It performs no parsing, initialization test, allocation or extension validation. The family retains the base value, the parent reference and exact tail range; an empty literal tail remains distinct from a borrowed tail. The source checks minimum length and the multisig collision before splitting the input and calling the actual generic Pack::unpack. On success it obtains the tail and drops the owned base if the tail stage fails or unwinds. A nonempty remainder first checks the version-specific minimum, then creates a zero-filled temporary Vec, compares padding, destroys that temporary, and only then decodes/checks the account marker. The comparison is captured before destruction, while the marker reads current input afterward. Token 8.0.1 rejects a remainder ending exactly at the marker; interfaces 2.1.0 and 3.0.1 admit that empty borrowed tail. The returned tail is not validated as a TLV stream. The old get_tlv_data_info allocates an empty vector after the resolved accessor returns. It decodes each type, stops at the sentinel or a final single spare byte, checks the length header, then pushes the type BEFORE checking that the payload fits. Thus a push failure may precede malformed-payload rejection. Reached errors destroy the temporary owner; success transfers the live ordered vector. This is deliberately distinct from the later interface scan that checks payload bounds before pushing. For nonempty input the old source constructs and fully deduplicates a temporary Vec<&ExtensionType> before attempting any fixed-width calculation. Equality compares referent values, while each stored reference retains the exact reached operand at the first encountered source occurrence, including its actual tag. A variable-length kind can therefore be preceded by allocation or push failure. It sums each successful distinct type length including the four-byte header, then destroys the temporary and applies the base/marker and multisig adjustment. TokenExtensionLegacyBounds derives at most 28 distinct ordinary kinds from actual empty/current/push laws and proves each fixed length at most 299, so the ordinary usize sum cannot overflow at the reviewed 64-bit target. No overflow or rate-domain hypothesis is added to the mathematical contract. The required-init function starts an empty Vec and performs ordered pushes for each input kind. It preserves duplicates; NonTransferable contributes NonTransferableAccount followed by ImmutableOwner. It does not read the existing result elements before a push. The family preserves each reached allocation/push exit and owned-vector cleanup, returning the same live vector identity on success. Rust evaluates get_tlv_data before the fallible new-extension get_packed_len callback, then scans the TLV bytes into an owned temporary. Measurement errors occur before that scan/allocation. The calculation uses the scanned used prefix rather than backing capacity, performs a fresh current-slice lookup for an existing extension, masks only that lookup ordinary error to length zero, applies saturating usize arithmetic and the multisig adjustment, then destroys the vector. Callback mutation, unwind, terminal exits and cleanup remain at those exact stages. The provided get_extension first invokes the actual get_extension_bytes implementation, then interprets its returned slice as the selected Pod V. Default byte lookup is supplied separately: requested/base type compatibility is checked before scanning; encountered types are decoded and their account association checked in source order; sentinel, unknown type, reached length errors and Pod size/alignment errors remain distinct. The result is a reference to the same source bytes, not a copied arbitrary V. The helper calls the resolved typed extension getter once. A returned extension maps its concrete nullable 32-byte field to Option<Pubkey>, where all-zero is None; the hook selects the second key after its authority. Result::ok consumes an ordinary getter error before returning None. A legacy BorshIoError may own a String, so the explicit reached error-destructor dependency preserves its deallocation effects, unwind or terminal exit; only a normal drop permits None. The error variant may abstract the message while its actual owner remains in the shared state. Neither helper invokes CPI. The selected GetterLaws helper proves the typed getter and reached error-drop consequences of these indexed contracts. It introduces no assumed successful getter or additional source operation.
<!-- /registry -->

<!-- registry:review:bb2d88bcfe61e203 -->
<a id="review-bb2d88bcfe61e203"></a>

The concrete StateWithExtensions trait implementation returns its stored borrowed TLV slice directly. It performs no parsing, initialization test, allocation or extension validation. The family retains the base value, the parent reference and exact tail range; an empty literal tail remains distinct from a borrowed tail. The source checks minimum length and the multisig collision before splitting the input and calling the actual generic Pack::unpack. On success it obtains the tail and drops the owned base if the tail stage fails or unwinds. A nonempty remainder first checks the version-specific minimum, then creates a zero-filled temporary Vec, compares padding, destroys that temporary, and only then decodes/checks the account marker. The comparison is captured before destruction, while the marker reads current input afterward. Token 8.0.1 rejects a remainder ending exactly at the marker; interfaces 2.1.0 and 3.0.1 admit that empty borrowed tail. The returned tail is not validated as a TLV stream. The old get_tlv_data_info allocates an empty vector after the resolved accessor returns. It decodes each type, stops at the sentinel or a final single spare byte, checks the length header, then pushes the type BEFORE checking that the payload fits. Thus a push failure may precede malformed-payload rejection. Reached errors destroy the temporary owner; success transfers the live ordered vector. This is deliberately distinct from the later interface scan that checks payload bounds before pushing. For nonempty input the old source constructs and fully deduplicates a temporary Vec before attempting any fixed-width calculation. A variable-length kind can therefore be preceded by allocation or push failure. It sums each successful distinct type length including the four-byte header, then destroys the temporary and applies the base/marker and multisig adjustment. TokenExtensionLegacyBounds derives at most 28 distinct ordinary kinds from actual empty/current/push laws and proves each fixed length at most 299, so the ordinary usize sum cannot overflow at the reviewed 64-bit target. No overflow or rate-domain hypothesis is added to the mathematical contract. The required-init function starts an empty Vec and performs ordered pushes for each input kind. It preserves duplicates; NonTransferable contributes NonTransferableAccount followed by ImmutableOwner. It does not read the existing result elements before a push. The family preserves each reached allocation/push exit and owned-vector cleanup, returning the same live vector identity on success. Rust evaluates get_tlv_data before the fallible new-extension get_packed_len callback, then scans the TLV bytes into an owned temporary. Measurement errors occur before that scan/allocation. The calculation uses the scanned used prefix rather than backing capacity, performs a fresh current-slice lookup for an existing extension, masks only that lookup ordinary error to length zero, applies saturating usize arithmetic and the multisig adjustment, then destroys the vector. Callback mutation, unwind, terminal exits and cleanup remain at those exact stages. The provided get_extension first invokes the actual get_extension_bytes implementation, then interprets its returned slice as the selected Pod V. Default byte lookup is supplied separately: requested/base type compatibility is checked before scanning; encountered types are decoded and their account association checked in source order; sentinel, unknown type, reached length errors and Pod size/alignment errors remain distinct. The result is a reference to the same source bytes, not a copied arbitrary V. The helper calls the resolved typed extension getter once. A returned extension maps its concrete nullable 32-byte field to Option<Pubkey>, where all-zero is None; the hook selects the second key after its authority. Result::ok consumes an ordinary getter error before returning None. A legacy BorshIoError may own a String, so the explicit reached error-destructor dependency preserves its deallocation effects, unwind or terminal exit; only a normal drop permits None. The error variant may abstract the message while its actual owner remains in the shared state. Neither helper invokes CPI.
<!-- /registry -->

<!-- registry:review:e1bd634e5e426cfc -->
<a id="review-e1bd634e5e426cfc"></a>

Account::is_frozen compares only its valid AccountState enum against Frozen. It neither invokes Pack nor requires initialization; Uninitialized is a valid receiver and returns false. Other account fields and the receiver remain unchanged. The concrete derived Default calls the default constructors for OptionalNonZeroPubkey, Pubkey, three String fields and Vec<(String,String)>. Both keys are zero and all containers are empty with zero capacity; constructing them needs no heap allocation or user callback. The mathematical value postcondition contains the six actual fields without imposing the documented additional-key uniqueness convention. A Rust binding must supply real owned empty container representations separately.
<!-- /registry -->

<!-- registry:review:a035c5adfc385b82 -->
<a id="review-a035c5adfc385b82"></a>

The Pod fields are decoded as unsigned little-endian 64/16-bit values. Checked u128 multiplication and ceiling division are followed by u64 narrowing BEFORE maximum-fee capping. The inverse helper retains the zero amount/rate branches, the full-rate cap branch and checked denominator/subtraction/addition behavior, then calculates the fee of the derived gross amount. No basis-points-at-most-10000 precondition is imposed: invalid raw rates are admitted and may return None. Epoch wrappers select newer at equality, retain the receiver and apply the same checked arithmetic. The source returns an existing reference to newer_transfer_fee when epoch is at least its epoch, otherwise older_transfer_fee. The complete shared reference family retains parent identity and selected field; later observation reads that field from the current parent. It is not a snapshot or a new allocated fee record.
<!-- /registry -->

<!-- registry:review:f8644a105bcbd709 -->
<a id="review-f8644a105bcbd709"></a>

For any program ID, retain four metas in source order: writable metadata, readonly update authority, readonly mint and readonly signer mint authority. Allocate metadata first; build discriminator-prefixed bytes, serialize the three actual current String owners, append then destroy the temporary vector, and finally destroy input strings after constructing the return place. UTF-8 byte lengths are u32 little endian. Returned output is Instruction directly; unwrap, allocation and destructor unwind/terminal outcomes are retained. The closed witness executes every allocation/append/drop and leaves only the constructed Instruction owners. Serialization reads live owners at its actual callback state, rather than a saved pre-allocation text snapshot.
<!-- /registry -->

<!-- registry:review:caed575a7d244b52 -->
<a id="review-caed575a7d244b52"></a>

Allocation-free aligned loader deserialization into the initialized prefix of a caller-owned array; exact duplicate header aliases, skipped account parsing, full input preservation and instruction/program views. The registered reference is the graph of the byte parser and source-ordered state transformation. Closed witnesses and native fixture replay are separate from the concrete source assumption. The account bridge installs the exact header identities into PinocchioAccount.State, retaining raw flags, signed resize delta and hidden data bytes. Nonzero resize histories require the account the separate validity condition of API.
<!-- /registry -->

<!-- registry:review:7ac18ee916b88cc8 -->
<a id="review-7ac18ee916b88cc8"></a>

Aligned loader deserialization with exact account offsets, original-length writes, allocation ordering and terminal behavior, shared Rc/owner aliases, realloc reserve, rent epoch and instruction/program views. The registered reference is the graph of the byte parser and source-ordered state transformation. Closed witnesses and native fixture replay are separate from the concrete source assumption. The shape and origin lemmas derive every newly allocated cell, owner reference and vector element from the parsed unique records; they do not assume a supplied post-state graph.
<!-- /registry -->

<!-- registry:review:9088a05f3cf38fca -->
<a id="review-9088a05f3cf38fca"></a>

The complete reviewed functions are interpreted by the registered shared mathematical families and current-state references. All ordinary, error, callback and reached terminal outcomes are retained. Pin-specific borrow credits and signed resize stages, and logger initialized-prefix state and cleanup, are explicit; generic source representation remains separate.
<!-- /registry -->

<!-- registry:review:803098b64c833657 -->
<a id="review-803098b64c833657"></a>

Model the whole local helper: validation PDA before first program lookup; optional first validation lookup; ordered Execute instruction and five owned infos; actual shared validation Ref and per-record collect of every current info Ref; whole-region TLV validation, first Execute range, PodSlice layout errors then count-capacity panic; fixed/key-data/ordered-seed resolution; 0.9 privilege union and first-match account lookup; clone-before-push; temporary cleanup; extras/validation/program copyback in source order. The source frame is not transactional: metadata extension precedes info extension, so later unwind retains actual partial mutation. Pubkey 2.2.1 supplies a zeroed destination and bump 255. No CPI body or result oracle is part of the family. See source-notes/transfer-hook-resolution-0.9.0.md for reached dependency comparisons and source admission.
<!-- /registry -->

<!-- registry:review:ea88b12210a600e5 -->
<a id="review-ea88b12210a600e5"></a>

Both checked loaders reject an incorrect instructions ID before borrowing data, then acquire a shared Ref and use the current cell. The current-index loader reads exactly the final two little-endian bytes; a short slice panics (checked subtraction or wrapping slice-range panic), and the Ref is released on unwind. The instruction loader reads count, checks index, reads table offset and account count, allocates the meta Vec, reads and pushes flags/key pairs, then reads program key and byte length and allocates data. High flag bits are ignored; every reached bounds error is SanitizeError::IndexOutOfBounds mapped to InvalidArgument. A 32-byte Pubkey conversion cannot produce ValueOutOfBounds after its bounds check. A parse Err drops local metas before releasing the shared Ref; successful Vecs move into Instruction. Terminal exits have no cleanup state.
<!-- /registry -->
