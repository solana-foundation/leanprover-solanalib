# Anchor SPL 1.0.2 token models

Reviewed anchor-spl 1.0.2 uses revision
`1314a6b83b16e6a31947b372d57988fd0e81559c` of
[`solana-foundation/anchor`](https://github.com/solana-foundation/anchor/tree/1314a6b83b16e6a31947b372d57988fd0e81559c/spl/src).
Complete-file hashes are
`7c709e2368c483768ef9ac9d38b5e25106cb69e28fcba4d4066b5fc013ea913e`
for token.rs and
`edc5a84f5c48f3bad56c3e288e348711dbb6d3e09497788f9d30dd9c45380419`
for token_interface.rs. The four modeled operations are the two Mint dereferences,
amount and transfer.

At that revision, [spl/Cargo.toml](https://github.com/solana-foundation/anchor/blob/1314a6b83b16e6a31947b372d57988fd0e81559c/spl/Cargo.toml#L7)
declares `edition = "2021"` directly; its complete-file SHA-256 is
`e28a186307aae36ab6aec29d7b1fe0edefa9f6225feb695ff1b441e7783662a3`.

Mint dereferences project decoded Token.Mint fields; they do not parse bytes.
Amount performs checked shared borrowing, reads little-endian bytes 64 through
71 and releases that guard. Short data panics. Borrow failure instead allocates
an owned Anchor ProgramError Box without releasing the guard of another caller.
There is no owner check or full account decoder in this accessor. Its family
and supporting observation require typed current data only after an actually
successful data borrow. Earlier borrow failures remain admitted. The condition
supplies the actual bytes and the complete local read result; acquisition proves
guard release on return or unwind. The owned wrapper preserves every actual
error-conversion outcome and its effects. Whole-AccountInfo validity, owner,
full-codec and scalar-width facts are not required. This is model admission;
the raw operations add no source check. Physical references and representation
remain separate binding obligations.

Transfer uses the shared allocated legacy-token instruction plan: fixed legacy
program ID, ordered source/destination/authority, no multisig signer keys and
the exact u64 amount. Byte construction precedes metadata construction through
explicit vector providers. Program admission cannot ordinarily reject the fixed
ID; dependency failure is separate. Usize width and TokenInstruction enum
reservation size remain source binding parameters. The 128-byte
reservation of the sample is not a measured layout.

The three AccountInfo fields move into the invocation array in order; they are
not cloned. Context program ID does not override the token program, remaining
accounts are not appended, and nested signer seeds are passed unchanged. The
request reads current instruction resources at the call rather than using a
saved byte snapshot.

The actual solana_invoke::invoke_signed signature is an opaque relation without
success or rollback guarantees. A normal ProgramError is boxed by map_err
before temporary destruction. The account array occurs in the tail expression of the function body at token.rs:27, while `ix` is a local binding at line 17. Under
the [edition-2021 tail-expression scope rule](https://doc.rust-lang.org/edition-guide/rust-2024/temporary-tail-expr-scope.html),
the array outlives that local scope. Cleanup therefore drops instruction
metadata, instruction bytes, the moved array in element order, then the
remaining vector. A builder unwind before the moves instead cleans the
still-owned context. Terminal exits have no fabricated state or later cleanup.

Each AccountInfo drop calls its two Rc dependencies. Remaining-vector drop owns
both element destruction and storage retirement; the SDK calls that provider
once. Its binding must use the same Rc interpretation. The concrete witness
performs those element calls before reference-ledger retirement. Valid Global
byte/AccountMeta/AccountInfo drops have no user unwind callback. Their three
non-unwind guarantees are explicit premises of the separate
`invocationDrops_no_unwind` theorem, with terminal outcomes still possible.

The transfer family requires `BuildReady`: both constructed vectors must be
readable at every actual successful instruction-builder return. The exact
request-domain equivalence uses their current contents in that returned state.
Its continuation theorem preserves every supplied invocation, error-conversion
and cleanup outcome. Earlier builder unwind or terminal exits need no request;
no provider termination or CPI success is assumed. General vector/error laws,
plan-range conditions and initial vector liveness are not required. The
resource interpretation carries no hidden non-unwind proof fields.
The conditional cleanup theorems use those source destructor guarantees to
rule out turning a pending return into an unwind. Concrete
composition separately uses current-content and retirement laws where their
conclusions are needed. A Rust binding must justify lifetime and held-resource
framing, including preservation of a pending returned error through cleanup.
Logical IDs are not raw addresses or ownership permissions. Observation facets
omit these resource effects and do not replace the primary families.

Tests compose the fresh empty owner of CpiContext with transfer and retirement,
retain a live boxed error after cleanup, preserve ordered calls and unwind
effects, and exercise terminal boxing. An order-sensitive dependency exits
terminally if an array element drops while either instruction vector remains
live; the edition-2021 sequence completes with the boxed error intact. Further
controls retain the amount read and release under an abstract unsupported width,
and a terminal builder exit before a missing abstract remaining owner is used.
Another control uses a remaining-vector provider that actually unwinds after
the instruction and moved-account cleanup. The raw family retains that outcome,
while the separate non-unwind premise excludes that provider. A positive
control applies the three real mathematical drop guarantees to rule out an
unwind replacing a pending owned-error return.
Request-admission controls reject an unreadable successful builder return even
when another return is readable. They also admit an invocation provider with
no finite exit and preserve a supplied error, boxing and cleanup continuation.
These controls claim no Rust representation for their inputs. A pre-move failure-injection test checks
the generic dependency-unwind branch; it does not claim a concrete Global
allocator unwind for this source call. No invocation body or invoked program
was read. The separate solana_cpi::invoke_signed boundary stays opaque. Rust
implementation, ABI/layout and dependency correctness remain open.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:4d1479e6a4ae5597 -->
<a id="review-4d1479e6a4ae5597"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The AccountInfo 3.1.1, Anchor 1.0.2 and Anchor SPL 1.0.2 functions compose identified borrows, current owner reads, explicit trait callbacks, owned resources and source-ordered cleanup. AccountInfo borrow/getter conditions support their actual typed-current and progress conclusions. Constructor admission covers only reached initialization reads, diagnostic Error resources and guarded decoder/discriminator continuations. Loading and amount admit earlier checked errors but require current data after successful acquisition; reached owned loading factories retain their held tokens. Their continuation results preserve actual finite exits without assuming dependency termination. Owned-error families retain their three boxing or four comparison capabilities; comparisons additionally require reached assignment availability, and with_values protects resources on continuing unwind/destructor paths through CallReady. Pure error observation facets retain their stated omissions. Context uses actual empty-provider current/fresh facts. Primary transfer requires current instruction vectors on each successful builder return; invocation remains opaque. Pinned edition-2021 cleanup destroys instruction metadata and bytes, the tail-expression account array, then the remaining vector. Conditional destructor non-unwind claims and concrete resource/reference/target interpretations remain explicit source bindings.

Borrowed tuple-field and program-ID models retain complete token and legacy stake pointees. The selected TokenAccount dereference follows its existing live parent, preserves the entire ambient state and creates no allocation or snapshot. Exact version bindings and the emitted pointer, extent and lifetime obligations remain separate evidence for the Rust binding.

Checked transfer uses the token2022TransferChecked0321 reference binding, with inspected 0.32.0–0.32.3 sources and declared 0.32 compatibility. Its profile requires token_2022 and the reviewed constructor, context and legacy error dependencies. Other historical Binding cases remain supporting definitions; detailed resource and source assumptions stay in the binding obligations.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.
<!-- /registry -->

<!-- registry:review:ba3c90b0837e2dfc -->
<a id="review-ba3c90b0837e2dfc"></a>

All 65 stable releases have the byte-identical Deref implementation (hash db15e5b8a77c0c20468213bdc0b240acebea7c93d92b542b4fc55efca7acb139): &self.0 with Target=spl_token::state::Mint. The source relation is a borrowed field projection with no parsing, allocation or callback. Legacy-token/interface alias and feature migrations retain the represented Mint fields; state.rs is identical between the selected token-interface 2.0.0 and 3.0.0 cohorts.
<!-- /registry -->

<!-- registry:review:ab6664cc18e379fc -->
<a id="review-ab6664cc18e379fc"></a>

The amount accessor appears in 0.4.5. Checked shared borrowing precedes a 64..72 byte read and little-endian conversion; the acquired guard drops on return or unwind and the conflicting guard of the caller remains held. There is no owner/full-codec validation. The complete family includes allocation of the returned ProgramError box. Bare errors through 0.21.0 and inline wrappers through 0.28.0 therefore do not correspond. From 0.29.0 onward the actual From<ProgramError> Box::new closure is unchanged, including the later anchor-lang-error split (hash 0d2ff72ff7608e507ee73a434bcaef545d097691e5a89758df619c8c17d3df4f). Native 0.28/0.29 observes exactly 0/1 error allocations. The older payload-bearing Borsh error variant is irrelevant to this reached AccountBorrowFailed conversion.
<!-- /registry -->

<!-- registry:review:acde494991844340 -->
<a id="review-acde494991844340"></a>

The amount accessor appears in 0.4.5. Checked shared borrowing precedes a 64..72 byte read and little-endian conversion; the acquired guard drops on return or unwind and the conflicting guard of the caller remains held. There is no owner/full-codec validation. The observation deliberately forgets owned error allocation. Its only reached program error is AccountBorrowFailed, so the exact bare error (0.4.5–0.21.0), inline Anchor wrapper (0.22.0–0.28.0), and boxed wrapper (0.29.0+) project to AnchorAccount.programError with absent origin/compared values. No arbitrary CPI error is abstracted here. Earlier lifetime spelling and empty-origin representation changes do not change this actual observation.
<!-- /registry -->

<!-- registry:review:7721120ba0170608 -->
<a id="review-7721120ba0170608"></a>

All releases build the same fixed legacy-token transfer bytes and three metadata entries with no multisig keys and preserve nested seeds. Through 0.19.0 the actual CPI info list additionally contains ctx.program. From 0.20.0 it has three infos; through 0.28.0 they are cloned and from 0.29.0 they are moved. Until 1.0.0 CpiContext still owns a separate program AccountInfo. Only 1.0.0+ removes the extra program owner and matches the existing source-ordered move/error/cleanup trace. Every such release is edition 2021: drop instruction metadata, bytes, the tail-expression moved-account array, then the remaining-accounts vector. Builder failures occur before moves, and returned CPI errors are boxed before cleanup. Existing BuildReady/current-vector, Rc and conditional non-unwind bindings are retained; no success or termination is assumed.
<!-- /registry -->

<!-- registry:review:96b8488d62e90601 -->
<a id="review-96b8488d62e90601"></a>

All releases build the same fixed legacy-token transfer bytes and three metadata entries with no multisig keys and preserve nested seeds. Through 0.19.0 the actual CPI info list additionally contains ctx.program. From 0.20.0 it has three infos; through 0.28.0 they are cloned and from 0.29.0 they are moved. Until 1.0.0 CpiContext still owns a separate program AccountInfo. For 0.20.0–0.32.3, request values agree after the intentional ownership projection, but the unrestricted CPI ProgramError output of the model cannot preserve the old BorshIoError(String) payload using the selected unit-payload vocabulary. The partial role omits ownership, not arbitrary error data. We do not add a no-Borsh-error assumption to widen it. From 1.0.0 the complete current value request and error vocabulary agree.
<!-- /registry -->

<!-- registry:review:36c7d83ee85684fd -->
<a id="review-36c7d83ee85684fd"></a>

The API first appears in 0.27.0. Every published implementation has the identical &self.0 projection and the same Target=spl_token_2022::state::Mint alias. The wrapper/inner mint relation preserves the five decoded fields and the same borrowed object. Package/interface and Pubkey/Address alias changes affect binding identities, not this projection. No decoder is reached by deref.
<!-- /registry -->

<!-- registry:review:732a33d3ba53373a -->
<a id="review-732a33d3ba53373a"></a>

References: 0.32.1, 0.32.2 and 0.32.3, with identical complete token_interface.rs/token.rs/lib.rs files, token_2022 feature expansion and relevant spl-token-2022 8 requirement. The declared [0.32.1, 0.33.0) range assumes preservation of &self.0: the complete decoded Account field is lent through the same live parent with its permission, provenance and repayment. The provider constraint below retains its emitted fields and layout, separately from the packed 165-byte wire format. No deserialization, owner validation, RefCell borrow, token-program call, allocation or cleanup occurs.
<!-- /registry -->

<!-- registry:review:205cceaae6b2ea12 -->
<a id="review-205cceaae6b2ea12"></a>

The declared compatible range assumes return of the same shared reference to the complete underlying Token-2022 Account value, with its original lifetime and state. The dependency type is not replaced by a projected key or a same-layout type. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:817e4eed1b706f75 -->
<a id="review-817e4eed1b706f75"></a>

Return &self.0 from the same live wrapper, with no decoding, owner check, allocation or cleanup. Retain all Token Account fields, the actual child tag and modal parent repayment. The full emitted pointee codec remains separate from packed serialization. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:b8251492ec5a8d00 -->
<a id="review-b8251492ec5a8d00"></a>

Reference source: anchor-spl 0.29.0. Return the contained old Token-2022 Account payload from the same live TokenAccount wrapper, preserving the actual field reference. Perform no deserialization, owner check or allocation. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:87fb1552e573872f -->
<a id="review-87fb1552e573872f"></a>

Anchor SPL 0.32.0–0.32.3 have identical token_2022 source, including this wrapper and account aggregate. The range assumes the same owned context program, from/mint/to/authority move order, reached signer-seed read, boxed legacy error conversion and cleanup. The 1.0.0 copied-program variant stays separate.
<!-- /registry -->

<!-- registry:review:ed2d056ef1cff831 -->
<a id="review-ed2d056ef1cff831"></a>

The 0.32 references build fixed ATA/System metas from wallet, token-program and mint seeds, forward the supplied account even if its key differs from the derived meta, and retain remaining accounts for cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:952845662a115197 -->
<a id="review-952845662a115197"></a>

The 0.32 references retain the six metadata metas, seven cloned context fields, remaining/program account order, capacity-seven allocation, discriminator 33, UTF-8 Borsh fields and owned error cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:757a338bb37d1598 -->
<a id="review-757a338bb37d1598"></a>

The 0.32 references return the selected SPL Token program ID by value; the context cannot substitute a different ID. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:4d58ef06dbc0354e -->
<a id="review-4d58ef06dbc0354e"></a>

The marker Id implementation returns the selected dependency ID by value. The complete 32-byte key is preserved and the source result is the exact Pubkey/Address tuple wrapper; no context-supplied program can override it. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:267c79dcbbc59a25 -->
<a id="review-267c79dcbbc59a25"></a>

The 0.32 references return the contained Token.Account field of the same live wrapper without deserialization, validation or allocation; all optional fields and the actual reference identity remain available. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:628466cda7c3879e -->
<a id="review-628466cda7c3879e"></a>

Return &self.0 with the original reference tag and parent repayment; do not deserialize, check ownership, allocate or clean up. Preserve the complete emitted pointee representation separately from packed serialization. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:f6e50aa67b5356cf -->
<a id="review-f6e50aa67b5356cf"></a>

The 0.32 transfer wrapper retains its owned program AccountInfo, ordered request accounts, exact moves/clones and boxed legacy ProgramError cleanup. This complete ownership variant remains distinct from the copied-program-ID wrapper. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:f0b0a62a74c11fa5 -->
<a id="review-f0b0a62a74c11fa5"></a>

The 0.32 references retain burn constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:3648a7a68b55a85c -->
<a id="review-3648a7a68b55a85c"></a>

The 0.32 references retain close_account constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:e23df75a52f42bf1 -->
<a id="review-e23df75a52f42bf1"></a>

The 0.32 references preserve constructor and CPI/getter effects, compare the returned program ID before requiring exactly eight bytes, and drop the owned return vector at each reached success/error site. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:2406828602ea7870 -->
<a id="review-2406828602ea7870"></a>

The 0.32 references retain initialize_account3 constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:7ec258f45e63460d -->
<a id="review-7ec258f45e63460d"></a>

The 0.32 references retain initialize_immutable_owner constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:c5bd5919759f8a9e -->
<a id="review-c5bd5919759f8a9e"></a>

The 0.32 references retain initialize_mint2 constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:a78a90af2f95adc3 -->
<a id="review-a78a90af2f95adc3"></a>

The 0.32 references retain mint_to constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:2dd3e8e3a92c3efe -->
<a id="review-2dd3e8e3a92c3efe"></a>

The 0.32 references retain set_authority constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:10866dbbfdc49abf -->
<a id="review-10866dbbfdc49abf"></a>

The 0.32 references retain group_member_pointer_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:0ae5950402ba8980 -->
<a id="review-0ae5950402ba8980"></a>

The 0.32 references retain group_pointer_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:793c6c457df396b0 -->
<a id="review-793c6c457df396b0"></a>

The 0.32 references retain metadata_pointer_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:1d34d08644d4e9cd -->
<a id="review-1d34d08644d4e9cd"></a>

The 0.32 references retain mint_close_authority_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:c39a0492489a1c3b -->
<a id="review-c39a0492489a1c3b"></a>

The 0.32 references retain non_transferable_mint_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:05d9b4d4d82c940d -->
<a id="review-05d9b4d4d82c940d"></a>

The 0.32 references retain permanent_delegate_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:50f55e09916a521c -->
<a id="review-50f55e09916a521c"></a>

The 0.32 references retain transfer_hook_initialize constructor-before-invocation order, exact account moves/clones, owned program AccountInfo, boxed legacy ProgramError and continuing/terminal cleanup. Compatibility within 0.32 assumes this local protocol and the selected dependency contracts remain unchanged; invocation stays opaque.
<!-- /registry -->

<!-- registry:review:ced2c98c7355d922 -->
<a id="review-ced2c98c7355d922"></a>

The inspected 0.32.0–0.32.3 Memo wrapper agrees. The declared range assumes ordered remaining-account key collection, arbitrary memo bytes and signer/read-only metas, temporary-key cleanup before opaque invoke_signed, duplicate occurrences and the owned program AccountInfo context. Reached reads, allocation and cleanup retain their actual finite effects.
<!-- /registry -->

<!-- registry:review:888d6248f086bfab -->
<a id="review-888d6248f086bfab"></a>

The declared compatible range assumes the selected Token-2022 constructor with the exact 17-case AuthorityType and optional new authority, source metadata/signature flags and account order account_or_mint, current_authority. Keep the actual copied program_id, complete context and instruction ownership, nested signer seeds, modern unit-Borsh ProgramError boxing and all invocation/cleanup exits. Remaining accounts are not silently appended; the older owned-program AccountInfo family is distinct. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:bd5e8b3bd31efc45 -->
<a id="review-bd5e8b3bd31efc45"></a>

The declared compatible range assumes ATA/System IDs, ordered wallet/token-program/mint PDA seeds, canonical metadata flags and create byte 1. Forward the supplied associated AccountInfo even if its key differs from the derived meta; remaining accounts participate only in cleanup. Preserve MaybeUninit Address output, copied program_id, nested signer seeds, boxed modern errors and every invocation/cleanup effect. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:65590fe59d8cdd02 -->
<a id="review-65590fe59d8cdd02"></a>

The instruction uses fixed ATA and System IDs, wallet/token-program/mint PDA seeds, canonical metadata flags, and source create byte 0 or idempotent byte 1. The supplied associated AccountInfo is forwarded even when its key differs from the PDA-derived instruction meta. Remaining accounts are retained for context cleanup, not appended to the request. Nested signer seeds and every returned invocation state are retained. In 0.32.1 the Pubkey syscall output begins as zero bytes; in 1.x the Address output is MaybeUninit. The old context owns a program AccountInfo; the modern context owns a Pubkey only. Error values use the complete release-specific payload and actual allocated box. Preserve the complete 1.0 operation, reached callbacks and cleanup at the original exact dependency/build gates; adding this alternative does not replace modern parent alternatives. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:14120ae73018a9e4 -->
<a id="review-14120ae73018a9e4"></a>

The declared compatible range assumes ATA/System IDs, ordered wallet/token-program/mint PDA seeds, canonical metadata flags and create byte 0. Forward the supplied associated AccountInfo even if its key differs from the derived meta; remaining accounts participate only in cleanup. Preserve MaybeUninit Address output, copied program_id, nested signer seeds, boxed modern errors and every invocation/cleanup effect. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:4fab62d037533498 -->
<a id="review-4fab62d037533498"></a>

The declared compatible range assumes the selected Token-2022 constructor with amount and decimals, source metadata/signature flags and account order mint, destination, authority. Keep the actual copied program_id, complete context and instruction ownership, nested signer seeds, modern unit-Borsh ProgramError boxing and all invocation/cleanup exits. Remaining accounts are not silently appended; the older owned-program AccountInfo family is distinct. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:22486f5b3260472b -->
<a id="review-22486f5b3260472b"></a>

The declared compatible range assumes the selected Token-2022 constructor with amount and decimals, source metadata/signature flags and account order source, mint, authority. Keep the actual copied program_id, complete context and instruction ownership, nested signer seeds, modern unit-Borsh ProgramError boxing and all invocation/cleanup exits. Remaining accounts are not silently appended; the older owned-program AccountInfo family is distinct. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:64341c00d460e705 -->
<a id="review-64341c00d460e705"></a>

The declared compatible range assumes the selected Token-2022 constructor with amount and decimals, source metadata/signature flags and account order source, mint, destination, authority. Keep the actual copied program_id, complete context and instruction ownership, nested signer seeds, modern unit-Borsh ProgramError boxing and all invocation/cleanup exits. Remaining accounts are not silently appended; the older owned-program AccountInfo family is distinct. This pre-cohort profile stops before the new 1.2.1 provider/feature selection.
<!-- /registry -->

<!-- registry:review:29a47a3a325442ac -->
<a id="review-29a47a3a325442ac"></a>

Preserve the exact token_2022 feature and resolved dependency gates. Token2022::id returns the fixed interface program ID. The wrappers pass ctx.program_id, retain the reviewed account order and move/cleanup effects, and preserve every builder/invocation/error-conversion exit. The older ctx.program.key owner and the later diagnostic-provider family are not relabeled. CPI remains an explicit assumed interface; the range proves no token processor or rollback behavior. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:857d5ab2e3ed8cae -->
<a id="review-857d5ab2e3ed8cae"></a>

Reference source: anchor-spl 0.29.0. Construct the 0.9 Token-2022 transfer_checked instruction before opaque invocation, using the supplied program and ordered from/mint/to/authority accounts. Retain the old context program owner, AccountInfo moves/clones, borrowed signer seeds, boxed Anchor errors and owned legacy ProgramError cleanup. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:79921c60f2695a89 -->
<a id="review-79921c60f2695a89"></a>

Reference source: anchor-spl 0.29.0. Return the fixed two-element [SPL Token, Token-2022] ID array in that order. Retain the 0.29 token_2022 feature and the old nominal Pubkey dependencies; no caller-supplied program key replaces either constant. Compatibility in [0.29.0, 0.30.0) assumes this complete operation and the scoped dependencies remain unchanged; source/ABI/provider obligations stay explicit.
<!-- /registry -->

<!-- registry:review:6e818e4681d4656b -->
<a id="review-6e818e4681d4656b"></a>

The 0.27 wrapper uses solana-program 1.15.2 stake instruction constructors. Deactivate encodes little-endian u32 tag 5 and stake/clock/staker; withdraw encodes tag 4 and the complete u64 amount, with stake/destination/clock/stake-history/withdrawer and an optional custodian signer. Count-5 literal construction owns moved AccountInfos before an optional push. Source cleanup preserves the order of infos-vector, instruction and context drops, including unwinds. Anchor 0.27 converts arbitrary complete legacy ProgramErrors inline, including owned Borsh Strings. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->

<!-- registry:review:61e539634a9f9b24 -->
<a id="review-61e539634a9f9b24"></a>

Reviewed exact immutable wrapper, account aggregate and constructor source. The selected Binding preserves the program owner of this release, move/clone profile, full ProgramError and source cleanup; no version-range inference is used. See source-notes/anchor-spl-token-operations.md for the per-wrapper account orders, size/extension branches and boundary limitations. Compatibility in [0.27.0, 0.28.0) assumes this operation and its selected dependency contracts preserve that behavior; the exact releases remain inspected references.
<!-- /registry -->
