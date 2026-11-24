# Address, Pubkey and derived address profiles

The [source registry](../source-map/solana-address.json) and
[build profiles](../source-map/solana-address.json) keep the immutable source of each operation, defining call identity and build conditions. Inspected
references are separate from the declared compatible ranges below. A
compatible catalog identity does not add a concrete source mapping,
callback certificate or native recording.

| Crate | Inspected references | Operations | Declared compatible range |
| --- | --- | --- | --- |
| `solana-program` | 1.15.2 | `Pubkey::{default, eq, to_bytes, as_ref, create_with_seed}`, Solana `create_program_address`/`find_program_address`, Borsh `serialize`/slice `deserialize` | `[1.15.2, 1.16.0)` |
| `solana-program` | 1.18.26 | `Pubkey::{default, clone, eq, to_bytes, as_ref, create_with_seed}`, Solana `create_program_address`/`find_program_address`, Borsh `serialize`/`deserialize_reader` | `[1.18.26, 2.0.0)` |
| `solana-pubkey` | 2.2.1, 2.4.0 | `as_ref`, Solana `create_program_address`, `create_with_seed`, `default`, Borsh `deserialize_reader`, `eq`, Solana `find_program_address`, Borsh `serialize` | `[2.4.0, 3.0.0)` plus the exact 2.2.1 reference |
| `solana-pubkey` | 2.4.0 | `clone` | `[2.4.0, 3.0.0)` |
| `solana-pubkey` | 2.2.1, 2.3.0, 2.4.0 | array `from`, `new_from_array`, `to_bytes` | `[2.2.1, 3.0.0)` |
| `solana-pubkey` | 2.2.1, 2.3.0, 2.4.0 | `cmp` | `[2.2.1, 3.0.0)` |
| `spl-associated-token-account-client` | 2.0.0 | `get_associated_token_address_with_program_id` | `[2.0.0, 3.0.0)` |
| `solana-address` | 2.6.0, 2.6.1 | Solana `create_program_address` | `[2.6.0, 3.0.0)` |
| `solana-address` | 2.6.1 | Borsh `serialize` and `deserialize_reader` | `[2.6.1, 3.0.0)` |
| `spl-associated-token-account-interface` | 2.0.0 | `get_associated_token_address_with_program_id` | `[2.0.0, 3.0.0)` |
| `solana-loader-v3-interface` | 6.1.1 | `get_program_data_address` | `[6.1.1, 7.0.0)` |

For array `from`, `new_from_array` and `to_bytes`, inspected Pubkey 2.2.1,
2.3.0 and 2.4.0 support the declared range `2.2.1 ≤ v < 3.0.0`. Other
operations retain their own profiles. These ranges do not create an exact
Borsh source mapping: the selected 0.10.4 trait, operation, nominal types,
callback, source environment and whole ABI must still match a reviewed row.
A full build containing both Borsh generations remains ambiguous.

Compatibility assumes that each operation and its relevant providers preserve
the complete reference contract. The eight exact 2.2.1 additions do not fill
the gap below 2.4.0 for those members. Build gates remain explicit; synthetic
range fixtures do not claim inspection or native execution of other releases.

Values contain exactly 32 initialized bytes. Default returns zero; cloning
and byte conversion preserve all bytes; equality compares the whole array.
A borrowed result describes those bytes without manufacturing its pointer,
ownership or lifetime. These remain source representation obligations.

## Seed checks and syscall results

The runtime profile selects `target_os = "solana"` and 64-bit slice counts.
Create PDA checks the number of seeds against 16, then each byte length
against 32, before any provider call. Failure returns `MaxSeedLengthExceeded`.
Seed order, boundaries and empty slices are retained. Pubkey starts its output
at `[0; 32]`, so a successful partial write still leaves initialized bytes.
This is distinct from the uninitialized-output Address family, whose reached
successful reply requires full initialization.

Status zero returns the actual output. Nonzero status 1 becomes `InvalidSeeds`.
The selected Pubkey 2.x and Address 2.6 profiles map status 2 to `IllegalOwner`;
higher statuses reach `Unsupported PubkeyError` or `Unsupported AddressError`
for the selected type. The `solana-program` 1.15.2 and 1.18.26 conversions
instead reach `Unsupported PubkeyError` for every other nonzero status,
including 2. Each conversion starts from the actual syscall return state.
The zero-status error-conversion arm is unreachable after the success branch.
Unwind and terminal replies bypass subsequent local code.

The directly registered Pubkey find forwards the ordered seeds, program ID
and initial bump 255 without a local seed-limit check. Status zero returns the
actual destination and bump,
including bump zero; other statuses reach
`Unable to find a viable program address bump seed`. The host retry loop and
its search order are not substituted for this syscall path.

`create_with_seed` counts UTF-8 bytes, rejects length above 32 before testing
the `ProgramDerivedAddress` suffix of the owner, and calls the actual hashv provider
on base bytes, seed bytes, owner bytes. It wraps the resulting 32 bytes without
a curve test. A cryptographic projection requires its separate returned-hash
agreement; the wrapper assumes neither hash termination nor a SHA body.

The associated-token client forwards wallet, token-program and mint keys as
three ordered PDA seeds under the fixed ATA ID, then discards the bump. Its
reviewed Pubkey 2.2.1 and 2.4.0 dependencies use the same zeroed-output find
path. The wrapper performs no account lookup or CPI and adds no signer,
writable or ownership check.

The associated-token interface keeps that seed order through Pubkey 3.0.0 and
the reexport from Address 1.1.0 to the defining 2.6 release. The loader helper passes
one program-key seed under the fixed upgradeable-loader ID through Pubkey
4.2.0. Their reviewed Address 2.6.0/2.6.1 providers use an uninitialized
destination, with full initialization required at an actual successful reply.
Both helpers discard the returned bump and retain the errors,
panic and effects of the provider. The exact forwarding units are required source facts.
A dependency-name projection or filtered full build does not establish them.

## Exact Borsh selection

Serialize makes one actual `W::write_all` call for the 32-byte field. Each
selected `deserialize_reader` starts a zeroed array and calls the actual
`R::read_exact`, including an override. Success returns that complete array. Both callbacks retain
partial effects, errors, unwind states and terminal reasons.

The `solana-program` 1.15.2 profile selects Borsh and Borsh derive 0.9.3.
Its slice `deserialize` rejects fewer than 32 bytes with `InvalidInput` and
`Unexpected length of input` before advancing the cursor. Success copies the
first 32 bytes and advances exactly 32, preserving the suffix. It performs no
reader callback.

The selected `solana-program` 1.18.26 reader and writer bind Borsh 0.10.4.
The reference Borsh 0.10.4 reader maps `UnexpectedEof` to
`InvalidInput` with `Unexpected length of input`. It constructs the replacement
before destroying the original error. Both operations use outcome-producing
callbacks: successful allocation and the destructor of a custom error payload can
change shared state, and destruction can unwind after `read_exact` returned
normally. Constructor unwind cleans the original error; a later destructor
unwind uses the selected return-place handling. The pinned rustc retains the
already constructed return place on that path (rust-lang/rust#47949). The
return-place callback must match the selected lowering. A second unwind reaches the
explicit terminal policy. Success and non-EOF errors invoke none of these
callbacks, and preserve the actual `read_exact` return state.
That profile cannot describe the `InvalidData` result of a linked 1.x reader.
The selected Address 2.6.1 reader uses Borsh 1.6.0 and maps
`UnexpectedEof` to `InvalidData` with the same message and cleanup order.
Select each call by its exact trait item, implementation, complete generic
arguments and Borsh generation. A reviewed finite source mapping may establish
that selection; bare Rust item paths or the presence of another generation do not.
Whole-build ambiguity remains rejected, and filtering out a candidate is not
evidence of the actual dependency edge.

For a concrete binding, select the actual slice `read_exact` override or the
actual writer receiver: Anchor `BpfWriter`, the private packed-length counter,
std `Cursor` or a mutable slice. The source descriptions, both generic
argument lists, selected array callee, I/O and error callbacks, compiler,
features, cfg, profile and build/source seals remain separate obligations.
A source binding for the counter must establish the actual receiver resources and returned postcondition, and reject changed call arguments, callbacks and build facts.
The [Pubkey catalog controls](../SolanalibTest/Specs/SolanaPubkey/Address.lean) and
[Address catalog controls](../SolanalibTest/Specs/SolanaAddress/Address.lean) check actual
compatible-release identities and reject missing features, other Borsh
generations and whole-build ambiguity. Range eligibility does not change
the exact selected calls above or their required dependency versions.

The six Program 1.18.26/Borsh 0.10.4 selections require separate source bindings: one slice reader and the Vec, BpfWriter, Cursor, WriteCounter and mutable-slice writers. Each binding must retain the complete set of data definitions used by the selected calls and reject an ambiguous complete build description.

The exact Pubkey 2.2.1 slice reader and its BpfWriter, Cursor and Vec writers
need the same source-selection checks as the 2.4.0 selections. Each concrete
binding must establish the selected source identity and complete argument and
result layouts. An assumed mapping remains conditional: it alone does not
establish the availability of a selected release or callback. Callback and
error-resource contracts remain separate requirements.

The [binding obligations](../BINDINGS.md) retain the actual receiver,
reader/writer resources, state effects, source ABI and target interpretation.
Solana cfg does not establish SBF layout equivalence. Source comparison and
mathematical witnesses prove no SDK, IO, compiler or cryptographic body.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:c015efbed86dc671 -->
<a id="review-c015efbed86dc671"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Exact versioned mathematical APIs retain closed reference, satisfiability and execution identities. PDA syscall families require SuccessInitialized, exactly the local status-zero decoding condition. Try-find preserves each admitted syscall exit; find preserves direct success/abnormal exits and each actual panic continuation after a nonzero reply. Finite find progress needs a finite panic exit only on that reached nonzero branch. Pure search still takes explicit hash/curve functions, with source hash width, integer widths, physical output storage and initialization correspondence left to the Rust binding. The derived Borsh serializer runs the registered Borsh 1.6.1 [T; N] serializer at T = u8, N = 32, which makes one write_all of all 32 bytes; the derived decoder maps Self over the Borsh 1.6.1 [u8; 32] decoder (one 32-byte read, short input InvalidData "Unexpected length of input"). Source anchors support this interpretation, not a Rust body or ABI proof.

Exact versioned mathematical API with closed reference, precondition and (where relation-based) execution witnesses. Source anchors support the value/request interpretation; they do not establish a Rust body or ABI proof.

Both exact releases derive Ord for the sole [u8; 32] field. Rust array ordering compares unsigned bytes in increasing index order; the first difference determines Less or Greater and equal arrays produce Equal. The model retains the native state. A Rust binding must additionally preserve both shared key permissions and the same caller world.

The shared families preserve exact value bytes, source guard and seed order, destination initialization, profile-specific error conversion, and actual callback state and exits. Version wrappers retain their complete family and source-dependent reader error kind. The source review is detailed in source-notes/address-profiles.md.
<!-- /registry -->

<!-- registry:review:8777c082259d9ee8 -->
<a id="review-8777c082259d9ee8"></a>

Every direct API release returns &self.0 as &[u8; 32], preserving all 32 bytes and borrowing the same field. The body is byte-identical; the mathematical model observes contents only, and storage/lifetime correspondence remains separate. Address 0.0.0 is a placeholder without Address. Address 1.1.0 reexports the 2.x public API, whose entire released dependency range was reviewed.
<!-- /registry -->

<!-- registry:review:381b06de65cb1a06 -->
<a id="review-381b06de65cb1a06"></a>

Every direct API release implements AsRef<[u8]> by &self.0[..], preserving length 32 and the same borrowed storage. The body is byte-identical; this concrete Address implementation introduces no arbitrary callback. Address 0.0.0 is a placeholder without Address. Address 1.1.0 reexports the 2.x public API, whose entire released dependency range was reviewed.
<!-- /registry -->

<!-- registry:review:dc046e80c911a861 -->
<a id="review-dc046e80c911a861"></a>

Every direct API release derives Default over the sole [u8; 32] field, therefore returns 32 zero bytes. Transparent representation is unchanged. Optional Copy/frozen-abi/stable-abi/wincode/serde derives do not change this field or the Default operation. Address 0.0.0 is a placeholder without Address. Address 1.1.0 reexports the 2.x public API, whose entire released dependency range was reviewed.
<!-- /registry -->

<!-- registry:review:505edc955f5fce5e -->
<a id="review-505edc955f5fce5e"></a>

All direct releases derive BorshDeserialize on the sole unannotated [u8; 32] field. Borsh 1.6.1 derive emits Ok(Self(<[u8; 32]>::deserialize_reader(reader)?)); its u8 array specialization reads exactly 32 bytes. Every 32-byte value is valid; no curve validation occurs. Success returns input.take 32 with input.drop 32 and preserves the success remainder pointer. Short input yields InvalidData / "Unexpected length of input". The contract uses DecodeMatches, leaving the error remainder unconstrained: std empties it while Borsh nostd_io retains it. This is not an arbitrary Read callback contract. The 1.1.0 facade forwards to the same implementation in every published 2.x dependency release. The retained source closure and ordinary decoding checks establish correspondence for all API-bearing releases under the common error-construction scope.
<!-- /registry -->

<!-- registry:review:8df7000ae1e6ad53 -->
<a id="review-8df7000ae1e6ad53"></a>

Every direct API release derives PartialEq for the sole [u8; 32] field, so equality compares all 32 bytes. The separate address_eq helper introduced in 2.0.0 is not the registered PartialEq operation. Copy feature changes do not change equality. Address 0.0.0 is a placeholder without Address. Address 1.1.0 reexports the 2.x public API, whose entire released dependency range was reviewed.
<!-- /registry -->

<!-- registry:review:e5601d9f2b0eeb4a -->
<a id="review-e5601d9f2b0eeb4a"></a>

Every API-bearing release implements the same pure host search result: seed limits count the added bump; try 255 down through 1, never 0; hash concatenated ordered seeds, bump, 32-byte program ID and ProgramDerivedAddress; accept the first digest whose explicit curve predicate is false; return no answer for invalid seed limits or exhaustion, reaching the fixed no-viable-address panic site. 2.9.0 replaces a fresh Vec/retry with a fixed 16-slice array and an early count check, preserving this mathematical facet while changing host allocations. 1.0.0 uses by-value Hash AsRef rather than Hash.as_ref(), with the same 32 bytes under the reviewed dependency representation. 1.1.0 delegates to its resolved 2.x implementation. This is the existing observation role; it is not complete host or target operational coverage.
<!-- /registry -->

<!-- registry:review:a52bf578c31f49ab -->
<a id="review-a52bf578c31f49ab"></a>

From 2.0.0 through 2.9.0 the selected target branch starts MaybeUninit<Address>, bump 255, passes ordered slices with u64 count and program ID, invokes the actual provider once without local seed-limit checks, reads address/bump only after status zero, and returns None on every nonzero u64 status. The find wrapper reaches its fixed panic provider only after ordinary None, from the actual returned state; abnormal syscall exits bypass it. The host-only 2.9.0 retry-allocation change does not alter this branch. 1.1.0 reexports compatible 2.x wrappers. 1.0.0 starts [0; 32], corresponding to an initialized Some(zero) request, whereas the existing pdaRequest supplies addressOutput = none; an arbitrary indexed provider can distinguish these requests. This request mismatch independently excludes 1.0.0. Its no/partial-write status zero successes are outside current SuccessInitialized, not in-precondition counterexamples.
<!-- /registry -->

<!-- registry:review:73b0ffa3f20afd45 -->
<a id="review-73b0ffa3f20afd45"></a>

At every API-bearing release, the host curve25519 branch passes the exact 32 Address bytes to CompressedEdwardsY::from_slice and returns whether decompress() is Some. Its local Address::is_on_curve body is byte-identical, but the reached target helper changes at 2.2.0; that helper difference is not hidden by this host observation classification. 1.1.0 follows the resolved 2.x type. The explicit mathematical curve predicate and optional normal-register correspondence remain interpretation obligations, not a full SDK postcondition or a cryptography proof.
<!-- /registry -->

<!-- registry:review:e69ef61140704968 -->
<a id="review-e69ef61140704968"></a>

1.0.0 and 2.0.0/2.1.0 have a callable selected-target is_on_curve but reach unimplemented!(), make no curve syscall and cannot match this family. 2.2.0 introduces the curve syscall helper and reexport; every subsequent released closure passes selector 0, the concrete Address full 32-byte AsRef, and null_mut() output to sol_curve_validate_point, returning exactly status == 0 while retaining provider effects and abnormal outcomes. A non-null scratch destination would be a different contract. 1.1.0 follows the chosen 2.x dependency: compatible only at 2.2.0 or later, incompatible at 2.0.0/2.1.0.
<!-- /registry -->

<!-- registry:review:244d888d9ea412ad -->
<a id="review-244d888d9ea412ad"></a>

Every direct API release constructs the one private [u8; 32] field from the exact input array. No padding, truncation, curve check or allocation is inserted. The function body is byte-identical from 1.0.0 through 2.9.0. Address 0.0.0 is a placeholder without Address. Address 1.1.0 reexports the 2.x public API, whose entire released dependency range was reviewed.
<!-- /registry -->

<!-- registry:review:78783e584906532a -->
<a id="review-78783e584906532a"></a>

All direct releases derive BorshSerialize on the sole unannotated [u8; 32] field. Under the existing Borsh 1.6.1 interpretation, the inspected derive emits one field serializer followed by ? and Ok(()); the nonempty u8 array serializer performs exactly one actual W::write_all over all 32 bytes. Ordinary errors, partial writer state, unwind and terminal exits are propagated; the source introduces neither rollback nor a successful-writer assumption. Address 1.0.0 enables Borsh std; 2.x permits nostd_io. 1.1.0 forwards the borsh feature to its resolved 2.x type. Optional Serde is not this operation.
<!-- /registry -->

<!-- registry:review:0cc6ce6fb0de67b9 -->
<a id="review-0cc6ce6fb0de67b9"></a>

The declared compatible range assumes one derived call to the selected Borsh serializer for the sole nonempty [u8; 32] field, reaching exactly one actual W::write_all and preserving its partial writer state, ordinary error, unwind and terminal result without retry or rollback.
<!-- /registry -->

<!-- registry:review:75ed24749002632b -->
<a id="review-75ed24749002632b"></a>

1.0.0 takes self by value and has unconditional Copy; 2.0.0 and later take &self with Copy opt-in. Both bodies return self.0, with identical 32-byte value observation and no destructor on Address. The receiver/ownership difference is preserved as a separate Rust binding obligation; this conclusion does not equate their callable signatures. Address 0.0.0 is a placeholder without Address. Address 1.1.0 reexports the 2.x public API, whose entire released dependency range was reviewed.
<!-- /registry -->

<!-- registry:review:c5c1e5df35c3e341 -->
<a id="review-c5c1e5df35c3e341"></a>

The reviewed sources derive Ord for the sole [u8; 32] field. Array ordering compares unsigned bytes from index zero: the first difference determines Less or Greater, and identical arrays produce Equal. The declared compatible range assumes preservation of this ordering, shared-reference validity, unchanged inputs and state, and absence of allocation or callbacks. The 2.8.0 stable-abi derive change does not alter Ord.
<!-- /registry -->

<!-- registry:review:ac56e80f81509652 -->
<a id="review-ac56e80f81509652"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: The defining derived Default implementation and reached core byte-array initialization return exactly 32 initialized zero bytes and preserve the observed source state, without adding allocation, callbacks, validation or abnormal exits.
<!-- /registry -->

<!-- registry:review:3d46b127d326346f -->
<a id="review-3d46b127d326346f"></a>

The inspected 2.2.1/2.3.0/2.4.0 definitions agree on returning every stored byte without changing source state. The declared 2.x range assumes that value behavior; reference identity, layout and any exact Borsh call binding remain separate. Pubkey 3.0.0 reexports Address and is outside this defining-item range.
<!-- /registry -->

<!-- registry:review:13439dfad7668590 -->
<a id="review-13439dfad7668590"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the actual Borsh 0.10 trait implementation and fixed-array specialization: serialize the single nonempty [u8; 32] through one reached W::write_all, retaining the complete result, partial writer state, errors, unwind and terminal outcomes. Preserve the selected receiver, both generic argument lists and reached callback identity; no success, rollback, other Borsh generation or merely present dependency substitutes for that selection.
<!-- /registry -->

<!-- registry:review:19f34d0ceb2a46b2 -->
<a id="review-19f34d0ceb2a46b2"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Observe all 32 initialized bytes in order and preserve the observed state. The returned pointer, legal shared borrow, source allocation and lifetime remain separate memory interpretation obligations.
<!-- /registry -->

<!-- registry:review:6a3a476823bcd970 -->
<a id="review-6a3a476823bcd970"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the reached hashv boundary and wrapper order: count UTF-8 bytes, reject length above 32 before the owner ProgramDerivedAddress suffix test, hash exactly [base bytes, seed bytes, owner bytes] once, and wrap the returned 32 bytes without a curve test. Keep state, error and abnormal outcomes. The actual hash callback remains indexed, with no termination, successful-hash or cryptographic body assumption.
<!-- /registry -->

<!-- registry:review:aa2f64e2332986a8 -->
<a id="review-aa2f64e2332986a8"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the Solana wrapper and reached runtime interface: check seed count above 16 before any per-seed length above 32, return MaxSeedLengthExceeded before the provider on guard failure, then forward the complete ordered slices/program ID once with a zero-initialized 32-byte destination. Status 0 returns its actual bytes, including retained zero bytes after partial writes; status 1 maps to InvalidSeeds, status 2 to IllegalOwner, and other nonzero statuses reach the same Unsupported PubkeyError panic from the reached state. Retain callback effects and every returned, unwound and terminal outcome. Do not replace this family with an uninitialized-output or legacy-status Address family.
<!-- /registry -->

<!-- registry:review:99ec6e885aac4b16 -->
<a id="review-99ec6e885aac4b16"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: The defining derived Clone implementation and reached core array copy preserve every one of the 32 initialized bytes, the source value and observed state; do not add allocation, mutation, validation or borrow acquisition.
<!-- /registry -->

<!-- registry:review:f305efe897dde2d6 -->
<a id="review-f305efe897dde2d6"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the actual Borsh 0.10 trait implementation and fixed-array specialization: start with a zeroed [u8; 32], invoke the reached R::read_exact override once, return its complete resulting array on success, and translate UnexpectedEof to InvalidInput with Unexpected length of input. Preserve all other errors, partial reader state, owned error cleanup, unwind and terminal outcomes. Borsh 1.x InvalidData and the older slice-reader API remain distinct.
<!-- /registry -->

<!-- registry:review:b9f4b57b20f8e3b5 -->
<a id="review-b9f4b57b20f8e3b5"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: The defining PartialEq implementation and reached core array equality compare the entire pair of 32-byte arrays and return true exactly when every byte is equal, preserving the observed state without prefix-only comparison or extra effects.
<!-- /registry -->

<!-- registry:review:aae69cfa3e295e95 -->
<a id="review-aae69cfa3e295e95"></a>

Reference: solana-pubkey 2.4.0. Compatibility in [2.4.0, 3.0.0) assumes that the defining operation and its reached dependencies preserve this behavior: Preserve the Solana try-find wrapper and actual runtime callback: no local seed guard, ordered seeds and UInt64 count, the complete program ID, a zeroed 32-byte output and initial bump 255. Status 0 returns the actual buffer and bump including bump 0; every nonzero status reaches Unable to find a viable program address bump seed from the reached state. Unwind and terminal outcomes bypass later callbacks. The host retry loop is a different branch and is not selected.
<!-- /registry -->

<!-- registry:review:91652df2c8613483 -->
<a id="review-91652df2c8613483"></a>

The inspected 2.2.1, 2.3.0 and 2.4.0 definitions derive unsigned lexicographic ordering of the same 32-byte array. Compatibility within the declared 2.x range assumes this value comparison and borrowed input preservation remain unchanged; 3.0.0 reexports an Address defined elsewhere.
<!-- /registry -->

<!-- registry:review:7cc6e47d2b7c3e09 -->
<a id="review-7cc6e47d2b7c3e09"></a>

The inspected 2.2.1/2.3.0/2.4.0 definitions agree on constructing the defining Pubkey from all 32 input bytes. The declared 2.x range assumes that value behavior; reference identity, layout and any exact Borsh call binding remain separate. Pubkey 3.0.0 reexports Address and is outside this defining-item range.
<!-- /registry -->

<!-- registry:review:7b5bb8ed33707a6f -->
<a id="review-7b5bb8ed33707a6f"></a>

The inspected 2.2.1/2.3.0/2.4.0 definitions agree on copying the complete input [u8; 32] into the defining Pubkey carrier. The declared 2.x range assumes that value behavior; reference identity, layout and any exact Borsh call binding remain separate. Pubkey 3.0.0 reexports Address and is outside this defining-item range.
<!-- /registry -->

<!-- registry:review:a2169aef50eb4062 -->
<a id="review-a2169aef50eb4062"></a>

The declared compatible range assumes the selected Solana syscall branch, ordered seed slices and program key, a MaybeUninit output whose initialization is required only on syscall success, exact status conversion and every callback state or abnormal exit. The host hashing/retry implementation is a separate branch.
<!-- /registry -->

<!-- registry:review:df5973550f5e654d -->
<a id="review-df5973550f5e654d"></a>

The declared compatible range assumes zero-initialization of the local 32-byte array followed by one actual R::read_exact, including user overrides. Success returns the entire resulting array; UnexpectedEof becomes the Borsh 1 InvalidData error with the exact Unexpected length of input text, while other errors, reader state and abnormal exits are retained.
<!-- /registry -->
