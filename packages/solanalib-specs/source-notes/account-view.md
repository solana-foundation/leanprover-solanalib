# AccountView function models

These mathematical contracts cover selected AccountView 1.0.0 and 2.0.0
observations, local mutations, data borrows and guard lifecycles, plus v1
resize. The exact function list of each version is in the
[source registry](../source-map.json). Shared contracts live in one
`Solanalib.Specs.SolanaAccountView` root; release-specific behavior has a named variant.
Rust implementation proofs,
executable Rust clients and invocation implementations remain outside this
package.

## Reviewed source

| Crate | Immutable SDK revision | Complete `src/lib.rs` SHA-256 |
| --- | --- | --- |
| [solana-account-view 1.0.0][v1] | `21fea2733e9f53f719253960cbf4e2dbc725f404` | `878e1130939b68f4fd1bc613169e73273690464a787ff13c04afc9d50e3ddb8f` |
| [solana-account-view 2.0.0][v2] | `1666707490c6c29e6e2edf69e2122b7cae3c9dbb` | `ef348c8f7214861389222600eb5dbef578383c4fc07abc5dd07d7ab921e6b74e` |

The argument below comes from these ordinary SDK Rust sources. The source
registry binds their hashes and anchors to canonical model declarations,
witnesses and mathematical controls.

## Shared state and version instantiations

`Solanalib.Specs.Core.AccountViewData` represents current account contents:
metadata, owner, working balance, logical length, entry length, physical backing
bytes, the v1 signed resize counter and an owner-reference generation.
`Solanalib.Specs.Core.AccountView` uses `Borrow.State Account Slice`; it does not
implement another resource registry. Equal handles denote the same cell.
`Borrow.Policy.accountView` admits at most 254 shared guards, matching source
borrow byte 255 for free, 0 for exclusive, and `255 - n` for `n` shared guards.

`AccountViewFacts`, `AccountViewProjection` and `AccountViewLifecycle` prove
the connections between current account contents, the common lease registry and
the byte observations. `AccountViewGuard`, `AccountViewMap` and
`AccountViewMapLaws` supply generic dereference, destruction and callback
semantics. `AccountViewWitness` supplies closed inhabited account instances.
The `Basic` and `Guard` modules instantiate these shared definitions for every
registered compatible release, using the pinned library sources and model tests.

`AccountViewRevisionData` supplies the v1 profile and resize data.
`AccountViewRevision` defines the signed resize and revision-dependent close
operations and contracts; `AccountViewRevisionFacts`,
`AccountViewRevisionLifecycle` and `AccountViewRevisionWitness` supply their
corresponding results. The shared `closeHeader` operation describes v2 close
directly, without a revision parameter.

The complete pool models live under `Solanalib.Specs.SolanaAccountView.AccountView.Pool`;
the six single-account observation contracts live under
`Solanalib.Specs.SolanaAccountView.AccountView.Observation`. The close variants are
`close_with_resize_delta` and `close_header`. Both releases use the shared
generic guard contracts under `Ref` and `RefMut`.

The complete `try_borrow_contract` and `try_borrow_mut_contract` return
identified guards. The cell and mode of the guard remain associated with a stable registry
identity. An ownership generation changes on a move through mapping and on
destruction. Consumed tokens cannot dereference or regain ownership when a
later acquisition occurs. Registry entries are a mathematical representation of
owned Rust guards, not freely duplicable Rust permissions.

## Observations and local mutations

`clone` preserves account identity. `address` returns an `AddressRef` to the
same cell. The v1 `owner` returns an `OwnerRef` with the current owner generation;
using it requires `OwnerRef.Valid` at the point of use. A modeled close advances
that generation and invalidates previous owner references. A source binding
must also account for any owner mutation performed by code outside these
selected operations; data-borrow counts do not establish owner-reference
validity.

`lamports`, `data_len`, `is_data_empty`, `is_signer`, `is_writable` and `owned_by`
require only `State.HasAccount`: the selected handle must have a current cell.
Their posts exhibit the actual lookup of that cell, the corresponding field value
or owner comparison, and the unchanged pool. This matches the scalar loads in
the pinned v2 source at lines 144–175 and 198–200; `is_data_empty` calls
`data_len` at lines 191–193. Each release admits only its registered subset through the
shared catalog. Source flag bytes
are interpreted by their nonzero Boolean observation. A signer or writable
observation alone supplies no authority.

`set_lamports` immediately replaces the working balance in the shared
cell. Its replacement post requires an existing cell; the mathematical equation
holds for every `Nat`. The source performs no signer, writable or ownership check in this
method. The model therefore preserves these metadata fields without requiring
them to authorize the local write. The Rust `u64` bound, conservation and runtime
permission checks remain separate source and boundary obligations.

The scalar references remain total mathematical functions, but their
`Account.empty` fallback on an absent handle is outside the admission of the scalar contracts and cannot satisfy the real-cell posts. Descriptor constructors and
raw checked-acquisition contracts retain their existing unrestricted input
domains, including the acquisition error for a missing handle. `HasAccount`
does not require `Ready`, source-width bounds or unrelated account validity.
Those stronger representation and physical-access obligations remain separate;
`Ready` is used by theorems about pool validity and represented observations.

The byte-length and read-after-write lemmas use data/backing containment and
the selected range, without unrelated header bounds. Header-preservation
lemmas take only the bounds of fields they preserve. Successful acquisition
itself supplies the presence of the account for the current-byte result.

In v1, the selected mutations use `&self`; v2 uses `&mut self` for
`set_lamports`, `try_borrow_mut` and `close`. These signatures impose distinct
Rust receiver obligations. Neither signature proves global uniqueness of the
pointed-to account, since multiple AccountView values can denote the same raw
account. The mathematical handle model preserves those aliases.

## Guard use, mapping and destruction

Dereference returns a `DataRef` carrying its guard token and access mode.
Constructing this descriptor does not establish a readable target: a consumed
token still fails when read. Its interpreted read uses current contents. The byte specialization
has a current `Slice`, so mutations are visible immediately; release performs
no delayed copyback. Same-size byte writes preserve the pool and valid view.
Destruction consumes one shared lease or the exclusive lease while preserving
all current account and captured contents. Its successful post requires only
that the guard resolve to a live registry slot. Target validity and the full
pool invariant remain premises of the results that preserve valid references.

The primary `Ref` and `RefMut` contracts are closed indexed `Family` values.
The index supplies arbitrary target descriptors, captured state and their
validity and footprint interpretation. A descriptor can encode a typed field,
a byte range, or external/static storage. Source and result reference types
need not be identical. Their interpretation must justify the permissions of the returned target independently of the retained original account lease.

The callback relation ranges over the entire account pool and captured state.
`CallbackSafe` quantifies over every finite callback exit. Returned exits need
the callback frame, pool validity and a valid returned target; unwinding exits
need the frame and pool validity. Terminal exits have no resulting world or
target-validity requirement. The common `Borrow.tryMap` relation forwards every finite callback exit;
its validity and history theorems require universal `MapCallback.Admissible`.
`CallbackSafe.admissible` supplies that premise to the source reference proof.
The mapping contract requires a live slot, its account cell, the selected lease
mode and `CallbackSafe`. It does not additionally require initial pool or target
validity: its callback premise supplies the final validity used by the post.
A source binding must separately justify the input reference of the callback.
At such a live input, `genericTryMap_of_callback` and
`genericTryMap_hasOutcome_iff` establish retention of the finite exits of the callback.
The shared frame preserves live guard identity, history and policy, and the
supplied reference footprint. It permits captured effects on other cells and
storage. In the byte profile, a shared callback preserves its held bytes but may
change unrelated header fields; an exclusive callback may write its data immediately.

On successful mapping, the new target retains the original lease and receives
the next ownership generation. On ordinary `try_map` failure, the result is
`Err (originalGuard, error)` in the order of the source. The original target is
returned under the new generation, and every callback mutation remains in the
world. An error is not a rollback. `Ref::map` uses the same protocol with an
empty ordinary-error type.

Both reviewed versions put the consumed guard in `ManuallyDrop` before calling
the closure. Accordingly, the source mapping contracts select the common
`retainLease` unwind policy: a finite unwind retains the lease and current
callback world, consumes the old token, and returns no guard. A terminal outcome
carries no fabricated final state. Divergence has no finite outcome. Whether a
particular Rust profile can unwind, abort or return remains a source binding;
the generic model does not assume callback termination.

## Close and v1 resize

`close` rejects every live data lease. Success zeros owner, balance and logical
length, invalidates old owner references, and leaves every physical data byte
unchanged. In v1, it additionally subtracts the old logical length from the
signed resize counter. The v2 model leaves its unobserved counter ghost
unchanged, reflecting the absence of that source update. The shared
`closeHeader` operation preserves the entry-length and length-delta fields.
The v2 contract requires a present account only on the unborrowed update
branch; the borrow-failure branch needs no unrelated account-validity premise.
Closing a nonzero working balance is a possible local SDK effect; it does not establish a
successful, balanced instruction at the runtime boundary.

The revision-specific close and resize branch contracts require an existing
account cell and a defined source `i32` computation. Where v1 resize reaches its
signed arithmetic (a free lease and a converted length), `data_len as i32` must
be exact and, for a changed length, `resize_delta + (new_len - data_len)` must
fit `i32` (`ResizeArithmetic`). Where v1 close reaches its signed update (a free
lease), `data_len as i32` must be exact and `resize_delta - data_len` must fit
`i32` (`CloseArithmetic`; v2 close has no such update). On other headers the
source conversion wraps or its arithmetic overflows, which panics with
overflow checks, and the returning models describe neither. The loader never
creates such a header, but `AccountView::new_unchecked` does not exclude one and
`RuntimeAccount::resize_delta` is public; the library conformance suite records
the panics on forged headers. Every `ResizeValid` header satisfies both
conditions (`resizeArithmetic_of_resizeValid`, `closeArithmetic_of_resizeValid`).
The reference proofs use account presence to justify the successful cell
update; the contracts do not claim representation or lifecycle preservation.
Separate lifecycle results preserve the pool from `Ready`, and the signed
counter from account presence and `ResizeValid`. Owner-reference invalidation
uses the validity of that reference. The helper lemmas take the specific
integer or byte-range conditions needed for their respective conclusions.

The v1 resize requires a **free** data lease and does not acquire a guard. It
checks borrow conflict first, then conversion to `i32`, then unchanged length,
then the accumulated growth bound of 10,240 bytes. The representation invariant
requires current and entry lengths at most `i32::MAX` and
`resizeDelta = currentLength - entryLength`. The signed bound on the requested length comes from the conversion check of the operation. The mathematical argument
is a `Nat`; interpreting a Rust call separately fixes its `usize` width.
The proved arithmetic bounds show that the modeled subtraction and addition
do not silently overflow on the stated invariant.

The mathematical write can extend its backing list; pool and signed-domain
preservation therefore do not require spare capacity. Preserving the original
physical backing length after accepted growth additionally requires enough
allocated capacity, as `Account.resize_backing_length` states. Relating that
fixed storage to Rust requires the runtime-created-account reserve
assumption of the source. It is neither an SDK capacity check nor a premise of the basic
branch contract. Shrink preserves backing bytes;
regrowth zeroes exactly the newly exposed range. `Account.resize_bytes` proves
that the logical effect equals canonical `Solanalib.Runtime.resizeZero`. This does not
identify the free-lease call convention of the SDK with the separate authorization requirements of the canonical store
operation.

## Observations and validation

Six single-account contracts in
`Solanalib.Specs.SolanaAccountView.AccountView.Observation` use `State`, `BorrowResult`,
`Operations`, `Spec` and the reference bundle. Getter and acquisition arguments
have type `Unit`; the setter argument has type `Nat`. Acquisition returns a byte
projection. The registry records these supporting observations and selects the
complete `AccountView.Pool` contracts for account and guard identities.

The observation setter requires `value < U64_LIMIT`, and both acquisitions
require `before.Valid`. These premises define the admitted inputs even though
the mathematical references work on a larger domain. The AccountView composition
scenario checks their use in a client proof.

The shared observation results `Spec.setLamports_valid`, `Spec.tryBorrow_valid`
and `Spec.tryBorrowMut_valid` prove that every conforming implementation
preserves the full observation invariant, on success and on borrow failure.
The integer bounds, byte lengths and lease counts support this invariant and
therefore subsequent calls. A client composes a bounded write and a shared
acquisition; another accepted setter deliberately ignores out-of-range inputs.
The pool projection lemmas remain narrower: the shared projection needs the
selected cell and its AccountView policy, and the mutable projection needs only
the selected cell. They do not require the complete pool invariant.

`observe_valid`, `scalar_observations`, `setLamports_observation`,
`shared_acquisition_projection` and `mutable_acquisition_projection` connect
them to the complete model. `acquisitionBytes_current` relates the returned
byte observation to the current contents of the fresh guard. These projections
intentionally discard the guard token and cannot by themselves specify its
later mapping, writes or destruction.

Every pool or observation declaration has an exact named reference and
closed reference/satisfiability witnesses. Each generic family proves reference
correctness for every index and names an explicit sample with a permitted
finite reference execution. The proof census audits these exact declaration,
reference and sample identities and rejects additional witness parameters.

The mathematical controls cover alias observations, conflicting borrows,
immediate writes, release and reacquisition, close without byte erasure, and
v1 signed resize/check precedence.
They also check the wide mathematical balance update, consumed-token read and
release failures, missing-handle acquisition, and the necessary conditional
byte-availability premise in the observation projection.
Callback controls cover shared captured
header effects, mutable writes preserved on error, retained-lease unwind,
terminal exits, and a mapped external target with an independent permission
failure control. Observation controls check the single-account types and
client proofs, equality with the shared contracts, and the connection
to current pool acquisition results. These are Lean model compositions, not
compiled Rust clients.

The package audit checks the registered source hashes, declarations and
witnesses; see [the validation commands](../README.md#build-and-audit). Remaining
implementation obligations include runtime account representation, exact
word widths and profiles, physical reference lifetimes and alias permissions,
valid pointer/guard construction, callback interpretation, and correspondence
between the selected Rust bodies and these mathematical transitions. CPI invocation remains opaque and
supplies no success or state-effect guarantee.

[v1]: https://github.com/anza-xyz/solana-sdk/blob/21fea2733e9f53f719253960cbf4e2dbc725f404/account-view/src/lib.rs
[v2]: https://github.com/anza-xyz/solana-sdk/blob/1666707490c6c29e6e2edf69e2122b7cae3c9dbb/account-view/src/lib.rs

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:845ff4bcc6974c0e -->
<a id="review-845ff4bcc6974c0e"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Versioned public aggregate of the reviewed mathematical models.

Instantiate the shared mathematical operations for this exact SDK version; keep closed reference, precondition and execution witnesses in the public version namespace.

The five Ref-backed contracts instantiate the constructor and operation-specific read domains. Their posts strengthen the unchanged raw computations with checked current-view decoding. The original guard, reference, sample and witness identities remain; physical source memory and lifetime correspondence is separate.

The four generic instruction contracts instantiate universal reached-prefix admission and retain every finite raw execution with an additional checked-current-memory derivation. Actual Deref calls, callback effects, raw computations and named reference/sample/witness identities remain unchanged.

The versioned from_account_view contract requires Rent111ReadReady and preserves the pool while returning Rent111ReadResult: an actual selected cell and the ordered borrow/address error or complete eight-byte rate read. The reference proof consumes both cell presence and the reached byte bound; its exact closed satisfiability and execution identities are preserved.

The signature families retain concrete source preparation and canonical Agave CPI stages. Borrowed and owned stable-instruction contracts are separate; checked signatures use the first matching AccountInfo and the shared lease world. C and Rust raw declarations share the runtime family but require distinct pointer-layout interpretations. Closed consistency witnesses use declared mock callee results only.

Allocation-free aligned loader deserialization into the initialized prefix of a caller-owned array; exact duplicate header aliases, skipped account parsing, full input preservation and instruction/program views. The registered reference is the graph of the byte parser and source-ordered state transformation. Closed witnesses and native fixture replay are separate from the concrete source assumption. The account bridge installs the exact header identities into PinocchioAccount.State, retaining raw flags, signed resize delta and hidden data bytes. Nonzero resize histories require the separate validity condition of the account API.

The complete reviewed functions are interpreted by the registered shared mathematical families and current-state references. All ordinary, error, callback and reached terminal outcomes are retained. Pin-specific borrow credits and signed resize stages, and logger initialized-prefix state and cleanup, are explicit; generic source representation remains separate.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

The source-owned pinocchio::syscalls::sol_get_clock_sysvar facade uses the same complete mathematical contract and reference as the inherited solana-define-syscall::definitions::sol_get_clock_sysvar family. Its exact defining source profile is kept separately. The checksum-pinned pinocchio 0.9.2 source defines this exact item with the recorded argument order and result type. The source supplies an extern-C declaration, not a runtime implementation. The reviewed macro/module gates are recorded explicitly; macro expansion does not transfer defining-crate ownership.

The raw C declaration is defined by Pinocchio itself. Dynamic raw CPI external declaration: exact pointer/count ABI, zero normal status after canonical success, and canonical/metering terminal outcomes; runtime invocation and callee remain assumed interfaces.
<!-- /registry -->

<!-- registry:review:42eb0b9a3501309d -->
<a id="review-42eb0b9a3501309d"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The 2.0.0 roots instantiate the shared contracts with exact access modes, result order and close behavior. Nine AccountView.Pool models retain account identity; seven Ref/RefMut families retain guard identity and lifecycle. The six single-account observations admit these inputs: value < U64_LIMIT for the setter, State.Valid for both borrows and True for getters. Generic preservation lemmas justify subsequent calls for every conforming implementation. The original client and an implementation that ignores out-of-range setter inputs check compatibility. Closed reference, satisfiability and named execution identities are preserved.

The 1.0.0 source-facing root instantiates the shared mathematical contracts with its shared receivers, signed close/resize behavior and required reference access modes. All contracts have closed reference and satisfiability witnesses; generic families also have a named finite sample execution. The nonfallible map Family, reference and closed samples are registered here with their first SDK consumer; they retain the shared callback-admission and guard-transfer semantics.
<!-- /registry -->

<!-- registry:review:3c98a61c49583f7c -->
<a id="review-3c98a61c49583f7c"></a>

The full existing getter contract agrees at every 0.10.x, 0.11.x and 0.12.0 release: the Clock ID, offset 0, length 40, MaybeUninit destination, success initialization requirement and status converter (0 success, 1 InvalidArgument, all other statuses UnsupportedSysvar) are unchanged. Every actual provider exit/effect is forwarded under the existing relation. 0.1.0–0.8.3 instead start from Default and invoke the typed clock syscall with ProgramError conversion; 0.8.4 changes to MaybeUninit but retains that call/converter. 0.9.0–0.9.2 use the typed syscall and fold all errors; 0.9.3 uses the generic request but still folds status 1 to UnsupportedSysvar. 0.12.0 adds the bpf-only generic-getter cfg branch, while the already required target_os=solana profile is unchanged. The 0.0.0 crate is a placeholder.
<!-- /registry -->

<!-- registry:review:a134057fa08f1e44 -->
<a id="review-a134057fa08f1e44"></a>

Every API-bearing release from 0.8.1 through 0.12.0 evaluates the first Deref for length, the second for the current data pointer, and only after the second return subtracts two and reads a bytewise little-endian footer. There is no current-index/count validation. This order preserves arbitrary supplied Deref effects and abnormal prefixes, including an empty first result followed by a second-call panic; later read obligations are not imposed on that prefix. The AccountView dependency transitions do not constrain the generic T contract.
<!-- /registry -->

<!-- registry:review:1f44b0bb1504f09d -->
<a id="review-1f44b0bb1504f09d"></a>

0.8.1, 0.8.2, 0.8.3 and 0.8.4 perform the first count read as native u16 and require alignment 2. Existing AtReady admits that count read at alignment 1, including immediate out-of-range errors; adding alignment would weaken the full applicability question, so those releases are incompatible despite all aligned samples passing. From 0.9.0 the count is read bytewise little-endian. Out-of-range returns InvalidInstructionData after only the first Deref; success performs a second Deref for the table entry and a third for the resulting pointer plus the saved offset. All effects/prefix failures remain ordered. The native-u16 table read through 0.11.2 uses existing alignment 2/little-endian assumptions. 0.12.0 switches that read to bytewise LE, which enlarges the source domain but remains compatible with the existing stronger table admission. Returned pointers may be one-past or arise from an empty third slice with zero offset; body readability belongs to later accessors.
<!-- /registry -->

<!-- registry:review:3257e6e01c555e2e -->
<a id="review-3257e6e01c555e2e"></a>

This is the supporting specialization over a live captured solana-account-view::Ref, not an independent callable binding. It exists at 0.10.0, 0.10.1, 0.10.2, 0.11.0, 0.11.1, 0.11.2 and 0.12.0. Earlier internal AccountInfo/Ref types are API-absent for this particular specialization. Its existing captured-slice/readiness and shared-lifetime assumptions are preserved. Ref deref returns the saved slice without changing availability, and the wrapper/guard drop increments availability exactly once. The source generic operation has this argument: Every API-bearing release from 0.8.1 through 0.12.0 evaluates the first Deref for length, the second for the current data pointer, and only after the second return subtracts two and reads a bytewise little-endian footer. There is no current-index/count validation. This order preserves arbitrary supplied Deref effects and abnormal prefixes, including an empty first result followed by a second-call panic; later read obligations are not imposed on that prefix. The AccountView dependency transitions do not constrain the generic T contract.
<!-- /registry -->

<!-- registry:review:aad46ea0db4adaec -->
<a id="review-aad46ea0db4adaec"></a>

This is the supporting specialization over a live captured solana-account-view::Ref, not an independent callable binding. It exists at 0.10.0, 0.10.1, 0.10.2, 0.11.0, 0.11.1, 0.11.2 and 0.12.0. Earlier internal AccountInfo/Ref types are API-absent for this particular specialization. Its existing captured-slice/readiness and shared-lifetime assumptions are preserved. Ref deref returns the saved slice without changing availability, and the wrapper/guard drop increments availability exactly once. The source generic operation has this argument: 0.8.1, 0.8.2, 0.8.3 and 0.8.4 perform the first count read as native u16 and require alignment 2. Existing AtReady admits that count read at alignment 1, including immediate out-of-range errors; adding alignment would weaken the full applicability question, so those releases are incompatible despite all aligned samples passing. From 0.9.0 the count is read bytewise little-endian. Out-of-range returns InvalidInstructionData after only the first Deref; success performs a second Deref for the table entry and a third for the resulting pointer plus the saved offset. All effects/prefix failures remain ordered. The native-u16 table read through 0.11.2 uses existing alignment 2/little-endian assumptions. 0.12.0 switches that read to bytewise LE, which enlarges the source domain but remains compatible with the existing stronger table admission. Returned pointers may be one-past or arise from an empty third slice with zero offset; body readability belongs to later accessors.
<!-- /registry -->

<!-- registry:review:e4e487739ba6ff62 -->
<a id="review-e4e487739ba6ff62"></a>

The reviewed AccountView/solana-account-view::Ref specialization exists at all seven releases 0.10.0–0.12.0. It compares the Instructions address first, returning UnsupportedSysvar without borrowing on mismatch, then calls try_borrow and propagates AccountBorrowFailed. Shared state >= 2 is decremented once and a captured slice is stored; ordinary drop restores that lease. No instruction serialization or footer validation occurs, so zero- and one-byte captured data are successful constructor cases. AccountView 1.0.0, 2.0.0/2.1.0 and 3.0.0 preserve these shared guard semantics. Earlier AccountInfo/internal-Ref constructors are distinct specializations and are API-absent for this AccountView contract.
<!-- /registry -->

<!-- registry:review:6e4a5c83a23c0e27 -->
<a id="review-6e4a5c83a23c0e27"></a>

All 15 releases from 0.8.1 through 0.12.0 read the two-byte LE metadata count, read the two-byte LE data length at offset 2 + 33 * count + 32, and borrow the full slice beginning two bytes later. Empty output still requires both earlier scalar reads and permits a one-past start. Metadata renaming, helper extraction and the transparent Pubkey-to-Address representation preserve these reads and sizes. The output aliases the current storage; it is not copied or normalized.
<!-- /registry -->

<!-- registry:review:06e60640236818df -->
<a id="review-06e60640236818df"></a>

All 15 releases from 0.8.1 through 0.12.0 read a two-byte LE metadata count and borrow the complete 32-byte program region at offset 2 + 33 * count. Older inline count reads and the later num_account_metas helper have identical reached reads. IntrospectedAccountMeta is renamed IntrospectedInstructionAccount in 0.10, but the repr(C) flags-plus-key size stays 33. Pubkey=[u8;32] becomes Address, whose reviewed 2.x representation is transparent [u8;32] with alignment 1. The raw-pointer field becomes private in 0.11 and lifetime spelling is made explicit without changing the borrowed output. Physical provenance/reference permissions remain the existing Rust binding obligations.
<!-- /registry -->

<!-- registry:review:7a9a26b21ad22bf5 -->
<a id="review-7a9a26b21ad22bf5"></a>

This is the supporting specialization over a live captured solana-account-view::Ref, not an independent callable binding. It exists at 0.10.0, 0.10.1, 0.10.2, 0.11.0, 0.11.1, 0.11.2 and 0.12.0. Earlier internal AccountInfo/Ref types are API-absent for this particular specialization. Its existing captured-slice/readiness and shared-lifetime assumptions are preserved. Ref deref returns the saved slice without changing availability, and the wrapper/guard drop increments availability exactly once. The source generic operation has this argument: All 15 releases from 0.8.1 through 0.12.0 read the two-byte LE metadata count, read the two-byte LE data length at offset 2 + 33 * count + 32, and borrow the full slice beginning two bytes later. Empty output still requires both earlier scalar reads and permits a one-past start. Metadata renaming, helper extraction and the transparent Pubkey-to-Address representation preserve these reads and sizes. The output aliases the current storage; it is not copied or normalized.
<!-- /registry -->

<!-- registry:review:616784e36ca090e8 -->
<a id="review-616784e36ca090e8"></a>

This is the supporting specialization over a live captured solana-account-view::Ref, not an independent callable binding. It exists at 0.10.0, 0.10.1, 0.10.2, 0.11.0, 0.11.1, 0.11.2 and 0.12.0. Earlier internal AccountInfo/Ref types are API-absent for this particular specialization. Its existing captured-slice/readiness and shared-lifetime assumptions are preserved. Ref deref returns the saved slice without changing availability, and the wrapper/guard drop increments availability exactly once. The source generic operation has this argument: All 15 releases from 0.8.1 through 0.12.0 read a two-byte LE metadata count and borrow the complete 32-byte program region at offset 2 + 33 * count. Older inline count reads and the later num_account_metas helper have identical reached reads. IntrospectedAccountMeta is renamed IntrospectedInstructionAccount in 0.10, but the repr(C) flags-plus-key size stays 33. Pubkey=[u8;32] becomes Address, whose reviewed 2.x representation is transparent [u8;32] with alignment 1. The raw-pointer field becomes private in 0.11 and lifetime spelling is made explicit without changing the borrowed output. Physical provenance/reference permissions remain the existing Rust binding obligations.
<!-- /registry -->

<!-- registry:review:762bb8549e987fd9 -->
<a id="review-762bb8549e987fd9"></a>

The AccountView API starts at 0.10.0. Its 0.10.x implementation checks the Rent key first, acquires a shared Ref and returns a borrowed 16-byte Rent. Starting at 0.11.0 it checks exclusive borrowing first (AccountBorrowFailed), checks the key second (InvalidArgument), then reads eight bytes unaligned into an owned value. It does not acquire a guard or alter borrow state, even with 254 shared leases. 0.11.0, 0.11.1, 0.11.2 and 0.12.0 preserve this complete reached-read/resource contract; malformed short data is admitted only on earlier error paths. Older from_account_info APIs are distinct and do not supply this AccountView operation.
<!-- /registry -->

<!-- registry:review:902a6f042689d6a3 -->
<a id="review-902a6f042689d6a3"></a>

try_minimum_balance is absent through 0.9.3. 0.11.0, 0.11.1, 0.11.2 and 0.12.0 use an 8-byte rate and independent ordered guards for data length <= 10485760 and rate <= 1759197129867; these bounds make (128 + data_len) * rate fit u64. Checked and wrapping profiles therefore agree. 0.10.x instead carries threshold bytes, lacks the unconditional rate check and can overflow/panic; it does not satisfy this complete contract.
<!-- /registry -->

<!-- registry:review:438a2d59c2661008 -->
<a id="review-438a2d59c2661008"></a>

Only 0.10.0, 0.10.1 and 0.10.2 retain the modeled 16-byte rate-plus-threshold representation, Rent ID, offset 0, length 16 and the generic getter status converter. Earlier releases through 0.9.2 invoke the typed Rent syscall using a 24-byte rate/f64/burn layout; 0.9.3 requests 17 serialized bytes and zeroes seven trailing padding bytes, and still folds every nonzero status. Starting at 0.11.0 Rent contains only an owned 8-byte rate and requests eight bytes. These differences change the provider request/value contract even when selected numerical balances happen to agree.
<!-- /registry -->

<!-- registry:review:74b7f91684683138 -->
<a id="review-74b7f91684683138"></a>

try_minimum_balance is absent before 0.10.0. All three 0.10.x releases retain the full branch structure: data length at most 10 MiB; the 879598564933 rate check applies only to threshold 2; its following else-if test against 1759197129867 is unreachable, so threshold 1 and arbitrary threshold bits are not rate-guarded. minimum_balance_unchecked preserves threshold-specific integer multiplication order, checked/wrapping overflow, host binary64 conversion/multiplication/cast and the BPF panic for other thresholds. Starting at 0.11.0 the threshold field is removed and an unconditional rate check changes both admitted results and panic/overflow behavior. Existing binary64/profile assumptions are retained, not replaced by a default-rent restriction.
<!-- /registry -->

<!-- registry:review:6911633088aede5f -->
<a id="review-6911633088aede5f"></a>

Every API release reads the current raw data_len and casts u64 to usize. On the represented 64-bit target this is the exact logical length and leaves state unchanged; the source cast must be interpreted explicitly on other word widths. This supporting observation projects one account into a state/result pair: acquisitions return current bytes and hide identities, while AccountView.Pool represents guard and alias lifecycles. Its preconditions specify the input domain of each observation, and its postconditions support invariant preservation. This review records source correspondence for the mathematical contract under its stated interpretation obligations; it does not prove the Rust body or register a callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:daf61cd98549d010 -->
<a id="review-daf61cd98549d010"></a>

Every API release reads the current is_signer u8 and returns whether it is nonzero. Noncanonical bytes such as 2, 127 and 255 normalize to true; the getter supplies no signer authority. This supporting observation projects one account into a state/result pair: acquisitions return current bytes and hide identities, while AccountView.Pool represents guard and alias lifecycles. Its preconditions specify the input domain of each observation, and its postconditions support invariant preservation. This review records source correspondence for the mathematical contract under its stated interpretation obligations; it does not prove the Rust body or register a callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:52ea08bdb7a68d15 -->
<a id="review-52ea08bdb7a68d15"></a>

Every API release directly reads the current u64 balance through raw. Aliased AccountView handles observe the same current cell; no lease or header field changes. This supporting observation projects one account into a state/result pair: acquisitions return current bytes and hide identities, while AccountView.Pool represents guard and alias lifecycles. Its preconditions specify the input domain of each observation, and its postconditions support invariant preservation. This review records source correspondence for the mathematical contract under its stated interpretation obligations; it does not prove the Rust body or register a callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:12bc79a131d9db02 -->
<a id="review-12bc79a131d9db02"></a>

All four API releases replace the raw u64 balance immediately, without checking signer, writable, owner or data-borrow state and without changing other bytes. 1.0.0 uses &self; 2.0.0 and later use &mut self. This receiver distinction is a source-reference obligation and does not alter the complete mathematical replacement post or imply global uniqueness of aliased account handles. This supporting observation projects one account into a state/result pair: acquisitions return current bytes and hide identities, while AccountView.Pool represents guard and alias lifecycles. Its preconditions specify the input domain of each observation, and its postconditions support invariant preservation. This review records source correspondence for the mathematical contract under its stated interpretation obligations; it does not prove the Rust body or register a callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:e536cfb54d1d6d70 -->
<a id="review-e536cfb54d1d6d70"></a>

All four releases check borrow_state < 2 first and return AccountBorrowFailed without change in that branch. Success decrements the byte and returns a Ref to the current complete data slice, retaining the same state-byte pointer. Free=255, exclusive=0 and 255 - n for n shared leases realizes the existing maximum of 254 shared guards; the same generic destructor releases one lease. This supporting observation projects one account into a state/result pair: acquisitions return current bytes and hide identities, while AccountView.Pool represents guard and alias lifecycles. Its preconditions specify the input domain of each observation, and its postconditions support invariant preservation. This review records source correspondence for the mathematical contract under its stated interpretation obligations; it does not prove the Rust body or register a callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:e27b82aa6e8396a3 -->
<a id="review-e27b82aa6e8396a3"></a>

All four releases first require borrow_state = 255, otherwise return AccountBorrowFailed unchanged; success sets the byte to 0 and returns a RefMut to the current complete data slice. The helper pointer changes from a mutable data_ptr in 1.0.0 to data_mut_ptr in 2.0.0+, and the receiver changes from &self to &mut self; the extent, exclusive lease and current-byte behavior remain the same. This supporting observation projects one account into a state/result pair: acquisitions return current bytes and hide identities, while AccountView.Pool represents guard and alias lifecycles. Its preconditions specify the input domain of each observation, and its postconditions support invariant preservation. This review records source correspondence for the mathematical contract under its stated interpretation obligations; it does not prove the Rust body or register a callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:c6041abc86cd991b -->
<a id="review-c6041abc86cd991b"></a>

Every API release returns &(*raw).address; the AccountView raw identity and 32-byte Address representation are unchanged. The model returns an AddressRef descriptor with the same account handle and unchanged state, rather than a copied key. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:8a5bd8311644d3d3 -->
<a id="review-8a5bd8311644d3d3"></a>

All four API releases return &(*raw).address. RuntimeAccount remains repr(C), Address remains a transparent 32-byte array, and the address offset stays 8 on the tested 64-bit layout. The return denotes the same account field, preserves the pool, and acquires no lease or allocation. The v2 padding change and v3 owned owner result do not affect this field reference.
<!-- /registry -->

<!-- registry:review:e70307d75779ab7e -->
<a id="review-e70307d75779ab7e"></a>

AccountView derives Clone over its sole raw pointer field in all four API releases. Cloning copies the account identity without copying account contents, issuing a lease, or allocating. Optional Copy adds no different Clone behavior. The 1-to-2 header revision does not change the pointed-to identity, and tests mutate/borrow through aliases.
<!-- /registry -->

<!-- registry:review:b33b9feba4938e13 -->
<a id="review-b33b9feba4938e13"></a>

2.0.0, 2.1.0 and 3.0.0 have identical reached bodies: reject borrow_state != 255, otherwise zero exactly the 48 owner/lamports/data_len bytes preceding data, leaving every data byte and the four padding bytes unchanged. 1.0.0 additionally computes resize_delta - (data_len as i32), modifying four real header bytes and potentially overflowing. The existing 2.0-root contract has neither that effect nor its arithmetic admission premise. Native Lean comparison rejects five nonempty 1.0.0 close cases; 1.0.0 is incompatible, not silently admitted under a new assumption. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:696f81bbb2dda0cb -->
<a id="review-696f81bbb2dda0cb"></a>

At 1.0.0 close rejects every nonfree borrow byte before arithmetic or writes, then computes resize_delta - data_len as i32 and zeros exactly the 48 bytes for owner, balance, and logical length. The existing HasAccount and CloseArithmetic .v1 premises admit that returning branch; backing bytes remain untouched and owner references are invalidated. In 2.0.0, 2.1.0, and 3.0.0 the signed field is replaced by padding and close performs no signed-counter update. A length-5 account closes with offset-4 value -5 in v1 and 0 in later releases. Keeping the full v1 state/effect excludes those releases rather than replacing its counter with a different ghost interpretation.
<!-- /registry -->

<!-- registry:review:e3bdf2b8b8197b60 -->
<a id="review-e3bdf2b8b8197b60"></a>

Every API release reads the current raw data_len and casts u64 to usize. On the represented 64-bit target this is the exact logical length and leaves state unchanged; the source cast must be interpreted explicitly on other word widths. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:f114d84cf9078a27 -->
<a id="review-f114d84cf9078a27"></a>

All four API releases load RuntimeAccount.data_len and cast u64 to usize; the selected cell and pool are unchanged. The existing contract only requires HasAccount. The tested Solana-source/64-bit profile preserves the u64 value; physical valid data extents and the actual usize width remain source interpretation obligations, not new mathematical preconditions. The offset remains 80 despite the v2 padding revision.
<!-- /registry -->

<!-- registry:review:654023651e7d092c -->
<a id="review-654023651e7d092c"></a>

All four API releases call data_len and test equality with zero. The complete data_len closure and its width/storage interpretation therefore apply. The only 2.0-to-2.1 textual change here removes a comment; the branch, returned Boolean, and unchanged pool are the same.
<!-- /registry -->

<!-- registry:review:f926483df2453ce6 -->
<a id="review-f926483df2453ce6"></a>

Every API release reads the current is_signer u8 and returns whether it is nonzero. Noncanonical bytes such as 2, 127 and 255 normalize to true; the getter supplies no signer authority. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:a9b6e8f4b043e5c6 -->
<a id="review-a9b6e8f4b043e5c6"></a>

All four API releases load the signer byte and compare it with zero. Any nonzero byte observes true, including 2, 127, and 255 in fresh native cases. The current cell is exhibited under HasAccount and the pool stays unchanged. No authentication, borrow, or authority check is introduced.
<!-- /registry -->

<!-- registry:review:32b98921bd656909 -->
<a id="review-32b98921bd656909"></a>

All four API releases load the writable byte and compare it with zero, leaving the pool unchanged. Nonboolean source bytes are observed by nonzeroness, as tested. HasAccount remains the sole mathematical precondition; this observation does not supply write authority.
<!-- /registry -->

<!-- registry:review:73ea6d85e312a73e -->
<a id="review-73ea6d85e312a73e"></a>

Every API release directly reads the current u64 balance through raw. Aliased AccountView handles observe the same current cell; no lease or header field changes. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:145369ea101e00a1 -->
<a id="review-145369ea101e00a1"></a>

All four API releases read the u64 balance at RuntimeAccount offset 72 with no borrow check and no state effect. It is the current shared account cell, including through cloned aliases after set_lamports. HasAccount is unchanged; the source u64-to-Nat interpretation is separate from the unrestricted mathematical value domain.
<!-- /registry -->

<!-- registry:review:3f2e4276f9551f54 -->
<a id="review-3f2e4276f9551f54"></a>

1.0.0 compares the immediately borrowed owner() with program; 2.0.0, 2.1.0 and 3.0.0 compare the owner field directly. All admitted Address 2.x releases are transparent 32-byte arrays with derived PartialEq. Neither branch retains an owner reference or changes state; the unrelated 3.0.0 owner-by-value API change is not reached. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:3c3577460774eec6 -->
<a id="review-3c3577460774eec6"></a>

Version 1 calls owner() and derived Address equality; versions 2.0, 2.1, and 3.0 compare the raw owner field directly. Both compare all 32 bytes of the current owner and preserve the whole pool. Every allowed released Address 2.x dependency retains the transparent [u8; 32] representation and derived Eq/PartialEq. The 3.0 change to owner() does not affect this direct comparison.
<!-- /registry -->

<!-- registry:review:e744b0cf4a369c1c -->
<a id="review-e744b0cf4a369c1c"></a>

Versions 1.0.0, 2.0.0, and 2.1.0 return a reference to raw.owner at offset 40, preserving its account identity and the creation generation represented by OwnerRef. The method is unsafe in v1 and safe in v2, but using a reference after owner mutation still needs the existing source validity/alias discipline. Version 3.0.0 returns an Address cloned by value. A saved native value remains valid and unchanged after close; it is not a reference to the account owner field. The complete borrowed-reference/generation contract is therefore incompatible at 3.0.0.
<!-- /registry -->

<!-- registry:review:d7cd0a461e7c58f8 -->
<a id="review-d7cd0a461e7c58f8"></a>

Only 1.0.0 exposes resize. Its reached closure checks free lease first, converts the request to i32, returns early for unchanged length, then checks resize_delta + (new_len - data_len) against 10,240 before updating length/counter and zeroing only positive growth. Shrink preserves hidden bytes and regrowth zeroes the newly exposed interval. Keep HasAccount and ResizeArithmetic exactly; fixed physical reserve is a separate source storage binding. Overflow on forged headers excluded by those arithmetic premises is observed separately. Both resize and resize_unchecked are absent in every 2.x/3.x release, not behaviorally approximated by a caller wrapper.
<!-- /registry -->

<!-- registry:review:d03f24fe96abe847 -->
<a id="review-d03f24fe96abe847"></a>

All four API releases replace the raw u64 balance immediately, without checking signer, writable, owner or data-borrow state and without changing other bytes. 1.0.0 uses &self; 2.0.0 and later use &mut self. This receiver distinction is a source-reference obligation and does not alter the complete mathematical replacement post or imply global uniqueness of aliased account handles. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:50e8598fe0bc8bb8 -->
<a id="review-50e8598fe0bc8bb8"></a>

All four API releases write the supplied u64 directly into the shared account balance and touch no other account field or lease. There is no writable, signer, owner, or balance-conservation check. The mathematical replacement uses only HasAccount; its Nat argument is not narrowed. Version 2 changes &self to &mut self, which changes the Rust receiver binding while preserving the full account transition and alias observations.
<!-- /registry -->

<!-- registry:review:6a97a60e4999879a -->
<a id="review-6a97a60e4999879a"></a>

All four releases check borrow_state < 2 first and return AccountBorrowFailed without change in that branch. Success decrements the byte and returns a Ref to the current complete data slice, retaining the same state-byte pointer. Free=255, exclusive=0 and 255 - n for n shared leases realizes the existing maximum of 254 shared guards; the same generic destructor releases one lease. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:751e15975bd99b0c -->
<a id="review-751e15975bd99b0c"></a>

All four API releases call check_borrow before changing the byte or forming the slice: bytes below 2 yield AccountBorrowFailed unchanged, otherwise the counter decreases by one and the returned Ref holds the current data pointer/length plus the original borrow-state pointer. The whole reached closure, 254-share policy, repr(C) header size, and generic Ref/drop representation agree across the padding revision. Success retains an identified live lease; saturation/exclusive conflicts and drop/reacquisition were executed.
<!-- /registry -->

<!-- registry:review:fd44f9b9c48167ed -->
<a id="review-fd44f9b9c48167ed"></a>

All four releases first require borrow_state = 255, otherwise return AccountBorrowFailed unchanged; success sets the byte to 0 and returns a RefMut to the current complete data slice. The helper pointer changes from a mutable data_ptr in 1.0.0 to data_mut_ptr in 2.0.0+, and the receiver changes from &self to &mut self; the extent, exclusive lease and current-byte behavior remain the same. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:4b90b07434e5dc40 -->
<a id="review-4b90b07434e5dc40"></a>

All four API releases require borrow_state == 255, otherwise returning AccountBorrowFailed unchanged. Success sets it to 0 and returns a RefMut over the current data range with the original state pointer. Version 1 obtains the data pointer through data_ptr; v2+ use data_mut_ptr and an &mut receiver. The pointer arithmetic still adds sizeof(RuntimeAccount), with unchanged tested size/offset, and release resets the same byte. Physical exclusive-target permissions remain separate from aliasable wrapper identities.
<!-- /registry -->

<!-- registry:review:d1708eb0849c330a -->
<a id="review-d1708eb0849c330a"></a>

Every API release has the identical generic Ref structure and Deref body: the stored NonNull<T> supplies the current reference, with no state-byte update, copied target value or second lease. T remains arbitrary and may be unsized or an external mapped target. The descriptor contract does not itself establish that the represented target is readable or writable. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:1f7fbdb3c219309b -->
<a id="review-1f7fbdb3c219309b"></a>

In every API release Ref<T> stores NonNull<T>, the source NonNull<u8> lease pointer, and PhantomData<&T>; Deref returns self.value.as_ref(). This preserves the world and target/guard identity without allocation, a new lease, or copying T. Generic targets may be sized, unsized, or outside the account; their existing profile supplies permission. Both byte targets and independently valid static [u64]/u64/str targets were exercised.
<!-- /registry -->

<!-- registry:review:54ace6be89daf3c2 -->
<a id="review-54ace6be89daf3c2"></a>

The entire generic Ref::map<T: ?Sized, U: ?Sized, F: FnOnce(&T) -> &U> closure is identical across all API releases. It first wraps orig in ManuallyDrop, calls F once, then stores NonNull::from(returned target) with orig.state. Success moves guard ownership to the new target while retaining the original lease and every permitted captured effect. A finite unwind after ManuallyDrop retains the lease and effects, consumes the input guard, and returns no guard. Terminal exits supply no final world; divergence has no finite result. Keep universal CallbackSafe and independent result-target permission rather than assuming a byte subslice or normal return.
<!-- /registry -->

<!-- registry:review:3c0bad56f5e63e1e -->
<a id="review-3c0bad56f5e63e1e"></a>

Every API release has the identical generic Ref destructor, which increments the source state byte by one. It never reads or copies back the target and is independent of T, including external and unsized targets. It retires the one owned guard while preserving account/captured contents; actual source guard construction and coherent state-byte representation justify the physical write. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:ff436b9138d64188 -->
<a id="review-ff436b9138d64188"></a>

Every API release implements Drop for Ref<T: ?Sized> by incrementing the original available-borrow byte once. No T drop, byte copyback, account mutation, or allocation is performed. With the existing live registry slot/lease interpretation this consumes exactly that guard while preserving current contents and captured state, even when the target was mapped into independent storage. Saturated, last, mapped, sized, and unsized releases were exercised.
<!-- /registry -->

<!-- registry:review:2b284178326028b1 -->
<a id="review-2b284178326028b1"></a>

All four releases have byte-identical Ref::try_map and reached generic dereference/guard definitions. ManuallyDrop is constructed before calling FnOnce, so normal success preserves the source lease with the returned target, ordinary failure returns (originalGuard, E) in that order while retaining all captured effects, and unwind consumes the owned guard without decrementing/releasing its lease. Terminal callback exits propagate without a fabricated final world; divergence has no finite outcome. T and U are ?Sized and E is arbitrary; external targets need their own permission rather than being forced into an account slice. No allocation is performed by the library mapping wrapper. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:4406b36f08596917 -->
<a id="review-4406b36f08596917"></a>

Every API release has the identical generic RefMut structure and Deref body: the stored NonNull<T> supplies the current reference, with no state-byte update, copied target value or second lease. T remains arbitrary and may be unsized or an external mapped target. The descriptor contract does not itself establish that the represented target is readable or writable. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:ad2489d6086e53da -->
<a id="review-ad2489d6086e53da"></a>

Every API release has the identical generic RefMut structure and DerefMut body: the stored NonNull<T> supplies the current reference, with no state-byte update, copied target value or second lease. T remains arbitrary and may be unsized or an external mapped target. The descriptor contract does not itself establish that the represented target is readable or writable. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:13c955d4232a1b49 -->
<a id="review-13c955d4232a1b49"></a>

Every API release returns self.value.as_mut() from the same generic NonNull<T>/NonNull<u8>/PhantomData<&mut T> representation. It preserves the world and issues no new lease; writes through the returned target are immediate. The full family retains arbitrary target profiles, including an external [u64; 3] exercised by the native supplement, with separately justified exclusive access.
<!-- /registry -->

<!-- registry:review:23b4090b2eb2f564 -->
<a id="review-23b4090b2eb2f564"></a>

Every API release has the identical generic RefMut destructor, which resets the source state byte to NOT_BORROWED (255). It never reads or copies back the target and is independent of T, including external and unsized targets. It retires the one owned guard while preserving account/captured contents; actual source guard construction and coherent state-byte representation justify the physical write. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:a1d2c4cfe58988ff -->
<a id="review-a1d2c4cfe58988ff"></a>

Every API release resets the original borrow-state pointer to NOT_BORROWED (255) on RefMut<T> drop. It does not drop T or copy target data back. The live exclusive guard is consumed and current account/captured contents remain unchanged by release; prior writes persist. Byte/empty/external targets and the absence of delayed copyback were exercised.
<!-- /registry -->

<!-- registry:review:e49ed387e5a0a19c -->
<a id="review-e49ed387e5a0a19c"></a>

All four releases have byte-identical RefMut::try_map and reached generic dereference/guard definitions. ManuallyDrop is constructed before calling FnOnce, so normal success preserves the source lease with the returned target, ordinary failure returns (originalGuard, E) in that order while retaining mutable data writes and all captured effects, and unwind consumes the owned guard without decrementing/releasing its lease. Terminal callback exits propagate without a fabricated final world; divergence has no finite outcome. T and U are ?Sized and E is arbitrary; external targets need their own permission rather than being forced into an account slice. No allocation is performed by the library mapping wrapper. This is source correspondence for the unchanged mathematical contract under its existing interpretation obligations, not a Rust body proof or a newly registered callable binding. Version 0.0.0 contains only the placeholder add function and has no AccountView or guard API.
<!-- /registry -->

<!-- registry:review:ab7578be4036ce92 -->
<a id="review-ab7578be4036ce92"></a>

The inspected 0.9.2/0.9.3 syscall declarations and defining macro are identical. The declared range assumes this exact extern-C item, argument order and result type under its existing dynamic-dispatch gates. The separately pinned runtime relation, registrations, source memory and effects remain unchanged.
<!-- /registry -->

<!-- registry:review:fcc5cc2136c4cefc -->
<a id="review-fcc5cc2136c4cefc"></a>

The inspected 0.9.2/0.9.3 body and C layout agree. The declared range assumes one borrowed CInstruction header, complete accounts.len() and signer forwarding, unit return and no borrow preflight. The Solana/64-bit/little-endian/abort and dynamic-dispatch gates remain; the entire CPI boundary stays opaque.
<!-- /registry -->

<!-- registry:review:45a01c82308f9e86 -->
<a id="review-45a01c82308f9e86"></a>

The inspected 0.9.2/0.9.3 deserializer bodies are identical. The declared range assumes allocation-free parsing of the aligned loader format, exact duplicate-header aliases, initialized output prefix and unchanged suffix/input, including skipped-account traversal. The nonempty-input/positive-capacity and backing-lifetime obligations remain; the unrelated panic-handler attribute change grants no startup proof.
<!-- /registry -->

<!-- registry:review:daf7e2b39ee287cc -->
<a id="review-daf7e2b39ee287cc"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes all 32 owner bytes and the unchanged header/lease state. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:178375f03fc67017 -->
<a id="review-178375f03fc67017"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the borrowed key location, receiver identity and unchanged full storage. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:670948c2b2b2777a -->
<a id="review-670948c2b2b2777a"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the borrowed owner location, receiver identity and unchanged full storage. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:c4c4f27629c6d0a3 -->
<a id="review-c4c4f27629c6d0a3"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the independent data-nibble exclusive acquisition, current mutable slice, alias identity, AccountBorrowFailed branch and exact release token. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:23fef928de538aa2 -->
<a id="review-23fef928de538aa2"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the exact current data length and unchanged header/lease state. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:d253920ba73686b9 -->
<a id="review-d253920ba73686b9"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes nonzero raw signer-byte truth and unchanged header/lease state. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:66f44f2d3e75bf46 -->
<a id="review-66f44f2d3e75bf46"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes nonzero raw writable-byte truth and unchanged header/lease state. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:8b5d808ee9da660b -->
<a id="review-8b5d808ee9da660b"></a>

The inspected 0.9.2/0.9.3 guard definitions agree. The declared range assumes ManuallyDrop before the actual closure, current callback mutations, fresh output generation and transferred field lease; unwind consumes the old token but retains the lease and reached state. Sized and unsized targets and all finite callback exits retain their existing interpretation.
<!-- /registry -->

<!-- registry:review:3ff239bf818f0c4c -->
<a id="review-3ff239bf818f0c4c"></a>

The inspected 0.9.2/0.9.3 definition is identical. The declared range assumes comparison of all 32 key bytes and unchanged input storage, with actual reference/layout obligations kept separate.
<!-- /registry -->

<!-- registry:review:2cc7975a33c4a679 -->
<a id="review-2cc7975a33c4a679"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes data-borrow checking before i32 conversion, the equal-length shortcut, signed cumulative 10240-byte growth limit, header writes before zeroing, unchanged spare suffix and actual primitive terminal effects. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:3851381e73d2a0d5 -->
<a id="review-3851381e73d2a0d5"></a>

The inspected 0.9.2/0.9.3 guard definitions agree. The declared range assumes current target storage and metadata, the actual reference identity/permission, and the unchanged field lease; no saved value is substituted. Sized and unsized targets and all finite callback exits retain their existing interpretation.
<!-- /registry -->

<!-- registry:review:24b48bbf363dda04 -->
<a id="review-24b48bbf363dda04"></a>

The inspected 0.9.2/0.9.3 constructor is identical. The declared range assumes the borrowed key identity and nonsigner/read-only flags, with the same initialized result fields and unchanged source state.
<!-- /registry -->

<!-- registry:review:82ec53fb1ba939bd -->
<a id="review-82ec53fb1ba939bd"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the current lamports value without borrowing or changing either lease nibble. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:2e2387f520be72c0 -->
<a id="review-2e2387f520be72c0"></a>

The inspected 0.9.2/0.9.3 constructor is identical. The declared range assumes the borrowed key identity and signer/read-only flags, with the same initialized result fields and unchanged source state.
<!-- /registry -->

<!-- registry:review:8785a04e907cea70 -->
<a id="review-8785a04e907cea70"></a>

The inspected 0.9.2 getter calls the dedicated clock syscall into MaybeUninit, returns the initialized Clock only at status zero and folds every nonzero status to UnsupportedSysvar. The declaration stops before 0.9.3, which changes to the generic syscall even though it still folds errors. Provider effects and finite abnormal exits are retained.
<!-- /registry -->

<!-- registry:review:b34c131b2e9933ae -->
<a id="review-b34c131b2e9933ae"></a>

The inspected 0.9.2/0.9.3 constructor is identical. The declared range assumes the borrowed key identity and signer/writable flags, with the same initialized result fields and unchanged source state.
<!-- /registry -->

<!-- registry:review:de5e6288fbce3e5a -->
<a id="review-de5e6288fbce3e5a"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the independent high-nibble exclusive acquisition, current mutable lamports cell, alias identity, AccountBorrowFailed branch and exact release token. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->

<!-- registry:review:6b5f5d86efba144c -->
<a id="review-6b5f5d86efba144c"></a>

The inspected 0.9.2/0.9.3 Seed conversion is identical. The declared range assumes the full borrowed array descriptor, const length and provenance are retained without allocation or byte mutation.
<!-- /registry -->

<!-- registry:review:e209576a36e3038c -->
<a id="review-e209576a36e3038c"></a>

The inspected 0.9.2/0.9.3 constructor is identical. The declared range assumes the borrowed key identity and nonsigner/writable flags, with the same initialized result fields and unchanged source state.
<!-- /registry -->

<!-- registry:review:74b315976835f0b1 -->
<a id="review-74b315976835f0b1"></a>

The inspected 0.9.2/0.9.3 account protocol differs only in documentation. The declared range assumes the independent low-nibble lease, seven shared credits, current slice projection, alias identity, AccountBorrowFailed branch and exact release token. The two-nibble protocol and actual source representation remain explicit.
<!-- /registry -->
