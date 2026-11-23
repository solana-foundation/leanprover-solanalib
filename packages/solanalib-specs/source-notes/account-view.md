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
