# Small SDK values

The [source registry](../source-map.json) records exact source references for
the following operations. Their [applicability profiles](../applicability.json)
separately declare compatible ranges and preserve each defining type,
source origin and dependency condition. Selection retains the actual
defining version; these ranges do not widen concrete source bindings or
nominal payload choices.

| Published crate | Registered operations |
| --- | --- |
| `solana-program` 1.15.2 | `COption::{is_none, contains, unwrap_or_default}` |
| `solana-program` 1.18.26 | `From<COption<T>> for Option<T>` |
| `solana-program-option` 2.2.1 | `COption::{is_none, as_ref, map, unwrap_or}` |
| `solana-program-option` 3.1.0 | `PartialEq::eq`, `COption::unwrap` |
| `spl-pod` 0.5.1 | `From<PodU16> for u16`, `From<PodU64> for u64` |
| `spl-pod` 0.7.3 | `From<OptionalNonZeroPubkey> for Option<Pubkey>` |
| `solana-zero-copy` 1.0.1 and 1.1.1 | `From<unaligned::U16> for u16` |
| `solana-sdk-ids` 3.1.0 | `bpf_loader_upgradeable::id`, `ed25519_program::id`, `sysvar::instructions::id`, `vote::id` |

The native POD reference is 0.5.1. Inspected 0.5.0 and 0.5.1 conversions
support `0.5.0 ≤ v < 0.6.0` with the same two-byte and eight-byte
little-endian values. Range eligibility supplies no new concrete layout or
source binding. COption keeps its existing per-operation profiles.

## Optional values and owned callbacks

The selected 1.15.2 `contains` accepts a possibly different query type `U`.
For `Some(payload)` it calls the selected `U::eq` with query then payload;
`None` returns false without a comparison. `unwrap_or_default` moves a
present payload unchanged and calls the actual `T::default` only for `None`.
Comparison and default providers retain their state effects, unwind and
terminal outcomes; no successful callback result is assumed.

The selected 1.18.26 conversion consumes the COption: `None` becomes `None`
and `Some` moves its complete payload into `Some`. It preserves the ambient
state without an allocation, payload callback or drop of the moved payload.

The 3.1.0 derived equality calls the selected payload comparison only for two
`Some` variants, with the left payload then the right. `unwrap` returns a
present payload; `None` calls the selected panic provider with the exact
source diagnostic. The return type of that provider is `Empty`, preventing a
fabricated successful None unwrap.

`is_none` inspects only the discriminant. `as_ref` returns a `FieldReference`
to the payload of the same parent, without a snapshot, allocation or fresh
borrow guard. Its source interpretation establishes the observed discriminant
and the current live parent borrow.

For `Some`, `map` moves the closure and payload into the actual `FnOnce`
provider, including the cleanup of that provider. For `None`, it drops the unused
closure before returning. These relations retain effects, ordinary returns,
unwind states, terminal reasons and the possibility of no finite outcome.

`unwrap_or` moves the already evaluated fallback for `None`. For `Some`, it
drops the fallback before returning the original payload. The pinned
nightly-2026-05-01 lowering retains that moved return-place payload if the
fallback destructor unwinds, as described by rust-lang/rust#47949. The source
index therefore selects `ReturnPlace.retain`. A separately indexed cleanup
policy in the generic family cannot be selected independently of the cleanup paths of the actual
compiler.

Generic payload and closure interfaces remain explicit. A specialization to
a plain key or Boolean additionally binds its nominal type, complete encoding
and actual callback/drop behavior. Equal layout alone does not establish that
selection. The Cargo unit of a COption crate need not depend on the defining crate of its generic
payload: a lookup projection for that unit does not establish
the actual payload or provider of the call. The two new concrete key profiles retain
the exact Address 2.6.0/2.6.1 identities of their selected nominal payloads; other
Address releases are not claimed behaviorally different. Key unwrap requires
`panic = abort`; unknown and unwinding profiles are rejected only for that
concrete selection. The generic family retains its actual panic provider.

The selected `OptionalNonZeroPubkey` conversion returns `None` for the
all-zero 32-byte key and otherwise moves the complete key into `Some`,
preserving the ambient state. It does not call the distinct
`TryFrom<Option<Pubkey>>` implementation that rejects `Some(zero)`.

## Integer values and source representation

The U16 and POD conversions decode respectively two or eight bytes in
little-endian order. Every byte pattern is valid, and the returned integer is
the exact decoded value. These value statements are independent of pointer
alignment; the source argument still needs its actual compiled representation.

The four ID functions return their declared canonical 32-byte keys. The
reviewed `declare_id!` providers in Address 2.6.0 and 2.6.1 return the same
constant bytes in BPF and non-BPF branches. The declared provider range
assumes those bytes and the full Address representation are preserved; the
reference sources and recordings stay exact. An actual defining provider and
reexport chain remain separate source facts; removing another same-named
dependency does not establish them.

Source codecs and callbacks must retain inactive enum bytes, padding, actual
reference provenance and the ownership appropriate to the selected value.
In particular, a returned borrowed payload is not an independent owner.
Stateful callbacks are not replaced by read-only or unit-state interpretations.
The [binding obligations](../BINDINGS.md) keep these source assumptions
separate from closed reference correctness, satisfiability and finite model
executions. None of those witnesses proves arbitrary callback termination,
SDK implementation correctness or target equivalence.

Program COption `contains`, `is_none` and `unwrap_or_default` have separate
generic and concrete-key profiles. The generic 1.15 range assumes preservation
of the complete callback/outcome contract. The `reviewed-key` profiles remain
exact 1.15.2 because those selections fix that nominal Pubkey source and
its full ABI. Selecting the generic family at another compatible version does
not extend those concrete source fixtures or their native evidence.
