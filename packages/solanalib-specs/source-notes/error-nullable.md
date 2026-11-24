# Error conversions and nullable Address values

The [library registry](../source-map.json) records reference bindings for the two
`solana-program-error 3.0.1` conversions and `solana-nullable 1.3.0::MaybeNull::get`.
Each registration seals its immutable source, exact callable identity, closed
mathematical witnesses and individually reviewed
[release profiles](../source-map.json).
The declared compatible ranges assume preservation of the complete operations
and their reached dependencies. The exact native lockfiles remain reproducible
test references; they do not restrict callers to those dependency versions.

## Error values

`From<u64> for ProgramError` recognizes complete status words. The custom-zero
sentinel is `2^32`; builtin error tags 2 through 26 occupy the upper word.
Unrecognized words become `Custom(status as u32)`, including raw zero. A nonzero
low word prevents a builtin match. Runtime success conventions are separate
from this ordinary conversion. The reverse conversion preserves each builtin
tag and uses the nonzero sentinel for `Custom(0)`.

This release has 26 Rust enum variants: `Custom(u32)` and 25 unit variants,
including payloadless `BorshIoError`. The complete source value codec has an
8-byte, 4-byte-aligned layout, with its u32 enum tag at offset 0 and the custom
payload at offset 4. The Rust variant tag is distinct from the runtime status
tag. Legacy string-carrying error types are outside these two registrations.

A source binding must select both conversion identities, supply the exact argument and result codecs, and preserve every mathematical result. The trait item and resolved implementation keep their distinct generic argument lists. Raw zero is admitted and returned as `Custom(0)`. Those execution bindings are outside this package.

## Nullable values and the Address instance

The general `NullableOperations` family calls the actual borrowed `is_none`
provider, including overrides. Its state contains mutable interior data, while
the payload retains its owner identity. A non-null value moves into `Some`.
A null value is dropped before returning `None`. A query unwind cleans the
retained owner in the final state of the query; another panic terminates. A terminal
query performs no later cleanup and has no fabricated final state. The equality and `NONE` temporary cleanup of the default
query belong to its provider.

The reference Address instance resolves `pinocchio 0.10.2::Address`
to `solana-address 2.6.1::Address`, with the `nullable` feature of the Address package.
The reexport, feature declaration, transparent byte array, derived equality,
and Nullable implementation are independently sealed. Its `NONE` is exactly
32 zero bytes; the payload and temporary have trivial drop. `NullableValue`
derives this pure graph from the general cleanup relation. This specialization
does not erase effects from the query or destructor of another payload.
Admission constrains the defining `solana-address` provider. Pinocchio supplies
only a reexport in the reference build, so it is not a required dependency.

A source binding of this specialization must fix the nominal `solana_address::Address` generic argument; a different 32-byte type
cannot select the same entry merely by sharing its layout. A verification tool must separately establish compiler correspondence and nominal type identity. A binding must retain distinct Address identities when a program links multiple SDK generations and preserve both transparent wrappers around the complete 32-byte key. The recorded reference layout of `Option<Address>` has size 33 and alignment 1, a u8 tag at offset 0, and the present Address at offset 1. Every nonzero key remains intact, including keys
with zero prefixes. The exact selected generic payload, resolved features,
source origin and actual compiled declaration must agree with that selection.

## Validation and boundary

`SolanalibTest.Specs.Core.ErrorNullable` checks every builtin status, custom
edge values, callback state, override selection, null destruction and double
panic. A binding must preserve the actual supplied state, admit all ordinary results, reject invalid enum tags, and represent these by-value source types without inventing an owned heap footprint.

The independently locked `error-nullable` native driver calls the real pinned
SDK functions. Its 86 error observations cover every variant and status-word
edge; its 34 Address observations cover zero, all-ones and a nonzero byte at
every position. Both corpora are recorded twice and replayed by the registered
references with negative controls. This driver contains no other SDK family.

A source binding must establish the selected compiler, release profile, Solana cfg, target endianness and width, panic strategy and the settings of any verification tool used. The retained native lockfile and source closure supply version and feature evidence for the recorded observations.
The native observation runtime uses unwind; the three concrete value operations
have no panic path. No equivalence with a different target layout is inferred.

Closed mathematical correctness and resource coverage do not prove SDK bodies,
compiler lowering or runtime implementation. Rust implementation refinement, actual source selection and compilation correspondence remain separate obligations.

The existing [mathematical controls](../SolanalibTest/Specs/Core/ErrorNullable.lean)
cover null and present values, overridden queries, query-unwind cleanup with its
actual state, destructor unwind and termination, double unwind, and terminal
queries that skip destruction. [Build controls](../SolanalibTest/Specs/Core/ErrorNullableProfiles.lean)
retain reviewed releases and reject missing or ambiguous Address providers.
The [native family](../../../tools/library-conformance/SolanalibTest/Conformance/Library/Families/ErrorNullable.lean)
replays the pinned error conversions and Address instance through the existing
conformance runner; it does not execute arbitrary user callbacks.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:cec27149e4a34a8d -->
<a id="review-cec27149e4a34a8d"></a>

This source module instantiates the shared SDK value family and closed witnesses at the exact source identities registered here. Imports do not add whole-crate coverage.
<!-- /registry -->

<!-- registry:review:ea5c88d7736c030b -->
<a id="review-ea5c88d7736c030b"></a>

Reference 1.3.0 calls the actual Nullable::is_none, including overrides, then moves a non-null value or drops the null owner before returning None. Query unwind cleans the retained owner in the reached state; a second unwind is terminal. A terminal query performs no later drop. The declared compatible range assumes preservation of this callback order, ownership transfer, cleanup and exceptional behavior.
<!-- /registry -->

<!-- registry:review:c9aa45c98a3949bf -->
<a id="review-c9aa45c98a3949bf"></a>

The reference Address Nullable implementation uses the all-zero NONE value and default borrowed equality query. Address and its NONE temporary have trivial drop, so this concrete index has no callback, cleanup or terminal effects. The declared compatible ranges assume preservation of the transparent 32-byte payload, equality, sentinel and trivial cleanup; other payloads retain the generic callback family. Exact native calls and emitted type layouts are recorded in source-notes/error-nullable.md.
<!-- /registry -->
