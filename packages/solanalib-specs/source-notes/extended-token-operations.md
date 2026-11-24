# Extended token operation contracts

The [source registry](../source-map.json) names each exact API,
mathematical contract and source interpretation. The
[profiles](../source-map.json) distinguish inspected reference
releases from declared compatible ranges and retain the build
conditions of each operation, separately from the public mathematical namespace.

The contracts covered here include selected Anchor lifecycle and loader operations,
account views, CPI wrappers, optional values, addresses, Token 2022 extensions
and instruction builders. Their closed reference, satisfiability and execution
witnesses describe the indexed mathematical operations. Reached trait methods,
allocation, cleanup, runtime calls and error construction retain their explicit
provider contracts and abnormal outcomes.

`AccountLoader::exit` keeps its exclusive data guard through a short partial
copy, owned `io::Error(WriteZero)` construction, borrowed `unwrap` formatting
and destruction of that same error during unwind. Successful diagnostic
allocations and cleanup retain their actual auxiliary state; the caller
releases the guard after cleanup. Terminal exits have no successor state,
and a second unwind follows the explicit cleanup policy. These reached
[dependency obligations](../BINDINGS.md#callbacks-and-outcomes) are separate
from source-body proofs; error-construction allocation failure remains outside
that boundary.

Token 2022 8.0.1 reuses the complete parameterized operational extension getter
from the Token 2022 interface model. Its sample supplies the legacy byte
provider. The import-policy edge records this mathematical alias; it does not
assert a Cargo dependency or transfer a source profile between libraries. The
legacy TLV scan, allocation order and marker-only unpack rejection remain
separate from operations with different behavior.

The Pubkey serialization and reader profiles require Borsh 0.10.4.
An owning-unit closure containing both Borsh 0.10.4 and 1.6.0 remains ambiguous
for whole-build dependency lookup. Selection of an individual call must use
the complete item and implementation descriptions, resolved arguments,
callback types and source seals. Neither a bare method name nor catalog
membership establishes that selection. The generic unit profile of COption likewise
does not establish the nominal key representation of a caller.

The panic requirement on the selected CPI profiles is unchanged. The profile field of a Cargo unit graph and an isolated native fixture do not establish the
effective flags of the consuming compilation; the actual compiler invocation
must supply that fact.

Concrete source selection, memory bindings and native checkers have separate obligations from the mathematical registrations and catalogs. A Token-2022 sizing binding must correctly represent the temporary `Vec<&ExtensionType>`; loader bindings must preserve the required layouts. Each must distinguish an allocator-root input from the actual immutable child reference passed by source code. Native observations and independent source reviews keep their recorded scope; this assembly supplies neither a concrete source-call binding nor SDK or standard-library body correctness.

Archive checksums identify the inspected reference sources. Declared ranges
assume that the complete operation and relevant dependency contracts remain
unchanged; SemVer is evidence for that assumption, not a source or native check
of every release. Unlisted prereleases and other source origins remain excluded.
AccountLoader initialization and exit stop before Anchor 1.2.0, which introduces
new size checks; the unchanged loader operations retain their separate ranges.
Token-2022 9.0.0 admits an exact marker-only tail that the 8.x unpack contract
rejects. These boundaries do not change the source-call, Borsh-generation,
provider or effective-panic gates. Rust body and target-layout obligations remain
separate from the mathematical witnesses.

The maintained tests cover the selected ownership and failure boundaries:
`SolanalibTest.Specs.Core.SdkValues` checks the two `COption::map` branches and
fallback destruction, including terminal callbacks that cannot return a
fabricated value or state. The Token 2022 tests apply the public epoch-fee
contracts to activation equality and checked inverse failure while retaining
the full configuration. The loader tests cover guard transfer, partial writes,
effectful WriteZero construction and cleanup, distinct unwind reasons, and
terminal outcomes without an after-state. A missing reached callback supplies
no finite exit; ordinary writes and skipped paths need no diagnostic outcome. The
registered applicability tests retain the exact Pubkey/Rent release unions and
the Borsh generation and ambiguity checks. Use the existing package test roots
and [conformance commands](../../../tools/library-conformance/README.md#run-the-tests);
the native corpora and their exact driver/version identities remain separate
from these mathematical and profile tests.
