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
