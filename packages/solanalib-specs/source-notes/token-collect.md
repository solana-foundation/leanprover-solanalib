# Token resolver guard collection

The source anchor is `spl-tlv-account-resolution` 0.11.1, `src/state.rs`,
lines 323–331, in `ExtraAccountMetaList::add_to_cpi_instruction`. For each extra
meta, the source iterates the current CPI account-info vector. Its closure first
copies `info.key`, then calls `info.try_borrow_data()?`, and returns that key and
the live shared reference. The iterator is collected by the higher-order
`collect::<Result<Vec<_>, ProgramError>>()` dependency. The resulting vector is
held during resolution and dropped when the inner scope exits.
The [source registry](../source-map.json) pins the reviewed revision, complete
file hash and source anchors.

`TokenRequestAllocatedCollect` computes that ordinary source closure over the
shared AccountInfo/Borrow model. `Iterator` retains the source length and reads
the current account-info element in the actual state. The `Provider` receives
this exact iterator and callback. Its finite outcome relation is the explicit
std dependency boundary. It is not a claim that the SDK itself calls a guessed
sequence of `Vec::new`, `reserve` or `push` operations.

`TokenRequestAllocatedCollectProtocol` describes the local dependency laws.
Every acquired element comes from an actual callback at the next index.
Provider-owned internal chunks can occur between callbacks; each supplies its
own actual return, unwind or terminal state. A callback error or unwind stops
iteration and cleans the acquired prefix. A terminal exit stops immediately.
The provider supplies the actual partial-cleanup order from its current
bookkeeping, and the protocol checks that it is a permutation of exactly the
acquired elements. A newly returned Ref can still be a pending insertion input:
if reserve then unwinds, that input can drop before the stored prefix. The
protocol admits this order directly and does not assume release commutation.
Cleanup then calls storage-only retirement; that last dependency must not release the elements again. These
element/drop obligations are separate from the generic `VectorOps.Laws`.

`Provider.Conforms` requires each admitted provider outcome to have such a
trace. It is a local higher-order dependency obligation, not an assumed token
helper postcondition. `ResourceLaws.finish_current` connects successful
transfer to the exact ordered sequence in the current vector observation.
This is the resource premise used by the success-current and length results.
Those results do not constrain the later destructor of a returned vector. Its element cleanup and storage retirement
remain the actual supplied operations and separate source-binding obligations.
The concrete reference below implements both in its destructor.
`Trace.calls_prefix` and `Trace.calls_bound` prove no skipping, repetition or
overrun. `Trace.success_current` and `Provider.success_length` derive completion
of every source callback and the exact length of the returned vector.

`OnchainAllocated.collectRefs_success_length` applies these laws to the actual
SDK collection call and its source account-info vector. Every successful call
returns a current guard vector whose length equals the account count observed
at entry. This conclusion does not require allocator success and does not by
itself assert that intervening effects preserve the readability of each guard.

The protocol and current-vector law alone do not prove the allocator preserves
held guards or the source iterator. `TokenRequestAllocatedCollectFrame` gives
read results under an explicit strong primitive frame: the particular internal
effect or final transfer preserves the complete AccountInfo guard world while
allowing auxiliary allocation state to change. Each read theorem takes only
the law for its actual call, with no bundled retirement obligation. A source
binding must justify that frame, or the weaker per-reference frame it uses. The actual
source callbacks and element releases are deliberately outside that frame,
because they acquire and retire guards.
This account frame also does not preserve an iterator stored in the auxiliary
state; a consuming source binding must establish that separate iterator frame.

`CollectionFrames.trace` composes actual acquisitions, internal and finish
exits, and cleanup. Its three laws cover internal work, transfer and the
`retire none` callback reached after failed collection has released its
acquired prefix. `collectRefs_frames` and `collectRefs_outer_read` take this
record, the `Conforms` proof of the actual provider and the guard
law of the panic callback. They need neither the successful vector-observation law nor an iterator
resource law. The trace derives the outer guard frame without assuming a
complete Token-helper frame, successful collection or callback termination.

The separate `collection_internal_iterator` theorem takes `Retains` for the
particular internal call. `collection_borrow_iterator` takes `CurrentOnAux`
for the info-vector observer, so an actual acquisition cannot erase the
iterator merely by updating the guard store. Each derives the next indexed
read from the observation and actual call state it consumes. These results
do not require unrelated finish or retirement behavior.

The operational family admits the selected primitives before a later SDK
read or checked release. `TokenRequestAllocatedAdmission` separates live-guard
frames, preservation of typed data on ordinary returns, and retention of the
collected Ref vector. Typed-data admission has no scalar or length bound and
imposes no new acquisition requirement on unwind paths. The admission records
contain the capabilities consumed by the actual local continuation proofs.
They require no premise about a completed helper.

One selected collection protocol is shared by its conformance, current-vector,
guard/data, ordinary-resource and cleanup-order obligations. Internal returns
retain the captured iterator element and the selected data input for the next
key-before-borrow callback. Successful transfer retains the data input used by
a later extra-entry iteration. Failed-collection retirement needs the existing
outer-guard/resource frame; it has no unused next-borrow typing gate.

`TokenRequestAllocatedBorrowAdmission` connects those conditional continuation
lemmas to actual source acquisition sites. Its collection site starts from the
validation/extra-entry prefix and the forward prefix of this same protocol, before
the selected callback runs. A successful acquisition must expose current data
and the protocol validity used by later read/release frames. An actual checked
borrow error remains admitted without those success-only conditions. The gate
does not assume a completed collection or enclosing preparation outcome.

`TokenRequestAllocatedCollectAdmission` records forward prefixes from actual
successful callbacks and internal returns. Its cleanup sites record an actual
callback error, internal unwind or finish unwind before any complete trace is
assumed. The admitted partial order contains exactly the acquired elements;
each actual downstream cleanup exit then extends the original trace with the
same state and reason. Neither storage-retirement termination nor a finite
second-unwind-policy result is assumed. This order check is distinct from
resource retention: a provider that keeps every guard but omits an element
from its cleanup order would otherwise lose the finite failure continuation.

The local guard helpers still take their individual laws directly. A
Ref-vector destructor may release its actual current elements while preserving
outer guards. Resolver primitives retain that current element list before the
source destructor begins. Ordinary vector lifetimes and captured-index reads
use the separate `TokenRequestAllocatedResourceAdmission` footprint; a guard
frame alone does not preserve a vector stored in auxiliary state.

`TokenRequestAllocatedCollectReference` is one mathematical interpretation:
callbacks run in order and the completed sequence is placed in a fresh logical
ledger slot. That chosen schedule establishes consistency, not correspondence
to the concrete Rust collector or allocator. The returned vector owns the
actual element releases, followed by retirement of its ledger slot. Closed
theorems prove conformance and resource linkage. Concrete call-state controls
exercise the independent account frame.

The controls in `SolanalibTest.Specs.Core.TokenAllocatedCollect` execute real
shared-model borrows. A complete successful path collects two distinct data
references, observes their current bytes, and drops both references and their
owning vector. A second-borrow failure releases only the newly acquired prefix,
retains a preexisting exclusive guard, and skips a third valid account. Further
controls reject missing elements, reordered/repeated callbacks and omitted
cleanup elements, cover an empty collection, and exercise internal mutation
before unwind, a pending-last Ref dropped before its stored predecessor,
terminal exits, and a second unwind during storage cleanup.

`TokenAllocatedGuards` and `TokenAllocatedInputs` reject actual destructive
prefixes at the registered family: a metadata push that destroys a held guard,
and an allocator that changes the kind of a selected data cell before the first
borrow. A separate nonempty collection control shows why its Ref-vector ledger
also needs retention. The raw callbacks and their failed subsequent reads or
drops remain unchanged. Admission excludes the bad interpretations before a
missing complete-body outcome could make a final-exit frame vacuous.

Positive controls retain auxiliary effects, changed unborrowed data, ordinary
errors, unwinds and terminal exits. They include nonempty collection with
actual element/storage cleanup and the full allocated the Rc of the sample, guard,
vector and CPI cleanup. Local continuation theorems quantify each actual
primitive exit and perform the next current read or checked release; they do
not assume that the complete SDK function already has an outcome.

The cells retained by `InputFrame` are logical account payload cells, not
physical Rc allocations. Owner counts and allocation retirement may live in
`Extra`; cell presence grants no ownership permission. The full sample
changes Rc counts and retires actual vector slots. A source binding remains
responsible for the relationship between those logical cells and live source
owners, layout and access permissions.

Concrete Rust iterator lifetimes, alias/capability validity, std collection
allocation and element-drop correspondence, and the interpretation of the
internal provider effects remain separate obligations. No Rust invocation
body, std implementation proof, compiled Rust client or allocator implementation
is included here. The exact upstream source record is shared with the token
instruction audit as `spl-tlv-account-resolution-0.11.1-state`.
The local input and resource laws protect the selected represented input or
retained observation at each reached call. They do not establish arbitrary
initial account representation, allocator success, or termination of opaque
callbacks. Concrete source bindings must justify the admitted primitive
behavior and the ownership of each current observation.
