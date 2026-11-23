# Token batch preparation

The four mathematical models in `Solanalib.Specs.PinocchioToken.Instructions` cover the
Batch constructor, unchecked-invocation wrapper, specialized
TransferChecked constructor, and generic IntoBatch implementation. Their source
is pinocchio-token 0.6.0, Cargo package checksum
`825f59c8348e5c2d3fd56432ef927f5819542b3b05fae4f5b6869801113e775e`, repository
`anza-xyz/pinocchio` at `cc937fec77a9888a9d7e60aba59bd2dc16291413`, under
`programs/token`. These are mathematical function models over the common account,
borrow, request and outcome infrastructure. All Rust implementation proof
statuses remain open.

| Source operation | Versioned contract | Mathematical witness |
| --- | --- | --- |
| `instructions/batch.rs`: `Batch::new` | `instructions.batch.Batch.new_contract` | Closed `RealizedBy` and satisfiability witnesses |
| `instructions/batch.rs`: `Batch::invoke_signed` | `instructions.batch.Batch.invoke_signed_contract` | Closed `FamilyReference`, sample `FamilyHasExecution`, and sample satisfiability witnesses |
| `instructions/transfer_checked.rs`: specialized `TransferChecked::new` | `instructions.transfer_checked.TransferChecked.new_contract` | Closed `RealizedBy` and satisfiability witnesses |
| `instructions/transfer_checked.rs`: generic `IntoBatch::into_batch` | `instructions.transfer_checked.TransferChecked.into_batch_contract` | Closed `FamilyReference`, nonempty-signer `FamilyHasExecution`, and sample satisfiability witnesses |

All names in the second column have the `Solanalib.Specs.PinocchioToken` prefix. The
[source registry](../source-map.json) records their Rust names, anchors and
witnesses. The trait interface alias for IntoBatch is not an additional
function or proof.

Batch creation rejects an empty data slice without modifying any buffer. A
nonempty slice receives discriminator 255 at byte zero; its prior suffix and
both account buffers remain intact. The three returned lengths are one, zero,
and zero. TransferChecked creation simply retains its four account references,
u64 amount and u8 decimals, and supplies an empty signer slice.

Generic IntoBatch first checks room for its two-byte instruction header. It
then writes the fixed ten-byte payload, writes account descriptors, and writes
instruction metadata. Each stage checks its own capacity before writing. The
account writer checks capacity before the source and destination borrow flags;
it does not check mint, authority or signer borrow flags. Those flags come from
the common identified lease state, not independent booleans. A failure in a
later stage preserves all earlier data writes, initialized descriptors and
callback effects. Only complete success updates the lengths and writes the
two-byte header. Header casts use `UInt8.ofNat`; the committed counts retain
their full natural values. No signer deduplication or maximum-multisig check is
introduced.

The source has two separate traversals of `MultisigSigner::as_ref`. The first
initializes each CpiAccount immediately after its callback returns. The second
calls every signer again and initializes its instruction metadata immediately.
`AsRef` is an arbitrary relation over the current common account world and an
arbitrary ambient state, with independent unwind and terminal types. It can
return different accounts or different effects on the two traversals, and can
be nondeterministic. The mathematical relation does not require a separate
whole-callback validity predicate. A Rust binding must establish that actual
returning callbacks preserve existing source references and return a valid
AccountView handle. There is no invented ProgramError for a missing
mathematical handle. Unwind preserves the actual
callback state and all earlier writes; a terminal exit has no fabricated
post-state. The separately borrowed Batch buffers are outside the callback
frame. An eventual Rust interpretation must justify that separation and every
callback effect.

Instruction-view 2.1.0 supplies the ordinary CpiAccount initializer and
InstructionAccount constructors. Its source is `anza-xyz/solana-sdk` at
`d8e311b30785b398f689528443ffd50db2a262f0`, under `instruction-view`. The model
retains an AccountView handle for the live address, lamports, data and owner
references, while copying data length, signer/writable/executable flags and
zero rent epoch when each CpiAccount is initialized. Metadata retains an
`Instruction.RefMeta AccountView.AddressRef`, with independent copied flags.
The actual provider receives those retained identities. `Request.observe`
explicitly reads keys from a supplied current world; it is not an implicit
snapshot substituted for the reference-bearing request. Raw pointer addresses,
padding, physical flag bytes and the representation of these fields remain
binding obligations.

Batch invocation reads exactly the three committed lengths. In pinned
`instructions/batch.rs:95-109`, `from_raw_parts` constructs slices over those
lengths; it cannot skip an uninitialized slot and compact later values.
`initializedPrefix` therefore decodes exactly the requested number of `some`
entries. A hole or out-of-bounds length gives `none`, and `request` constructs
no request unless all three prefixes decode. This is mathematical source
admission, not a new Rust error or abort. `invokeFamily.requires` uses
`InvocationReady` for exactly the three complete initialized prefixes, including
their bounds within the supplied buffers. All three premises are consumed by
request decoding. Private Batch invariants, source-sized lengths, valid Rust
storage and retained-reference lifetimes remain separate binding obligations;
they are not unused gates on this mathematical forwarding relation.

`initializedPrefix_exact` and `request_exact` prove equality with every
committed source slot and the exact committed lengths. Together they preserve
order and multiplicity, rather than only membership or a filtered subsequence.
`request_domain` proves that the three admission gates are exactly equivalent
to existence of a decoded request, with no unrelated precondition.
`InvocationReady.progress` uses the three initialization premises to construct
a request and allows every actual finite outcome of the supplied provider to
continue. It assumes neither provider termination nor determinism.

The request preserves the exact signer seed tree and fixed legacy Token program
ID. The actual `invoke_signed_unchecked` provider is opaque. Its source signature
returns unit. Accordingly, only an ordinary provider unit return becomes
`Ok(())`; provider unwind and terminal exits keep their actual effects. The
wrapper cannot produce an invented ordinary ProgramError. No invocation
implementation body was inspected, traversed or proved, and no callee
execution, runtime admission, authorization, copyback or transaction guarantee
is inferred.

The constructors and IntoBatch writers retain their mathematical natural
amounts, decimals, lengths and counters, with explicit byte conversions in the
encoders and header writes. Rust interpretation separately requires u64 amounts,
u8 decimals, target-sized slice lengths/counters and representable source
additions. A mathematical execution outside those bounds is not evidence for
Rust overflow behavior or a target panic policy. Invocation has the exact
initialized-prefix admission described above. A Rust interpretation must also
establish the private Batch invariants of the source (including its discriminator),
source-width lengths, buffer separation, physical layout and retained-reference
lifetimes. No whole-account-world validity assumption is needed merely to
construct these reference-bearing requests. Family correctness quantifies over every model type and callback
index; the registered sample establishes one actual permitted finite execution
and does not assert that arbitrary callbacks terminate.

The controls include both constructors, wire-byte order, capacity/borrow
precedence, retained partial writes, empty and nonempty signer slices, aliasing,
distinct accounts returned on the two callback passes, changed ambient state,
nondeterministic outcomes, unwind, terminal exit, borrowed mint/authority,
retained current-world address references and copied CPI fields. A generic
constant-callback execution lemma also provides an actual 256-signer control:
both committed account counts are 260 and the metadata-count header byte is
four. The control derives its writes and counts from both actual callback
passes. Additional controls retain the existing capacity error for an oversized
mathematical counter. Invalid invocation controls reject a hole independently
in each of the three prefixes and reject an out-of-bounds committed length.
The malformed `[some 255, none, some 7]` state is not admitted, constructs no
request and cannot produce any provider outcome. The complete two-pass sample
is admitted: its provider receives all thirteen committed bytes and adds its
own effect to the two preceding signer-callback effects. These are local
construction and opaque-boundary controls; runtime admission is separate.

Build the controls from `packages/solanalib-specs` with
`lake build +SolanalibTest.Specs.PinocchioToken.Instructions`. The
[package audit](../README.md#build-and-audit) checks the registered source hashes,
declarations, witnesses and axiom dependencies.
