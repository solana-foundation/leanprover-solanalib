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
