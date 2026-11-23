# Address, Pubkey and derived address profiles

The [source registry](../source-map/libraries.json) and
[build profiles](../source-map/applicability.json) keep the immutable source of each operation, defining call identity and build conditions. Inspected
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
