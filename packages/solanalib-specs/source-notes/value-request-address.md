# Address values, search and serialization

The Address 2.6.0 and 2.6.1 models under `Solanalib.Specs.SolanaAddress` interpret SDK addresses
as the canonical `Solanalib.Runtime.Pubkey`, whose byte list has length 32. An array argument
includes this length equation. `new_from_array` uses those exact bytes; it does
not pad or truncate a list. `as_array`, `as_ref` and `to_bytes` preserve all 32
bytes, `default` supplies 32 zeros, and equality compares the whole byte list.
Borrowed return values are value observations; Rust references, lifetimes and
storage correspondence remain separate bindings.

The two roots remain distinct even where their mathematical operations agree.
The source registry retains the exact Rust names, source files and
anchors of each version. A shared definition is not evidence for a different version.

The primary `find_program_address_solana_contract` in both roots models the
selected Solana/bpf branch as finite stateful outcomes. The reusable supporting
`try_find_program_address_solana_contract` supplies the local wrapper around the
actual `sol_try_find_program_address` primitive provider. It starts with an
uninitialized address output and a bump initialized to 255, passes the ordered
seed slices, their u64 count and the program address, then inspects the status.
Only status zero reads the initialized address and the actual returned bump.
Every other returned status yields `None`, regardless of whether outputs were
initialized or changed. The wrapper does not precheck the seed limits of the runtime.

Both PDA families require `SuccessInitialized` at the actual call state and
inputs: every returned status-zero reply must carry an initialized address.
`decodePda_hasResult_iff` proves this is exactly what the local decoder needs.
`tryRun_retains` preserves every actual finite provider exit, including its
returned state, and `tryRun_hasOutcome_iff` proves that the admitted wrapper has
a finite exit exactly when the provider does. The law quantifies over every
reply, so one good nondeterministic branch cannot conceal a malformed one.
It neither requires the runtime to succeed nor asserts provider termination.
A status-zero reply with an uninitialized address is excluded by admission;
the unchanged raw relation assigns it neither a fabricated key nor `None`.
A source binding must establish this output-initialization law before
`assume_init`; it is not obtained from a sample execution.
An address output recorded as `None` may include partial initialization; exact
private output bytes and storage identity remain physical bindings. The source
does not observe those bytes on a nonzero status.

The find wrapper calls its non-returning panic provider only after an ordinary
`None` result, using the actual post-syscall state. `findRun_retains` composes
each actual panic exit from that state. `findRun_hasOutcome` requires a finite
panic exit only on a reached nonzero-status branch; a missing panic exit is
not replaced with an invented outcome. An ordinary successful pair skips that
provider. Syscall unwind and terminal exits are retained independently
of the pure PDA answer and never call the local panic site. The model introduces
no host allocation or host retry loop into this selected source path. Selecting
the Solana/bpf branch does not establish deployed layout equivalence. The source
binding must justify the word widths of the model and the actual feature profile.
Primitive admission, metering, target panic strategy and physical
syscall correspondence remain explicit implementation obligations.

The primary `is_on_curve_solana_contract` of Address 2.6.0 calls
`sol_curve_validate_point` with selector zero, all 32 address bytes and a **null
output destination**, then returns `status == 0`. It preserves the actual returned state of the syscall, unwind state or terminal reason. The known Address
`AsRef` is a byte observation; no arbitrary generic AsRef callback is invented.
This null destination differs from the initialized scratch
byte of the separate Curve SDK. Neither scratch storage nor a scratch-output value is introduced here.

The earlier `is_on_curve_contract` and both `find_program_address_contract`
declarations remain **pure observations**, excluded from the primary API model
selection. Their crypto facet uses canonical `findProgramAddressBytes` with
explicit hash/curve functions. It tries bump 255 through 1, never 0; invalid
seed limits and exhaustion produce no address. The mathematical result still
passes through `Pubkey.ofBytes`. A source binding must establish 32-byte hash
outputs and their correspondence to source Address values. That facet alone
cannot characterize finite syscall failures.
`NormalPdaAgreement` and `NormalCurveAgreement` state primitive ordinary-reply
correspondence, and the projection theorems derive the pure returned-value
facets under those laws. The laws do not constrain abnormal exits or assume a
complete SDK postcondition. The sample crypto and syscall providers establish
mathematical consistency only.

The derived Borsh serializer of Address 2.6.0 runs the Borsh 1.6.1 `[u8; 32]`
serializer, which makes one `write_all` of all 32 bytes, over a writer carried
in the family index (Borsh `WriterIndex`). The ordinary errors of the writer,
partial changes, unwind state and terminal reasons are preserved; neither a
successful writer nor rollback is supplied. The derived decoder reads the 32
bytes through the `[u8; 32]` decoder. See
[the Borsh derive notes](sysvar-codec-logging.md#address-260-borsh-derive).

Source anchors checked against the pinned crate archives:

| Version | Source | Relevant anchors |
| --- | --- | --- |
| 2.6.0 | [address/src/lib.rs](https://github.com/anza-xyz/solana-sdk/blob/b658e468fe1c0021dd86c1175dea5ee92cd28a08/address/src/lib.rs#L90) | Borsh derive 90; Default/PartialEq derive 100; 32-byte field 101; constructor 223; byte getters 296/302/325; curve query 313; curve syscall/null output 209–215 |
| 2.6.1 | [address/src/lib.rs](https://github.com/anza-xyz/solana-sdk/blob/14a725d6e9180e6cfbd98054473d61ef3aabde57/address/src/lib.rs#L107) | Default/PartialEq derive 107; 32-byte field 108; constructor 230; byte getters 303/309/332 |
| 2.6.0 | [address/src/syscalls.rs](https://github.com/anza-xyz/solana-sdk/blob/b658e468fe1c0021dd86c1175dea5ee92cd28a08/address/src/syscalls.rs#L277) | Non-optional search 277; fallible search 300 |
| 2.6.1 | [address/src/syscalls.rs](https://github.com/anza-xyz/solana-sdk/blob/14a725d6e9180e6cfbd98054473d61ef3aabde57/address/src/syscalls.rs#L277) | Non-optional search 277; fallible search 300 |
| Borsh 1.6.1 | [borsh/src/ser/mod.rs](https://github.com/near/borsh-rs/blob/f8109c75dd9462a2bc756c9d6fe3c0bc9c3e24ac/borsh/src/ser/mod.rs#L576) | `u8_slice` 72; array implementation 576; one `write_all` 585 |

The Borsh anchor is the ordinary array serializer supporting the derived Address
implementation. A generated Rust derive body, writer implementation and compiler
binding are not proved by this source review. Current source and model hashes,
exact API bindings and closed witnesses belong in the [source map](../source-map.json).

Controls include a pure PDA answer with an admitted syscall terminal exit and
an impossible local panic callback, every nonzero status with arbitrary output
slots, rejection of uninitialized successful replies and mixed good/bad
providers, changed output bumps, panic using the actual syscall state, absence
of an invented panic exit, seed strings beyond the runtime limit still reaching
the primitive, and the curve null/scratch distinction.
