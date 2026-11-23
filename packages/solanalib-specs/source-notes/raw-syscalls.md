# Raw syscall models

These are mathematical models of six syscalls that a program can call directly. Their reference and execution witnesses prove consistency of the stated models, without a Rust implementation, compiler, memory or runtime implementation theorem. The [source registry](../source-map.json) records the models of `sol_sha256`, `sol_log_`, `sol_panic_` and `abort` at SDK 5.1.0, and `sol_sha512` and `sol_curve_multiscalar_mul` at SDK 5.2.0, with their source anchors.

The ordinary sources are pinned separately:

| Package | Source | Revision | SHA-256 |
| --- | --- | --- | --- |
| solana-define-syscall 5.1.0 | `define-syscall/src/definitions.rs` | `20460d626da00db050d46a103f58116bda2b3403` | `3f7587731dac4d70f4e2be26d89a61d43185e2d581684a3150eabdd449134e50` |
| solana-define-syscall 5.1.0 | `define-syscall/src/lib.rs` | `20460d626da00db050d46a103f58116bda2b3403` | `f997481296d2fa184c646de11c5af9892376cdf362b02de5317be5992d19581d` |

The version basis is the crate manifests. On Solana targets, pinocchio 0.11.1 and solana-instruction-view 2.1.0 depend on solana-define-syscall 5 (requirements `5.0` and `5.0.0`), which resolves to 5.1.0, and solana-sha256-hasher 3.1.0 depends on solana-define-syscall 4 (`4.0.0`), which resolves to 4.0.1, as `cargo metadata` reports. The four registered function identities are `solana_define_syscall::definitions::<name>`. A binding must establish the exact Rust item path and dependency version from the build manifests. Matching a declaration does not establish its implementation.

## Declarations

[`definitions.rs`](https://github.com/anza-xyz/solana-sdk/blob/20460d626da00db050d46a103f58116bda2b3403/define-syscall/src/definitions.rs) declares `sol_log_(message, len)` at line 10, `sol_sha256(vals, val_len, hash_result) -> u64` at line 21, `sol_panic_(filename, filename_len, line, column) -> !` at line 36 and `abort() -> !` at line 37, each through `define_syscall!`. Without the `static-syscalls` target feature, [`lib.rs` lines 32–47](https://github.com/anza-xyz/solana-sdk/blob/20460d626da00db050d46a103f58116bda2b3403/define-syscall/src/lib.rs#L32-L47) expand that macro to an `extern "C"` block declaring the function. With the feature, the macro defines an inline function that calls the syscall through its hash; that is another implementation and is not modeled.

An `extern "C"` function cannot unwind, so the models have no unwind exit.

## Models

`Solanalib.Specs.Core.RawSyscall` states each call with the requests and answers of the canonical runtime model. The call asks a syscall environment, the provider of the family index, and returns its answer; the terminal exits of the environment are also the terminal exits of the call.

- `sol_sha256` asks `.hash .sha256 slices`, with the slices in order and empty and repeated slices kept. It has no precondition. Its answer has the shape that a `u64` status and a 32-byte result carry, one 32-byte digest on status `0` and no bytes on any other status (`HashShape`), which the post states; the shape is a law of the index (`Index.hashShape`), as `SyscallHash` in Agave 4.3.2 writes `size_of::<Hash>()` bytes on success. Its arguments (`Sha256Args`) also say whether `vals` is 8-aligned. A call with more slices than the limit of the index does not return (`Sha256Args.overLimit`), and neither does, where the index checks alignment, a call with a slice at an unaligned `vals` (`Sha256Args.unaligned`): both stop as the environment stops `abort` (`Sha256Args.rejected`, `aborted`).
- `sol_log_` asks `.log message` and returns `()` when the environment answers it. Every message is admissible: one that the environment does not answer has only the terminal exits of the environment, as `sol_panic_` and `abort` have, and does not return (`logPost_unanswered`).
- `sol_panic_` and `abort` return `!`, which has no values: an answer cannot be returned, so their only outcomes are the terminal exits of the environment. An environment that answers these requests gives the call no outcome.

An index also records whether pointer arguments must be aligned for their types (`Index.checkAligned`): for `sol_sha256`, whether an unaligned call stops. The model reads this flag; a source binding must require alignment only where it is set and justify the choice against the ABI of the program. `canonical` takes it from `check_aligned` in Agave. An index also records the greatest allowed number of slices (`Index.maxHashSlices`, `none` for no limit). The model stops an excessive-count call before asking its provider. A binding must establish that this count is the register argument `val_len`; it then requires no memory for that rejected call. `canonical` takes the limit from the profile (`maxHashSlices`, the `sha256_max_slices` of Agave). A binding must supply and justify that limit separately; the native conformance shim does not check the count.

### Checks in Agave in `sol_sha256`

[`SyscallHash`](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L2717-L2788) checks, in order: the slice count against the limit, failing with `TooManySlices` (lines 2733–2742); the base compute cost (2744); the translation of `hash_result` (2748–2756); and, only when `val_len > 0`, the translation of `vals` as `val_len` `VmSlice<u8>`s with `check_aligned` (2758–2764), which fails with `UnalignedPointer` when the translated pointer is not 8-aligned ([`program-runtime/src/memory.rs` lines 113–115](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/memory.rs#L113-L115)). Each failure aborts the program. So a call with more slices than the limit does not return, and Agave aborts it before it charges compute or translates any address. A call within the limit with a nonempty descriptor list at an unaligned translated host address also aborts when the runtime checks alignment, whichever earlier check fails first. The model stops a call without asking exactly when the first or the last check fails (`Sha256Args.rejected`). Agave checks the host address that `vals` translates to (`host_buf.ptr()`), not its VM address, and `Sha256Args.aligned` stands for that check. A source binding that sets the `aligned` argument of the model from the VM address of `vals` must restrict admission as described below. solana-sbpf 0.23.0, which this Agave pins, translates an address to the host start of its region plus its offset in the region ([`MemoryRegion::vm_to_host_buffer`](https://github.com/anza-xyz/sbpf/blob/9476336b901181d68e00c5b38252a15694d4d6aa/src/memory_region.rs#L374-L405)), so they agree when the host and VM starts of the region do. That holds for the regions that Agave backs with `AlignedMemory<HOST_ALIGN>`: the stack, the heap ([`program-runtime/src/vm.rs` lines 89–101](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/vm.rs#L89-L101)) and the serialized input buffer, whose regions Agave places so that the addresses agree ([`program-runtime/src/serialization.rs` lines 196–203](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/serialization.rs#L196-L203)). It need not hold for account data that Agave maps directly from the buffer of the account (`create_memory_region_of_account`, [lines 55–70](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/serialization.rs#L55-L70)) or for read-only data that the loader of solana-sbpf copies into a `Vec<u8>` ([`Section::Owned`](https://github.com/anza-xyz/sbpf/blob/9476336b901181d68e00c5b38252a15694d4d6aa/src/elf.rs#L975-L988)).

Within the slice limit, such a binding must exclude calls with a nonempty descriptor list at a VM-unaligned `vals` when `index.checkAligned` is set. Such a call can return in Agave when its translated host address is aligned, so excluding it from admission does not prove that it never returns. A VM-aligned call whose translated host address is unaligned may abort; a partial-correctness binding must permit that terminal outcome without claiming termination. No agreement between host and VM alignment is assumed.

An empty descriptor list skips the `vals` alignment check, but a call within the slice limit still requires ownership of its 32-byte result buffer. Only calls over the slice limit have an empty memory precondition, regardless of alignment, because Agave rejects their register count before translating memory.

How a program passes these values in memory is not part of the models. A separate binding to the Rust implementation must account for the 16-byte `(ptr, len)` descriptors at `vals` and the bytes they point to, the digest written at `hash_result` on status `0`, the message bytes and the file name bytes.

## The canonical runtime

`canonical W c` is the canonical runtime as an environment: its answers are those of `Solanalib.Runtime.Env W c`, its terminal exits the failures of `Solanalib.Runtime.sysStep`, as the `sys`, `sysFail` and `unregistered` rules of `Solanalib.Runtime.Exec` have them. Under it:

- `sol_sha256` returns status `0` and `W.prims.sha256` of the concatenated slices, for a call that passes the alignment check and is within `maxHashSlices`, and leaves the state unchanged; beyond the limit, and on an unaligned call, it fails with `ProgramFailedToComplete` (`canonical_overLimit_iff`, `canonical_rejected_eq_false_iff`, `canonical_sha256_returned_iff`, `canonical_sha256_terminated_iff`, `canonical_sha256_unaligned_iff`). Hashes stay symbolic. The digest has 32 bytes by the width law of `Solanalib.Runtime.Prims` (`sha256_length`), which discharges the hash-shape law of the index, so a return is a 32-byte digest with no premise on the world (`canonical_sha256_post_iff`).
- `sol_log_` returns for a UTF-8 message and appends it to the logs (`canonical_log_returned_iff`). It answers only UTF-8 messages (`canonical_log_answered_iff`) and fails any other with `ProgramFailedToComplete` (`canonical_log_terminated_iff`), as the Agave `SyscallLog` aborts on `InvalidString` ([`syscalls/src/logging.rs` lines 24–33](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/logging.rs#L24-L33), [`syscalls/src/lib.rs` lines 583–596](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L583-L596)).
- `sol_panic_` and `abort` fail with `ProgramFailedToComplete` and have no other outcome (`canonical_panic_iff`, `canonical_abort_iff`).
- The runtime checks alignment for ABI `v1`, the ABI of every program not owned by `bpf_loader_deprecated`, as `InvokeContext::get_check_aligned` does (`Solanalib.Runtime.Abi.checkAligned`, `canonical_checkAligned`), so a `sol_sha256` call is unaligned exactly when it has a slice, its `vals` is not 8-aligned and the ABI is `v1` (`canonical_unaligned_iff`).

## SHA-512 and multiscalar declarations

The same `Solanalib.Specs.Core.RawSyscall` module defines the SHA-512 and multiscalar families.
A concrete binding must interpret each family separately or combine them under one shared mathematical state. The `Solanalib.Specs.SolanaDefineSyscall` catalog groups their references and consistency samples by function name. `catalog.forBuild` selects the actual identity of each compatible release with the same complete model. Selecting another release requires a matching source/build identity and a justified implementation and memory interpretation. These models do not prove an SDK body or an Agave implementation.

Applicability checks package, release, source and structured build constraints.
Profile `conditions`/`argument`/`evidence` and constraint `reason` fields describe
the scope below; the matcher ignores this prose and does not discharge its obligations.

### Supported releases and dispatch

SHA-512 uses one model for all four published releases from **5.1.0 through 5.4.0**;
multiscalar multiplication uses one model for all eleven from **2.2.0 through 5.4.0**.
Every release in these sets has the same defining path, argument and return types, and dynamic
`extern "C"` expansion. Earlier releases lack the respective declaration. All 33 published
archives were reviewed; their immutable checksums and revisions are recorded under
`solana-define-syscall` in [the applicability sources](../source-map/applicability.json).
The declared ranges also admit unlisted stable releases within each Cargo compatibility line,
under the recorded compatibility assumption. Those releases have not been inspected;
prereleases require explicit entries.

There is no relevant difference between 5.1.0 and 5.2.0: optional macro trailing commas and the
new curve-constant module do not change either call. Release 5.4.0 introduces a bulk declaration
macro that forwards the same signatures to `define_syscall!`. These declarations perform no
validation or cryptography themselves; the existing provider and runtime obligations still apply.

The representative source and native test remain
[solana-define-syscall 5.2.0](https://static.crates.io/crates/solana-define-syscall/solana-define-syscall-5.2.0.crate),
archive SHA-256 `bf8209ece2bd9f1450e672858ffc0e5c8c786ff6916d2a862b126dd0128f380f`,
SDK revision `882ea29f565810bfdf6a85700f95c004d24fceda`, under `define-syscall/`.

| Source | Reviewed declaration | SHA-256 |
| --- | --- | --- |
| [definitions.rs](https://github.com/anza-xyz/solana-sdk/blob/882ea29f565810bfdf6a85700f95c004d24fceda/define-syscall/src/definitions.rs) | SHA-512 line 25; MSM line 28 | `4fea9c6578e40f84f18f5826e1b380d0b1c3a8c6147b0036f94992adee7ae89f` |
| [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/882ea29f565810bfdf6a85700f95c004d24fceda/define-syscall/src/lib.rs#L33-L48) | Dynamic declaration macro | `737b180ccbb655a63db26c48a92996ddee2580f87bdde4f2e0aac0e86b81fa1e` |
| [curve_constants.rs](https://github.com/anza-xyz/solana-sdk/blob/882ea29f565810bfdf6a85700f95c004d24fceda/define-syscall/src/curve_constants.rs) | Edwards 0, line 8; Ristretto 1, line 11 | `edfdafc11c1029621f421b479b7f91690f322dad3ac046d835f12b2416fd2644` |

For 2.2.0 through 3.0.0, the dynamic branch requires only `!static-syscalls`.
From 4.0.0 onward it requires `!static-syscalls && (arch != bpf || !unstable-static-syscalls)`:
the first feature is a compiler target feature, the second a crate feature. The profiles retain
this difference without imposing architecture or crate-feature facts on the earlier releases.
There is no `target_os` gate. Static thunks are unregistered; these `extern "C"` declarations
have no unwinding exit. The runtime correspondence uses the separate Agave pin below.

Runtime correspondence uses Agave 4.3.2, revision
`a203300045b405f86c9c84308b2eae76af69ac3b`,
[syscalls/src/lib.rs](https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs)
(SHA-256 `30ff4ba8492d77a26a24da1aae5c46d646f00a939f974a705663e0f181495672`).
Registration at lines 398–425 requires `enable_sha512_syscall` or
`curve25519_syscall_enabled`, respectively.

## SHA-512

`sol_sha512(vals, val_len, result) -> u64` reads ordered 16-byte `(pointer, length)`
descriptors. The Agave `SyscallHash` (lines 2717–2788) checks the slice limit first,
charges base compute, validates the 64-byte output, then maps nonempty descriptors
(alignment 8 when checked), reads/charges/hashes each slice, remaps the output and writes it.
The limit is the `sha256_max_slices` setting of the hasher (lines 274–298), not the 512 limit of MSM.
The canonical return is status 0 with `Prims.sha512 slices`, whose width follows
from `Prims.sha512_length`; request state is unchanged. Slice order, empty and
repeated slices are retained; no segmentation-independence theorem is assumed.

Generic providers require 64 bytes on status 0; other u64 statuses have no output.
They also retain terminal exits.
A source binding must own the 64-byte result even for empty input; an excessive
count needs no memory. Checked, nonempty descriptors must be VM-aligned. Agave instead
checks the translated **host** address: no host/VM alignment equality is assumed,
and a VM-aligned call may still terminate on that check.

## Multiscalar multiplication

`sol_curve_multiscalar_mul(curve, scalars, points, count, result) -> u64` takes paired
32-byte scalar/point encodings (alignment 1), including encodings that fail decoding.
The handler of Agave (lines 1710–1831) checks `count > 512` before curve dispatch or any
pointer access. Invalid curves access no memory and return 1, or terminate when
`abort_on_invalid_curve` is enabled. Curves 0/1 charge compute and map scalars, then points;
successful decoding/arithmetic maps and writes the 32-byte result and returns 0.
Failure returns 1 without mapping the result. Zero count is allowed and skips input
mapping. Canonical ordinary returns preserve request state. The generic response
law also restricts returns to 0/1 and forbids success on invalid curves.

`Prims.curveMultiscalarMul` leaves decoding and arithmetic symbolic. `MsmWidth`
requires 32-byte outputs only for successful supported calls within the count limit;
it assumes neither decoding success nor a zero-input identity law. In
solana-curve25519 4.0.1 at SDK revision `a947d32fb1ab7d06b69bd96bd97eb4d002eb454e`,
[`Scalar::from_canonical_bytes`](https://github.com/anza-xyz/solana-sdk/blob/a947d32fb1ab7d06b69bd96bd97eb4d002eb454e/curve25519/src/scalar.rs#L17-L25)
rejects noncanonical scalars without modular reduction.
[`edwards.rs`](https://github.com/anza-xyz/solana-sdk/blob/a947d32fb1ab7d06b69bd96bd97eb4d002eb454e/curve25519/src/edwards.rs#L64-L74)
and [`ristretto.rs`](https://github.com/anza-xyz/solana-sdk/blob/a947d32fb1ab7d06b69bd96bd97eb4d002eb454e/curve25519/src/ristretto.rs#L64-L74)
use Dalek decompression: Edwards adds no canonical-y/subgroup/torsion checks;
Ristretto decoding is canonical. These are primitive interpretation obligations,
not input preconditions.

## Source ownership and validation limits

A source binding must preserve input shares and write output only on status 0;
failure must preserve old bytes, including uninitialized bytes. A supported, within-limit MSM
call owns a **separate** 32-byte result even on decoding failure. This sufficient
footprint excludes the unmapped failure output of Agave and input/output overlap.
Invalid-curve and excessive-count MSM calls own no memory.

A persistent memory context does not by itself connect physical memory to the
mathematical invocation state or its `InvState.buf`. Such a binding must relate
the live invocation state to memory and compose writes into that buffer, including
serialized-input writes in copying mode. Directly mapped account memory may have
additional effects. Pointer translation, compute exhaustion and termination are
outside these partial-correctness results; a successful request alone proves none
of them. Cryptographic arithmetic is not proved.

[Conformance](../../../tools/library-conformance/README.md)
records the extern calls on a host target with a scripted provider and replays
their observations against the registered models. This does not establish
provider correctness or sBPF execution.
