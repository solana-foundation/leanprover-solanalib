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
`solana-define-syscall` in [the applicability sources](../source-map/solana-define-syscall.json).
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

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:85ad56313a32ba6d -->
<a id="review-85ad56313a32ba6d"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact native reference into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The crate root imports the four raw syscall models and their capability catalog.

sol_sha256, sol_log_, sol_panic_ and abort of src/definitions.rs (lines 21, 10, 36, 37) instantiate the shared request-level families of Solanalib.Specs.Core.RawSyscall at their requests .hash .sha256 slices, .log message, .panic file line column and .abort, with the closed sample environment, which checks alignment and allows MAX_HASH_SLICES slices, for the satisfiability and execution witnesses; the sol_sha256 witness hashes two slices at an aligned vals.

Shared named syscall families with per-function release and dynamic-declaration selection.

Named source families have closed references, satisfiable samples and concrete executions. Reference defining packages and compatible-range profiles select those same families while retaining the dynamic-dispatch gates; macros do not transfer ownership. Wrapper families select only the Solana64 forwarding branches. The mathematical buffer is a fixed initial request snapshot. A physical memory interpretation must retain that snapshot for model indexing and compose ordered output stores into the actual returned invocation state.

The signature families retain concrete source preparation and canonical Agave CPI stages. Borrowed and owned stable-instruction contracts are separate; checked signatures use the first matching AccountInfo and the shared lease world. C and Rust raw declarations share the runtime family but require distinct pointer-layout interpretations. Closed consistency witnesses use declared mock callee results only.
<!-- /registry -->

<!-- registry:review:5094f94ba0affada -->
<a id="review-5094f94ba0affada"></a>

The signature families retain concrete source preparation and canonical Agave CPI stages. Borrowed and owned stable-instruction contracts are separate; checked signatures use the first matching AccountInfo and the shared lease world. C and Rust raw declarations share the runtime family but require distinct pointer-layout interpretations. Closed consistency witnesses use declared mock callee results only.
<!-- /registry -->

<!-- registry:review:ffe28c7df5555b69 -->
<a id="review-ffe28c7df5555b69"></a>

The defining solana-cpi syscalls module supplies the raw sol_get_return_data declaration. Its complete family is RawState.getReturnStep at every fixed runtime invocation: it returns full stored length, retains ordered output writes and the actual state, and preserves translation, overlap and terminal failures. The macro provider is dependency provenance and does not own this public contract. Exact source and dynamic-dispatch build selection remains per function.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Named source families have closed references, satisfiable samples and concrete executions. Exact reviewed defining packages and dynamic-dispatch build profiles select those same families; macros do not transfer ownership. Wrapper families select only the Solana64 forwarding branches. The mathematical buffer is a fixed initial request snapshot. A physical memory interpretation must retain that snapshot for model indexing and compose ordered output stores into the actual returned invocation state.
<!-- /registry -->

<!-- registry:review:079e6ebac962b669 -->
<a id="review-079e6ebac962b669"></a>

The complete reviewed functions are interpreted by the registered shared mathematical families and current-state references. All ordinary, error, callback and reached terminal outcomes are retained. Pin-specific borrow credits and signed resize stages, and logger initialized-prefix state and cleanup, are explicit; generic source representation remains separate.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

The source-owned pinocchio-log::logger::syscalls::sol_memcpy_ facade uses the same complete mathematical contract and reference as the inherited solana-define-syscall::definitions::sol_memcpy_ family. Its exact defining source profile is kept separately. The checksum-pinned pinocchio-log 0.5.1 source defines this exact item with the recorded argument order and result type. The source supplies an extern-C declaration, not a runtime implementation. The reviewed macro/module gates are recorded explicitly; macro expansion does not transfer defining-crate ownership.

The source-owned pinocchio-log::logger::syscalls::sol_memset_ facade uses the same complete mathematical contract and reference as the inherited solana-define-syscall::definitions::sol_memset_ family. Its exact defining source profile is kept separately. The checksum-pinned pinocchio-log 0.5.1 source defines this exact item with the recorded argument order and result type. The source supplies an extern-C declaration, not a runtime implementation. The reviewed macro/module gates are recorded explicitly; macro expansion does not transfer defining-crate ownership.
<!-- /registry -->

<!-- registry:review:0f30b0cfb5804209 -->
<a id="review-0f30b0cfb5804209"></a>

No abort definition exists through 3.0.0 (26 releases). All seven releases from 4.0.0 through 5.4.0 declare the same dynamic extern-C fn abort() -> !, including through the 5.4.0 generation macro. Its only modeled outcomes are actual provider terminal exits; an answering provider does not create a return value of !. The crate supplies a declaration, not an abort runtime implementation.
<!-- /registry -->

<!-- registry:review:75b423598790bb04 -->
<a id="review-75b423598790bb04"></a>

The eleven published releases from 2.2.0 through 5.4.0 share this dynamic paired-array/count ABI; the dispatch filters follow each release.
<!-- /registry -->

<!-- registry:review:bed7c13206ec1363 -->
<a id="review-bed7c13206ec1363"></a>

The definitions module is absent in the 22 releases through 2.1.21. All 11 releases from 2.2.0 through 5.4.0 have the same dynamic extern-C signature: fn sol_log_(message: *const u8, len: u64). The extra generation macro in 5.4.0 preserves the declaration. The declaration neither validates UTF-8 nor defines rendering or runtime effects. The generic provider may answer any byte message; the separately pinned canonical runtime terminates on invalid UTF-8. Native malformed-byte cases exercise that generic-provider boundary, not canonical-runtime UTF-8 acceptance.
<!-- /registry -->

<!-- registry:review:92ce085d6e1e6425 -->
<a id="review-92ce085d6e1e6425"></a>

There is no definition through 2.3.0 (25 releases). Version 3.0.0 introduces the four-argument declaration with no return annotation, so its return type is unit. A native returning provider was called twice and the call returned normally with the exact file bytes, line and column preserved. It is therefore incompatible with the existing never-returning family, even though the canonical runtime itself terminates. All seven releases from 4.0.0 through 5.4.0 declare the same dynamic extern-C four-argument function returning !; the 5.4.0 generation macro preserves it. Only provider terminal exits are outcomes of this family. These declarations do not establish a panic-runtime implementation theorem.
<!-- /registry -->

<!-- registry:review:5c1cb4fa3e7ac237 -->
<a id="review-5c1cb4fa3e7ac237"></a>

The definitions module is absent in the 22 releases through 2.1.21. All 11 releases from 2.2.0 through 5.4.0 have the same dynamic extern-C signature: fn sol_sha256(vals: *const u8, val_len: u64, hash_result: *mut u8) -> u64. Release 5.4.0 generates it through an additional define_syscalls! macro, which expands to the same define_syscall! invocation. This is declaration and call-boundary compatibility only. The crate does not implement the hash, slice-count check, translated-host alignment check, output-shape law or runtime state effects. All those remain requirements of the existing index/provider interpretation and the separately pinned Agave runtime binding.
<!-- /registry -->

<!-- registry:review:77c71d07debbb60f -->
<a id="review-77c71d07debbb60f"></a>

The four published releases from 5.1.0 through 5.4.0 share this dynamic descriptor/output ABI; see the per-release source review.
<!-- /registry -->

<!-- registry:review:768a71178f6244da -->
<a id="review-768a71178f6244da"></a>

The checksum-pinned solana-define-syscall 2.3.0 source defines this exact item with the recorded argument order and result type. The source supplies an extern-C declaration, not a runtime implementation. The reviewed macro/module gates are recorded explicitly; macro expansion does not transfer defining-crate ownership. The declared compatible range assumes preservation of this defining identity, argument order, pointer types, return type and dynamic-declaration gates. It does not broaden runtime registration, feature behavior or memory configuration.
<!-- /registry -->

<!-- registry:review:ce3110321f880316 -->
<a id="review-ce3110321f880316"></a>

The declared compatible range assumes the exact extern-C declaration of sol_create_program_address, including argument order, widths, return type and the recorded module/macro gates. Static thunks remain excluded; a declaration does not establish its runtime implementation or transfer defining-crate identity.
<!-- /registry -->

<!-- registry:review:938afd7b87ad5365 -->
<a id="review-938afd7b87ad5365"></a>

The declared compatible range assumes the exact extern-C declaration of sol_memcpy_, including argument order, widths, return type and the recorded module/macro gates. Static thunks remain excluded; a declaration does not establish its runtime implementation or transfer defining-crate identity.
<!-- /registry -->

<!-- registry:review:0990d68b8e9497ff -->
<a id="review-0990d68b8e9497ff"></a>

The declared compatible range assumes the exact extern-C declaration of sol_memset_, including argument order, widths, return type and the recorded module/macro gates. Static thunks remain excluded; a declaration does not establish its runtime implementation or transfer defining-crate identity.
<!-- /registry -->

<!-- registry:review:4de07d16c22dee79 -->
<a id="review-4de07d16c22dee79"></a>

Reference: solana-define-syscall 2.3.0. The declared [2.3.0, 3.0.0) range assumes preservation of the dynamic unsafe extern-C declaration, its three *const u8 pointers and two interleaved u64 counts in the exact recorded order, u64 result and module/macro dispatch gates. The Rust-suffixed name selects Rust instruction/account/seed data layouts; its calling convention remains C. CPI stays opaque under the unchanged runtime, successful-zero-only return and canonical translated copy-back conditions. Static thunks and nonzero-returning host stubs are separate behaviors.
<!-- /registry -->

<!-- registry:review:5470016f1e6c7833 -->
<a id="review-5470016f1e6c7833"></a>

The declared compatible range assumes the exact extern-C declaration of sol_invoke_signed_rust, including argument order, widths, return type and the recorded module/macro gates. Static thunks remain excluded; a declaration does not establish its runtime implementation or transfer defining-crate identity.
<!-- /registry -->

<!-- registry:review:efbb080f20f656a4 -->
<a id="review-efbb080f20f656a4"></a>

Reference: solana-invoke 0.4.0. The declared [0.4.0, 0.5.0) range assumes the same checked borrowed-buffer path: ordered instruction metas, first matching AccountInfo, writable/shared RefCell choice, lamports before data and immediate release of each temporary guard. Local AccountBorrowFailed remains an ordinary error; missing accounts reach the opaque runtime checks. StableInstructionBorrowed uses a ManuallyDrop header over the original ordered Vec descriptors of the caller, acquiring and destroying no buffer ownership. The scoped providers below preserve those used operations and representations; no Instruction::clone is required. The owned-clone and SDK 3 routes stay separate.
<!-- /registry -->

<!-- registry:review:9a90674563821f55 -->
<a id="review-9a90674563821f55"></a>

The declared compatible range assumes the Solana forwarding path: move the instruction into its ManuallyDrop stable header, preserve borrowed account and nested signer descriptors, call the exact raw invoke signature and convert its full status without cloning or dropping the moved buffers. CPI behavior remains supplied by the existing invocation interpretation.
<!-- /registry -->

<!-- registry:review:850b238b1cd2b109 -->
<a id="review-850b238b1cd2b109"></a>

The inspected 2.2.0 and 2.2.1 declarations have the same extern-C argument order and u64 result. Compatibility within 2.x assumes that declaration and selected macro expansion remain unchanged under the existing Solana cfg/ABI gates. The defining item belongs to solana-cpi; the macro provider supplies no runtime implementation.
<!-- /registry -->

<!-- registry:review:c5cf90c6e5262f9a -->
<a id="review-c5cf90c6e5262f9a"></a>

The 0.4.0 reference delegates to invoke_signed with empty seeds and retains ordered RefCell probes and the ManuallyDrop borrowed StableInstruction descriptors. Compatibility within 0.4 assumes this borrow/effect protocol and selected SDK 2.x representations remain unchanged. Version 0.5.0 changes resolved SDK providers; invocation remains opaque.
<!-- /registry -->

<!-- registry:review:ff9e9b188968fdf5 -->
<a id="review-ff9e9b188968fdf5"></a>

The two checked signatures perform the same ordered RefCell probes. The private StableInstructionBorrowed has a ManuallyDrop stable instruction and borrowed Vec descriptors, so its temporary header does not clone or destroy caller buffers. Exact dependencies differ between major SDK generations and are selected below. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->

<!-- registry:review:eaa07032ea8b5658 -->
<a id="review-eaa07032ea8b5658"></a>

The 0.5.1 archive is the inspected reference. The declared 0.5 range assumes the same full/zero-capacity branch, initialized-prefix writes, truncation, by-value Log destructor, receiver identity and partial state through formatter/drop unwind and double-unwind termination. Macro enablement, source layout and runtime interpretation remain separate.
<!-- /registry -->

<!-- registry:review:60b0df85f4722e4a -->
<a id="review-60b0df85f4722e4a"></a>

The 0.5.1 archive is the inspected reference. The declared 0.5 range assumes the same uninitialized backing array with length zero and no invented initialized suffix. Macro enablement, source layout and runtime interpretation remain separate.
<!-- /registry -->

<!-- registry:review:41434152873df17c -->
<a id="review-41434152873df17c"></a>

The 0.5.1 archive is the inspected reference. The declared 0.5 range assumes the same current initialized prefix and length forwarded to the Solana logger, preserving provider effects and terminal outcomes; the host UTF-8/println path stays outside the source profile. Macro enablement, source layout and runtime interpretation remain separate.
<!-- /registry -->

<!-- registry:review:67fcf6f56931f125 -->
<a id="review-67fcf6f56931f125"></a>

The 0.5.1 archive is the inspected reference. The declared 0.5 range assumes this exact dynamically dispatched extern-C memcpy declaration, argument order and unit return under the existing Solana and 64-bit gates. Macro enablement, source layout and runtime interpretation remain separate.
<!-- /registry -->

<!-- registry:review:85eb0cc39314aea2 -->
<a id="review-85eb0cc39314aea2"></a>

The 0.5.1 archive is the inspected reference. The declared 0.5 range assumes this exact dynamically dispatched extern-C memset declaration, u8 fill argument and unit return under the existing Solana and 64-bit gates. Macro enablement, source layout and runtime interpretation remain separate.
<!-- /registry -->

<!-- registry:review:730495133d19ff4c -->
<a id="review-730495133d19ff4c"></a>

The declared compatible range assumes the exact extern-C declaration of sol_set_return_data, including argument order, widths, return type and the recorded module/macro gates. Static thunks remain excluded; a declaration does not establish its runtime implementation or transfer defining-crate identity.
<!-- /registry -->

<!-- registry:review:a3fe9c9bb79a37a7 -->
<a id="review-a3fe9c9bb79a37a7"></a>

The declared compatible range assumes the 64-bit Solana forwarding call with the original data pointer and length and the existing return-data state interpretation. The host stub and runtime implementation are separate boundaries.
<!-- /registry -->

<!-- registry:review:9bb0de3a888e25af -->
<a id="review-9bb0de3a888e25af"></a>

Preserve the literal defining item, extern-C argument/result types and dynamic-declaration gates. Both static-syscalls target features and BPF unstable-static-syscalls remain excluded. Trailing-comma macro support and a later declaration-group macro do not change these declarations. The range does not change the fixed runtime profile, registration or memory configuration. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->
