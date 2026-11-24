# Solana library test reference

[README.md](README.md) gives the test and reproduction commands. This reference
describes native drivers, checked observations, preconditions and negative controls.
Version-specific corpus and driver names identify the exact source/build; shared
model declarations use their canonical library and function names.

## Families

A family owns Rust drivers, corpus files and one registered Lean module:

1. **Drivers** `rust/<driver>/`, members of compatible Cargo workspaces, discovered by
   their `driver.toml`:
   `corpora = [...]` (the corpus files it writes, exactly; names `[a-z0-9_]+`,
   unique across drivers), optional `inputs = [...]` (extra files it includes)
   and optional `unobserved = [...]` (see [Controls](#negative-controls)).
   The recorded inputs of a driver are its own files (Cargo.toml,
   `.cargo/config.toml`, driver.toml, `build.rs`, `src/**`), the sources of its
   path dependencies (`rust/recorder`, `rust/shim`, `rust/accounts`, family
   helper crates), its `inputs`, `native-pins.toml` and the Cargo manifests of
   its workspace, every member and their path dependencies. A change to any of
   these inputs requires recording that driver again. A file a hashed source includes (`#[path = ...]`,
   `include!`, `include_str!`, `include_bytes!`) must be among them, else
   recording and authentication fail. `run.py --record --driver D` writes only the corpus files of `D` and `corpus/manifests/D.json`. Drivers build separately, sharing a target directory within each workspace.
2. **Checkers** `SolanalibTest/Conformance/Library/Families/<Family>.lean`, defining
   `SolanalibTest.Conformance.Library.Families.<Family>.corpora : List (String × List Checker)`
   (corpus name and its checkers). Helper modules live in
   `SolanalibTest/Conformance/Library/Families/<Family>/`. `SolanalibTest/Conformance/Library/Registry.lean`
   is generated from the family modules (`run.py --generate-registry`);
   `--model-only` and the offline controls reject a stale one.

### Native dependencies

Each driver pins modeled direct and transitive registry dependencies with `=version`,
or names a public Git source at an exact revision. The source registry supplies the
modeled crate inventory; [native-pins.toml](native-pins.toml) adds reached serialization,
derive and cryptographic providers. Optional `pin-` aliases with
`default-features = false` constrain transitive versions without enabling features.
Required direct dependencies retain their declared features.

The 131 drivers belong to 16 [Cargo workspaces](rust/workspaces). Exact provider
versions determine which members can share a workspace. The runner compiles one
driver at a time so unrelated member features are not unified. The workspace
profiles preserve the selected panic, optimization and overflow settings.

Every recording discards the temporary workspace `Cargo.lock` and resolves afresh.
Incidental dependencies can select compatible releases. For an exact yanked pin,
the runner reads its checksum from the public crates.io index and seeds only that
package identity into the temporary resolution, without copying a dependency graph.
When a broad upstream range selects another modeled compatibility line, the runner
can select the unique exact version explicitly pinned by the workspace; ambiguous
choices fail. The subsequent build uses this fresh resolution with `--locked`.
No Cargo lockfile is committed or included in recording input hashes.

The `resolution` receipt lists the modeled packages actually selected by the
compiler unit graph, with versions, public origins and registry archive checksums.
It excludes unused workspace members and records unused optional pins separately.
Authentication checks these identities against the exact driver constraints and
reviewed archive checksums where available. It also checks source hashes, the
compiler/profile, build probes and complete corpus bytes. These are consistency
checks against supplied receipts; they do not independently reproduce native calls.
The scheduled native job performs that reproduction, records twice and fails on
any change to a complete corpus file.

Before running a direct Cargo control below, resolve its workspace with
`just test-native-library DRIVER EVIDENCE` from the repository root, using a fresh
evidence directory. The `--locked` controls then use that local resolution. Add
`--offline` only when all dependencies of the control are cached.

Builds use the
repository toolchain (`rust-toolchain.toml`). `--record` runs `rustc -vV` at
the repository root and in each driver directory, and requires the two to be
identical and to belong to the pinned nightly: its commit date is the date of the
channel or up to three days before. A `rust-toolchain` file under
`rust/` fails recording and authentication. Each manifest records the `rustc -vV` of the driver, and authentication checks it against the pinned
channel again. Builds use the host target
`x86_64-unknown-linux-gnu`, the selected workspace profile, and
`-A explicit_builtin_cfgs_in_flags --cfg target_os="solana"` for target units
only (`.cargo/config.toml`), so the libraries compile their Solana branches. A
driver that records the host branch of a library says so and sets empty rustflags.

The default panic strategy is `unwind`. Drivers with an explicit `scope` supply
a `[build_probe]` table in `driver.toml`, naming `--build-config`, the selected
profile and expected panic strategy. The existing launcher selects that profile
and checks the panic, target and scope observations of the executable before recording.
Authentication rejects a changed profile, panic or scope claim. Drivers without
this table still record and authenticate their compiler profile.

The `whole-signature-mock` and `projected-wrapper` scopes retain their mock
boundaries and require the compile-only `signature-check` feature to be disabled.
`linked-source` uses the same configuration checks for an actual source-call
driver. These scopes do not imply execution of an invocation body.

### Value operations

These families use independently pinned drivers and preserve the versioned
corpus names. Select a family with `--family NAME` or record its driver with
`--record --driver NAME`, using the [commands in the guide](README.md#reproduce-native-results).

| Family | Native driver | Checked observations |
| --- | --- | --- |
| [AddressComparison](SolanalibTest/Conformance/Library/Families/AddressComparison.lean) | [address-comparison-261](rust/address-comparison-261) | Six lexicographic comparisons against the fixed Address 2.6.1 native reference. |
| [ErrorNullable](SolanalibTest/Conformance/Library/Families/ErrorNullable.lean) | [error-nullable](rust/error-nullable) | 86 ProgramError 3.0.1 status conversions and 34 complete-key sentinel observations for MaybeNull 1.3.0 at Address 2.6.1, reexported by Pinocchio 0.10.2. |
| [TokenStateVersions](SolanalibTest/Conformance/Library/Families/TokenStateVersions.lean) | [token-state-interface-3-1-1](rust/token-state-interface-3-1-1) | 12 concrete Mint 3.1.1 clones: all five fields, unchanged receiver, uninitialized values, distinct None and Some(zero), and the recorded host layout. |

The nullable native cases use the reviewed Address instance. Its generic query,
destructor, unwind and terminal effects have separate [Lean scenario tests](../../packages/solanalib-specs/SolanalibTest/Specs/Core/ErrorNullable.lean).
Build and range controls for [error and nullable](../../packages/solanalib-specs/SolanalibTest/Specs/Core/ErrorNullableProfiles.lean),
[comparison](../../packages/solanalib-specs/SolanalibTest/Specs/SolanaAddress/Address.lean) and
[Mint](../../packages/solanalib-specs/SolanalibTest/Specs/SplToken2022Interface/state/Mint.lean)
check accepted and rejected versions and required field providers. These declared
ranges are separate from the fixed native references. Native observations and
host layouts do not establish SDK body correctness or sBPF layout equivalence.

### Raw runtime and SDK utilities

`RawRuntime` and `Utilities` keep the native corpus names
`raw_runtime_solana_define_syscall_2_3_0`, `utility_split222` and `utility_split230`.
The matching drivers are `raw-runtime-define2`, `utility-split222` and
`utility-split230`. Library model roots have no release suffix; native names
identify the recorded dependency versions.
Native evidence remains limited to those pinned builds.

The three corpora contain 267 observations: 32 raw declarations, 196 split222
SDK calls and 39 split230 getters. Their 15 registered checker keys select all
267 observations, including the 39 split222 Clock and Rent getter records.
Getter controls check String contents, capacity, freshness and liveness. Hash
controls distinguish the zero tail of a partial write and the singleton empty slice.
Mathematical tests also retain provider unwind and terminal outcomes, which
these finite native fixtures do not cover.

Raw SHA-256 reuses its existing request-level family. The initialized hash,
unconditional host stdout and owned String-error getters use distinct
`zero_initialized`, `host_stdout` and `string_error` variants. The raw driver
uses a symbolic provider for published declarations; SDK drivers run wrappers
against scripted providers. These runs do not execute Agave or prove SDK bodies,
cryptography or target equivalence. Reference builds, compatible ranges and remaining
ABI obligations are recorded in the [source/API registry](../../packages/solanalib-specs/source-map.json), [applicability profiles](../../packages/solanalib-specs/VERSION_COMPATIBILITY.md) and [binding guide](../../packages/solanalib-specs/BINDINGS.md).

### Registered checker selection

`--registered-checkers` authenticates the complete corpus and driver
inputs, then joins exact `(corpus, function, generics)` keys to the compiled
checkers. Every record requires a checker except the fixed record identities in
`checker_selection.KNOWN_OMISSIONS`, which names the exact versioned corpus,
record ID, function and generic arguments. The family sections below describe
these unchecked operations. A related catalog entry or shared model does not
itself supply a checker for a recorded call.

The unmatched identities must equal that set exactly. A removed checker, a new
unknown function or generic instantiation, an extra omitted observation, or a
stale exception fails before replay. Extending a partial corpus in a later PR
requires reviewing its exact versioned identities and updating the set explicitly.
The Lean runner still checks the identity and multiplicity of every omission. Counts
are accounting checks, not the coverage baseline. Without this flag, every record
requires a registered checker.

Complete runs also require explicit entries for wholly omitted corpora and
reject missing files or policy corpora. Their bytes remain authenticated, but
they receive no Lean checker or count credit. The complete corpus directory
and post-authentication file hashes are checked even when no key selects a
corpus; an unknown empty corpus is not an implicit exception.

Omitted records do not count as model conformance. Their counts and controls
without a selected target are reported in `run-status.json` and
`selection-omitted-controls.json`. Original corpus and manifest files stay intact.
An omission can concern an unregistered function or an unselected release or
callable alias of a checked model. A compatible profile supplies neither a
source binding nor a conformance result for that native row.
The synthetic selector controls exercise the real Lean runner after
`lake build SolanalibTest.Conformance.Library.Runner` in this directory:
`SOLANA_CONFORMANCE_SELECTION_LEAN=1 python3.12 -m unittest test_checker_selection`.
They test the harness and execute no Rust.

Manifests identify checked inputs; they do not independently establish that Rust
emitted the corpus. CI runs `--model-only --registered-checkers` over the complete
compiled registry and authenticates every retained corpus. It caches successful
counts and omission receipts by exact model, registry, harness, toolchain and
native input Git entries. Python controls run on documentation and unrelated
changes too. Fresh native recording is a separate `run.py --record --twice` check.

## Method

### Recording

`rust/recorder` (no dependencies) writes the records: function identity,
generic instantiation, state before, arguments, outcome. Cases are
deterministic: `run.py --record --twice` (as `run.sh` runs it) records each
driver twice and requires byte-identical corpus files. `--record` first runs
the self-tests of `rust/shim` and `rust/accounts`.

### Syscalls

Under `target_os = "solana"` every pinned crate imports the `sol_*` syscalls of the runtime through `solana-define-syscall` (3.x to 5.x) as `extern "C"`
functions. `rust/shim` defines them for the test:

- Each call appends a **request** to a log: the syscall name and its
  arguments as the runtime would read them (bytes, seeds, the prepared CPI
  instruction, account infos and signer seeds, the initial bump byte, a null
  result pointer).
- A call that returns data consumes the next **scripted reply** the case chose
  (return value, output bytes, program id, bump, CPI account effects), in call
  order; each reply names the syscall it answers, and a missing or mismatched
  reply fails the recording. Replies are applied as agave applies results:
  sysvar getters and `sol_get_sysvar` write only on status 0 and at most the size of the
  sysvar or the requested length; `sol_get_return_data` returns the length of the
  return data `len` (the value of the reply, which must equal its data
  length) and writes `min(length, len)` bytes and the program id only when
  that is nonzero. Memory syscalls (`sol_memcpy_`, `sol_memmove_`, `sol_memset_`,
  `sol_memcmp_`) perform the operation and log it.
- A shim assertion (an out-of-range CPI account write, a return-data reply
  without a program id or whose value differs from its data length) and a panic that cannot unwind (a panic inside a syscall, or a failed `unsafe`
  precondition check of the debug build) end the case with reason
  `shim-fault`, and the recording fails: these are faults of the test, not
  program behavior.
- The state before a call holds `"syscalls": {"replies": script, "log": []}`;
  the state after it the unconsumed replies and the full log.

The shim therefore tests the **program side** only: what a library asks the
runtime, in which order, and what it does with the answer. The behavior of the runtime (hashing, address derivation, sysvar contents, CPI execution) is the choice of the
case, exactly as the models take it from an explicit provider.

Each shim case runs in a **forked child process**: syscalls that do not return
can end the case without ending the recorder, and cases cannot affect each
other.

The raw syscall declarations themselves (`sol_sha256`, `sol_log_`, `sol_panic_`
and `abort` of solana-define-syscall 5.1.0, registered as request-level models)
are also called directly, by `rust/runtime-pinocchio-0-11-1` (corpus
`solana_define_syscall_5_1_0`). They are decided on these new direct calls
rather than on the existing `hashv` and `sol_log` records because those link
other versions of the crate (solana-sha256-hasher 3.1.0 links 4.0.1 and
solana-msg 3.1.0 links 5.2.0), and no record calls `sol_panic_` or `abort`;
The pinocchio 0.11.1 driver already links 5.1.0 through pinocchio 0.11.1.

`rust/raw-syscalls-5-2-0` calls the ordinary `sol_sha512` and
`sol_curve_multiscalar_mul` declarations of **solana-define-syscall 5.2.0**
directly through the shared `rust/shim`, using its reply queue, request log
and process isolation alongside the other syscalls.
The shared handlers write exactly 64 bytes for a successful SHA-512 reply and 32 for a
successful multiscalar reply; failures do not write. It rejects malformed
scripts as harness faults. These records check the ABI of the declarations and the observations of the
caller under an explicit provider. They do not execute the
Agave handlers or validate cryptographic implementations.

### CPI

`sol_invoke_signed_c` logs the prepared `SolInstruction` (program id, account
metas, data), the `SolAccountInfo` array (key, lamports, data, owner, rent
epoch, flags) and the signer seeds, applies the account effects of the reply (the writes of the
callee to lamports, data and owner, through the account
memory of the caller) and returns the value of the reply. `sol_invoke_signed_rust` is decoded by
the driver, whose crate versions fix the Rust layouts. The invocation itself
stays opaque, as in the models: the reply is the outcome of the external contract.
A failed CPI never returns to the program in the runtime, so cases record it
as a terminal reply where the caller ignores the return value (pinocchio,
solana-instruction-view). The `invoke_signed` of solana-cpi converts a nonzero
return value into `Err` (`ProgramError::from(u64)`), and the families that
record it (Anchor `transfer`, TokenInterface `bare_mint_cpi_error`) record that
returned `Err`; their sections say so.

### Accounts and the input region

`rust/accounts` builds the serialized program input of the loader (BPF loader ABI
v1, aligned, as `agave` writes it) from an account list: account count;
per account a duplicate marker, or the `0xff` marker (the borrow
state of the account-view), signer/writable/executable flags, the 4-byte resize/original-length
field, key, owner, lamports, data length, data with 10 KiB of realloc space
and alignment padding, rent epoch; then instruction data and program id, in a
16-aligned buffer. The entrypoint deserializers (`pinocchio::entrypoint`,
`solana_program_entrypoint`) run on it unchanged. After the call the region is
read back at the offsets of the original layout, every byte: the account-count
word; per account the marker (the account-view borrow state), flag bytes, the
4-byte field, key, owner, lamports, data length, data, every spare byte up to
the original length plus 10 KiB, the alignment padding and the rent epoch;
the 7 padding bytes of each duplicate entry; instruction data and program id. The
state before holds `"input"` as the account list or the read-back region, the
state after the read-back region (some families use the key `region`).

Every account state after the call is covered by one rule, applied by the
runner itself:

- a read-back region (state key `input` or `region`) must have its count word
  and a region before;
- a `frame` (AccountsV1: the region bytes outside the projection) must equal
  the frame before;
- other account lists fail, unless the driver declares `region = "none"` in
  `driver.toml` (it builds its accounts as values, with no loader region; today
  token-interface-onchain).

For a read-back region, the runner requires the bytes no model represents to
be unchanged by the call. It compares them with the region before (under the
same key, else under the other one):

- the count word, the instruction data and the program id;
- the padding of each duplicate entry;
- the alignment padding of each account, rent epoch and spare bytes, every byte of
  each.

Against an account list (a fresh serialization) the count is the number of
entries, and the padding and spare bytes must be zero. A function whose calls
may change spare bytes is listed in the `driver.toml` of its driver as
`spare_writes = ["<function glob>"]`. For those functions the models of the family
must represent every spare byte. Today the list is the `AccountView::close` of accounts-v2, which leaves the closed data behind as spare bytes; the projection of the
family compares the whole data area. A listing that matches no
record fails.

The shared region reader (`Runtime.region`) also gives the first nonzero spare offset of each account (`spareNonzeroAt`). It computes the offset from the
recorded spare bytes and requires it to agree with the recorded summary
`spare_nonzero_at`.

### Exit mapping (fixed)

| Native exit | Record | Model outcome |
| --- | --- | --- |
| return, including `Err` | `{"exit": "returned", "result", "state"}` | `Outcome.returned` |
| Rust panic caught by `catch_unwind` | `{"exit": "unwound", "reason", "state"}` (state observed after unwinding) | `Outcome.unwound` |
| `sol_panic_`, `abort`, a reply marked terminal | `{"exit": "terminated", "reason", "detail", "syscalls"}` | `Outcome.terminated` |
| the child process dies otherwise | `{"exit": "terminated", "reason": "process", "detail": {"status"}}` | `Outcome.terminated` |
| shim fault, panic that cannot unwind | the recording fails | none |

A terminated outcome has no post-state; its `syscalls` field is the log up to
the terminal call. A host build unwinds where the panic handler of an sBPF program
calls `sol_panic_`; a family whose model fixes the aborting panic strategy
decides its registered contract, which states which exits it admits, rather
than mapping exits itself. A family with empty `Unwind`/`Terminal` types admits
no such record, so an observed panic of a function modeled as non-panicking is
a mismatch.

### Case selection (family Codecs)

The corpus keeps every distinct behavior once or twice rather than every
input. The rule, applied by the drivers:

1. **Primitive decoders** (`deserialize_reader` of `u8`, `i8`, `bool` and the
   `VerificationLevel` tag): all 256 tag bytes (each followed by one trailing
   byte for the tag), the empty input and trailing bytes. Wider integers: boundary values (0, 1, sign and byte
   boundaries, minimum, maximum), every proper prefix of one encoding and
   trailing bytes. `f64`: every IEEE-754 class, including signalling and
   payload NaNs and both infinities.
2. **Composite decoders** (`deserialize_reader` of `Option<T>`, `[T; N]`,
   `Vec<T>`, `Address`, `StakeStateV2`, `PriceFeedMessage`, `PriceUpdateV2`):
   `Option` tags 0, 1, 2 and 255; invalid enum tags (including `u32::MAX` and
   big-endian tags for `StakeStateV2`); each variant exactly and with trailing
   bytes or account padding (200-byte stake account, 126-byte price-update
   tail); and two truncation classes per field: cut at the start of the field (the
   field is missing) and one byte into it (the field is short). `Vec` adds
   lengths 0 to 3 and `u32::MAX` with a short body; borsh 0.10.4
   `deserialize_reader` of `Vec<T>` (heap requests recorded) also takes
   `Option<u64>` elements (16 bytes) and, per element type, lengths one below
   and at the `hint::cautious` bound `4096 / size_of::<T>()` with a one-element
   body and above it with one element more than the bound (the `push` growth),
   and for `u8` a 1 MiB + 1 body and a 3 MiB length with 1 MiB + 5 bytes (the
   `resize` beyond the 1 MiB initial buffer).
3. **Wrappers** (`deserialize`, `try_from_slice`) at each `Self`: the inputs of
   rule 1 or 2 are grouped by the outcome class of `deserialize_reader` on them
   (`Ok`, or the error kind and message with numbers removed, or a panic; and
   whether bytes remain). From each class the first and the last input are
   kept, in recording order (for truncations, the shortest and longest
   prefix), at most 20 per `Self`; the largest set has 12. So every error class,
   the empty input, success with and without trailing bytes and each truncation
   class reach each wrapper.
4. **Serializers**: boundary values per type (for `u8`: 0, 1, 127, 128, 255),
   each with the recording writer failing at every call index up to one past
   the last call, and once over `Vec<u8>`.
5. **bytemuck**: `bytes_of` at three aligned addresses per value;
   `try_from_bytes` at the exact size for start offsets 0 to 8 modulo 16 and at
   every other length (0 to `size + 1`) for offsets 0 and 1, since the size
   check precedes the alignment check; `zeroed` once per type.
6. **No-std `write_all`** (borsh 1.6.1 without `std`, driver
   `borsh-1-6-1-nostd`, corpus `borsh_1_6_1_nostd_io`): each branch of the
   loop over a scripted writer that implements only `write`. The cases are an
   empty buffer (with and without a script that would fail), one call taking
   everything, partial counts (one byte at a time, two at a time, 31 then 1),
   `Ok(0)` first and after a partial count, counts above the remaining length
   (by one, after a partial count, `usize::MAX`), `Interrupted` (custom and
   simple errors, retried once and twice, after a partial count, followed by
   `Ok(0)` or by another error), other errors (custom and simple, the `WriteZero` of the writer, after a partial count) and a panic of `write`, first and
   after a partial count.

The drivers also assert during recording that the remaining slice of a decoder is a
suffix of its input (same memory); this native-only property is checked, not
stored.

Serializers run over two writers `W`: the `RecordingWriter` of the recorder, whose
`write_all` logs each chunk and fails at a chosen call index (every index up to
one past the last call), and `Vec<u8>` with two bytes already present. `write` and `flush` are logged too, so a call the
models do not describe becomes a mismatch.

The no-std `write_all` runs over the `ScriptedWriter` of the driver: its call `k`
answers the `k`-th scripted response (a count, an error, or a panic of the
writer) and later calls take the whole buffer. Its state is the log of its
calls; `flush` is logged, and the record reader rejects it. The recording
build unwinds, so the slice panic of `&buf[n..]` is recorded as an unwind with
the message of core; the checker instantiates the panic callback of the model with that
unwind. The driver links the system allocator, so the checker instantiates the
allocation callback of the message of the `WriteZero` error with a return.

### Corpus format

`corpus/<name>.json` holds one record per line:

| Field | Meaning |
| --- | --- |
| `id` | stable case name, unique within its corpus file |
| `function` | Exact Rust item path used by the native driver and checker |
| `generics` | concrete generic arguments by parameter name (`Self`, `T`, `N`, `R`, `W`) |
| `layout` | `size_of`/`align_of` of the instantiation, for layout-indexed models (bytemuck; the element `T` of borsh 0.10.4 `Vec<T>` and `hint::cautious`) |
| `state` | state before the call |
| `args` | arguments |
| `outcome` | `{"exit": "returned", "result", "state"}`, `{"exit": "unwound", "reason", "state"}` or `{"exit": "terminated", "reason", "detail", "syscalls"}` |
| `observed` | optional native-only observations, never compared (borsh 0.10.4 `hint::cautious`: the record it is derived from and the allocation size) |

Encodings: byte sequences as lower-case hex, in which every maximal run of
at least 64 zero bytes is written `[N]` (its decimal length; e.g. the realloc space of an account `[10240]`), a canonical form that `run.py` validates and the `parseHex` of Lean expands; integers exact; `f64` as the hex
of its 64 bits; `Option` as `null` or `{"some": v}`; `Result` as `{"ok": v}` or
`{"err": e}`; `io::Error` as its `ErrorKind` Debug name and `to_string()`;
`PodCastError` as its name; enums as `{"variant", "fields"}`. The `"syscalls"` field of a state holds the script and log of the shim ([Syscalls](#syscalls)), its
`"input"` field the loader input region ([Accounts](#accounts-and-the-input-region)).
The decoders of the Codecs family at `R = &[u8]` record the slice before
(`state.slice`) and after the call; its bytemuck addresses are
`0x1000 + offset` inside a 16-aligned buffer, which keeps every residue modulo
the tested alignments and makes the corpus independent of address-space
randomisation.

### Checking (Lean)

The root `solanalib` Lake package owns the model libraries and the conformance Lean modules, so the runner evaluates the references of the current checkout. The conformance executable reads every registered corpus file and, for each record, parses state, arguments and
outcome into the types of the model at one family index and **decides the registered
relation or contract on the recorded outcome**:

- a reference registered as the graph of a function (`returnsOf model`, the model of a plain contract, `Callback.ofFunction`) is decided by evaluating that
  registered function (with a theorem proved by `rfl` where the registered
  name differs from the evaluated function);
- a relation over callbacks or providers is decided through an iff lemma
  between the registered relation and an executable decider, the graph lemma of the model or one proved in the family module, at the registered name, with
  the index callbacks set to the function forms of the registered members they
  stand for.

Each checker declares the registered constants it decides (`decides`). The
audit of `--model-only` reads every checker of the `corpora` of a family by
weak-head reduction to `Checker.mk` and takes its decision code, the `check`
and `checkModels` fields, with the transitive closure of the constants they
use through the types and values of the SolanalibTest.Conformance.Library declarations. Each
declared name must be a registered contract, reference, family, sample or run
of the specs source map, and the closure of that checker must use it; a
registered model of the Rust function of the checker (the `rust_names` of the source map) that the closure uses must be declared. The audit only shows
that the code mentions those names (a dead mention passes it). That the code
also decides something is shown by the per-checker semantic control (see
Negative controls), and that a declared model belongs to the function of the checker by the `rust_names` rule below. A declared name decides the model it identifies: a
name of one model only, or the receiver of an observation (`{projection,
receiver}`) whose projection the checker code uses. `decides.json` lists,
per decided model, its checkers and whether the `requires` of its contract reduces
to `True`. A control audits the `address` checker of AccountsV2 with `decides :=
[pool "close"]`, and the run fails unless the audit reports both problems. A
checker that decides several models (an API model and its observation)
reports one verdict per model (`checkModels`), and a record is admitted only
if every model admits it. In a run over every family, the registered models
minus the decided ones must be exactly those of `not-tested.toml` (see Not
tested).

A checker decides a model on the records of its own function: the source-map `rust_names` of each declared model (through the API entries that list it) must include the `function` of the checker. Observations, shared and supporting
models, and models the source map binds to no Rust item are listed with the
deciding function in `cross-function.toml`, and the table below is generated
from it. A declared model that is in neither place fails the audit, and so
does a listing no checker uses in a run over every family.

<!-- cross-function:begin (generated by run.py --generate-registry) -->
| Model | Checker function | Family | Reason |
| --- | --- | --- | --- |
| `solana-account-info::AccountInfo::clone_observation` | `<solana_account_info::AccountInfo<'a> as core::clone::Clone>::clone` | AccountsV1 | Observation of the call, with no Rust item of its own in the source map; decided on the records of `<solana_account_info::AccountInfo<'a> as core::clone::Clone>::clone`. |
| `solana-address::Address::find_program_address` | `solana_address::syscalls::<impl solana_address::Address>::find_program_address` | Address | The api entry of the source map for this model binds `solana_address::syscalls::<impl solana_address::Address>::find_program_address` only to `solana-address::Address::find_program_address_solana`; this model is decided on the records of the same Rust function. |
| `solana-address::Address::is_on_curve` | `solana_address::Address::is_on_curve` | Address | The api entry of the source map for this model binds `solana_address::Address::is_on_curve` only to `solana-address::Address::is_on_curve_solana`; this model is decided on the records of the same Rust function. |
| `solana-address::Address::try_find_program_address_solana` | `solana_address::syscalls::<impl solana_address::Address>::try_find_program_address` | Address | Registered without an api entry (no `rust_names`); decided on the records of `solana_address::syscalls::<impl solana_address::Address>::try_find_program_address`. |
| `anchor-lang::ToAccountInfo::to_account_info_observation` | `<T as anchor_lang::ToAccountInfo<'info>>::to_account_info` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `<T as anchor_lang::ToAccountInfo<'info>>::to_account_info`. |
| `anchor-lang::accounts::account::Account::try_from_observation` | `anchor_lang::accounts::account::Account::<'a, T>::try_from` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::accounts::account::Account::<'a, T>::try_from`. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_mut_observation` | `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_mut` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_mut`. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_observation` | `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load`. |
| `anchor-lang::accounts::account_loader::AccountLoader::try_from_observation` | `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::try_from` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::try_from`. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_from_observation` | `anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::try_from` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::try_from`. |
| `anchor-lang::context::CpiContext::new_with_signer_observation` | `anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer`. |
| `anchor-lang::error::Error::from_anchor_error_observation` | `<anchor_lang::error::Error as core::convert::From<anchor_lang::error::AnchorError>>::from` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `<anchor_lang::error::Error as core::convert::From<anchor_lang::error::AnchorError>>::from`. |
| `anchor-lang::error::Error::with_pubkeys_observation` | `anchor_lang::error::Error::with_pubkeys` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::error::Error::with_pubkeys`. |
| `anchor-lang::error::Error::with_values_observation` | `anchor_lang::error::Error::with_values` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_lang::error::Error::with_values`. |
| `anchor-spl::token::accessor::amount_observation` | `anchor_spl::token::accessor::amount` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_spl::token::accessor::amount`. |
| `anchor-spl::token::transfer_observation` | `anchor_spl::token::transfer` | Anchor | Observation of the call, with no Rust item of its own in the source map; decided on the records of `anchor_spl::token::transfer`. |
| `solana-instruction::Instruction::new_with_bincode` | `solana_instruction::Instruction::new_with_bincode` | Instructions | Registered without an api entry (no `rust_names`); decided on the records of `solana_instruction::Instruction::new_with_bincode`. |
| `solana-instruction::Instruction::new_with_wincode` | `solana_instruction::Instruction::new_with_wincode` | Instructions | Registered without an api entry (no `rust_names`); decided on the records of `solana_instruction::Instruction::new_with_wincode`. |
| `solana-system-interface::instruction::create_account` | `solana_system_interface::instruction::create_account` | Instructions | The api entry of the source map for this model binds `solana_system_interface::instruction::create_account` only to `solana-system-interface::instruction::create_account_operational`; this model is decided on the records of the same Rust function. |
| `solana-system-interface::instruction::transfer` | `solana_system_interface::instruction::transfer` | Instructions | The api entry of the source map for this model binds `solana_system_interface::instruction::transfer` only to `solana-system-interface::instruction::transfer_operational`; this model is decided on the records of the same Rust function. |
| `pinocchio::sysvars::instructions::Instructions::load_current_index` | `pinocchio::sysvars::instructions::Instructions::<T>::load_current_index` | Runtime | `Ref`-backed support model with no Rust item; decided on the records of `pinocchio::sysvars::instructions::Instructions::<T>::load_current_index` at `T = Ref<'_, [u8]>`. |
| `pinocchio::sysvars::instructions::Instructions::load_instruction_at` | `pinocchio::sysvars::instructions::Instructions::<T>::load_instruction_at` | Runtime | `Ref`-backed support model with no Rust item; decided on the records of `pinocchio::sysvars::instructions::Instructions::<T>::load_instruction_at` at `T = Ref<'_, [u8]>`. |
| `pinocchio::sysvars::instructions::IntrospectedInstruction::get_instruction_data` | `pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_instruction_data` | Runtime | `Ref`-backed support model with no Rust item; decided on the records of `pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_instruction_data` at `T = Ref<'_, [u8]>`. |
| `pinocchio::sysvars::instructions::IntrospectedInstruction::get_program_id` | `pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_program_id` | Runtime | `Ref`-backed support model with no Rust item; decided on the records of `pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_program_id` at `T = Ref<'_, [u8]>`. |
| `spl-token-2022-interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee` | `spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee` | TokenInterface | The api entry of the source map for this model binds `spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee` only to `spl-token-2022-interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee_live`; this model is decided on the records of the same Rust function. |
| `spl-token-2022-interface::instruction::close_account_value` | `spl_token_2022_interface::instruction::close_account` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::instruction::close_account`. |
| `spl-token-2022-interface::instruction::initialize_account3_value` | `spl_token_2022_interface::instruction::initialize_account3` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::instruction::initialize_account3`. |
| `spl-token-2022-interface::instruction::transfer_checked_value` | `spl_token_2022_interface::instruction::transfer_checked` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::instruction::transfer_checked`. |
| `spl-token-2022-interface::instruction::withdraw_excess_lamports_value` | `spl_token_2022_interface::instruction::withdraw_excess_lamports` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::instruction::withdraw_excess_lamports`. |
| `spl-token-2022::onchain::invoke_transfer_checked_value` | `spl_token_2022::onchain::invoke_transfer_checked` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022::onchain::invoke_transfer_checked`. |
| `spl-token-interface::instruction::initialize_account3_value` | `spl_token_interface::instruction::initialize_account3` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_interface::instruction::initialize_account3`. |
| `spl-token-interface::instruction::transfer_value` | `spl_token_interface::instruction::transfer` | TokenInterface | Value model of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_interface::instruction::transfer`. |
| `spl-token-2022-interface::extension::BaseStateWithExtensions::get_extension` | `spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension` | TokenInterface | Observation of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension`. |
| `spl-token-2022-interface::extension::BaseStateWithExtensions::get_extension_types` | `spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_types` | TokenInterface | Observation of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_types`. |
| `spl-token-2022-interface::extension::StateWithExtensions::unpack` | `spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack` | TokenInterface | Observation of the call, with no Rust item of its own in the source map; decided on the records of `spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack`. |
| `shared-token::amount` | `pinocchio_token::state::account::Account::amount` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::amount` | `pinocchio_token_2022::state::account::Account::amount` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::decimals` | `pinocchio_token::state::mint::Mint::decimals` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::decimals` | `pinocchio_token_2022::state::mint::Mint::decimals` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::mint` | `pinocchio_token::state::account::Account::mint` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::mint` | `pinocchio_token_2022::state::account::Account::mint` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::owner` | `pinocchio_token::state::account::Account::owner` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::owner` | `pinocchio_token_2022::state::account::Account::owner` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::state` | `pinocchio_token::state::account::Account::state` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `shared-token::state` | `pinocchio_token_2022::state::account::Account::state` | TokenViews | Shared token-state model with no Rust item; the getter of each library version decides it on its own records. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_init_observation` | `anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::load_init` | AnchorLoader | The supporting initialization observation is decided on the same actual load_init records as the primary owned family. It has no separate Rust call identity and does not replace owned diagnostic/guard cleanup. |
| `anchor-lang::accounts::account::Account::deref_mut` | `<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as core::ops::deref::DerefMut>::deref_mut` | AnchorViews | The exact recorded Anchor 1.1.2 method uses the same registered canonical view model. Its source-map alias is listed here for native checker accounting. This supplies no additional API, source interface, Rust body, or cross-version applicability claim. |
| `anchor-lang::accounts::borrowed_info_ref` | `<anchor_lang::accounts::program::Program<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref` | AnchorViews | The exact recorded Anchor 1.1.2 method uses the same registered canonical view model. Its source-map alias is listed here for native checker accounting. This supplies no additional API, source interface, Rust body, or cross-version applicability claim. |
| `anchor-lang::accounts::wrapper_key` | `<anchor_lang::accounts::program::Program<'_, T> as anchor_lang::Key>::key` | AnchorViews | The exact recorded Anchor 1.1.2 method uses the same registered canonical view model. Its source-map alias is listed here for native checker accounting. This supplies no additional API, source interface, Rust body, or cross-version applicability claim. |
| `anchor-lang::accounts::borrowed_info_ref` | `<anchor_lang::accounts::interface::Interface<'info, T> as core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref` | AnchorViews | The exact recorded Anchor 1.1.2 method uses the same registered canonical view model. Its source-map alias is listed here for native checker accounting. This supplies no additional API, source interface, Rust body, or cross-version applicability claim. |
| `anchor-lang::accounts::wrapper_key` | `<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key` | AnchorViews | The exact recorded Anchor 1.1.2 method uses the same registered canonical view model. Its source-map alias is listed here for native checker accounting. This supplies no additional API, source interface, Rust body, or cross-version applicability claim. |
<!-- cross-function:end -->

The runner does not evaluate the `requires` predicate of a contract by itself: a
checker decides the registered reference relation, or the contract where the
reference fixes an execution strategy the native run does not follow. Passing
the reference check alone does not show that a recorded input satisfies a
precondition; Preconditions below says how records are kept inside each
non-trivial one.

### Preconditions (`requires`)

Audit logs retain canonical Lean declaration names. The precondition check recognizes `Solanalib.Contracts.Model.requires`; SDK contract names and all other names still match
exactly. Family metadata uses the canonical `Solanalib.Contracts.Model.Family` projections.

`decides.json` records, for every decided model, whether the `requires` of its contract reduces to `True`. A record outside a precondition tests behavior
the contract leaves open, so every decided model whose `requires` does not
reduce to `True` is handled in one of two ways:

1. Each checker of the model lists it in `decidesRequires`. Its decision code
   then rejects a record outside the precondition. The audit requires that
   code to use `Solanalib.Contracts.Model.requires` and the registered
   contract of the model, typically
   `if decide (contract.requires before args) then ... else throw ...`, with a
   `Decidable` instance from an iff theorem where the predicate is not
   computable as stated.
2. The model is listed in `requires-open.toml` (`id`, the deciding family as
   `detail`, `reason`). The reason says why every record satisfies the
   precondition (through the parser, the index, or a named theorem) or what is
   open.

Each precondition a checker decides must also be exercised, in one of three
ways:

1. A family control mutates a record of that checker and requires it to be
   rejected as outside the precondition (see below).
2. `requires-theorems.toml` lists a `[[theorem]]`: kernel-checked negative
   evidence. Its statement, under its binders, is `¬ P` or `b = false`. Here
   `P` is the `requires` of the model (or a predicate the `requires` unfolds to),
   and `b` is `decide P` or the Boolean of a decider.
3. `requires-theorems.toml` lists a `[[trivial]]`: the precondition is trivial
   at the decided index. Its statement is `requires … ↔ True` (or `requires …`)
   at exactly the index the checker uses (or that index unfolded once).

The audit reads the shape of each statement. A theorem in either list must also use
a decider of that model. A decider is a declaration of the code of the checker that
mentions `requires` and the contract of the model (directly or through one family
alias), a family declaration such a declaration uses directly, or a family
decision procedure of a predicate the `requires` unfolds to. Core instances and
helpers of other models do not count.

Where the deciders of a checker are generic, so that none mentions the model, the
rules depend on the list. A negative theorem stating the precondition of the model
may use any of them; a trivial theorem may use them only at the index of the checker.

Two controls run on the real audit:

- `theorem DecidesControl.trueByDecide : True := by decide`, listed under a
  decided precondition, must be rejected;
- the first `[[trivial]]` entry, offered as negative evidence, must be
  rejected.

The second runs only when the run decides the precondition of a model with a
`[[trivial]]` entry.

<!-- requires-theorems:begin (generated by run.py --generate-registry) -->
| Model | Theorem | Kind | Family | Reason |
| --- | --- | --- | --- | --- |
| `anchor-lang::accounts::account_loader::AccountLoader::load` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.load_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided admission rejects a data handle that holds lamports. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_mut` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.load_mut_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided admission rejects a data handle that holds lamports. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_mut_observation` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.load_mut_observation_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided `LoadReady` rejects a data handle that holds lamports. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_observation` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.load_observation_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided `LoadReady` rejects a data handle that holds lamports. |
| `anchor-lang::accounts::account_loader::AccountLoader::try_from_observation` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.loader_observation_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided precondition rejects an ill-typed data cell. |
| `anchor-lang::context::CpiContext::new_with_signer` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.new_with_signer_decider_rejects` | negative: the decider rejects an input | Anchor | Every recorded ledger is empty; the theorem shows the decider rejects a non-empty vector ledger. |
| `anchor-spl::token::accessor::amount` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.amount_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided `DataBorrow.Ready` rejects a data handle that holds lamports. |
| `anchor-spl::token::accessor::amount_observation` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.amount_observation_rejects_illTyped` | negative: the decider rejects an input | Anchor | The parser types every cell; the theorem shows the decided `DataBorrow.Ready` rejects a data handle that holds lamports. |
| `switchboard-on-demand::on_demand::accounts::pull_feed::PullFeedAccountData::parse` | `SolanalibTest.Conformance.Library.Families.Instructions.Switchboard.requires_rejects_free` | negative: the decider rejects an input | Instructions | The theorem shows the decided precondition rejects a free (unleased) cell for every byte string. |
| `spl-token-2022::onchain::invoke_transfer_checked_value` | `SolanalibTest.Conformance.Library.Families.TokenInterface.Onchain.illTyped_not_ready` | negative: the decider rejects an input | TokenInterface | Every recorded world has two typed cells per account; the theorem shows the decided `PreparationReady` rejects a data handle that holds lamports. |
| `solana-account-view::AccountView::Pool::close_header` | `SolanalibTest.Conformance.Library.Families.AccountsV2.close_pre_rejects_missing` | negative: the decider rejects an input | AccountsV2 | The reader makes every handle a parsed account; the theorem shows the decided `isBorrowed = false → HasAccount` rejects an unborrowed missing account. |
| `solana-account-view::AccountView::Pool::data_len` | `SolanalibTest.Conformance.Library.Families.AccountsV2.data_len_pre_rejects_missing` | negative: the decider rejects an input | AccountsV2 | The reader makes every handle a parsed account; the theorem shows the decided `HasAccount` rejects a missing account. |
| `solana-account-view::AccountView::Pool::is_signer` | `SolanalibTest.Conformance.Library.Families.AccountsV2.is_signer_pre_rejects_missing` | negative: the decider rejects an input | AccountsV2 | The reader makes every handle a parsed account; the theorem shows the decided `HasAccount` rejects a missing account. |
| `solana-account-view::AccountView::Pool::lamports` | `SolanalibTest.Conformance.Library.Families.AccountsV2.lamports_pre_rejects_missing` | negative: the decider rejects an input | AccountsV2 | The reader makes every handle a parsed account; the theorem shows the decided `HasAccount` rejects a missing account. |
| `solana-account-view::AccountView::Pool::owned_by` | `SolanalibTest.Conformance.Library.Families.AccountsV2.owned_by_pre_rejects_missing` | negative: the decider rejects an input | AccountsV2 | The reader makes every handle a parsed account; the theorem shows the decided `HasAccount` rejects a missing account. |
| `solana-account-view::AccountView::Pool::set_lamports` | `SolanalibTest.Conformance.Library.Families.AccountsV2.set_lamports_pre_rejects_missing` | negative: the decider rejects an input | AccountsV2 | The reader makes every handle a parsed account; the theorem shows the decided `HasAccount` rejects a missing account. |
| `solana-account-view::AccountView::Observation::set_lamports` | `SolanalibTest.Conformance.Library.Families.AccountsV2.obs_set_lamports_pre_rejects_2_64` | negative: the decider rejects an input | AccountsV2 | The reader rejects values of 2^64 and more; the theorem shows the decided `value < U64_LIMIT` rejects 2^64. |
| `pinocchio-token::instructions::batch::Batch::invoke_signed` | `SolanalibTest.Conformance.Library.Families.TokenViews.Batch.invokeRequires_rejects_hole` | negative: the decider rejects an input | TokenViews | Recorded buffers are fully initialized, so no record can hold an uninitialized committed slot; the theorem shows the decider of the checker (`invokeRequiresDec`) rejects one. A committed length past its buffer is exercised by a control. |
| `solana-sysvar::clock::Clock::get` | `SolanalibTest.Conformance.Library.Families.Runtime.Syscalls.sdk_clock_decider_rejects` | negative: the decider rejects an input | Runtime | The destination of the typed getter starts as `Default`, so `GetterReady` holds in every recorded state (`typed_getter_ready`); the theorem shows the decision of the checkers (`getterReadyDec`) rejects a successful reply that leaves the destination uninitialized. |
| `solana-sysvar::rent::Rent::get` | `SolanalibTest.Conformance.Library.Families.Runtime.Syscalls.sdk_rent_decider_rejects` | negative: the decider rejects an input | Runtime | The destination of the typed getter starts as `Default`, so `GetterReady` holds in every recorded state (`typed_getter_ready`); the theorem shows the decision of the checkers (`getterReadyDec`) rejects a successful reply that leaves the destination uninitialized. |
| `pinocchio::sysvars::instructions::Instructions::try_from` | `SolanalibTest.Conformance.Library.Families.Runtime.Accounts.overlong_rejected` | negative: the decider rejects an input | Runtime | The AccountsV2 parser requires `data_len <= backing.length`, so no record can break `constructorReady`; the theorem shows the decision of the checker rejects an Instructions account whose length exceeds its backing. |
| `pinocchio-token::instructions::batch::Batch::invoke_signed` | `SolanalibTest.Conformance.Library.Families.TokenViews.Batch.invokeRequires_rejects_long_prefix` | negative: the decider rejects an input | TokenViews | The theorem shows the decider of the checker (`invokeRequiresDec`) rejects a committed length beyond its buffer; a control exercises the same case on a record. |
| `anchor-spl::token::transfer` | `SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck.transfer_decider_rejects` | negative: the decider rejects an input | Anchor | The checker fixes the builder state (empty vector ledgers), where every built instruction is readable (`Sample.build_ready`), so no record leaves the precondition; the theorem shows the decider `buildReadyWithB` answers false for a build whose instruction its liveness test rejects. |
| `solana-sysvar::clock::Clock::string_error::get` | `SolanalibTest.Conformance.Library.Families.Utilities.Syscalls.splitClock_decider_rejects` | negative: the decider rejects an input | Utilities | Native typed destinations start initialized. The exact registered precondition decider rejects a successful abstract provider reply that fails to initialize its destination. |
| `solana-sysvar::rent::Rent::string_error::get` | `SolanalibTest.Conformance.Library.Families.Utilities.Syscalls.splitRent_decider_rejects` | negative: the decider rejects an input | Utilities | Native typed destinations start initialized. The exact registered precondition decider rejects a successful abstract provider reply that fails to initialize its destination. |
| `anchor-lang::accounts::account::Account::clone_borrowed_info` | `SolanalibTest.Conformance.Library.Families.AnchorViews.cloneReadyBorrowed_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `anchor-lang::accounts::borrowed_info_ref` | `SolanalibTest.Conformance.Library.Families.AnchorViews.infoReadyBorrowed_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `anchor-lang::accounts::account::Account::deref_mut` | `SolanalibTest.Conformance.Library.Families.AnchorViews.mutableReady_shared` | negative: the decider rejects an input | AnchorViews | Rejects a shared parent loan for the exclusive field operation. |
| `anchor-lang::accounts::wrapper_key` | `SolanalibTest.Conformance.Library.Families.AnchorViews.keyReady_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `anchor-lang::context::CpiContext::AccountInfoProgram::new_with_signer` | `SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts.empty_ready_rejects_reused` | negative: the decider rejects an input | AnchorOperations | The selected vector primitive always satisfies readiness; the same generic decider rejects reusing an already-live empty Vec owner. |
| `anchor-lang::context::CpiContext::AccountInfoProgram::new_with_signer` | `SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts.empty_ready_rejects_nonempty` | negative: the decider rejects an input | AnchorOperations | The selected vector primitive always satisfies readiness; the same generic decider rejects a fresh but nonempty Vec result. |
| `anchor-lang::context::CpiContext::AccountInfoProgram::new` | `SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts.empty_ready_rejects_reused` | negative: the decider rejects an input | AnchorOperations | The selected vector primitive always satisfies readiness; the same generic decider rejects reusing an already-live empty Vec owner. |
| `anchor-lang::context::CpiContext::AccountInfoProgram::new` | `SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts.empty_ready_rejects_nonempty` | negative: the decider rejects an input | AnchorOperations | The selected vector primitive always satisfies readiness; the same generic decider rejects a fresh but nonempty Vec result. |
| `anchor-spl::token_2022::transfer_checked` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022TransferChecked0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-lang::accounts::account::Account::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::close` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.account_close_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::try_from_unchecked` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.account_try_from_unchecked_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::close` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.boxed_close_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.boxed_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.interface_account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.interface_account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::reload` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.account_reload_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::reload` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.interface_account_reload_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_init` | `SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires.init_rejects_illTyped` | negative: the decider rejects an input | AnchorLoader | The native reader types each data cell; the actual selected admission rejects a lamports cell used as data. |
| `anchor-lang::accounts::account_loader::AccountLoader::load_init_observation` | `SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires.init_observation_rejects_illTyped` | negative: the decider rejects an input | AnchorLoader | The supporting selected-data decision rejects a wrong-content data handle. |
| `anchor-lang::accounts::account_loader::AccountLoader::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires.accounts_rejects_illTyped` | negative: the decider rejects an input | AnchorLoader | The popped head must satisfy checked-loader admission; its same executable decision rejects a wrong-content data handle. |
| `anchor-lang::accounts::account_loader::AccountLoader::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires.exit_rejects_illTyped` | negative: the decider rejects an input | AnchorLoader | The actual matching-owner, not-closed exit branch rejects an unreadable data handle. |
| `anchor-lang::accounts::account_loader::AccountLoader::try_from_unchecked` | `SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires.unchecked_diagnostic_loss_rejected` | negative: the decider rejects an input | AnchorLoader | The native Owner script preserves the error heap. The exact inner second-Owner decision rejects an actual callback result whose state lost the diagnostic Box. |
| `anchor-spl::token::transfer_with_program_owner` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.tokenTransfer0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::burn` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022Burn0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::close_account` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022CloseAccount0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::get_account_data_size` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022GetAccountDataSize0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::initialize_account3` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022InitializeAccount30321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::initialize_immutable_owner` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022InitializeImmutableOwner0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::initialize_mint2` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022InitializeMint20321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::mint_to` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022MintTo0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::set_authority` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022SetAuthority0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::group_member_pointer::group_member_pointer_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.groupMemberPointer0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::group_pointer::group_pointer_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.groupPointer0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::metadata_pointer::metadata_pointer_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.metadataPointer0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::mint_close_authority::mint_close_authority_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.mintCloseAuthority0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::non_transferable::non_transferable_mint_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.nonTransferableMint0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::permanent_delegate::permanent_delegate_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.permanentDelegate0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022_extensions::transfer_hook::transfer_hook_initialize` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.transferHook0321_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-lang::accounts::clone_borrowed_info` | `SolanalibTest.Conformance.Library.Families.AnchorViews.infoCloneReadyBorrowed_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `anchor-lang::Lamports::get_lamports` | `SolanalibTest.Conformance.Library.Families.AnchorViews.lamportsReady_wrong_cell` | negative: the decider rejects an input | AnchorViews | Rejects a mistyped lamports cell reached after AsRef. |
| `pinocchio::account_info::AccountInfo::lamports` | `SolanalibTest.Conformance.Library.Families.Pinocchio09.Accounts.lamports_pre_rejects_missing` | negative: the decider rejects an input | Pinocchio09 | Every parsed loader account has a balance cell; the same registered precondition decider rejects a missing balance cell in the kernel-checked control. |
| `anchor-spl::token_2022::burn_checked` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022BurnChecked112_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::mint_to_checked` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022MintToChecked112_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::set_authority_program_id` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022SetAuthority112_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::transfer_checked_program_id` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022TransferChecked112_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `solana-instructions-sysvar::load_current_index_checked` | `SolanalibTest.Conformance.Library.Families.Utilities.Checked.current_missing_cell_rejected` | negative: the decider rejects an input | Utilities | Native AccountInfo supplies a real data cell. The checker uses the registered Ready admission; its exact decider rejects a missing reached cell at the correct sysvar ID. |
| `solana-instructions-sysvar::load_instruction_at_checked` | `SolanalibTest.Conformance.Library.Families.Utilities.Checked.missing_cell_rejected` | negative: the decider rejects an input | Utilities | Native AccountInfo supplies a real data cell. The checker uses the registered Ready admission; its exact decider rejects a missing reached cell at the correct sysvar ID. |
| `anchor-lang::accounts::account::Account::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::close_checked` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.account_close_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.interface_account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.interface_account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::try_from_unchecked` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.account_try_from_unchecked_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.boxed_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::reload_released_guard` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.interface_account_reload_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_from_unchecked` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.interface_account_try_from_unchecked_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.interface_account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.interface_account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.boxed_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_from_unchecked` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.interface_account_try_from_unchecked_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-spl::token_2022::initialize_account3_program_id` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022InitializeAccount3102_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token_2022::transfer_checked_program_id_interface` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022TransferChecked102_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `solana-sysvar::epoch_schedule::EpochSchedule::get` | `SolanalibTest.Conformance.Library.Families.Utilities.Syscalls.epoch_decider_rejects` | negative: the decider rejects an input | Utilities | Native typed destinations start initialized. The exact registered precondition decider rejects a successful abstract provider reply that fails to initialize its destination. |
| `anchor-lang::accounts::account::Account::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::close` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.account_close_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::exit_cloned_info` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.interface_account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::interface_account::InterfaceAccount::exit_cloned_info` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.interface_account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::try_from_unchecked` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.account_try_from_unchecked_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::close` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.boxed_close_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.boxed_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-spl::token_2022::transfer_checked_legacy_interface` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.token2022TransferChecked029_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-lang::accounts::account::Account::into_inner` | `SolanalibTest.Conformance.Library.Families.AnchorViews.moveReadyBorrowed_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `solana-program::sysvar::clock::Clock::get` | `SolanalibTest.Conformance.Library.Families.Utilities.Syscalls.legacy118Clock_decider_rejects` | negative: the decider rejects an input | Utilities | Native typed destinations start initialized. The exact registered precondition decider rejects a successful abstract provider reply that fails to initialize its destination. |
| `solana-program::sysvar::rent::Rent::get` | `SolanalibTest.Conformance.Library.Families.Utilities.Syscalls.legacy118Rent_decider_rejects` | negative: the decider rejects an input | Utilities | Native typed destinations start initialized. The exact registered precondition decider rejects a successful abstract provider reply that fails to initialize its destination. |
| `anchor-lang::accounts::account::Account::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_try_accounts_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::close_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_close_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::exit_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::reload_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_reload_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::try_from_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_try_from_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::account::Account::try_from_unchecked_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_try_from_unchecked_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-lang::accounts::boxed::Box::exit` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.boxed_exit_admission` | negative: the decider rejects an input | AnchorLifecycle | The parser constructs correctly typed cells and a live Box. The exact contract and its decision reject the exhibited malformed resource. |
| `anchor-spl::token::burn` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.tokenBurn027_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token::mint_to` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.tokenMintTo027_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-spl::token::transfer_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.tokenTransfer027_rejects_missing_metas` | negative: the decider rejects an input | AnchorSplTokenOperations | Native constructors produce current vectors; the same decision bridge rejects missing metadata after an actual successful constructor and account-preparation prefix. |
| `anchor-lang::accounts::owned_info_ref` | `SolanalibTest.Conformance.Library.Families.AnchorViews.infoReadyOwned_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `anchor-lang::accounts::sysvar::Sysvar::deref` | `SolanalibTest.Conformance.Library.Families.AnchorViews.payloadReady_missing` | negative: the decider rejects an input | AnchorViews | Rejects a missing wrapper owner or source loan. Rust fixture inputs cannot construct such references. |
| `anchor-lang::accounts::account::Account::set_inner` | `SolanalibTest.Conformance.Library.Families.AnchorViews.setReady_shared` | negative: the decider rejects an input | AnchorViews | Rejects a shared parent loan for the exclusive field operation. |
| `solana-program::sysvar::rent::Rent::get_legacy_error_table` | `SolanalibTest.Conformance.Library.Families.Utilities.Syscalls.legacy115Rent_decider_rejects` | negative: the decider rejects an input | Utilities | Native typed destinations start initialized. The exact registered precondition decider rejects a successful abstract provider reply that fails to initialize its destination. |
| `spl-token-2022-interface::extension::transfer_fee::TransferFeeConfig::get_epoch_fee_live` | `SolanalibTest.Conformance.Library.Families.TokenInterface.Fees.live_requires_iff` | trivial at the decided index | TokenInterface | At the decided index `getEpochFeeLiveSample` the state is the configuration itself and its parent is always live, so no input lies outside the precondition; the theorem is the equivalence through which the checker decides `requires` (it holds in every state). |
| `anchor-spl::token_interface::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_32_1_token_interface_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `solana-instruction::AccountMeta::clone` | `SolanalibTest.Conformance.Library.Families.InstructionExtensions.metadata_requires_at_recorded_index` | trivial at the decided index | InstructionExtensions | Every native record is made under the original live shared Rust borrow; the checked unit-reference index always has the parsed current metadata. Generic expired-reference rejection is separately kernel-tested. |
| `anchor-lang::system_program::allocate` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedLegacy_allocate_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::assign` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedLegacy_assign_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::create_account` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedLegacy_create_account_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::transfer` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedLegacy_transfer_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::accounts::program::Program::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.program_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::signer::Signer::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.signer_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::account_info::AccountInfo::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.account_info_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::interface::Interface::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.interface_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::sysvar::Sysvar::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.sysvar_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::unchecked_account::UncheckedAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_32_1.unchecked_account_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-spl::metadata::create_metadata_accounts_v3` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_32_1_metadata_create_metadata_accounts_v3_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-spl::associated_token::create` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_32_1_associated_token_create_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-spl::token::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_32_1_token_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `anchor-spl::memo::build_memo` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_32_1_memo_build_memo_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `spl-token-2022::extension::transfer_fee::TransferFeeConfig::get_epoch_fee` | `SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values.selectedFee_requires` | trivial at the decided index | TokenExtensionVersions | The exact recorded index keeps the configuration itself as its live parent, so every parsed configuration satisfies the decided precondition. The checker uses this equivalence. |
| `anchor-spl::associated_token::create_program_id` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v1_1_2_associated_token_create_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-spl::token_interface::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v1_1_2_token_interface_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `anchor-spl::associated_token::create_idempotent` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v1_1_2_associated_token_create_idempotent_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-lang::system_program::allocate_unit_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedModern_allocate_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::assign_unit_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedModern_assign_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::create_account_unit_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedModern_create_account_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::transfer_unit_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.boxedModern_transfer_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::accounts::interface::Interface::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.interface_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::program::Program::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.program_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::signer::Signer::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.signer_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::unchecked_account::UncheckedAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_1_2.unchecked_account_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::interface::Interface::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.interface_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::program::Program::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.program_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::signer::Signer::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.signer_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::system_account::SystemAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.system_account_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::sysvar::Sysvar::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.sysvar_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::unchecked_account::UncheckedAccount::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls1_0_2.unchecked_account_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-spl::token_interface::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v1_0_2_token_interface_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `anchor-spl::associated_token::create_idempotent` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v1_0_2_associated_token_create_idempotent_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-spl::token::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v1_0_2_token_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `anchor-lang::accounts::program::Program::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.program_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::program::Program::try_from` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.program_try_from_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::signer::Signer::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.signer_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::account_info::AccountInfo::try_accounts` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_29_0.account_info_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-spl::token_interface::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_29_0_token_interface_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `solana-program::instruction::AccountMeta::clone` | `SolanalibTest.Conformance.Library.Families.InstructionExtensions.Program.metadata_requires_at_recorded_index` | trivial at the decided index | InstructionExtensions | Every native record is made under the original live shared Rust borrow; the checked unit-reference index always has the parsed current metadata. Generic expired-reference rejection is separately kernel-tested. |
| `anchor-lang::accounts::program::Program::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.program_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::signer::Signer::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.signer_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::system_account::SystemAccount::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.system_account_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::sysvar::Sysvar::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.sysvar_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::unchecked_account::UncheckedAccount::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.unchecked_account_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-lang::accounts::account_info::AccountInfo::try_accounts_inline_error` | `SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Controls0_27_0.account_info_try_accounts_admission` | trivial at the decided index | AnchorLifecycle | The exact provider retains diagnostic resources; the theorem validates every input at the same index through the checker decision. |
| `anchor-spl::stake::withdraw` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_27_0_stake_withdraw_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-spl::stake::StakeAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_27_0_stake_StakeAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `anchor-spl::token::TokenAccount::deref` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_27_0_token_TokenAccount_deref_ready` | trivial at the decided index | AnchorSplSupport | The native deref transport starts from an existing shared wrapper. The same checker lemma proves admission for every parsed complete pointee; missing/expired parents remain separately rejected by the general model controls. |
| `anchor-spl::stake::deactivate_stake` | `SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires.v0_27_0_stake_deactivate_stake_ready` | trivial at the decided index | AnchorSplSupport | The checker fixes the input fixture and script before evaluating outcomes. Its own source-prefix admission lemma covers every script/custodian choice at this exact index; arbitrary providers/stores are not declared admissible. |
| `anchor-lang::system_program::allocate_inline_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.inlineLegacy_allocate_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::assign_inline_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.inlineLegacy_assign_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::create_account_inline_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.inlineLegacy_create_account_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `anchor-lang::system_program::transfer_inline_borsh` | `SolanalibTest.Conformance.Library.Families.AnchorSystem.inlineLegacy_transfer_requires` | trivial at the decided index | AnchorSystem | The fixed constructor resource interpretation always produces readable current vectors; this theorem uses the actual precondition decider at the same opaque-provider index. |
| `solana-program::instruction::Instruction::clone` | `SolanalibTest.Conformance.Library.Families.InstructionExtensions.clone_requires_at_recorded_index` | trivial at the decided index | InstructionExtensions | Every native record supplies the live original instruction and both input vector slots; this is the exact checked index, including allocator-failure records. The generic family separately rejects expired references. |
<!-- requires-theorems:end -->

`--model-only` fails on a model that is neither decided nor listed, on a
precondition that is decided but not exercised, on a listing for a model whose checkers all decide the precondition, and, in a run over every family, on a
listing of a model no checker decides. A control requires the run to fail
without a needed listing: it removes one, or, while the file is empty, drops
the decision of one checker of a decided precondition.

A precondition control is a family control built with
`outside_precondition(record_id, change)` from `controls/common.py` (or a
record control whose `expected` names the precondition). Its `expected` is the message of the
checker for that precondition, and it must appear in the report of
that record. The table below is generated from
`requires-open.toml` by `run.py --generate-registry`; the offline controls
reject a stale one.

<!-- requires-open:begin (generated by run.py --generate-registry) -->
| Model | Reason |
| --- | --- |
| `spl-token-2022::onchain::invoke_transfer_checked` (TokenInterface) | Open. At the closed index of the record `OnchainIndex.Index env` the `requires` of the family is `∃ protocol, Admission.Admitted ∧ Admission.ResourceReady ∧ Admission.BorrowReady`: an existential over collection protocols of conditions quantified over every finite primitive exit, which is not decidable. A proof at the closed index would adapt the `Witness*Admission` proofs and the resource and borrow admission proofs of the registered sample to the record-driven index. The checker decides the registered reference itself on every record (`OnchainAllocatedRun.invoke_fn`), and decides the precondition of the value observation `PreparationReady` on the same records. |
<!-- requires-open:end -->

`SolanalibTest/Conformance/Library/Core.lean` holds the checker vocabulary,
`SolanalibTest/Conformance/Library/Runtime.lean` the readers for syscall logs, CPI requests,
terminal exits and input regions. The checker fails on any rejected record,
unknown function instantiation, unreadable record, checker without records,
missing or unregistered corpus file, and a corpus registered twice. The computed outcome of the
model is printed next to each rejected record.
Per-family runs evaluate the same checkers through the Lean interpreter.

Family indices are test choices; family Codecs uses bytemuck `Encoding`/`Decoding` instances for
`u8`, `u16`, `u32`, `u64`, `i64`, `f64` (bits), `[u8; 32]`, `[u64; 4]`, `bool`,
`()` and `[u64; 0]` (layouts checked against the recorded `size_of`/`align_of`);
borsh writers `RecordingWriter` and `Vec<u8>`; the `Vec` allocation providers:
the `Vec` of std at the element layout for borsh 0.10.4 `deserialize_reader` of
`Vec<T>` (below), else the always-returning one.

Heap requests (borsh 0.10.4 `Vec<T>`). The tracking `#[global_allocator]` of the borsh 0.10.4 driver (`rust/codecs-borsh-0-10-4-bytemuck-1-25-2/src/heap.rs`) logs every `alloc`,
`alloc_zeroed`, `realloc` (with its new size) and `dealloc` of the call with
size, alignment and block (allocation order within the call; no addresses),
as `"heap"` in the state after the call (`[]` before it). The model reports
its `Vec` calls to the provider of the index; the provider of the checker interprets
them as the `Vec` of std does at the size and alignment of the element
(`Vec::with_capacity`, `vec![0u8; n]` by `alloc_zeroed`, growth by
`grow_amortized`: `max(2 * capacity, required, min_non_zero_cap)` through
`realloc`), keeping the buffer (block 0) and the requests as its state, and
decides that the registered relation admits an outcome whose result,
remaining slice and requests the record observes: on `Ok` exactly the requests of the
provider; on `Err` those of the provider, then the allocations of the returned `io::Error` (other blocks, not freed; not compared), then one `dealloc` of the final buffer of the
vector, a projection rule (the model does not report
deallocation). `hint::cautious` is private in borsh 0.10.4; its records are
derived by the driver from these runs wherever the source reaches
`Vec::with_capacity(hint::cautious::<T>(len))` (argument `len`, result the size
of the first request divided by `size_of::<T>()`, one record per element type
and `len`) and decided at the recorded `size_of::<T>()`: the checker requires
the size to equal that of `T`, then checks that the truncated divisor gives a normal
return for these corpus instantiations. The full model has no size
precondition and includes the division panic.

The separate native regression in
[`cautious_truncation.rs`](rust/codecs-borsh-0-10-4-bytemuck-1-25-2/tests/cautious_truncation.rs) exercises
the published implementation with a valid 4 GiB element layout, without
constructing an element. It checks division panic after reading the length,
before vector allocation or element callbacks, with zero-length, short-header,
zero-size and `u8` controls. From the repository root, resolve and record the
driver before running the control in its pinned toolchain and configuration:

```sh
just test-native-library codecs-borsh-0-10-4-bytemuck-1-25-2 "$(mktemp -d)"
(
  cd tools/library-conformance/rust/codecs-borsh-0-10-4-bytemuck-1-25-2
  cargo test --locked --release --test cautious_truncation
)
```

The corresponding Lean tests also cover nonzero
truncated sizes and terminal panic policies.

### Negative controls

`--model-only` mutates copies of the corpus and requires the checker to reject
each one:

- structural, for every checked corpus: an unknown function, an
  instantiation without records; in a full run, an extra corpus file;
- runtime record kinds, for every function instantiation that has them (its
  first such record outside listed divergences): a dropped request from the
  log after the call (the log of the shim, the log of a terminated exit, or a host stub
  log), a changed lamports value in the account region after the call (state
  keys `input`, `region` or `accounts`), spare byte 3000 (in the 10 KiB realloc
  padding) and the last spare byte of the first account that has them in that
  region, flipped with `spare_nonzero_at` kept consistent, the account-count
  word dropped from that region, and a changed terminal reason. Each mutated record must be rejected. A driver whose models
  do not observe a kind lists it in `unobserved` in its `driver.toml`, with a
  comment saying why;
- a spare byte after an earlier nonzero spare byte, in the first record of
  each function instantiation. The control flips the last spare byte of an
  account whose spare bytes after the call already have a nonzero byte, so
  `spare_nonzero_at` does not change. For a function without such a record,
  it takes the first record whose regions before and after are read back,
  sets spare byte 0 in both, requires that setup alone to be admitted, and
  then flips the later byte. Each flip must be rejected;
- a semantic change of the first record of each checker (outside listed
  divergences): the first changeable leaf of the returned result (in key
  order) changes. A number moves by one, a Boolean is negated, a byte string
  changes its first byte, and a text or an enum value (`variant`) becomes
  another one recorded at that path by the same function (else in the
  corpus). A result without such a leaf becomes an unwind, and an unwind or a
  terminal exit changes its reason. The checker must report a MISMATCH, so a
  checker that admits everything fails. Where a model genuinely admits the
  change, the family gives another mutation with a reason in
  `controls/<Family>.py` (`SEMANTIC = [(corpus, on_record(id, change),
  reason)]`). Each replay reports the semantic controls exercised by its selected checkers;
- the decides audit:
  - the `address` checker of AccountsV2 declaring `pool "close"` must be reported
    as declaring a model its code does not use and as using `address_model`
    undeclared;
  - a Codecs checker claiming `decidesRequires` for its models must be
    reported as not using `Solanalib.Contracts.Model.requires`;
  - a Codecs checker declaring `Owned.Array.construction_run` with a dead
    mention must be reported as declaring a model whose `rust_names` do not
    include its function;
  - removing one `requires-open.toml` listing must fail the run;
- family controls: semantic corruptions a family adds in `controls/<Family>.py`
  (`CONTROLS = [(label, corpus, mutate[, expected])]`, with `on_record(id,
  change)` from `controls/common.py`); each must be reported as a mismatch of
  its record, and the offline tests require each to change its corpus. Any
  family can add them. The replay reports their exact selected and omitted identities. Codecs controls include heap requests of borsh 0.10.4 `Vec<T>`, `cautious` results and layouts, and the no-std `write_all` of borsh 1.6.1;
- family Codecs: an `Ok` value, the remaining slice after an error, an error
  kind and message, a writer chunk, an unwind exit, a layout.

## Limits

- Host build, not sBPF: the Solana `cfg` branches are compiled for x86-64 with
  the host `std`. Layout facts recorded here (sizes, alignments, little-endian
  order) are those of x86-64; the models take them as index parameters.
- Shimmed syscalls test the program side only; the answers of the runtime are the choices of the
  cases.
- Generic functions are checked at the chosen instantiations only.
- Agreement on finitely many runs is evidence, not proof, of model fidelity.

Family Codecs:

- Only observable parts are compared: return values, errors, the slice after
  the call, writer calls and writer state, addresses of returned references,
  and the heap requests of borsh 0.10.4 `Vec<T>::deserialize_reader` (the `Vec` calls of the model through the `Vec` of std at the element layout; see Heap
  requests above). The heap requests of an error value are attributed by
  block and not compared; element destructors are not observed (the element
  types have none); allocation failure is not exercised (the host allocator
  does not fail). `hint::cautious` (private in borsh 0.10.4) is checked on
  records derived from the first allocation of those runs, not on direct
  calls. The wrappers at `Self = Vec<T>` use the always-returning provider
  and do not observe allocation.
- Generic functions are checked at the listed instantiations only; other derived types are not recorded.
- The contracts deliberately leave the slice after a decoding error
  unconstrained (the `nostd_io` reader of borsh differs from the one in `std`); the checks
  decide the executable references, which follow `std`, so they also confirm
  that `std` empties the slice on a short read.
- The no-std `write_all` is checked at one writer, the scripted one, with the
  unwinding panic strategy and an allocator that succeeds. Aborting panic and allocator-free execution are distinct instantiations of the panic and allocation callbacks. A writer that is
  interrupted forever (no finite outcome) is not recorded, and neither is a
  failed allocation of the message of the `WriteZero` error.

Family Address (solana-address 2.6.0 and 2.6.1):

- `find_program_address_contract` (an observation, both versions) is decided
  through the post of the registered contract. Its reference `findReference` fixes
  the aborting panic strategy (a failed search terminates); a native unwind
  build records that panic as `unwound`, which the contract admits. Reference
  and contract agree on returned outcomes (`find_reference_returned_iff`,
  proved for 2.6.0).
- The pure observations (`find_program_address`, 2.6.0 `is_on_curve`) are
  recorded on the plain host branch (drivers `address-2.6.*-host`: feature
  `curve25519`, no `target_os = "solana"` cfg). Their `Crypto` argument is a
  SHA-256 and curve-membership table computed in the driver with `sha2` 0.10.9
  and `curve25519-dalek` 4.1.3 along the queries of the model; an input outside
  the table makes the model fail, so a missing entry rejects the record.
- Syscall cases do not record a zero status without a fully written address
  (the `assume_init` of the wrapper would be undefined behavior; the `SuccessInitialized` of the models excludes it). The uninitialized address slot of a
  request is not observable and is not compared. Syscall unwinds are not
  recorded (an `extern "C"` call cannot unwind); terminal syscall exits are.
- `create_program_address` (both versions) and 2.6.1 `is_on_curve` have no
  registered model and are not recorded.

Family AccountsV2 (solana-account-view 2.0.0; driver `accounts-v2` with exact modeled dependency pins):

- Inputs safe Rust cannot produce are not recorded: an `AccountView` of a
  missing account (the missing-cell acquisition error of the model), consumed or
  forged guard tokens (`invalidGuard`), flag bytes other than 0 and 1 (the
  loader writes 0 or 1).
- `try_map` closures are scripted at the byte-range index (`sliceProfile`,
  `Failure = u8`, `Unwind = String`, no terminal exit): targets inside the
  leased account only (no external or static target); effects are
  `set_lamports` through captured views and writes through `&mut [u8]`; no
  guard acquisition inside a closure, no abort or divergence.
- Ghost parts are fixed by projection rules, not observed: guard ids
  (acquisition order) and generations (+1 per `try_map` exit with a state),
  owner epochs (successful closes), `resizeDelta = 0`, `entryLen` = serialized
  length.
- The six Observation models are decided on the records of the method they
  observe, through the `AccountView.observe` of the specifications (verdict: both the
  observation and the API model admit the record).
- Targets are `T = [u8]` and mapped `u8` only.

Family AccountsV1 (solana-account-view 1.0.0, solana-account-info 3.1.1; driver `accounts-v1` with exact modeled dependency pins; each
crate is reached through the deserializer of its clients, pinocchio 0.10.2
`entrypoint::deserialize` and solana-program-entrypoint 3.1.1 `deserialize`):

- Ghost parts are not observed: guard identities are the creation
  order of the driver (a map keeps the identity); generations, owner epochs (successful
  closes) and entry lengths come from the state before, and the state after is
  compared without them. The frame (region bytes outside the projection) and
  the raw flag bytes must be unchanged.
- Every checker decides the registered precondition of its models (`requires`)
  before the reference. Every record of `solana_account_view` and
  `solana_account_info` must satisfy it (a record outside it fails).
- Inputs safe Rust cannot produce are not recorded: an `AccountView` of a
  missing cell, consumed or stale guard tokens. Headers the loader cannot
  produce (`resize_delta` near the `i32` bounds, flag bytes 2 and `0xff`) are
  in the separate corpus `solana_account_view_1_0_0_forged`. Its three
  `resize`/`close` records where the `i32` arithmetic of the source overflows are
  outside the `resize`/`close` preconditions (`ResizeArithmetic`,
  `CloseArithmetic`): the checker asserts that, and that Rust panics there
  with the overflow message and leaves the state as before. The other twelve
  forged records are inside the preconditions and admitted by the models.
  The guard families (including the `CallbackSafe` of `Ref::map`) and the
  AccountInfo checkers decide their preconditions too (see Preconditions).
- `Ref::map` closures are scripted at the byte-range index
  `⟨sliceProfile, String, Empty⟩`: targets inside the leased account
  (`U = [u8]`, `u8`), captured `set_lamports` effects and panics; no external
  target, no guard acquisition inside a closure, no abort or divergence. Guard
  families at `T = [u8]` and mapped `T = u8`.
- AccountInfo: `RefCell` lease kinds are probed with `try_borrow_mut` and
  `try_borrow` (temporaries restore them) and shared counts are the live guard
  objects; `RefCell` saturation (`isize::MAX` shares) and `Rc` count overflow
  are not reachable; the profile is 64-bit unwinding, so the terminated (abort) branch of the getters is not exercised.
- Case selection: per instantiation every outcome class once or twice (values
  on each account and alias, borrow errors, saturation at 254 shared guards,
  `i32` conversion and growth-limit boundaries, regrowth over a hidden suffix,
  close after resize and close), at most 20 records.

Family TokenViews (pinocchio-token 0.6.0, pinocchio-token-2022 0.3.1; driver `token-views` with exact modeled dependency pins):

- Every case runs in `shim::case` over a `rust/accounts` region; the state
  before is read back after the driver acquired the borrows it holds across the
  call (real `Ref`/`RefMut` guards, so markers 254 to 1 and 0 occur). Checkers
  decide "the registered relation admits an outcome whose observation equals
  the record" through graph lemmas of the registered relations; guard ids and
  generations are ghost. Region parts no model represents (rent epoch, spare
  bytes, instruction data, program id; syscall state for models without
  syscalls) must be unchanged.
- `Batch` committed lengths are private: they are read from the words of the `Batch`
  value at positions calibrated on a fresh batch; the two account
  lengths are equal in every reachable state (asserted), so their order is
  immaterial.
- CPI descriptors are observed through the raw CPI header bytes of the shim (every
  recorded path copies the account header as one word): token-2022 records
  with noncanonical flag bytes and nonzero padding decide the `RawHeader` capture and `copiedPadding` of the model; Batch buffers observe pointer
  identity directly. Boolean `AccountView` worlds reject noncanonical flag
  bytes and nonzero padding as unrepresentable.
- Case selection: each admission class and check order once with its first and
  last input and the layout/length boundaries, borrow counts 1, 253 and 254,
  getter boundary values, each `Batch` writer stage short by one and exact,
  unwinds at every callback position.

Family Instructions (solana-instruction 3.4.0, solana-instruction-view 1.0.0
and 2.1.0, pinocchio-system 0.6.0, pinocchio-associated-token-account 0.4.0,
solana-system-interface 3.2.0, solana-borsh 3.0.2, switchboard-on-demand
0.12.1, shared token getters; drivers
`instructions-3-4-0-bincode`, `instructions-3-4-0-wincode` and `instruction-view-2-1-0-cpi`):

- `InstructionBuilder` (`new_with_bincode`, `new_with_wincode`, System
  `*_operational`): index state `()`, resources carry their contents, the
  serializer is the bincode/wincode encoding or the script of the record, `unwrap`
  panics with the message of Rust; allocation and the accounts-`Vec` drop are not
  observable.
- CPI wrappers: descriptors are compared through the account pool (key,
  lamports, data of the copied length, owner, rent epoch, flags); pointer
  identities are not compared; the `Box`
  allocation and drop of v1 are not observable; instruction-view 2.1.0
  `invoke_signed` is checked at the identity `AsRef` and at a scripted
  recording `AsRef`; the copied padding byte and noncanonical flag bytes of v2 are
  observed through the raw CPI header of the shim (v1 builds the struct field by
  field, so its padding is not logged).
- switchboard `parse`: guard ids and generations are ghost; decided as "the
  registered relation admits an outcome whose projection (error, returned
  range, borrow state) equals the record".
- The shared token getters (`amount`, `mint`, `owner`, `decimals`, `state`) are
  checked on the pinocchio-token 0.6.0 and pinocchio-token-2022 0.3.1 getter records from TokenViews, whose references are these models by definition.

Family Runtime (pinocchio 0.10.2 and 0.11.1, solana-sysvar 3.1.1,
solana-rent 3.0.0, solana-msg 3.1.0, solana-program 4.0.0,
solana-sha256-hasher 3.1.0, solana-curve25519 3.1.12, solana-hash 4.5.0,
solana-sdk-ids 3.1.0, solana-zero-copy 1.2.0, solana-program-option 3.1.0,
solana-define-syscall 5.1.0 and 5.2.0; drivers `runtime-pinocchio-0-10-2`, `runtime-rent-3-0-0` and `runtime-pinocchio-0-11-1` (Solana cfg, shim,
accounts), `runtime-pinocchio-0-10-2-wrapping` and `runtime-rent-3-0-0-wrapping` (`overflow-checks = false`,
the wrapping profile of the models) and `runtime-program-4-0-0-host` and `runtime-sysvar-3-1-1-host`
(`host = true`: the `hostStub`/`hostStd` targets through recording
`program_stubs` and captured stdout)), plus `raw-syscalls-5-2-0` for the separate
SDK 5.2.0 dependency selection:

- Syscall providers (getters, `hashv`, `validate_edwards`, logs, return data)
  are decided with the shim (target `solana`) or the recording stubs and
  stdout (host targets) as the provider of the family index. The initial
  `MaybeUninit` destination of `sol_get_sysvar`/`sol_sha256` (a model field,
  constant `none`) is not compared. `validate_edwards` compares the `result_initial` of the shim with the `initialScratch` of the model request; it is 0 in every
  record, because solana-curve25519 3.1.12 owns that byte
  (`let mut validate_result = 0u8`) and a caller cannot set it.
- The raw syscalls of solana-define-syscall 5.1.0 (`sol_sha256`, `sol_log_`,
  `sol_panic_`, `abort`; see Syscalls) are decided at one index whose provider
  over `Solanalib.Runtime.SysReq` is the shim: a hash request is logged and answered by
  the next reply as `⟨status, [data]⟩` on status 0 and `⟨status, []⟩`
  otherwise, a log request is logged and answered `.ok0`, and `sol_panic_` and
  `abort` are the terminal exits of the shim with their recorded details. A hash reply
  outside the hash shape (a status of 2^64 or more, or status 0 without exactly
  32 bytes) ends the run with reason `sol_sha256`. No recorded script has one
  (`rust/shim` holds a status as a `u64`, and the scripts give 32 bytes with
  status 0 and none otherwise); the reference ends the run on one so that its
  answers satisfy the index law `hashShape` (`rawIndex_hashShape`), and
  `sol_sha256` has no precondition. The native shim handles replies differently:
  The `sol_sha256` in `rust/shim` (`hasher!`) copies `min(len, 32)` of the bytes of the reply to `hash_result` and returns its status, while a separate source execution binding must establish representable status words and the complete 32-byte digest on status 0, rejecting malformed provider replies under its selected protocol. The reference reads a nonzero status with bytes as
  `⟨status, []⟩`, ignoring the bytes, which `rust/shim` copies; a source execution binding must reject that case; no script has one either. A `sol_sha256` record
  keeps the status and the 32-byte result buffer, which starts with a recorded
  pattern; it is read as `⟨status, [buffer]⟩` on status 0 and `⟨status, []⟩`
  otherwise, and a buffer changed under a nonzero status is rejected. The
  index checks alignment, under which a call with a slice at an unaligned
  `vals` stops without asking. The checker reads every record as aligned,
  `⟨slices, true⟩`: the driver passes the descriptors as a `&[&[u8]]`, which
  is 8-aligned by its type, and the records carry no `vals` address. So
  conformance does not exercise the unaligned branch, on which Agave aborts and
  the descriptor reads by the shim are undefined behavior. `sol_log_` has no
  precondition: a message that the provider does not answer only stops, and
  the shim answers every one.
- Not recorded: panic strategy `abort` (drivers unwind),
  `PinocchioProfile.targetBpf = true` (BPF floating panic; host
  `target_arch`), `Hash.Syscall.Target.bpfArch` (the same branch as
  `solanaOS`), `TextTarget.hostNoStd` (solana-msg without `std`, another
  feature build), pinocchio host getters (`black_box` of the address; no
  separate model target).
- Inputs with native undefined behavior are not recorded: a pinocchio getter
  success without a full destination, a `hashv` return without 32 written
  bytes, `Instructions` table reads out of bounds or misaligned,
  `load_current_index` on fewer than 2 bytes (the debug build panics on
  `len - 2`; the raw model truncates).
- Case selection: Rent arithmetic at its guard and `u64` overflow edges,
  binary64 roundings (exact, ties to even both ways, below and above half, to
  2^64), one integer per threshold class; the unreachable threshold-1.0 rate guard of pinocchio 0.10.2 (checked build panics, wrapping build wraps, as the
  model states); getters at each value class and each status class (0, 1, 2,
  other, 2^32, max), status 1 with bytes, terminal replies, partial and no
  writes over `Default`, the host stub panic; raw `sol_sha256` over no slice,
  one slice and several with an empty and a repeated slice, each with status 0
  and 32 bytes, every error status class without bytes and a terminal reply;
  raw `sol_log_` of an empty, an ASCII and a non-UTF-8 message; `sol_panic_`
  with a file, line and column and with an empty file at the `u64` extremes;
  `abort`.

The same Runtime provider and raw-syscall checkers cover two more declarations
from solana-define-syscall 5.2.0 (46 records, driver `raw-syscalls-5-2-0`):

- The checker decides the registered `sol_sha512_run` and
  `sol_curve_multiscalar_mul_run` references at the recording provider, using
  proved graph equivalences. It compares output, status, every request,
  remaining replies and terminal details. It also checks both eight-byte
  output guards. Every nonzero return preserves the original result buffer.
- SHA-512: empty, one and segmented inputs (including an empty and a repeated
  slice), success with 64 bytes, nonzero statuses and terminal replies.
  Nonzero statuses exercise the generic provider contract; the canonical
  Agave hash handler instead returns zero or fails. The descriptors of Rust are
  aligned, and this shim sets no hash slice limit; native records do not test
  rejection for alignment, hash count or feature registration. The kernel tests of the specs cover those model branches separately.
- Multiscalar multiplication: both supported curves at counts 0, 1, 3 and
  512, each with success, failure and a terminal reply; invalid curve IDs 2
  and `u64::MAX`, each with return 1 or a terminal reply; count 513 at both a
  supported and an invalid curve. The latter calls use null pointers and
  terminate before logging a request. Invalid-curve calls use null input and
  result pointers, and their log records no input bytes. The supplied scalar
  and point values are encoded inputs, not assumptions of successful
  decoding. The scripted response does not perform scalar or point decoding.
- Family mutations test 64-versus-32-byte width, failed writes, guards,
  lost inputs, missing or mismatched replies, impossible status/curve success,
  unequal input counts, short scalar encodings, terminal detail and the
  count-before-curve order. The native tests of the shared shim reject malformed
  replies, exercise a null failure destination and input/output overlap, and
  check that SHA-256, SHA-512 and MSM share one reply queue and request log.
  Run those with
  `(cd tools/library-conformance/rust/shim && cargo test --offline -- --test-threads=1)`
  in the pinned build environment. Record with
  `run.py --record --driver raw-syscalls-5-2-0 --twice`; replay with
  `run.py --model-only --corpus solana_define_syscall_5_2_0`, passing `--evidence-dir` to each.

Families AddressProfiles, InstructionExtensions and StakeCodecs retain these
native profiles:

| Family | Driver and corpus | Registered functions |
| --- | --- | --- |
| AddressProfiles | `pubkey-profiles-240` / `pubkey_profiles_240` | Pubkey 2.4.0 byte/value operations, constructors and ordering, `create_with_seed`, Solana PDA creation/search, Borsh 0.10.4 serialize/read with owned EOF-error destruction and unwind, and the ATA client helper; all 142 recorded observations across 14 keys. |
| InstructionExtensions | `instruction-extensions-v2` / `instruction_extensions_v2` | AccountMeta 2.3.3 constructors/clone and system-interface 1.0.0 `create_account_with_seed`; all 40 observations across 4 keys. |
| StakeCodecs | `stake-codecs-interface` / `stake_codecs_interface` | Lookup-table-interface 2.2.2 deserialize and solana-borsh 2.2.1 Borsh 0.10 packed length; all 130 observations across 2 keys. |

The linked [library Test roots](../../packages/solanalib-specs/LIBRARIES.md) contain the
matching contract scenarios and source/build selection controls. Those controls
exercise exact references, declared ranges and rejected dependencies; unlisted
fixture versions are synthetic matcher tests. Native coverage remains limited
to the versions in the table.

Pubkey checks keep seed order and guards, zeroed output bytes after partial
writes, modern status conversion, actual bump, Borsh EOF translation and
partial callback state. Its controls also reject a consumed reply after a
local guard, changed terminal details and a different program ID. The
`new_from_array` and `From<[u8; 32]>` constructors, ordering and the
associated-address helper all have selected checkers.

Instruction checks retain every metadata position and flag, unchanged clone
inputs, UTF-8 byte lengths, long seeds and allocation terminals. Seeded
construction keeps three positions even when their keys alias. The
`instruction_extensions_v2_2` corpus additionally checks all 16 seeded
construction records. Instruction cloning remains unregistered; the modern
Wincode prefund reference is selected as described below.

Lookup checks retain the offset-56 alias, decode-before-size error order,
slop rejection and decoder error cleanup; packed length keeps each write and
serializer effect on normal/error/unwind paths. Checked overflow versus
wrapping and destructor terminals have separate mathematical controls.
The host observations do not establish sBPF layout, allocator correctness,
arbitrary callback termination or selection of the owning compilation unit for a production Borsh call.

Replay these exact registered keys with the existing runner:

```sh
python3 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --family AddressProfiles --family InstructionExtensions --family StakeCodecs \
  --evidence-dir /tmp/slc-address-instruction
```

In the pinned Rust environment, record the unchanged SDK calls twice with
`run.py --record --offline --twice --no-write-corpus`, the three `--driver`
names from the table, and an `--evidence-dir`. This keeps reproduction
receipts separate from the committed corpus.

Family Anchor (anchor-lang 1.0.2, anchor-spl 1.0.2; driver
`anchor`):

- Twelve of the 21 checked functions decide the primary model and its
  `_observation` model; the `key`, `deref` and `sol_log_data` checkers decide
  one model each (33 models in all).
- Generic callbacks are scripted per record (`Owner`/`CheckOwner`/
  `AccountDeserialize` steps, `ToString`/`Drop` operands, the `AsRef` holder,
  the CPI reply); errors returned by scripts are boxed `ProgramError`s.
- Owned error, vector and guard ledgers are compared through observations:
  error values (current `Box` contents), `String`/`Box` identity (input or
  fresh) and liveness through a tracking `#[global_allocator]`, cell contents
  and coarse leases (free, shared, exclusive, by `RefCell` probing; shared
  counts are not observable), `Rc` strong counts. Guard ids, slot histories,
  ledger events and allocation budgets are ghost.
- Not observed: the private owner copy of `InterfaceAccount` (no accessor); the `AccountInfo.owner` snapshot of the
  model (compared through the owner read via
  `ownerRef`); allocation-failure terminals and the abort profile (host build,
  `panic = "unwind"`, the allocator never fails); the length-overflow panic of `load` (unreachable on 64-bit).
- `with_values` records whose operand destructor panics show rustc leaving the
  moved receiver live (rust-lang/rust#47949: the return place is not dropped
  when the destructor of a later local unwinds). They were known divergences; the
  owned model now admits both the released and the live receiver on exactly
  that path (`AnchorErrorOwned.protectReturnPlace`), and controls reject a
  live receiver on every other path and a partial leak.
- Case selection: one case per model branch (each error path, each callback
  exit kind including unwind, each borrow state, duplicate accounts, owner
  assignment during callbacks) plus boundary values (amount 0 and max, codes 0
  and `u32::MAX`, empty data, short slices); at most 20 per instantiation
  except `with_values` (7 inputs by 7 operand scripts, 49).

Family TokenInterface (spl-token-interface 2.0.0, spl-token-2022-interface
3.1.1, spl-token-2022 11.0.0; drivers `token-interface`
(interface profile) and `token-interface-onchain` (on-chain profile:
spl-token-2022 11.0.0 with interface 3.0.0, transfer hook 2.1.0,
spl-tlv-account-resolution 0.11.1, spl-type-length-value 0.9.1, pod
0.7.3)):

- Instruction constructors: the operational families are decided at
  `Witness.sampleTypes` from empty ledgers; observed are the returned
  instruction (through the `observe` of the model) and the heap counts (fresh
  allocations as ledger slots, deallocations as retired slots); capacities and
  vector growth are not observed.
- Extension type listing: decided at `extensionTypeReaderReference` of the TLV bytes of the
  record; only the returned list is observed, not the vector drop
  on error.
- Extension lookup: every production extension Pod has alignment one, so the
  alignment branch is unreachable natively; `V = TransferFeeConfig` uses the
  registered representation, other `V` a raw-bytes representation (tag, size,
  identity observation).
- Unpack: `Mint` and `Account` have no destructor, so the drop-after-layout-error branch of the operational family runs only its trivial instance.
- `invoke_transfer_checked`, value model: the opaque provider is interpreted as
  solana-cpi 3.1.0 `invoke_signed` (the `RefCell` pre-check, then the scripted `sol_invoke_signed_rust` reply of the shim through `ProgramError::from(u64)`);
  the PDA crypto is the table of the recorded `sol_try_find_program_address`
  requests and replies; released-guard tombstones and cell policies are not
  observable; only `aborts = false` (host unwind) is exercised; hook extra
  metas cover the fixed-address kind only.
- `invoke_transfer_checked`, operational family: decided by the same checker
  at the closed index of the record `OnchainIndex.Index env` (the account owners,
  the scripted `sol_try_find_program_address` replies in order, the CPI reply
  under the interpretation of the value model) from the borrow world of the record and
  its Rc strong counts before the call (`state.counts`), through
  `OnchainAllocatedRun.invoke_fn`: the family admits exactly the outcome of
  `invokeF`, evaluated as compiled code. Observed are the exit, the cells and
  live guards, each CPI request with the Rc counts of the model at the call
  (against the `counts` of the request), the ordered syscalls and unconsumed
  replies, and the Rc counts after the call (against `outcome.state.counts`).
- `invoke_transfer_checked`, operational family, limits: an extra account
  meta resolved from seeds has no outcome at the closed index (its seed
  vectors are empty-only), so such a record would be rejected, and no record
  has one; the literal provider never answers `.again`, and the collect
  protocol has no internal steps, so neither set of internal-step rules is
  exercised at this index; heap allocation counts are not compared (the shim has no pause hook to exclude its own allocations and those of the decoder, and the model has no heap ledger); the `requires` of the family
  (`∃ protocol, Admitted ∧ ResourceReady ∧ BorrowReady`) is not decidable and
  stays open (`requires-open.toml`); the `tokenEnumSize`, vector capacities and terminal (double-unwind) outcomes of the index are not observable
  natively (`observeAllocated?` maps a terminal outcome to `none`); only
  `aborts = false` (host unwind) is exercised.
- Case selection: per instantiation, the first and last candidate of each
  class (outcome by branch: program own, other accepted or rejected, by signer
  shape; fee branches in source order with `u128` arithmetic; TLV kind by
  outcome); exhaustive only for the 29-tag decode table.

## Known divergences

A known divergence is a recorded behavior that a registered model rejects and
that is kept as evidence without failing the run, such as a compiler behavior
outside the model. (the `with_values` leak of Anchor, rust-lang/rust#47949, was one
until its model admitted the leaked outcome; the example below shows the form of that
listing.) The
family that owns the corpus lists its records in `divergences/<corpus>.toml`:

```toml
[[divergence]]
records = "with_values/*/left_drop_panics"   # glob over record ids (`*` matches any text)
model = "Solanalib.Specs.AnchorLang.error.Error.with_values_run"   # a model in the `decides` list of the deciding checker
exit = "unwound"                              # optional pin: the recorded exit kind
reason_contains = "drop L"                    # optional pin: a substring of the recorded reason
reason = "..."
link = "https://github.com/rust-lang/rust/issues/47949"   # upstream issue or evidence (optional)
```

The listed `model` must be one the deciding checker declares in `decides`.
The checker requires that model to reject every listed record and every other
model it decides to admit it, and the optional pins `exit` and
`reason_contains` fix the recorded exit kind and a substring of the recorded
reason, so a listed record differs from the model only where documented. The
run fails if a listed record is admitted by its model, rejected by another, or
differs from its pins, if a listing matches no record, and on every unlisted
mismatch. Counts report the rejected records separately
(`[N known divergent]`). Three controls run for each listing; a glob that
matches every id the first control could use (such as `*`) is rejected:

- a copy of a listed record under an unlisted id must mismatch, so the glob
  does not exempt records it was not written for;
- removing the listed records must fail as a stale listing;
- unlisting the divergence must make its records mismatch.

The table below is generated from `divergences/*.toml` by
`run.py --generate-registry`, and the offline controls reject a stale one.

<!-- known-divergences:begin (generated by run.py --generate-registry) -->
| Corpus | Records | Model | Reason | Upstream |
| --- | --- | --- | --- | --- |
| none | | | | |
<!-- known-divergences:end -->

## Models without a native entry point

Models not decided by a native conformance checker, with their mathematical
tests and the reason for that boundary. `--model-only` over every family fails unless the registered
models minus the models its checkers decide (`decides.json`) are exactly the
models of `not-tested.toml`, from which `run.py --generate-registry` generates
this table; the offline controls reject a stale one.

<!-- not-tested:begin (generated by run.py --generate-registry) -->
| Model | Reason |
| --- | --- |
| `shared-owned-array::construction` (`Solanalib.Specs.Core.Owned.Array.construction_run`) | Abstract protocol with no standalone Rust identity. [Lean scenario tests](../../packages/solanalib-specs/SolanalibTest/Specs/Core/OwnedArray.lean) cover ordered evaluation, partial failure, cleanup, terminal exits and rejected traces. The operational Token-2022 checker covers its concrete literal use, not this independent construction family. |
<!-- not-tested:end -->

### AccountInfo, Anchor views and opaque CPI

The existing `SdkAccounts`, `AnchorViews`, `AnchorSplSupport`, `CpiSignatures`
and `CpiRawSignatures` families check account views and invocation boundaries.
The library roots link to their mathematical tests in `LIBRARIES.md`.

| Family | Selected behavior | Additional boundaries |
| --- | --- | --- |
| `SdkAccounts` | Owner assignment; lamports borrowing; temporary length borrowing; reallocation, resize, AccountInfo AsRef and `data_is_empty` | Borrow and equality checks precede original-length/backing access; shrink retains spare bytes; zeroing growth may terminate; source-header and lease geometry are separate Rust-binding obligations. |
| `AnchorViews` | Account/InterfaceAccount keys and clones, Account mutable dereference, selected wrapper clones and borrowed AccountInfo views, Pubkey Key and Lamports getter | Native fixtures use debug disabled. Lean scenarios also retain debug log/panic effects and callback unwind/terminal exits. A shared family does not merge payload loans with AccountInfo RefCell guards. |
| `AnchorSplSupport` | Token and TokenInterface account dereference, Token ID, associated-account creation, Memo construction and metadata creation | Dereference exposes the decoded account through its live parent; the emitted 176-byte host pointee is distinct from the 165-byte wire format. Creation retains instruction/account construction and the opaque CPI boundary. |
| `CpiSignatures` | Signed SDK borrowed/owned signatures, unsigned solana-invoke, ordered RefCell preflight and explicit supplied outcomes | Typed whole-signature mocks execute no invocation implementation or callee. The owned public constructor control is separate from the opaque invocation and preserves fresh clone/drop effects. |
| `CpiRawSignatures` | Dynamic raw extern-C invocation signature and canonical zero status | Runtime failures remain terminal. A byte-memory binding must preserve the selected runtime configuration, pointer checks, canonical translated copy-back and source-layout distinctions. |

The seven native drivers contain 164 observations. The selected checkers
cover 129 observations over 35 function-instantiation keys. The remaining
35 are 34 Anchor wrapper observations and one unsigned
`solana_program::program::invoke` 2.3.0 observation. The unsigned 2.2.1
native reference is checked separately. Their exact identities remain in
`checker-selection.json`; controls without a selected target remain in
`selection-omitted-controls.json`. Checking a shared model at another
callable or release does not check these native rows.

Replay the selected families with the existing runner:

```sh
python3 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --family SdkAccounts --family AnchorViews --family AnchorSplSupport \
  --family CpiSignatures --family CpiRawSignatures --evidence-dir /tmp/account-cpi-replay
```

Fresh recordings use the same version-specific driver names and pinned Rust
toolchain. With the pinned toolchain and dependency cache, run:

```sh
python3 -B tools/library-conformance/run.py --record --offline --twice \
  --driver sdk-accounts-2 --driver anchor-views-0-32-1 \
  --driver anchor-spl-support-v0321-interface --driver anchor-spl-support-v0321-pubkey240 \
  --driver cpi-invoke-0-4-0-i2-3-3 --driver cpi-program-2-3-0 \
  --driver cpi-raw-define-2-3-0 --target-dir /tmp/account-cpi-target \
  --evidence-dir /tmp/account-cpi-native
```

The three CPI drivers also have a `signature-check` feature that checks their
function-pointer type declarations. From the repository root, resolve each
workspace before checking the driver with that feature:

```sh
for driver in cpi-invoke-0-4-0-i2-3-3 cpi-program-2-3-0 cpi-raw-define-2-3-0; do
  just test-native-library "$driver" "$(mktemp -d)"
  (
    cd "tools/library-conformance/rust/$driver"
    cargo check --locked --features signature-check
  )
done
```

The ordinary recordings keep that feature disabled and invoke only the typed
mocks. The Lean checker compares complete retained source-type observations
and rejects omitted signer arguments or reinterpreted descriptor layouts.
Those observations do not establish the ABI of an arbitrary compiled program.

The Anchor SPL projector handles exactly the retained support drivers. With
the pinned Anchor SPL 0.32.1 source directory already available, check both
projections without writing files:

~~~sh
python3.12 -B tools/library-conformance/project_anchor_spl_support.py \
  --registry "$CARGO_REGISTRY_SRC" --check
~~~

To regenerate them, omit `--check`. A change to the projector requires fresh
recordings of both retained support drivers because their manifests hash it.

For Program 1.15.2/1.18.26 and account-info 2.3.0/3.1.1, an implementation binding still requires complete account-type and signature evidence at the actual compiler and build configuration. The replay suite does not discharge those obligations.

The `CpiSourceAbi` data records the observations used by the pure checker. It does not prove the layout or ABI of an arbitrary compiled program. A concrete binding still supplies matching source/signature evidence and implementation and representation premises; CPI bodies remain opaque.

The public catalogs retain their full source/build gates. CPI selection uses
the declared operation/provider ranges at the actual matched release and
requires the recorded registry origin, Solana OS, 64-bit pointers, little
endian, abort panic and known dynamic syscall dispatch. SDK selection checks
every listed instruction, AccountInfo, ProgramError and stable-layout
dependency, plus entrypoint/raw-syscall providers for borrowed invocation or
solana-cpi for the owned wrapper. Build controls reject missing, ambiguous,
out-of-range or forked dependencies and incomplete target facts. These
compatibility declarations do not alter the exact native builds above. These checks
do not discharge the explicit callee, allocator, source-memory or target
interpretation obligations.

### Anchor context and diagnostic operations

The `AnchorOperations` family checks the registered operations below against the
versioned `anchor_operations_0_32_1` corpus. From the repository root, run the
existing library tests and replay the committed corpus with its controls:

```sh
lake --wfail build SolanalibTest.Specs.AnchorLang
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --family AnchorOperations --corpus anchor_operations_0_32_1 \
  --evidence-dir /tmp/anchor-operations-model
```

To reproduce the pinned native driver separately, record twice into a separate evidence directory without replacing the committed corpus:

```sh
python3.12 -B tools/library-conformance/run.py --record \
  --driver anchor-operations-032 --twice --offline --no-write-corpus \
  --evidence-dir /tmp/anchor-operations-native
```

Driver, corpus and source-version labels continue to identify the exact native build.

The first eleven profiles in the table use inspected crates.io `anchor-lang`
0.32.1, 0.32.2 and 0.32.3
as references for the declared range `[0.32.1, 0.33.0)`, under the per-operation [compatibility assumptions](../../packages/solanalib-specs/VERSION_COMPATIBILITY.md).
The writer retains its known 64-bit pointer-width gate. The generated
`ErrorCode` methods require `anchor-syn` in `[0.32.1, 0.33.0)`; logging requires
`solana-program-error` in `[2.2.2, 3.0.0)` with the owned Borsh error String.
The [library gate tests](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorLang/Operations.lean)
cover inspected references, range boundaries, source origins and missing or
ambiguous required facts. Native observations remain tied to the exact 0.32.1 build; the additional source references do not extend them.

| Source operation | Model under `Solanalib.Specs.AnchorLang` | Effects retained by the checker |
| --- | --- | --- |
| `Context::new` | `context.Context.new` | Borrowed program/accounts/remaining references and the moved bumps payload; no account trait callback. |
| `CpiContext::new` | `context.CpiContext.AccountInfoProgram.new` | Moved accounts and program `AccountInfo`, fresh logical empty vector owner, empty borrowed signer descriptor. |
| `CpiContext::new_with_signer` | `context.CpiContext.AccountInfoProgram.new_with_signer` | The same owned fields and vector creation, with the supplied borrowed signer descriptor. |
| `CpiContext::with_signer` | `context.CpiContext.AccountInfoProgram.with_signer` | Replacement of the borrowed descriptor; preservation of program, accounts and existing vector state. |
| `BpfWriter::write_all` | `bpf_writer.BpfWriter.write_all` | One bounded copy; fitting prefix and cursor retained on `WriteZero`; zero-count copy reached only while capacity remains. |
| `Error::with_account_name` | `error.Error.GenericProgram.with_account_name` | Name conversion, source-ordered replacement, owned capacity and cleanup, including callback unwind. |
| `Error::with_pubkeys` | `error.Error.GenericProgram.with_pubkeys` | The current boxed error and full program-error payload; comparison replacement and destruction. |
| `Error::with_values` | `error.Error.GenericProgram.with_values` | Ordered displays, replacement and temporary destruction, including unwind and moved return-place cleanup. |
| `From<ErrorCode> for Error` | `error.Error.from_error_code` | All 77 selected enum variants, name/message allocation order and the resulting box. |
| `ErrorCode::name` | `error.ErrorCode.name` | Exact generated names and owned string state. |
| `Error::log` | `error.Error.log` | Exact error/origin/comparison rendering, ordered logs and temporary cleanup; the borrowed receiver is preserved. |
| `Error::eq` | `error.Error.eq` | Borrow both actual boxed payloads; compare Anchor numeric codes or the complete legacy ProgramError, including Borsh String contents. |
| `From<std::io::Error> for Error` | `error.Error.from_io_error` | The actual consuming IO-to-ProgramError conversion, Display/Drop effects, and unwind before Anchor box construction. |

`AccountInfoProgram` distinguishes the reviewed source representation from
the inherited `CpiContext` family whose program field is a copied pubkey. Its
complete family still quantifies over field, seed and account representations;
a Rust binding must supply the actual types. `GenericProgram` keeps the
complete program-error representation and raw ordered primitive relation as
indices. The inherited annotation families have different readiness premises
and ownership postconditions. An individual `Ops.fromOwned` translation or
agreement at a sample index does not equate those complete families.

`Error::from_io_error` was inspected at Anchor Lang 0.32.0 through
0.32.3 and declares `0.32.0 ≤ v < 0.33.0`, with the legacy string-bearing
ProgramError dependency range. The actual consuming Display/Drop conversion
may mutate state or unwind before Anchor box construction. The exact 0.32.1
source binding and native reference have their own authenticated inputs; this range does not
apply to unrelated lifecycle methods.

The complete native corpus has 221 records. In the authenticated replay,
the registered family selects all 221 records across 13 function keys,
including the inherited Error equality and the IO conversion. Exact
function/type keys determine that selection; shared source tables and helpers
do not create additional registrations. The writer comparison retains
buffer/cursor and syscall effects; native allocation bookkeeping does not
establish arbitrary allocator behavior.
The `Error::eq` profile retains its inspected 0.32.0–0.32.3 references and
declared `[0.32.0, 0.33.0)` range under its own complete operation and
dependency conditions.

The [shared mathematical tests](../../packages/solanalib-specs/SolanalibTest/Specs/Core/AnchorOperations.lean)
cover partial mutation, reached versus skipped zero-copy calls, terminal copy
outcomes, diagnostic effects, and fresh vector ownership in nonempty state.
The tests of the existing native driver also check a sequence after a short write
and signer replacement with aliased, nonempty remaining accounts. The
[negative controls](controls/AnchorOperations.py) alter results, retained
payloads, callback order, vector/Rc facts and syscall effects. Run those tests
and controls through the existing tools; model reference execution and native
observations remain separate evidence.

All eleven selected source signatures require implementation bindings. Full callback metadata is a separate obligation for `Context::new`, the three selected `CpiContext` operations, `with_account_name` and `with_values`. Complete dependency-body evidence remains open for `write_all`, `with_pubkeys`, `log`, `ErrorCode::name` and `From<ErrorCode>`; signature matching does not fill that gap. A binding must establish the actual compiler, target, source cfg, layout and selected generic instantiations; host observations do not establish sBPF layout equality.

A separate binding to the Rust implementation must establish source entry selection, representation coverage and reached primitive behavior.
Allocation, formatting, destruction and callback behavior remain explicit
assumptions. Joint resource satisfiability does not establish a general heap transition. These models and observations do not prove an SDK
body, and CPI remains opaque.

### Anchor System and checked transfer

The public contracts are grouped under `Solanalib.Specs.AnchorLang.system_program` and
`Solanalib.Specs.AnchorSpl.token_2022`. The System functions, checked transfer and the
sixteen additional token wrappers retain their 0.32.1 reference bindings.
Their per-function profiles separately declare compatible source ranges and
complete dependency/build conditions. Native coverage remains at 0.32.1.

| Family | Registered functions | Native corpus | Selected / recorded |
| --- | --- | --- | --- |
| `AnchorSystem` | `allocate`, `assign`, `create_account`, `transfer`, `id` | `anchor_system_0_32_1` | 31 / 31 |
| `AnchorSplTokenOperations` | Legacy transfer, nine Token-2022 operations and seven extension initializers | `anchor_spl_token_0_32_1` | 188 / 188 |

All 31 System records, including `id`, are selected. The token family selects the
registered 0.32.1 wrappers from the authenticated 188-record corpus.
The earlier `token::transfer` primary and observation models retain native
coverage through `anchor_spl_1_0_2`; the new 0.32.1 transfer family keeps its
distinct owned context program and boxed legacy error.
The two drivers retain their versioned names, exact projection spans, modeled
dependency pins, observed build probes and complete corpora.
They exercise the projected wrappers on the pinned x86-64 Solana-cfg
`dev`/unwind build, with complete invocation signatures supplied by the test.
They do not execute the callee or establish sBPF layout equivalence.

The [System scenarios](../../packages/solanalib-specs/SolanalibTest/Specs/Core/AnchorSystem.lean)
check instruction bytes and flags, ordered accounts and nested signer seeds,
aliased Rc owners, current-resource cleanup, String-bearing errors, unwind,
terminal exits and providers with no finite exit. The selected `CheckedTransfer`
[scenarios](../../packages/solanalib-specs/SolanalibTest/Specs/Core/AnchorSplTokenOperations.lean)
check request fields, success and error results, provider effects, error-box
allocation, cleanup order, unwind state and the absence of a terminal state.
An admitted incorrect-program case has no signer-seed view and rejects before
instruction allocation or invocation while releasing the intact context.

The selected [System controls](controls/AnchorSystem.py) and
[checked-transfer controls](controls/AnchorSplTokenOperations.py) corrupt those
observable results. The existing
[selection regression](test_checker_selection.py) obtains the compiled checker
keys and requires every one of these 32 mutations to reach its registered
checker and produce the expected mismatch. These 32 controls remain checks of the four System functions and checked
transfer; controls of other token wrappers keep their own selected identities.

From the repository root:

```sh
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --family AnchorSystem --family AnchorSplTokenOperations --evidence-dir /tmp/slc-anchor-cpi
SOLANA_CONFORMANCE_SELECTION_LEAN=1 python3.12 -B -m unittest discover \
  -s tools/library-conformance -p test_checker_selection.py
python3.12 -B tools/library-conformance/run.py --record --offline --twice --no-write-corpus \
  --driver anchor-system-0-32-1 --driver anchor-spl-token-0-32-1 --evidence-dir /tmp/slc-anchor-cpi-native
```

The [System source note](../../packages/solanalib-specs/source-notes/anchor-system.md) and
[checked-transfer source note](../../packages/solanalib-specs/source-notes/anchor-spl-token-operations.md)
retain the dependency releases, constructor and serialization contracts,
boxed legacy error representation, owned String payloads and allocation
assumptions. Source entry selection, source ABI agreement, representation coverage and implementation correctness remain separate obligations. Mathematical tests, source matching
and native replay each retain that boundary; CPI remains opaque.

### Anchor account lifecycle

Family `AnchorLifecycle` checks twenty registered methods from Anchor Lang
0.32.1 with driver `anchor-lifecycle-0_32_1`. The registry separately declares the 0.32 compatible range from inspected references; these recordings remain evidence only for their pinned source and host-unwind configuration.

- The selected Account, InterfaceAccount, Interface, Sysvar, UncheckedAccount,
  Program, Signer, AccountInfo, Box and Option methods
  and provided `AccountsExit::exit` use the `Solanalib.Specs.AnchorLang` catalog. Their full
  [source and build scope](../../packages/solanalib-specs/source-notes/anchor-lifecycle.md)
  remains per operation. Native function, corpus and driver identities retain
  the pinned release.
- The linked source uses explicit generic trait fixtures. Comparisons retain
  callback order, consumed account tails, error resources, Rc counts, current
  payloads, partial serializer writes, and the balance/owner/backing effects of the close.
  Option constructor cases include a non-sentinel key on inner error and unwind.
  Controls separately corrupt the effects retained after those failures.
- The driver records dev/unwind on host x86-64 with the Solana cfg. The two payload source bindings require a separate 64-bit panic-abort profile.
  Native recordings and signature equality do not establish the execution or sBPF layout of that profile. Allocator terminal cases are mathematical tests;
  this driver does not induce allocation failure.
- The compiled family compares all 180 records. Interface,
  InterfaceAccount, Sysvar and UncheckedAccount constructors,
  InterfaceAccount exit, and Account/InterfaceAccount reload methods select
  their records with exact concrete generic arguments. These records have no exceptions in `checker_selection.KNOWN_OMISSIONS`.
- `--model-only --registered-checkers --family AnchorLifecycle` reports all
  selected and omitted observations. Only the selected operations are model
  comparisons. The projection normalizes the documented RefCell and unwrap
  panic messages; terminal outcomes carry no promised returned state.

### Token, loader and optional-value operations

The existing families keep complete result, state and resource comparisons for
their selected calls. Native file and driver names retain the exact tested
releases and build profiles. Applicability separately records inspected source
references and conditional compatible ranges; those ranges add no native-test
credit. A replay reports its selected records and omissions in the existing
selection receipts.

| Family | Selected behavior and boundaries | Native driver |
| --- | --- | --- |
| `AnchorLoader` | Owner/discriminator order, mutable guard transfer, load-init observation, partial discriminator writes and release on unwind | `anchor-loader-0_32_1` |
| `SdkValues` | COption branches, borrowed reference, map callback and fallback destruction, including exact Pubkey instantiations | `sdk-values-v2`, `sdk-values-pubkey-240` |
| `TokenBuilders` | Ordered metas, instruction bytes, UTF-8 arguments, ID checks, constructor rejection and temporary owners | `token-instructions` |
| `TokenExtensionVersions` | Token-2022 8.0.1 TLV unpack/lookup/sizing, temporary vectors, permanent-delegate lookup and epoch fees; TokenMetadata 0.7.0 default | `token-state-8-0-1` |
| `RawRuntime` | Return-data length, copied bytes and program destination under the defining `solana-cpi` 2.2.1 signature | `raw-runtime-cpi2` |

The loader corpus observes bytes, borrow guards, Owner calls and
panic text; it does not record diagnostic allocation counters. The existing
[loader scenarios](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorLang/AccountLoaderExtensions.lean)
also check effectful WriteZero construction, borrowed unwrap, same-error
cleanup before guard release, missing dependency outcomes and distinct
unwind/terminal branches. These mathematical scenarios do not add native
observations to that corpus.

The `write_zero_effects` Cargo tests of the same driver inspect successful
allocation identities and their frees while the exclusive guard is held,
then check guard release after the actual loader unwind. They use the System
allocator without failure injection; later panic allocations are counted
separately. From the repository root, resolve and record the driver, then run
the tests serially with its pinned toolchain and configuration:

```sh
just test-native-library anchor-loader-0_32_1 "$(mktemp -d)"
(
  cd tools/library-conformance/rust/anchor-loader-0_32_1
  cargo test --locked --target x86_64-unknown-linux-gnu \
    write_zero_effects -- --test-threads=1 --nocapture
)
```

The two public epoch-fee wrappers are checked immediately before and at the
activation epoch. Sixteen added native observations include zero input,
excessive basis points, a full-rate cap with checked inverse addition, and
raw-fee narrowing before a zero cap. The complete configuration remains in
the result state, including unrelated fields. Seven existing-family mutation
controls corrupt these selected observations. `TokenEpochControls` in the
[selection test](test_checker_selection.py) obtains the compiled checker keys,
passes the existing region metadata, checks a successful baseline, and requires
each mutation to produce a mismatch for its own selected record.

The `sdk_values_spl_pod_0_5_1` corpus selects all 19 PodU16 and PodU64
conversion observations. The `spl_token_8_0_0_instructions` corpus selects
101 of 102 records for `mint_to`, `burn_checked`, `close_account`,
`set_authority` and `native_mint::check_id`. Its `native_mint::id` row
remains an explicit omission; that constant getter has no registered model.

The eight `sdk_values_solana_zero_copy_1_0_1` U16-to-u16 observations remain
an explicit whole-corpus omission. The U16 conversion model is checked
through the separate `sdk_values_solana_zero_copy_1_1_1` native reference;
that comparison gives no conformance credit to the 1.0.1 rows.

The 34 `sdk_values_spl_pod_0_7_3` OptionalNonZeroPubkey-to-Option observations
are another explicit whole-corpus omission. That source function has no
registered model here. Both omitted files remain fully authenticated.

`KNOWN_OMISSIONS` lists the exact identities omitted by the current
registered-checker selection. The per-corpus counts above describe this
checker selection; later registered checkers can remove its allowances. Each complete replay records observations, checker keys and corpus coverage in
`checker-selection.json` and `run-status.json`. Remove an allowance when its
exact checker is added.
The complete-registry selection test reads the actual compiled keys, while
the shared-driver unit fixture uses synthetic descriptors.

The [COption scenarios](../../packages/solanalib-specs/SolanalibTest/Specs/Core/SdkValues.lean)
also cover terminal callback and cleanup outcomes without a fabricated value
or post-state. The [public Token-2022 tests](../../packages/solanalib-specs/SolanalibTest/Specs/SplToken2022/Models.lean)
exercise activation equality and checked inverse failure through the actual
registered contracts. A resource/layout witness supplies only its stated receiver or array interpretation; without a matching source execution it does not prove SDK body execution.

```sh
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers \
  --family AnchorLoader --family SdkValues --family TokenBuilders --family TokenExtensionVersions \
  --evidence-dir /tmp/slc-extended-token
SOLANA_CONFORMANCE_SELECTION_LEAN=1 python3.12 -B -m unittest discover \
  -s tools/library-conformance -p test_checker_selection.py
python3.12 -B tools/library-conformance/run.py --record --offline --twice --no-write-corpus \
  --driver token-state-8-0-1 --evidence-dir /tmp/slc-token-epochs-native
python3.12 -B tools/library-conformance/run.py --record --offline --twice --no-write-corpus \
  --driver anchor-loader-0_32_1 --evidence-dir /tmp/slc-loader-native
```

The [source note](../../packages/solanalib-specs/source-notes/extended-token-operations.md)
retains the exact build and provider assumptions. Pubkey 2.2.1/2.4.0 profiles
retain their Borsh 0.10 reference and compatibility gates; a second Borsh
generation does not supply an unambiguous dependency edge. Source entry selection, complete source ABI, representation coverage, implementation correctness and actual execution remain distinct. CPI and return-data
providers are opaque, and host Solana-cfg observations establish no sBPF layout
equivalence or SDK body correctness.

The `spl-token-2022` `id` call selects `Solanalib.Specs.SplToken2022.id_reference`; its two exact Pubkey dependency profiles remain separate from the equal constant defined by `spl-token-2022-interface`. The recorded native call remains at 8.0.1, while source applicability declares the reviewed 8.x range. Source entry selection, the declared source ABI and the native call each retain their own identity.

## Pinocchio accounts, entrypoints and transfer-hook resolution

Family Pinocchio09 (pinocchio 0.9.2 and pinocchio-log 0.5.1; drivers
`pinocchio-09` and `pinocchio-09-values`):

The accounts corpus selects 54 of 56 records. Its two standalone
`Ref::drop` and `RefMut::drop` observations remain explicit omissions.

- Account checks retain both independent borrow nibbles, seven shared credits,
  alias identity, noncanonical nonzero flags, signed cumulative resize, growth
  zeroing and the untouched spare suffix. Guard mapping compares the actual mutations of the callback, the new generation and the retained lease after unwind.
- Value checks retain AccountMeta and Seed reference identity, full Pubkey
  equality and the error and terminal behavior of the dedicated Clock syscall.
  Logger checks retain initialized bytes, truncation markers, receiver identity,
  by-value argument destruction and formatter/drop exits. Generic logger capacities in the corpus do not establish a source binding for every capacity; each binding must justify the actual Logger layout.
- Existing mathematical tests also exercise the committed header of the resize at a
  terminal zeroing call, stale mapped generations, zero-capacity logger cleanup
  and double unwind. Native records use the selected unwind profile; terminal
  outcomes carry no after-state.

Family EntryDeserialize (program-entrypoint 2.3.0 and pinocchio 0.9.2;
driver `entry-deserialize`):

- The input is the admitted unsafe loader format. Checks distinguish equal keys
  from actual duplicate aliases, retain the full reserve/padding and compare
  returned pointer offsets. Pinocchio keeps untouched output slots and still
  finds instruction data after skipped accounts. Nonempty input at zero
  capacity is excluded without calling the unsafe Rust function.
- SDK checks retain the vector/Rc allocation sequence, original-length write
  before data-Rc allocation, duplicate strong counts and terminal allocation
  failure. The three unit tests of the driver cover alias/capacity edges, the
  zero-capacity exclusion and allocator termination. From the repository root,
  resolve and record the driver before running its tests serially:

  ```sh
  just test-native-library entry-deserialize "$(mktemp -d)"
  (
    cd tools/library-conformance/rust/entry-deserialize
    cargo test --locked -- --test-threads=1
  )
  ```

  See the [format and binding
  boundaries](../../packages/solanalib-specs/source-notes/entry-deserialize.md).

Family TransferHookResolution (transfer-hook-interface 0.9.0;
driver `transfer-hook-resolution`):

- This helper constructs the instruction/accounts of the caller and performs no CPI.
  Checks retain the mandatory validation-PDA request before program lookup,
  first matching AccountInfo and Rc identity, privilege reduction, borrowed-data
  cleanup, POD error/panic distinction, caller copyback order and partial
  effects. A closed mathematical error test checks the PDA event and all four
  argument drops when the program is absent.
- The native sample covers fixed/key-data extras, malformed input and empty
  PDA seed vectors, with a nonfailing allocator. Nonempty borrowed-seed storage
  remains outside that sample. The driver keeps its optimized dev profile with
  debug assertions and overflow checks disabled and panic unwind. Exact
  dependency pins and source-profile obligations are recorded in the
  [resolution note](../../packages/solanalib-specs/source-notes/transfer-hook-resolution-0.9.0.md).

Replay each of these families with the existing
`run.py --model-only --registered-checkers --family FAMILY --evidence-dir DIR`.
Fresh recordings use `run.py --record --offline --driver DRIVER --twice
--evidence-dir DIR`. Recordings and model replay remain separate evidence;
complete ABI/source matching and physical provider obligations are not supplied
by either command.

Each native recording authenticates its exact source and build inputs. A changed input requires recording the affected driver again; a change only to applicability metadata requires a fresh model replay. The replay reports the exact selected observations, negative controls and omissions, including the two generic guard-drop observations above. Newly inspected releases receive no native-run credit without their own recordings.

The Pinocchio 0.9.2 dedicated Clock getter starts with an uninitialized
destination and converts every nonzero status to `UnsupportedSysvar`; its
profile is `0.9.2 ≤ v < 0.9.3`. Version 0.9.3 switches to the generic
Clock-ID request but still folds every nonzero error, so it is not covered
by either this dedicated family or the later generic family that maps
status 1 to `InvalidArgument`. Other inspected 0.9.2/0.9.3 helpers retain
their operation-specific ranges. Raw declarations keep their own defining
libraries, exact ABI and dynamic-dispatch gates even when sharing a
mathematical family. Token-2022 constructors retain their complete allocated
families, failures and cleanup, with separate source/dependency profiles.
A declared range does not add native observations or exact source bindings.

## Modern Anchor and SDK profiles

The existing AddressProfiles, AnchorOperations, AnchorViews, AnchorSystem,
AnchorLifecycle, AnchorLoader, AnchorSplSupport and AnchorSplTokenOperations
families replay exact recorded source versions. The 1.1.2 error operations
belong to `Solanalib.Specs.AnchorLangError`; older Anchor families remain independently
selectable. Modern System and selected Token-2022 wrappers retain unit Borsh
errors and copied program IDs. Account close uses checked arithmetic,
InterfaceAccount reload releases its guard before replacing the payload, and
CPI calls remain opaque.

Exact inspected/native references and declared catalog ranges are separate.
The Anchor 1.1.2 operation profiles stop before the new mutually exclusive Solana provider cohorts of 1.2.1. This is a build/provider selection boundary,
not evidence that every call changes its result. The error conversion/name
profiles stop earlier, before the two ErrorCode variants added in 1.2.0;
Account/InterfaceAccount exit also gains a distinct unowned-account path in
1.2.2. Each dependency range assumes only the reached operation and retains
the recorded representation, ownership and cleanup conditions.

The exact native reference of Address is 2.6.1 with Borsh 1.6.0. Its reader calls the
actual `read_exact` once and maps UnexpectedEof to InvalidData, retaining the state and other exits of the reader. The loader-v3 and associated-token address
helpers preserve MaybeUninit PDA outputs. Token-2022 interfaces 2.1.0 and
3.0.1 share the complete owned-base unpack family, including its temporary
padding Vec and borrowed tail. The 3.0.1 profile stops before 3.1.0 removes
that allocation; the returned tail is still not a validated TLV stream.

Utilities covers checked instructions-sysvar loading, including ID rejection,
borrow state, bounds/allocation order, owned metadata/data and cleanup.
CpiSignatures, CpiRawSignatures, RawRuntime, SdkAccounts, SdkValues and
InstructionExtensions retain the actual declarations and selected ABI.
The concrete key profiles of COption still require nominal Address 2.6.0/2.6.1;
only the concrete unwrap profile requires abort. The generic family retains
its actual panic provider. The Wincode catalog branch of Prefund takes precedence
when both features are enabled, while its concrete source entry remains
Bincode-specific.

The `instruction_extensions_wincode` corpus selects 37 of 43 records. Its
six `Instruction::clone` observations remain omitted, and their duplicate-order
mutation remains unregistered. This source function has no registered model
here. Metadata cloning and prefunding have their own selected checks. The
Anchor 1.1.2 views corpus selects 22 of 61 records and retains 39 explicit
omissions. Registered models checked through another callable or native
reference do not confer conformance credit on omitted rows.

The [library Test roots](../../packages/solanalib-specs/LIBRARIES.md) check actual selected
identities, compatible versions and rejected source/dependency/build gates.
The [Anchor error tests](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorLangError.lean) also
exercise the exact name/number of the migration error, boxed allocation order,
account-name replacement and cleanup after a logger unwind. An Address implementation binding must retain finite per-call mappings and full argument/callback checks.

Catalog compatibility does not add an exact source factory, selected generic
argument tuple, `Binding` certificate or native observation. Concrete AccountLoader abort bindings must establish complete panic/width facts and source correspondence; supported unwind selection remains distinct. Native host callbacks
are test instances, not evidence of on-chain layout or an invocation body.
The [source/API registry](../../packages/solanalib-specs/source-map.json),
[applicability profiles](../../packages/solanalib-specs/VERSION_COMPATIBILITY.md) and
[binding guide](../../packages/solanalib-specs/BINDINGS.md) retain
the exact reference identities, declared ranges and remaining obligations.

## Account and token source profiles

The Anchor 1.0.2 source references extend the lifecycle, loader, context/error,
System, view and SPL families. Their compatible ranges are preservation
assumptions, separate from the inspected releases and recorded native builds.
The 1.0 alternatives retain their exact dependency and build gates and are added
beside the existing modern profiles. Generic `Program<T>::try_accounts` starts
at 1.0.2: 1.0.0 and 1.0.1 skip the ID check for a zero `T::id()`. Loader close
stays below the changed read/error protocol of 1.1; clone and the Solana stack-height
branch use separate declared 1.x compatibility ranges.

The error table retains all 77 ordinals, including account-migration variants.
The logger keeps its defining Anchor facade; loader close borrows the source and
cleans up the moved destination. Token-2022 wrappers use copied program IDs and
their exact account order. Source entry selection, complete ABI/layout facts, actual loans, primitive implementations and caller bindings remain separate obligations;
catalog selection does not establish implementation correctness, a token processor proof or CPI rollback.

The native references remain `anchor-lifecycle-1_0_2`, `anchor-loader-1_0_2`,
`anchor-operations-102`, `anchor-system-1-0-2`, `anchor-views-1-0-2`,
`anchor-spl-support-v102` and `anchor-spl-token-1-0-2`. Companion drivers
`address-profiles-260`, `instruction-extensions-bincode`, `raw-runtime-anchor`
and `utility-instructions3` use their exact modeled dependency pins, inputs and recorded modes.
Compatible-release selector fixtures are not additional native runs.

The SDK and Token interface controls retain the singleton MaybeUninit hash,
typed-default EpochSchedule getter, saturating first-slot query, fixed IDs and
infallible optional-key conversion. They distinguish push-before-payload
validation, deduplication before length checking, ordered duplicate required
extensions and checked epoch fees. Existing scenarios remain beside literal
source-identity and independent range/build rejection tests in the `Test` root of each library. Versioned corpus names continue to identify exact Rust inputs.

For example, build the existing Anchor tests and replay the recorded loader
corpus through its registered checker:

```sh
lake --wfail build SolanalibTest.Specs.AnchorLang SolanalibTest.Specs.AnchorSpl
python3.12 -B tools/library-conformance/run.py --model-only \
  --registered-checkers --family AnchorLoader --corpus anchor_loader_1_0_2 \
  --evidence-dir /tmp/anchor-loader-1-0-2-replay
```

## Program and Anchor profiles

The exact Program 1.18.26 and Anchor 0.29.0 observations use the existing
SdkAccounts, SdkValues, AddressProfiles, StakeCodecs, InstructionExtensions,
Utilities, RawRuntime, CPI and Anchor family checkers. Their 15 pinned native
drivers contain 1,056 observations, including two Option effects cases in the
lifecycle driver.
Each corpus keeps its literal versioned identity and authenticated input manifest.

These releases remain the source and native references. The Program profiles
declare compatibility in `[1.18.26, 2.0.0)`; profiles already citing both 1.15.2
and 1.18.26 use `[1.15.2, 2.0.0)`. The Anchor and Anchor SPL profiles use
`[0.29.0, 0.30.0)`. Each operation records its preservation assumptions and any
dependency intervals. These ranges add no inspected or native-tested release,
and source, ABI and provider correspondence remains explicit for another version.

The existing [Program tests](../../packages/solanalib-specs/SolanalibTest/Specs/SolanaProgram.lean),
[Anchor tests](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorLang.lean) and
[Anchor SPL tests](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorSpl.lean) cover operational
scenarios, literal identity, actual-version, boundary, source, target,
feature and dependency-selection checks. Synthetic patch versions exercise
compatibility declarations without claiming native observations.

Program-defined APIs use the `Solanalib.Specs.SolanaProgram` catalog. Their complete source
profiles retain the defining library, cfg, dependencies and arithmetic behavior.
Anchor checked transfer keeps the `transfer_checked_legacy_interface` family
because its full typed binding index differs. The cloned-info exit and legacy
error-code/logging families likewise retain their distinct behavior.

The six Program 1.18.26 Borsh selections require separate bindings for a slice reader and Vec, BpfWriter, Cursor, WriteCounter and mutable-slice
writers. Each binding must retain the exact source arguments and data definitions and reject ambiguous complete dependency Builds. The scripted native
wrapper observations do not establish all six Rust callback implementations.

Rent implementation bindings must retain the explicit checked arithmetic and abort source selections. The 108
checked/unwind native observations do not establish native abort
behavior. Model terminal scenarios and source-profile selection are separate
checks. Source representations, callback implementations and ordinary
source and interface binding obligations remain separate; CPI effects are opaque
at the invocation signature.

## Program 1.15 and Anchor 0.27 dependency

The `anchor-lifecycle-0_27_0`, `anchor-views-0-27-0`,
`instruction-extensions-legacy-15`, `sdk-accounts-legacy-15` and
`stake-codecs-legacy` drivers pin the published crates.io ahash 0.7.9 release.
It compiles with the pinned nightly and reproduces the complete recorded observations.
No vendored dependency or Cargo patch is needed.

## Legacy Program and Anchor interfaces

Program 1.15.2 and Anchor 0.27.0 use the same library and function organization,
with separate complete families where inline errors, account ownership or
cleanup differ. The selected subset adds instruction cloning, stake getters,
constructors and arrays, Pack wrappers, account views and lifecycle operations,
and token/stake CPI preparation. The 15 pinned native drivers retain all 1,088
observations; each recording is authenticated against its exact source and build inputs.

The [applicability profiles](../../packages/solanalib-specs/VERSION_COMPATIBILITY.md)
separate those inspected references from declared compatibility within
`[0.27.0, 0.28.0)` for Anchor and Anchor SPL, and `[1.15.2, 1.16.0)` for Program.
Each range assumes preservation of the complete operation and relevant dependency
contracts. The exact Borsh/derive 0.9.3, bincode 1.3.3 and token 3.5.0 gates remain;
the three concrete COption key profiles stay exact 1.15.2. These declarations
add no native observations or concrete source/ABI proofs. Existing newer profiles
are preserved independently.

The [Anchor](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorLang.lean),
[SPL](../../packages/solanalib-specs/SolanalibTest/Specs/AnchorSpl.lean) and
[Program](../../packages/solanalib-specs/SolanalibTest/Specs/SolanaProgram.lean) tests use literal defining
identities at the inspected release and synthetic compatible versions. They
retain exclusive boundaries, dependency generations/origins, ambiguous Builds
and the relevant feature, width, cfg and panic rejection checks.

The four Program 1.15.2 Borsh selections require separate bindings fixing the slice reader and three concrete writers, their full generic arguments
and source signatures. Complete dependency Builds with multiple Borsh
generations remain rejected. The selected Rent source bindings preserve checked
arithmetic and abort source profiles separately from host native observations.

The two forwarded-input CPI operations remain manual conditional selections with empty automatic profiles. Their
post-preflight request and legacy ABI obligations do not identify ordinary
Instruction storage with StableInstruction. Physical implementation bindings must preserve the fractional owners, source-cell counts and loan repayment. These
callable specifications and callback-driven native observations leave the
source/provider implementations and source/interface binding assumptions explicit; invocation effects remain opaque.
