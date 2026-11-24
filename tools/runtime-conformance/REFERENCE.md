# Focused Agave conformance checks

This suite executes **the unmodified Agave 4.3.2 libraries** at revision
`a203300045b405f86c9c84308b2eae76af69ac3b` and the
[runtime model](../../packages/solanalib-runtime/README.md) on shared concrete
fixtures. It currently has 79 differential cases: 46 account checks, 27
serialization/read-back cases and six nonempty CPI calls.

The native driver calls `BorrowedInstructionAccount` methods,
`serialize_parameters`, `deserialize_parameters`, and `cpi_common` with the Agave functions that translate C-ABI instructions and account-info descriptors from guest addresses into runtime values. It does not reproduce these implementations. Cargo builds
only `solana-program-runtime` and its dependencies using the pinned workspace lockfile; `rustc` links the driver to those exact emitted libraries.
The run keeps the Cargo workspace, lockfile, source archive and runtime model unchanged.

The native target is `x86_64-unknown-linux-gnu`, with the `target-cpu=x86-64-v2` setting of the source and a development profile. The `agave-unstable-api`
and `dev-context-only-utils` features of Agave expose the runtime API and test environment.
Compiler artifact records retain the actual transitive features and profiles.
These native runtime tests make no SBF layout or native/SBF equivalence claim.

The [memory configurations](../../packages/solanalib-runtime/README.md#memory-configurations-and-account-operations) are `L` (one writable input buffer with checked account copy-back), `S` (separate account-data regions) and `D` (regions that map transaction-account storage directly). These cases exercise `L`.

## Replay

The repository contains the exact outputs of the successful native run recorded
in `expected-native.tsv.gz`; `expected-native.json` records the date and build identity. Standard gzip with a zero
timestamp reduces the 1,194,581-byte TSV to 6,762 bytes. Expand it for review with:

```sh
gzip -dc tools/runtime-conformance/expected-native.tsv.gz > /tmp/agave-native.tsv
```

`expected-native.json` records both compressed and uncompressed output hashes, the
exact fixture/driver hashes, Rust version, target, source archive, Cargo lockfile
and native binary. The uncompressed TSV SHA-256 is
`18aa38b20764ab09c36869e25bfa3a23fefd8411c3adee24faf6e4cb8aac507b`.
The committed TSV contains the exact native observations authenticated by this metadata.

Use Python 3.12 and Lean **4.34.0** to compare a
fresh model execution against these native results. This replay needs no Rust
installation or Agave source archive:

```sh
python3.12 -B tools/runtime-conformance/test_run.py -v
python3.12 -B tools/runtime-conformance/run.py --model-only \
  --evidence-dir /tmp/solana-conformance-model
```

The runner checks the recorded native input/output hashes, builds the current
runtime model, evaluates `SolanalibTest/Conformance/Runtime.lean` and compares all 79 cases. It also
parses the complete `#print axioms` report of the local theorem and rejects anything
outside `{propext, Quot.sound}`, including `sorryAx`, custom axioms,
`Lean.ofReduceBool` and generated `native_decide` axioms. Missing or malformed
audit output fails.
The replay evaluates the checked-out model sources and records their hashes. Fixture or native-driver changes require freshly obtained native
outputs and updated provenance.

The runtime job in [.github/workflows/ci.yml](../../.github/workflows/ci.yml) runs this replay on every pull request and push to main. It checks the Python comparator and input controls, the model outputs and the axiom audit. Use `just test-runtime` for the runtime build and offline controls, or `just replay-runtime` for the replay as well. The regular runtime job does not upload replay artifacts; the separate [native workflow](../../.github/workflows/native.yml) uploads native reproduction evidence.

## Reproduce the native run

The exact sealed archive is the public GitHub commit archive for
[the Agave revision of Anza `a203300045b405f86c9c84308b2eae76af69ac3b`](https://github.com/anza-xyz/agave/tree/a203300045b405f86c9c84308b2eae76af69ac3b).
Download it directly from codeload:

```sh
curl --fail --location \
  https://codeload.github.com/anza-xyz/agave/tar.gz/a203300045b405f86c9c84308b2eae76af69ac3b \
  --output /tmp/agave-a203300.tar.gz
```

Its SHA-256 must be
`917912ac67fc0b6ffec94e33e1ce113db581e1f1706aa1ecbe4224b967b15f30`.
The runner verifies this hash before extracting anything and rejects a different archive.

A native replay additionally requires Rust **1.97.1** and the system build
dependencies of the `solana-program-runtime` of Agave. Run in the intended build
environment; do not substitute a compiler version or alter source manifests:

```sh
python3.12 -B tools/runtime-conformance/run.py \
  --source-archive /tmp/agave-a203300.tar.gz \
  --evidence-dir /tmp/solana-conformance-native
```

The runner creates a pristine source input under the evidence directory from
that sealed archive, and checks every archived file and symlink before and
after execution. It
also authenticates compiled registry dependency archives against Cargo.lock and
checks their extracted files. Build outputs stay in the evidence directory;
each subprocess has a 900-second limit and Cargo defaults to four build jobs.
The runner snapshots its harness, controls and shared fixtures before parsing
or compilation. Both drivers use that retained snapshot, whose files are
checked again and included in the evidence manifest. Later edits in the
working tree cannot change the fixtures between native and model execution.
Snapshots reject extra files and directories, including cached Python bytecode.
The runner executes only the declared control script, with bytecode writes disabled.
Cargo target/profile environment overrides are removed from subprocesses.
Setup or build failure fails the run rather than falling back to another pin.


Use `run-status.json` to establish whether the latest run passed.
`comparison.json` records every fixture, compared field, result and observed
account state. Complete byte strings remain in `native.tsv` and `model.tsv`;
JSON records their lengths and hashes. Commands, compiler identities, Cargo
units, registry inputs, source/model hashes and native-only observations are
kept alongside them. `MANIFEST.json` hashes the evidence files of the completed run;
the axiom audit of the local Lean theorem is in `run-model-axioms.out` and its checked
allow-list result is in `model-axioms.json`.
`SUMMARY.md` summarizes the latest successful comparison and its recorded evidence.

## What the cases establish

Account cases include owned and external balance changes, read-only no-op
rejection, arithmetic overflow precedence, zero extension and shrink, owner
change restrictions, exact rent exemption, invalid resize precedence and
missing accounts. Success compares every transaction account field, signed
resize accounting and the actual pop outcome.

Serialization cases compare the complete ABI v0/v1 buffers, including flags,
owner, lamports, data, masked rent epoch, instruction data, duplicate references
and the 255/256-reference boundary. Read-back checks simultaneous lamport,
data and owner changes; unchanged read-only data; error precedence; duplicate
application; and the ignored encoded length and owner changes of ABI v0.

CPI fixtures use distinct caller and callee program keys. The caller edits its
current serialized data, length and owner before calling the Agave `cpi_common`.
C account-info descriptors live in separate aligned heap memory; their flag
bytes are zero. Duplicate instruction metas also have a second occurrence
with zero flags. Agave performs pointer checks, privilege merging, entry
synchronization, native callee dispatch and return synchronization. A small
fixture callee checks the data it receives and then writes its fixture result.
The caller continuation reads the returned full buffer, account-info
length and return data from that same call. Grow/shrink and shrink/grow cases
make stale caller data and stale length words observable. Additional cases
reject an invalid pointer, privilege escalation and unexpected callee input.

The native CPI feature vector enables `syscall_parameter_address_restrictions`
and leaves the remaining `SVMFeatureSet` flags at their false defaults. Selected
operations use configuration L, ABI v1, no signer seeds, native dispatch and
rent 5080; their relevant settings agree with the Lean `mainnet` profile.
The fixture is not a claim about every mainnet feature combination. A mock
program-cache environment supplies the registered native fixture callee;
no SBF program image is executed.

## Boundaries

These are finite executable comparisons, separate from kernel-checked
mathematical proofs and from Rust body correctness. `SolanalibTest/Conformance/Runtime.lean` imports
the runtime model and evaluates its actual functions. Its one local theorem
proves that the no-signer preparation used by the executable comparison equals
`cpiPrepare` for **every** primitive environment. No placeholder cryptographic
implementation is supplied. These checks do not verify a CPI or callee body.

The native fixture callee and its finite model counterpart are explicit test
inputs. They establish no behavior of a deployed external program. Bank
admission, quantitative compute accounting, complete validator refinement,
separate and direct account-data mappings (`S` and `D`), whole-transaction rollback and SDK Rust representation/body
proofs remain separate work.

The runtime `Except` operations erase intermediate state on error. Error
codes are compared, while the native partial account effects are retained as
observations without claiming a model state or rollback. For CPI errors, the
returned native buffer is also an observation only. The raw invalid-pointer
error is `CpiError::InvalidPointer`; the driver compares its
`ProgramFailedToComplete` outcome abstraction after checking that exact raw
error variant. Other non-instruction CPI errors fail the harness. The conversion of the enclosing SBF VM
to an instruction error is not executed by this harness.

Four extra native borrow observations cover conflicting runtime mutable/shared
borrows, release after drop and an aliased SDK `AccountInfo` data borrow. The
runtime transaction state does not retain outstanding host borrows, so these
are marked **native only** and do not count toward the 79 comparisons.

The negative controls of the comparator reject changed bytes, state, errors,
missing/duplicate cases, malformed kinds and invented model error states.
Successful serialization/CPI cases must include their buffers; successful CPI
also requires structured length, return-data and stack observations. Unknown
error names are rejected even when both runners print them.
Account snapshots distinguish an empty data buffer from missing data bytes.
They also check that unrepresented native error-state effects remain visible
without silently entering the conformance claim.
