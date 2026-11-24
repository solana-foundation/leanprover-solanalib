# Transfer-hook account resolution

The native and exact source reference for
`spl-transfer-hook-interface::onchain::add_extra_accounts_for_execute_cpi`
is 0.9.0. The helper prepares the instruction and AccountInfo vector of the caller
and makes no CPI invocation. Its declared range is `0.9.0 ≤ v < 0.10.0`
under the recorded operation and dependency conditions. The
[source registry](../source-map.json) retains SPL revision
`13ecf4dd65abfe60f38cc99b66a2d14d9c731de4`, path
`token/transfer-hook/interface`, and archive SHA-256
`4aa7503d52107c33c88e845e1351565050362c2314036ddf19a36cd25137c043`.

| Reached dependency | Native reference release |
| --- | --- |
| `spl-tlv-account-resolution` | 0.9.0 |
| `spl-type-length-value` | 0.7.0 |
| `spl-pod` | 0.5.1 |
| `spl-discriminator` | 0.4.1 |
| `solana-account-info` | 2.3.0 |
| `solana-instruction` | 2.2.1 |
| `solana-pubkey` | 2.2.1 |
| `solana-program-error` | 2.2.2 |
| `bytemuck` | 1.22.0 |

Declared dependency ranges are TLV resolution `[0.9.0, 0.10.0)`,
type-length-value `[0.7.0, 0.8.0)`, POD `[0.5.0, 0.6.0)`, discriminator
`[0.4.1, 0.5.0)`, AccountInfo and ProgramError `[2.1.0, 3.0.0)`,
Instruction and Pubkey `[2.2.1, 3.0.0)`, and bytemuck `[1.22.0, 2.0.0)`.
The inspected Pubkey 2.2.1, 2.3.0 and 2.4.0 paths all initialize the PDA
destination to zero and the bump to 255. These ranges preserve the defining source of each
dependency, reached ABI and current-state behavior;
passing SemVer alone does not discharge those obligations. The later TLV
0.11.4 helper clears fresh signer privileges and is outside the profile;
0.10.0 and 0.11.0 must not be described as having that same signer change.

These exact native origins remain unchanged. The per-dependency profiles
separately declare compatible ranges supported by the reached source review;
they do not replace a native lock or create an exact source binding. The
profile selects Solana source branches, 64-bit pointers/counts and the actual panic and double-unwind behavior of the
compilation. Archive and Git hashes
remain distinct: the two reached bytemuck files need explicit CRLF-to-LF
normalization, while the reached discriminator files match its pinned
revision despite the recorded dirty tree of the archive. Solana cfg alone does
not establish SBF equivalence.

## Lookup and validation

The helper requests the validation PDA before looking for the program
account, using seeds `b"extra-account-metas"`, mint key. Missing the first
matching program account returns `TransferHookError::IncorrectAccount`.
Validation is optional and also selected by first match. Without validation,
the helper appends readonly nonsigner program metadata, then clones and
appends its AccountInfo. The four moved standard accounts remain live until
function-exit cleanup. Equal keys need not identify equal cells.

With validation, it builds Execute data from the discriminator and
little-endian amount, four readonly standard metas, validation metadata and
five AccountInfos: the four moved arguments and a validation clone. An actual
shared Ref holds validation data through resolution and is released before
caller copyback.

The TLV scan validates the whole region. It allocates a discriminator vector,
checks headers and pushes each nonzero discriminator before checking the payload bound of that entry. That vector drops before the first Execute lookup.
A short zero tail is permitted. A malformed later entry fails even if an
earlier Execute entry exists. The entire reached 0.7.0 scan, including this
allocation order, is the source argument for reuse of the shared validator.

`PodSlice::unpack` checks the four-byte count and 35-byte, alignment-one record
shape. A nonmultiple payload yields `BufferTooSmall` when no complete record
fits, otherwise `BufferTooLarge`. `PodSlice::data` subsequently panics if count
exceeds physical capacity; this is not a ProgramError. Zero active records may
leave physical spare records.

## Current data, privileges and aliases

For each active extra, resolution borrows data from **every current Execute
AccountInfo**, even for a fixed address. Thus an unrelated borrow conflict
can fail that case. Failed collection releases the acquired prefix. Earlier
extras participate in later collections; the final append alone does not
cause another borrow.

Discriminator 0 copies a fixed key; 1 resolves a PDA under the program of Execute;
values at least 128 select an external program account before unpacking seeds;
2 obtains a key from instruction/account data. Other values fail. Literal,
instruction-data, account-key and account-data seeds retain order and current
views at the PDA call. Missing or resized retained views are representation
failures, not invented source errors.

Collected Refs drop before privilege reduction and matching. Resolver 0.9.0
clamps signer and writable requests against the union of matching existing
metas; a new key retains both requests. It does not use the later rule that
always clears signer requests. POD flags use nonzero-to-Boolean conversion.
The first matching additional AccountInfo is cloned before metadata push,
and that owner is cleaned if the push unwinds.

## Copyback and primitive interpretation

Copyback extends caller metadata with the suffix of Execute after five entries,
then clones/extends the corresponding info suffix and appends validation
metadata and its clone. Local infos and instruction fields drop before the
final program append. Program/validation aliases still produce both appends.
The program ID and data of the caller remain distinct from temporary Execute data.

Under the primitive storage frames, resolution errors leave caller vectors
untouched. After metadata extension, a later failure retains that extension
and any actual partial info extension. Cleanup uses that state; there is no
transactional rollback. Terminal exits skip remaining cleanup and have no
after-state; divergence has no finite outcome.

Pubkey 2.2.1 starts with a zeroed address and bump 255. The model retains
partial writes and the fixed panic after nonzero status through `zeroFindRun`.
It does not substitute a MaybeUninit output, add local seed admission checks
or assume cryptographic success.

Parameters describe reached vector/storage, Rc, collection, panic and syscall
operations, not an arbitrary resolved-list or complete-helper oracle.
Continuation conditions supply current vectors, typed cells, live guards,
literal progress and cleanup at reached primitive exits, independently of a
successful overall result. Actual owning fields, borrowed additional slices,
moved AccountInfos, retained loans and frames need one coherent source
interpretation; a full allocation graph alone does not grant compatibility
with arbitrary fractional or retagged caller resources.

The error-domain theorem derives only `InvalidAccountData`,
`AccountBorrowFailed` or `Custom code` with `code < 2^32` from actual ordinary
paths, without assuming validity of a completed result. Cleanup cannot invent
another ordinary error. The compiled error type is still String-bearing
2.2.2; a 3.x layout is not a substitute. The
[binding obligations](../BINDINGS.md) remain separate from the `True` precondition of the mathematical
family, and no allocator, SDK, later callee or Rust body
correctness follows from a finite reference witness.

## Regression scope

The existing `TransferHookResolution` conformance family checks native records
from the independently locked `transfer-hook-resolution` driver. Its sample
interprets fixed/key-data extras and empty PDA seed vectors with a nonfailing
allocator. It does not instantiate nonempty borrowed-seed storage. The native
dev profile uses optimization level 3, no debug assertions, no overflow checks
and panic unwind. Applying the contracts to a Solana build that aborts on panic
requires a separate binding to that execution profile.

The mathematical test root also checks a missing-program execution: the PDA
request remains recorded, all four moved AccountInfos are dropped, and the data and vectors of the
caller remain unchanged. It checks privilege union across
matching aliases, unused POD capacity and malformed storage before a declared
count panic. The concrete source binding still requires its source and storage
interpretation; these examples do not make those premises automatic.

Seed-unpack and selection errors before the first seed-view push are covered by
the finite fixture. Terminal recordings stop at the first mandatory PDA call
and check its forced request without a synthetic post-state. Shared seed-view
controls retain current referenced data across callbacks. Successful nonempty
seed vectors and arbitrary allocator/destructor schedules remain generic model
cases, rather than native coverage of this fixture.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:1f14e27e10408d0d -->
<a id="review-1f14e27e10408d0d"></a>

Model the whole local helper: validation PDA before first program lookup; optional first validation lookup; ordered Execute instruction and five owned infos; actual shared validation Ref and per-record collect of every current info Ref; whole-region TLV validation, first Execute range, PodSlice layout errors then count-capacity panic; fixed/key-data/ordered-seed resolution; 0.9 privilege union and first-match account lookup; clone-before-push; temporary cleanup; extras/validation/program copyback in source order. The source frame is not transactional: metadata extension precedes info extension, so later unwind retains actual partial mutation. Pubkey 2.2.1 supplies a zeroed destination and bump 255. No CPI body or result oracle is part of the family. See source-notes/transfer-hook-resolution-0.9.0.md for reached dependency comparisons and source admission.

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.
<!-- /registry -->

<!-- registry:review:ac3d6123b8712718 -->
<a id="review-ac3d6123b8712718"></a>

The 0.9.0 helper and locked dependency chain are the inspected reference. The declared 0.9 range assumes validation PDA before program lookup, whole-region TLV/POD validation, every-current-info borrowing, fresh signer preservation and alias privilege union, ordered first-match resolution/clone-before-push and cleanup. Copyback remains metadata before infos, retaining partial mutation on unwind; the zeroed PDA provider and resource frames remain explicit. This helper performs no CPI.
<!-- /registry -->
