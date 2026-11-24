# Agave 4.3.2 source correspondence

The runtime reference is Agave **4.3.2**, commit
[`a203300045b405f86c9c84308b2eae76af69ac3b`](https://github.com/anza-xyz/agave/tree/a203300045b405f86c9c84308b2eae76af69ac3b).
This analysis re-reads the function bodies at that revision and the exact SDK
packages in its [dependency lock][agave-dependency-lock]. The review date is
3 November 2026.

## Scope

The comparison concerns the modeled account state and transaction outcome under
the conditions below. It is a source argument, not a formal refinement of the
validator or a claim about every inhabitant of a Lean record. The declaration
and axiom audits establish properties inside the model. Source hashes establish
which implementation was inspected. Neither substitutes for the other.

The principal configuration is `mainnet`: Agave 4.3.2, memory configuration L,
active pointer restrictions, and the fixed feature/rent snapshot in
[Profile.lean](../Solanalib/Runtime/Profile.lean). Historical release selectors remain
mathematical definitions; this review does not revalidate those releases.
Additional configurations have the explicit differences recorded below.

The source representation requires these conditions:

- Account balances, rent epochs, return codes, syscall operands and encoded
  lengths fit their source integer types. Account data is at most 10 MiB.
  Stored accounts with zero balance are represented as absent.
- Transaction keys are distinct, account and key arrays agree, instruction and
  program indices are valid, header counts describe the actual static keys,
  duplicate instruction privileges agree, and the fee payer is the first
  signer/writable account. The full native message sanitizer remains outside
  the model. `Message.WF` expresses only part of this domain.
- Fees, heap size and loaded-data limits are actual admitted bank values; the
  loaded-data limit is from 1 through 64 MiB. Account lookups, program/cache
  entries, builtin registration, sysvar values and extra loaded-data charges
  denote the actual bank inputs. `BankEnv.WF` does not prove those connections.
- A runtime context starts with zero balance/resize counters and valid bounded
  accounts. Setter arguments and subsequent counters remain in the machine
  domain. The Lean arithmetic over unbounded integers is not itself a proof of
  checked or saturating machine arithmetic for arbitrary starting states.
- Layouts, buffers, request values and output locations come from the same
  admitted invocation. Source memory access and the interpretation of program
  traces remain explicit boundary obligations. A total Lean slice or a Boolean
  pointer summary does not establish a successful source translation.
- Cryptographic parameters implement the named algorithm, operation version,
  input domain, result width and error classification. The result widths of
  the four hash syscalls are laws of `Prims`. Program and opaque
  builtin behaviors satisfy their supplied contracts. No callee success or
  state-effect guarantee follows merely from invocation.

`Profile.WF`, `BankEnv.WF`, `Message.WF` and `Sysvars.WF` are useful partial
predicates, not one complete source-correspondence premise. The following
sections explain the additional conditions at each operation.

## Profile and limits

Re-read [the current feature fields][runtime-feature-fields], their
[bank-to-SVM projection][runtime-feature-projection],
[transaction constants][runtime-constants] and
[execution-budget defaults][runtime-budget]. These establish the source switches
and limits: 256 transaction-account positions, 255 instruction references,
10 KiB instruction data, 10 MiB account data, 20 MiB net transaction growth,
64 trace entries, stack capacity 5 or 9, at most 256 KiB heap and 20,000 hash
slices. The 256-position ceiling is distinct from the active 64/128 account-lock
limit. Compute-budget parsing, heap alignment and fee calculation are bank inputs.

The source establishes what a feature does. Activation at a particular slot is
a separate observation. `mainnet` records slot 462,908,421 on 29 October 2026;
its values are fixed inputs, not a claim about all later slots. The rent values
were corroborated by the recorded finalized observation at slot 464,457,632 on
2 November: rate 5,080, threshold 1.0, burn percent 50, and minimum balances
650,240, 655,320 and 1,488,440 for lengths 0, 1 and 165. A history crossing a
feature or rent change needs a separate history argument.

The NoOp fee-payer feature is excluded by `Profile.WF`. Current builtin
registration does not register loader-v4; the presence of a loader-v4 selector
in a mathematical profile does not establish that deployment path. The source
check of `SysReq.registered` covers invocation services, not full deployment
admission. Allocation syscall registration additionally depends on the loader
configuration that rejects broken deployments.

## Accounts and rent

`Account` represents the five stored fields of the
[current account record][account]. `Account.missing` agrees with the
[loader][account-loader]: zero balance, empty data, System owner,
non-executable, maximum rent epoch. A stored dead account is represented as
absent before loading.

The actual dependency is **solana-rent 4.4.0**. Its
[`try_minimum_balance`][rent-current] checks the data length and rent rate before
using the exact integer branches. At threshold 1 the rate must be at most
1,759,197,129,867; at threshold 2 it must be at most 879,598,564,933. The data
length is at most 10 MiB. On that domain `RentParams.minBalance` agrees with
`(128 + length) * rate * threshold`. `RentParams.WF` alone is weaker: its rate
bound of `2^64` does not imply these source checks. The selected 5,080/1 profile
satisfies them.

The relaxed rent condition is derived from the implemented
[pre/post account-state construction][transaction-account-state] and
[rent-state transitions][rent-state], including the account-key wrapper:

1. With the relaxed feature active, a positive pre-balance becomes pre-state
   `RentExempt`; zero becomes `Uninitialized`.
2. Relaxed final exemption is available exactly when the pre-balance is positive,
   the owner is unchanged and the data does not grow.
3. A final zero balance is `Uninitialized`. Other final balances are exempt when
   `post ≥ minimum`, or when relaxation is available and `post ≥ pre`.
4. For these pre-states, `transition_allowed` accepts precisely final
   `Uninitialized` or `RentExempt`.

Consequently the test reduces to
`post = 0 ∨ post ≥ (if eligible then min minimum pre else minimum)`, where
`eligible` means positive pre-balance, unchanged owner and no data growth.
This is `relaxedMinBalanceOk`. The incinerator exemption remains in the current
account-key wrapper used by `rentCheck`. The static fee-payer transition has no
such wrapper or exemption. Fee subtraction preserves owner and length, giving
the specialized floor in `feePayerRentCheck`. These conclusions come from the
4.3.2 implementation, not from the SIMD proposal alone.

## Account mutation

The [current instruction-account setters][instruction-accounts] and
[transaction-account bookkeeping][growth] establish the following order:

| Modeled operation | Source checks and successful effect |
| --- | --- |
| `setOwner` | Current ownership, writable privilege, zero data, then equality; a changed owner touches the account |
| `setLamports` | Foreign debit, writable privilege, then equality; a change touches and updates the balance delta |
| `canDataBeResized` | 10 MiB limit, 20 MiB net-growth limit, writable privilege, current ownership |
| `setDataLength` | Resize checks, then same-length shortcut; growth zero-fills and shrinkage truncates |
| `setDataFromSlice` | Resize checks and replacement; even an identical byte replacement touches |
| `setExecutable` | Rent exemption, ownership, writability, then equality |

Agave 4.3.2 has no early foreign-length-change `AccountDataSizeChanged` test.
The release-specific branches encode the corresponding check orders separately.
Numeric helper checks precede their setter call. These comparisons require
valid account indices, source-width arguments and the rent domain above.

Touch flags are operation metadata, not final-value inequality. `TxState.touched`
represents membership in the source flags. The administrative Instructions-sysvar
index update is separate from program mutation. `TouchChanges` is a theorem
about these modeled operations and retains that sysvar exception.

## Transaction admission and loading

The [transaction processor][transaction-execution] takes the bank check result,
revalidates a selected nonce, then validates the fee payer. `ProcTx` follows that
order. Bank rejection and nonce rejection leave the account map unchanged.
Only successful nonce admission can reach `validateFeePayer`.

The [fee loader][account-loader] masks an exempt payer rent epoch, rejects zero
balance, classifies the payer, reserves the nonce minimum when applicable,
checks subtraction of the minimum and fee, subtracts the fee and checks the
static rent transition. `isInitializedNonceAccount` implements the
[fee-payer classifier][nonce-account-validation]: System ownership, exactly
80 bytes, version tag 0 or 1 and initialized-state tag 1. It accepts legacy
initialized state and does not check the message hash, authority or freshness;
it still requires exactly 80 bytes even when durable-nonce admission permits
a tail.

`loadedAccount` loads the validated payer first, constructs the Instructions
sysvar when present, masks an existing writable exempt account, preserves
read-only account fields, and defaults a missing ordinary account. These rules
were re-read at `account_loader.rs:223–250,355–365,593–684`.

For `loadedSize` and `checkLoad`, source loading at
`account_loader.rs:488–617` charges lookup-table bases, payer/accounts and
non-explicit deduplicated loader-v3 program-data accounts before checking
program existence and owner. `extraLoadedSize` must equal that actual extra
charge. Every accounting overflow/limit failure and Instructions-sysvar
construction failure has the modeled error `MaxLoadedAccountsDataSizeExceeded`.
For an admitted limit at most 64 MiB, replacing monotone saturated increments
by an exact nonnegative total preserves that error class. It does not preserve
intermediate cache/inspection effects or size metrics on failure; those are
outside `ProcTx`.

## Nonce admission

Re-read the [bank age check][bank-nonce-selection],
[SVM nonce validation][nonce-validation],
[message nonce/signature accessors][svm-message-current],
[nonce-account validation][nonce-account-validation],
[current-version rule][nonce-current-version],
[nonce state/hash construction][nonce-state] and
[state write operation][nonce-state-write].

`Tx.nonce` contains only a selected index. `checkNonceSelection` checks it against
the actual bank recent-blockhash decision: a recent blockhash selects no nonce;
otherwise the first instruction must identify the selected durable nonce.
`Message.durableNonceIndex` requires a System instruction whose first four bytes
are little-endian tag 4 and whose first account is a static writable key.
Trailing instruction bytes are permitted; a lookup-table nonce is not.
`isRecentBlockhash` is an explicit bank-queue boundary, including the configured
maximum age. This consistency check prevents a caller from bypassing selected
nonce validation by simply supplying `none`; it does not implement the queue.

`validateNonce` then follows the SVM revalidation order:

1. Resolve the selected key and load its current nonzero-balance account;
   absence gives `AccountNotFound`.
2. Apply the configured strict 80-byte size check.
3. Require System ownership and a current initialized nonce whose stored hash
   is the message blockhash. Legacy state is rejected here even though it can
   pass fee-payer classification.
4. Require a different next nonce and the nonce authority among the signer
   accounts of instruction zero. A signature only elsewhere is insufficient.
5. Compute the next state from the stored authority, the bank signature fee and
   `SHA256("DURABLE_NONCE" ++ environment_blockhash)`.

`nextDurableNonce` uses the shared symbolic SHA-256 parameter. Its result has 32
bytes by the width law of `Prims` (`Prims.sha256_length`; `BankEnv.WF.nonceHash`
is a theorem); correctness of the concrete algorithm is an additional primitive
premise. The next signature fee has type `UInt64`.
`advanceNonceAccount` changes only nonce data. With strict size checking disabled,
the codec accepts at least 80 bytes and state replacement preserves any tail.
No arbitrary replacement account enters the transaction type.

`validateNonce_advanced`, `validateNonce_preserves_fields` and
`validateNonce_preserves_length` establish the connection to the actual stored
account. The computed result carries an address rather than an unchecked index.
Every fee/load/execution constructor of `ProcTx` requires this validator result.
`ProcTx.nonce_error` proves that a failed validation has only the unchanged,
uncharged outcome. `commitRollback` is a lower-level helper; its nonce argument
is validated by the public processing relation, not by the helper itself.

Signature verification, status-cache checks, account locking and the native
sanitizer remain external bank-admission facts. The nonce checks do not replace
a contract for executing System nonce instructions later in the transaction.

## Execution and commit

Re-read [invoke dispatch][invoke-context], [loader dispatch][loader-dispatch],
[builtin identities][builtin-table], [VM execution][vm-execution],
[transaction context][runtime-context], [final transaction checks][transaction-execution]
and [account saving][account-saver].

`push` rejects non-immediate reentry, an unbalanced caller, exhausted trace
capacity and excessive depth, then updates the Instructions-sysvar index.
`pop` checks the balance of a successfully pushed frame. A nonempty-stack
premise is necessary: the raw Lean helper accepts a balanced empty stack,
whereas the source reports `CallDepth`. Accepted instruction processing calls
it only after a successful push. The source advances its top-level counter on
push and preallocates top-level trace slots; the model advances on final pop and
records chronological calls. Stack/index/sibling comparisons therefore require
the stated valid-context and trace interpretation, not raw structure equality.

`dispatch` uses the program owner and actual registered program/cache entry.
`BuiltinsWF` checks distinguished identities but does not prove an arbitrary
additional table equals the deployed registration. `Program` and opaque native
behaviors supply traces/contracts; the model does not execute their binaries.
`Exec` checks replies and successful zero-return read-back. A program error
prevails over a subsequent pop error. The model discards partial local state on
failure, including return-data resets or partial synchronization, and compares
terminal outcomes and rollback effects. It makes no intermediate error-state
identity claim. Compute failure choices abstract the meter; they give no exact
cost or sufficient-budget guarantee.

After successful message execution, `Execute` checks rent of writable accounts
in index order and then total balance. The current source uses checked `u128`
sums, which cannot overflow for at most 256 accounts with `u64` balances.
`commitSuccess` saves writable, touched accounts other than invoked-only program
accounts. The source explicitly marks the payer touched because its fee was
charged before invocation. An untouched writable account retains its stored
rent epoch; a touched account saves the loaded working value.

[Rollback construction][rollback] has three cases: without a nonce restore the
stored payer rent epoch; with the payer as nonce replace only validated payer
data; with a separate nonce save the payer and the validated advanced nonce.
A zero-balance stored result denotes absence. Loading failure after fees and
execution failure use this rollback; rejection before payer validation stores
nothing. The new resolved-address result prevents a default-key write from an
out-of-range nonce index.

## Transaction-local program cache

`TxState.modifiedPrograms` records cache entries changed during the transaction.
Its newest-first lookup precedes `World.programs`, matching
[`store_modified_entry`][cache-store] and [`find`][cache-find]. The list may retain
shadowed writes that the source map replaced; the correspondence concerns lookup
results, not literal map identity or a count of distinct modifications. The same
overlay flows through top-level instructions and CPI, whose source invocations
share the mutable transaction cache.

The exact lock-selected [loader-v3 instruction codec][loader-v3-instruction-codec]
and [state codec][loader-v3-state-codec] are version 7.0.0. Their fixed-width
bincode tags and the [loader handler][loader-v3-handler] give these direct effects:

| Successful operation | Instruction tag | Program-key position | Cache write |
| --- | --- | --- | --- |
| [DeployWithMaxDataLen][loader-v3-deploy] | 2 | 2 | `Unloaded` |
| [Upgrade][loader-v3-upgrade] | 3 | 1 | `Unloaded` |
| [ExtendProgram][loader-v3-extend] | 6 | 1 | `Unloaded` |
| [Close ProgramData][loader-v3-close] | 5 | 3 | `Closed` |

Positions are zero-based instruction-account positions. Close decodes the original
state of position 0 before truncating it; `loaderV3CacheAction` therefore uses the
pre-state. Closing Uninitialized or Buffer state has no direct cache write. The
other preserving tags are InitializeBuffer, Write, SetAuthority and
SetAuthorityChecked (0, 1, 4 and 7). This pin has no Migrate or ExtendProgramChecked
variant. `LoaderV3ResultContract` requires a classified action for success, so a
missing target or invalid classification cannot silently become preservation.
`Exec.loaderV3` applies the write after the opaque account behavior, and
`RunProgram.loaderV3_cache` proves every successful selected loader call has it.
The generic builtin rule excludes loader-v3. Classification does not validate the
full instruction payload, ProgramData linkage, account privileges, authority,
funding or executable code; those remain conditions of the opaque source behavior.

The [deployment helper][loader-deployment] verifies code and inserts
[`Unloaded`][cache-unloaded], with effective slot
`min (deployment_slot + 1) U64_MAX`. Close inserts a
[`Closed` tombstone][cache-closed] effective at its deployment slot.
The [effective-slot rule][cache-effective-slot] supplies `DelayVisibility` only
while `deployment_slot ≤ slot ∧ slot < effective_slot`. At `U64_MAX` the delay
interval is empty, but the Unloaded entry still rejects current-batch dispatch.
The deployment slot is the actual `World.sysvars.clock.slot`:
the [deployment macro][loader-deployment-slot] requires agreement with the
transaction-cache slot, and the [bank constructs Clock][bank-clock-slot] from
its execution slot. `Profile.slot` records the dated feature snapshot and is
not that execution clock. Slot agreement and source-width bounds are explicit
correspondence conditions. [Loader dispatch][loader-dispatch] rejects Closed,
Unloaded and DelayVisibility with `UnsupportedProgramId`; none can fall through
to the previously loaded `Program` after a successful management operation.

The source [drains local modifications][transaction-cache-drain] after every
completed execution and [merges them only on complete success][transaction-cache-success],
after rent and balance checks. `ProcTxWithCache` uses the same `Execute` derivation
for accounts and the exported cache changes. Its proved projection and completeness
recover `ProcTx`; its failure theorem exports no committed modifications on any
other outcome. The source may retain transient modifications in a failed-execution
receipt; the model does not claim that receipt is empty or reproduce intermediate
error states. The [batch merge][cache-batch-merge] and
[bank commit][bank-cache-commit] preserve the success-only condition.

`BankEnv.withCommittedPrograms` supplies the dispatch view for subsequent
transactions retaining that batch cache, projecting both modified entry kinds to
`notDeployed`. It does not load code. A fresh batch or bank cache load must bind
the actual entries produced by [global extraction][cache-global-extract],
verification and environment selection; [global merging][cache-global-merge]
alone does not make an Unloaded entry executable. At ordinary slots below
`U64_MAX`, the one-slot visibility rule also rejects newly deployed programs
after a same-slot reload. The saturated endpoint needs its own refresh argument.

The pinned [native registration][native-cache-scope] has no loader-v4 entry.
[Legacy loader management][legacy-loader-management] rejects in this source;
execution of already loaded programs owned by those loaders remains supported.
The generic opaque management behavior of the model does not prove that rejection.
The production native source audit found only the three loader-v3 deployment
calls and ProgramData Close as direct cache mutations. Additional registrations,
development helpers and bank migrations need their own contracts; `BuiltinsWF`
alone does not establish the actual registration or absence of extra effects.

## Message privileges and Instructions sysvar

The [legacy message][message] and [loaded-message][message-loaded] sources, together
with [reserved account keys][reserved-accounts], justify header-based signer and
writable flags, loaded writable/read-only segments, reserved-key demotion and
invoked-program demotion. Header coherence, unique keys and valid indices are
preconditions. A writable flag is instruction authority, not an account field.

Re-read [Instructions-sysvar construction][instructions-sysvar]. Instruction `i`
starts at `2 + 2 * instruction_count + sum(previous_entry_lengths)`; an entry has
`36 + 33 * account_count + data_length` bytes. The source checks each start fits
`u16`; the final entry may end beyond 65,535. `ixSysvarOffsetsFit` models that
check when the message actually loads this sysvar. Its failure becomes the
loaded-data-size error. The serialized flags, account keys, program ID and data
come from the same resolved message used to build frames.

## Serialization and read-back

Re-read [serialization][serialization] and [deserialization][read-back], including
`serialize_parameters`, both `*_for_abiv0` bodies and both `*_for_abiv1` bodies.
The 255-reference guard counts duplicates and precedes ABI selection.
`serializationAccountCheck` and `serializeChecked` expose that boundary.
Loader-v1 uses ABI v0; the selected modern loaders use ABI v1.

ABI v1 records flags/padding, key at 8, owner at 40, lamports at 72, length at 80,
data at 88, growth reserve, alignment padding and maximum rent epoch. A duplicate
record refers to its first instruction occurrence. The optional pointer array
exists only in ABI v1. Model positions and entry lengths derive from the original
layout and are not authority supplied by edited header bytes.

For ABI v1 read-back, owner bytes are read early but the owner setter runs last:
lamport update, entry-growth and absolute-length checks, configuration-specific
data step, then owner update. Duplicates are skipped. ABI v0 ignores rewritten
length and owner fields. Source reads can fail on a short buffer; the total Lean
slice operations do not recreate that error. The source argument requires the
same admitted serialized extent and valid saved layout, rather than arbitrary
calls to `readBack` with short byte lists.

The proofs of record offsets, `WritesLegalL` and `readBackL_of_legal` are internal
model results. They retain distinct layout indices, actual privileges, numeric
bounds and conservative positive-growth premises; they do not prove the source
layout/trace interpretation automatically.

## Memory

The [serializer][serialization], [VM setup][vm-execution] and
[current transaction access handler][runtime-context] were re-read for input
regions and access faults. L uses a working input buffer and synchronizes later.
S separates data regions; D relates them directly to account data. `loadRegion`
and `storeRegion` cover the represented input region. Other program memory and
actual machine instructions enter through the supplied program trace.

Allowed S/D stores can grow an account up to the reserved entry extent, the
10 MiB account limit and remaining transaction growth, with zero-filled new
bytes. Actual syscall destination translation can trigger growth before a
reply or output write; the model delays growth to its output store. This is a
known difference, so full S/D syscall correspondence is not claimed. L avoids
this growth-timing difference while still requiring successful source pointer
translation. S/D CPI also needs an explicit relation for its mutable regions.

## CPI

The current source is [prepare_next_cpi_instruction][cpi-preparation] and the
[shared invocation path][cpi], including the checked translation and
synchronization bodies in the source map.

Preparation has two distinct account passes. First, every transaction-account
lookup succeeds and repeated metas have signer/writable flags merged. Second,
first occurrences are visited in order: check membership in the caller, then
writable privilege, then signer privilege. Only then resolve the callee program.
`mergeMeta`, `checkPrivileges` and `prepareCallee` implement this order. Duplicate
caller flags must be consistent, as stated by `Frame.FlagsConsistent`.

`message_frame_flagsConsistent` proves this invariant for message frames, and
`calleeAccounts_flagsConsistent` and `prepareCallee_flagsConsistent` prove it for
constructed CPI frames. These construction results need no additional
well-formedness premise. For an arbitrary supplied caller,
`flagsConsistent_queries` relates `writableTx` and `signerTx` to the account
returned at `firstIdx`, using optional indexing to establish its existence.
`checkPrivileges_first` proves exact equality with the first-occurrence
membership/writable/signer check sequence of the source. Its premise is the consistency of the caller, because those are the flags being queried.

An escalated read-only account followed by an account missing only from the
caller gives `PrivilegeEscalation`. Reversing them gives `MissingAccount`.
An account missing from the transaction entirely fails in the first pass before
privilege checks. Later duplicate metas contribute their flags before the
second pass. The focused ordering regressions cover these distinctions.

With `pointerChecks = true`, the source translates all account infos before
`update_callee_account`, then synchronizes balance, data and owner under caller
authority before invoking the callee. Translation selects first matching infos,
skips duplicate instruction positions and executable accounts, and uses the
original caller metadata. PDA signer authority comes from the caller program.
Boolean pointer summaries and request values need a binding to actual translated
addresses; they are not independent evidence that translation succeeded.

Successful return copies out only callee-writable accounts, enforces the entry
reserve, zeroes released bytes when appropriate and updates the local and
serialized lengths. The selected output destinations must represent the actual
caller observation. `cpiAnswer` does not encode identity of shared length-word
locations: observing an updated length through other aliases needs an explicit
binding argument. No such alias theorem is supplied by the response encoding.

With `pointerChecks = false`, Agave interleaves each account-info translation and
synchronization; the model still separates them. Its source-order argument does
not cover that combination. On errors, partial source synchronization is erased
by the model outcome. A failed CPI is terminal to its caller; `cpi_common` does
not produce a recoverable error reply followed by normal continuation.

## Syscalls and primitives

Re-read current registrations and service bodies in
[the syscall implementation][return-data], [sysvar getters][sysvars],
[logging][syscall-logging] and [memory helpers][syscall-memory]. The following
source comparison is at the admitted value/result boundary:

| Model family | Checked behavior and additional obligations |
| --- | --- |
| PDA creation and search | Ordered seeds, at most 16 seeds of at most 32 bytes; correct SHA-256/Edwards predicate; bumps 255 through 1; no destination write/check on exhausted search |
| Hash replies | Ordered input slices and 20,000-slice bound; actual algorithm; result widths of 32, 32, 32 and 64 bytes as laws of `Prims`; translations and meter supplied by the boundary |
| secp256k1 recovery | 32-byte hash, 64-byte signature, recovery-ID error before signature error, 64-byte recovered result |
| Curve and pairing operations | Exact identifiers/opcodes and fixed widths; multiscalar and pairing arrays have the same source count; native operation/version and error contract remain explicit |
| BN254 | Selected G1/G2/pairing primitive versions, endianness, widths and error classification; mathematical group arithmetic alone is insufficient |
| Modular exponentiation | Current little-endian primitive, at most 512 bytes per operand, modulus-sized output; primitive rejects empty, zero, one and even moduli; inactive in `mainnet` |
| Typed/generic sysvars | Correct source value widths, cache bytes, destination checks and layout; typed absence errors and generic statuses 2/1/0 |
| SBF return data | 1,024-byte setter limit; getter reports full length but copies at most capacity; zero copied bytes write neither data nor program ID |
| Sibling and stack queries | Well-nested chronological trace related to the source caller-index trace; actual four destination ranges, with empty data/account outputs excluded from sibling overlap checks |
| Memory services and allocation | Actual reads/writes supplied by the program trace; memcpy overlap rule; admitted word-sized parameters and bounded heap for allocation |

[`SyscallHash`][syscall-hash] writes `size_of::<H::Output>()` bytes, with the
[output types][hasher-outputs] of its four hashers: `Hash` of solana-hash 4.6.0
has [32 bytes][hash-bytes], and the [Keccak][keccak-hash] and
[BLAKE3][blake3-hash] hashers re-export it; `Hash512` has [64 bytes][hash512-bytes].
`Prims` states these widths as laws (`sha256_length`, `keccak256_length`,
`blake3_length`, `sha512_length`), so a successful hash reply carries one digest
of `HashAlg.width` bytes (`sysStep_hash`). The hash functions themselves remain
parameters.

[`get_check_aligned`][check-aligned] holds unless the owner of the program is
`bpf_loader_deprecated`, the owner that selects ABI `v0`; `Abi.checkAligned` is
that switch. Where it holds, the syscalls reject a pointer argument that is not
aligned for its type. The model applies it to the typed sysvar destinations;
the alignment of the other translated arguments belongs to the boundary.

The direct native [transaction-context setter][native-return-data] is a separate
API. It takes an explicit `program_id` and byte vector, writes both return-data
fields and returns success, without instruction-account access or a 1,024-byte
check. The delegated [scratchpad length setter][native-return-length] only assigns
its length. `setNativeReturnData` and `Exec.havocReturnData` model those effects;
represented byte lengths must still fit the source integer domain. The SBF wrapper
performs its size check and supplies the current program ID before calling this
native API. The empty-account, 1,025-byte native witness establishes the capability
for a hypothetical registered builtin, not observed use by a current mainnet
builtin.

`sysStep` follows the [processed-sibling output branches][processed-sibling].
If no sibling exists, the source returns zero without translating outputs. If
the supplied lengths differ, it translates and updates only the 16-byte header.
When the lengths match, it translates the program ID, data, account metas and
header together. The request ranges must describe those actual outputs, with
32 bytes for the program ID, 16 for the header, the data byte count and 34 times
the account count. Successful nonempty translations and their alignment remain
premises of this admitted-value comparison.

The [mutable-output macro][sibling-output-translation] checks translated host
ranges. For a zero count, [the initial touch][sibling-output-touch] does no mapping,
and [slice translation][runtime-slice-translation] returns an empty dangling slice
independently of the supplied VM address. Those empty destinations are outside
the actual nonempty host buffers. `siblingOutputsDisjoint` therefore removes
zero-byte ranges before checking the others. Nonempty ranges must preserve the
overlap relation between the VM destinations and the translated host buffers;
the model does not establish that memory connection. Nonempty header, program-ID,
data and account-meta overlaps still fail. This normalization is specific to
sibling outputs: `nonOverlapping` retains the raw source arithmetic for other
checks, including `sol_memcpy_`.

`Sysvars.WF` relates Clock, Rent and EpochSchedule prefixes and excludes unknown
cache IDs. It does not prove optional EpochRewards/LastRestartSlot coherence,
all numeric widths or a 32-byte parent blockhash. These are additional premises.
Typed layouts and complete account encodings differ: sizes are respectively
40/40/24/96/8/8 and 40/33/17/81/8/8 for Clock, EpochSchedule, Rent, EpochRewards,
LastRestartSlot and Fees. The current zero-padding derive and getters justify
padding; the source map pins their SDK versions and the cache implementation.

Two further feature combinations differ from the source. Disabled BLS with
`abortOnInvalidCurve = false` produces a generic status in the model where Agave
unconditionally rejects known disabled BLS identifiers. With G2 enabled and
little-endian disabled, `altBn128OpKnown` rejects G2-LE operations that the
current source admits. `mainnet` enables BLS, G2, little-endian and abort-on-invalid,
so these differences do not apply to that selected combination.

Logs are an observation abstraction: the model retains values or flattened bytes,
while runtime diagnostics may encode or format them differently. Exact log text
and compute cost are outside the comparison. Where translation or diagnostic
completion is assumed, that premise includes normal completion and the stated
error classification; it is not inferred from a pure reply.

## System instructions

Re-read the [current System processor][system-program],
[instruction codec][system-instruction-codec], [error codes][system-error-codes]
and [decode configuration][system-codec-config]. The model decodes fixed-width
little-endian tags/numbers and bounded UTF-8 strings, permits trailing bytes,
and applies the 1,232-byte bound to consumed decode bytes.

`sysAllocate` checks signature, existing data/owner and then size. `sysAssign`
returns early for unchanged owner before checking signature. `sysTransfer`
checks signature, empty source data, sufficient balance, debit and credit.
`sysCreateAccount` checks destination balance, allocates/assigns and then transfers.
The prefunded form checks its feature and arity, allocates/assigns, and transfers
only nonzero funding. These are source-order comparisons for valid indices,
source-width operands, matching System identity and the stated primitive contract.

The [System nonce handlers][system-nonce-instructions] have additional state,
authority, rent and freshness checks. `Exec.systemNonce` remains opaque and its
generic modeled effects do not imply those exact handlers. Checked transaction
nonce admission is separate from execution of these instructions; the former
does not supply an execution contract for the latter.

## Library state and derived proofs

`AccountState`, `StoreOps`, `View` and `Store` are mathematical state/observation
interfaces grounded in [AccountView 2.0.0][account-view] and the selected
[entrypoint][sdk-entrypoint]. They require authenticated entry lengths and alias
identities. Data leases have at most 254 shared holders; the source byte encodes
free as 255 and exclusive as zero. Resize in the store is an abstract operation
factorization, not a literal source trace of the safe method. The model is not a
complete AccountInfo 3.1.1 interpreter. See [the focused SDK analysis](sdk-abi.md).

`CopyBack` proves a model-to-model observation theorem under `CopyRel` and
`WellBracketedRun`; no source SDK operation performs that delayed copying.
`Protocol` and `Env` formalize state threading and its consequences, including
fixed-context Clock agreement. They do not establish concrete request encodings.

`FlagConsistency`, `Frame`, `Executable`, `LamportFrame`, `StackFrame`, `SysvarCoherence`,
`ReadonlyFrame`, `WritesLegal`, `Theorems` and `Transfer` prove consequences of the actual
Lean transitions. Retain every premise, including active indices, consistent
layouts and the Instructions-sysvar exception. A proved model theorem does not
supply an unproved bank, primitive, program or representation connection.

## Source identities and replay

The [source registry](../source-map/sources.json) records each public source path,
Git revision or published archive checksum, line/text anchor and full-file hash.
Its correspondence entries name model modules and declarations, the exact reviewed
model hashes, this written argument, assumptions and limitations. Model changes
invalidate those review identities. The checker detects missing modules, stale
names, mismatched model/source hashes and inconsistent anchors. These mechanical
checks validate the evidence record; the semantic argument above remains manual.

SDK versions come from the pinned Agave dependency lock, except the explicitly
selected AccountView, AccountInfo and Pinocchio interfaces. Published crate
archives are authenticated against that lock where applicable. The address 2.7.0
and sysvar 4.2.0 entries use those immutable archives and link to their published
package sources.

Check the source correspondence and complete proof dependencies from the
repository root with actual source copies:

```sh
uv run --no-project --python 3.12 python tools/model-audit/check_runtime.py \
  --registry /path/to/pinned/cargo/sources \
  --agave-source /path/to/pinned/agave \
  --require-source-checks --output /tmp/runtime-audit.json
```

The strict option requires every source anchor to be checked. Without source
copies, the audit checks the Lean development and records zero checked source
anchors. The runtime tests construct successful and execution-error transactions,
successful CPI, loader cache changes, native return data, legal read-back and
allocation boundaries. Their closed witnesses establish that the specified
transition premises can be satisfied. Source, bank and memory correspondence
require the arguments stated above. Focused CPI, nonce and sibling-output
error-order regressions exercise the corresponding model branches.

[account]: https://github.com/anza-xyz/solana-sdk/blob/a541f77a1d482fdbcf420084d27fac42880d78bf/account/src/lib.rs#L61
[instruction-accounts]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/transaction-context/src/instruction_accounts.rs#L91
[account-loader]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/account_loader.rs#L373
[transaction-execution]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/transaction_processor.rs#L1033
[rollback]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/rollback_accounts.rs#L65
[account-saver]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/runtime/src/account_saver.rs#L54
[message]: https://github.com/anza-xyz/solana-sdk/blob/cd508efc69f65c3900d60a2f4c65212a037f4e98/message/src/legacy.rs#L571
[message-loaded]: https://github.com/anza-xyz/solana-sdk/blob/cd508efc69f65c3900d60a2f4c65212a037f4e98/message/src/versions/v0/loaded.rs#L160
[invoke-context]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/invoke_context.rs#L603
[serialization]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/serialization.rs#L490
[read-back]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/serialization.rs#L612
[account-view]: https://github.com/anza-xyz/solana-sdk/blob/1666707490c6c29e6e2edf69e2122b7cae3c9dbb/account-view/src/lib.rs#L180
[sdk-entrypoint]: https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/entrypoint/mod.rs#L307
[sdk-account-info]: https://github.com/anza-xyz/solana-sdk/blob/9b18fb2c3539bae21b4f7a8f97a0f087e4bf3c23/account-info/src/lib.rs#L28
[sysvars]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/sysvar.rs#L55
[instructions-sysvar]: https://github.com/anza-xyz/solana-sdk/blob/00981086d76170fe10efd543a1a71e3d42edc2a4/instructions-sysvar/src/lib.rs#L73
[pda]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L861
[return-data]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L1914
[native-return-data]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/transaction-context/src/transaction.rs#L504
[native-return-length]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/transaction-context/src/vm_slice.rs#L50
[processed-sibling]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L2010
[sibling-output-translation]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L662
[sibling-output-touch]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L640
[runtime-slice-translation]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/memory.rs#L63
[syscall-hash]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L2719
[hasher-outputs]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/lib.rs#L176
[check-aligned]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/invoke_context.rs#L800
[hash-bytes]: https://github.com/anza-xyz/solana-sdk/blob/6a572b07c36ace73db12d9f3d8e294570db3b702/hash/src/lib.rs#L34
[keccak-hash]: https://github.com/anza-xyz/solana-sdk/blob/82ac9cd1f2677eb12efb729585dcc673bdd7bc36/keccak-hasher/src/lib.rs#L9
[blake3-hash]: https://github.com/anza-xyz/solana-sdk/blob/4997949515c1862acc306c7cf40f0343321f5705/blake3-hasher/src/lib.rs#L7
[hash512-bytes]: https://github.com/anza-xyz/solana-sdk/blob/5f2f4b8dea572456dc687b3e4a87b80e63ed9cb1/hash-512/src/lib.rs#L30
[cpi]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L773
[growth]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/transaction-context/src/transaction_accounts.rs#L309
[runtime-context]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/transaction-context/src/transaction.rs#L407
[runtime-constants]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/transaction-context/src/lib.rs#L14
[rent-state]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/rent_calculator.rs#L102
[transaction-account-state]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/transaction_account_state_info.rs#L20
[runtime-budget]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/execution_budget.rs#L74
[runtime-feature-projection]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/feature-set/src/lib.rs#L20
[runtime-feature-fields]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm-feature-set/src/lib.rs#L3
[reserved-accounts]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/reserved-account-keys/src/lib.rs#L141
[builtin-table]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/builtins/src/lib.rs#L28
[loader-dispatch]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L83
[compute-budget-builtin]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/compute-budget/src/lib.rs#L6
[rent-current]: https://github.com/anza-xyz/solana-sdk/blob/91123d4cf58736d1c8a7c247eafc5a0c222bd2d1/rent/src/lib.rs#L187
[instruction-errors-current]: https://github.com/anza-xyz/solana-sdk/blob/e658c42f7dfdbe5431fa9bbf58709824c64ea706/instruction-error/src/lib.rs#L371
[program-errors-current]: https://github.com/anza-xyz/solana-sdk/blob/7cdfc06b7deb076e3d95e84eb6f23b8dc4f12378/program-error/src/lib.rs#L15
[svm-message-current]: https://github.com/anza-xyz/solana-sdk/blob/067f44a2a9dae54e4b75ecd64878645f848e118a/svm-transaction/src/svm_message.rs#L142
[system-program]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/system/src/system_processor.rs#L319
[system-nonce-instructions]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/system/src/system_instruction.rs#L25
[sysvar-cache]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/sysvar_cache.rs#L130
[syscall-logging]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/logging.rs#L7
[syscall-memory]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/syscalls/src/mem_ops.rs#L28
[precompile-set]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/precompiles/src/lib.rs#L54
[address-derive]: https://docs.rs/crate/solana-address/2.7.0/source/src/syscalls.rs
[address-seed]: https://docs.rs/crate/solana-address/2.7.0/source/src/lib.rs
[sysvar-clock-layout]: https://github.com/anza-xyz/solana-sdk/blob/e0ca04e3649138b4481cb58530ac1ce7243debe9/clock/src/lib.rs#L152
[sysvar-epoch-schedule-layout]: https://github.com/anza-xyz/solana-sdk/blob/309a177c3618c1c8e04d5c026ff9fc68195a340a/epoch-schedule/src/lib.rs#L60
[sysvar-epoch-rewards-layout]: https://github.com/anza-xyz/solana-sdk/blob/043c766a4365aa8565e16d42f10d1da46c3955a4/epoch-rewards/src/lib.rs#L27
[sysvar-rent-layout]: https://github.com/anza-xyz/solana-sdk/blob/91123d4cf58736d1c8a7c247eafc5a0c222bd2d1/rent/src/lib.rs#L28
[sysvar-last-restart-layout]: https://github.com/anza-xyz/solana-sdk/blob/3c7e4f3b1e3a5275e1dceee6d265bb4e31bbe3e1/last-restart-slot/src/lib.rs#L16
[sysvar-fees-layout]: https://docs.rs/crate/solana-sysvar/4.2.0/source/src/fees.rs
[sysvar-clone-zeroed]: https://github.com/anza-xyz/solana-sdk/blob/444d56c9badaece3de86586216e6f5f7b750b938/sdk-macro/src/lib.rs#L236
[system-instruction-codec]: https://github.com/anza-xyz/solana-sdk/blob/ab3e8a14bf2bab443bb8af32e95efe2fb65944db/system-interface/src/instruction.rs#L93
[system-error-codes]: https://github.com/anza-xyz/solana-sdk/blob/ab3e8a14bf2bab443bb8af32e95efe2fb65944db/system-interface/src/error.rs#L14
[system-codec-config]: https://github.com/anza-xyz/solana-sdk/blob/269703bfc3b7d941a038501f7ee486a8362b343e/bincode/src/lib.rs#L10
[big-mod-exp-contract]: https://github.com/anza-xyz/solana-sdk/blob/31d3c1c05f39ab7ca4d5c4e243d720d7277d1b77/big-mod-exp/src/lib.rs#L38
[edwards-validation]: https://github.com/anza-xyz/solana-sdk/blob/a947d32fb1ab7d06b69bd96bd97eb4d002eb454e/curve25519/src/edwards.rs#L80
[curve-codes]: https://github.com/anza-xyz/solana-sdk/blob/882ea29f565810bfdf6a85700f95c004d24fceda/define-syscall/src/curve_constants.rs#L24
[sdk-account-resize]: https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/lib.rs#L457
[cpi-preparation]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/invoke_context.rs#L349
[cpi-instruction-size]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L129
[cpi-authorization]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L159
[cpi-caller-data]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L216
[cpi-caller-rust]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L272
[cpi-caller-c]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L408
[cpi-instruction-rust]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L538
[cpi-signers]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L631
[cpi-instruction-c]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L676
[cpi-account-infos]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L901
[cpi-account-translation]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L955
[cpi-callee-update]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L1108
[cpi-caller-region]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L1179
[cpi-caller-update]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/cpi.rs#L1235
[nonce-validation]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/transaction_processor.rs#L833
[bank-nonce-selection]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/runtime/src/bank/check_transactions.rs#L229
[agave-dependency-lock]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/Cargo.lock#L1
[vm-execution]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/vm.rs#L186
[nonce-account-validation]: https://github.com/anza-xyz/solana-sdk/blob/ec7a0467e268774b724d55120ad952b518f27d64/nonce-account/src/lib.rs#L40
[nonce-current-version]: https://github.com/anza-xyz/solana-sdk/blob/5f79ee8637285d7ec2d39669142cafb7854530e1/nonce/src/versions.rs#L47
[nonce-state]: https://github.com/anza-xyz/solana-sdk/blob/5f79ee8637285d7ec2d39669142cafb7854530e1/nonce/src/state.rs#L66
[nonce-state-write]: https://github.com/anza-xyz/solana-sdk/blob/a541f77a1d482fdbcf420084d27fac42880d78bf/account/src/state_traits/wincode.rs#L70
[cache-store]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/loaded_programs.rs#L316
[cache-find]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/loaded_programs.rs#L326
[cache-drain]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/loaded_programs.rs#L322
[cache-batch-merge]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/loaded_programs.rs#L357
[cache-global-extract]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/loaded_programs.rs#L638
[cache-global-merge]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/loaded_programs.rs#L766
[cache-unloaded]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/program_cache_entry.rs#L243
[cache-closed]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/program_cache_entry.rs#L310
[cache-effective-slot]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/program_cache_entry.rs#L350
[loader-deployment]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/deploy.rs#L104
[loader-deployment-slot]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/program-runtime/src/deploy.rs#L129
[loader-v3-handler]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L148
[loader-v3-deploy]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L316
[loader-v3-upgrade]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L488
[loader-v3-close]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L767
[loader-v3-extend]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L973
[legacy-loader-management]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/programs/bpf_loader/src/lib.rs#L99
[transaction-cache-success]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/transaction_processor.rs#L594
[transaction-cache-drain]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/svm/src/transaction_processor.rs#L1230
[bank-cache-commit]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/runtime/src/bank.rs#L4440
[bank-clock-slot]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/runtime/src/bank.rs#L2491
[native-cache-scope]: https://github.com/anza-xyz/agave/blob/a203300045b405f86c9c84308b2eae76af69ac3b/builtins/src/lib.rs#L28
[loader-v3-instruction-codec]: https://github.com/anza-xyz/solana-sdk/blob/182207e7bc89c0f961696b37651c8bf55957779f/loader-v3-interface/src/instruction.rs#L26
[loader-v3-state-codec]: https://github.com/anza-xyz/solana-sdk/blob/182207e7bc89c0f961696b37651c8bf55957779f/loader-v3-interface/src/state.rs#L10
