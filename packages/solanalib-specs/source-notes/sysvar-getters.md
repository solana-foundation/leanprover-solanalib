# Versioned sysvar getters

The getter families preserve the status, destination value and state of the callback.
The callback is an explicit mathematical interpretation of the selected syscall
or host stub. It may return, unwind with a changed state, or terminate. The
family requires `GetterReady` at the actual read state: every returned status
classified as success by the supplied converter must have an initialized
destination. An error status needs no readable destination. The unchanged raw
relation has no continuation for a successful status without a destination;
admission rejects that case. A present but invalid destination is forwarded
without filtering it by a representation predicate. Mathematical forwarding
does not establish legal Rust access.

`forwardGetter_hasOutcome_iff` proves the exact local initialization condition.
`get_retains` preserves every actual finite callback exit through that same
forwarding relation. `get_hasOutcome_iff` proves that the admitted getter has a
finite exit exactly when its provider does, without asserting termination. The
universal provider condition matters for nondeterministic callbacks: one valid
reply cannot hide another reply with an absent destination.

The separate `GetterValid` law says that an initialized successful destination
has the configured value property. `get_success_valid` consumes this law to
prove validity of an actual successful getter result. Value validity is not
part of initialization admission, and a separately chosen value cannot replace
the destination of the callback. The closed sample initializes its destination and
has an execution for either success or ordinary error conversion.

Clock uses `Solanalib.Runtime.Clock`, with the unsigned and signed 64-bit field bounds of the source. Rent 3.0.0 preserves the rate, exact binary64 threshold bits and burn
percentage; its projection to `Solanalib.Runtime.RentSysvar` retains those values. These are
value interpretations. Typed Rust storage, padding, alignment, destination origin
and permissions remain interpretation obligations.

| Version and getter | Request and initialization | Status conversion |
| --- | --- | --- |
| Pinocchio 0.10.2 Clock | Generic Clock sysvar, offset 0, length 40; `MaybeUninit` | 0 succeeds; 1 is `InvalidArgument`; every other status is `UnsupportedSysvar` |
| Pinocchio 0.10.2 Rent | Generic Rent sysvar, offset 0, length 16; `MaybeUninit` | Same generic conversion |
| Pinocchio 0.11.1 Clock | Generic Clock sysvar, offset 0, length 40; `MaybeUninit` | Same generic conversion |
| Solana Sysvar 3.1.1 Clock | Typed Clock syscall or host stub; initialized from `Default` | 0 succeeds; every nonzero status is `UnsupportedSysvar` |
| Solana Sysvar 3.1.1 Rent | Typed Rent syscall or host stub; initialized from Rent 3.0.0 `Default` | Same typed conversion |

The source bindings for these Pinocchio getters select `target_os = "solana"`.
Their ordinary host branch zeros the destination and treats its pointer bits as a status;
that branch needs its own callback interpretation. The raw family passes the
supplied target tag to the callback without a target admission gate. It does
not establish that a supplied host callback implements the host branch of Pinocchio,
or assume a successful runtime read or an installed sysvar. Its closed sample
callback proves an inhabited mathematical execution.

The two Sysvar 3.1.1 typed families support both listed targets. Their callback
interpretations must implement the selected syscall or host stub; neither
family assumes the behavior of a default host stub.

Ordinary source anchors:

| Package | Immutable source | Anchors |
| --- | --- | --- |
| Pinocchio 0.10.2 | [sysvars/mod.rs](https://github.com/anza-xyz/pinocchio/blob/5697fdd59d201466a23d67d0bceb284c5e6d9e79/sdk/src/sysvars/mod.rs#L70) | Generic macro 70; callback 84; host branch 92; status conversion 99 |
| Pinocchio 0.10.2 | [clock.rs](https://github.com/anza-xyz/pinocchio/blob/5697fdd59d201466a23d67d0bceb284c5e6d9e79/sdk/src/sysvars/clock.rs#L43), [rent.rs](https://github.com/anza-xyz/pinocchio/blob/5697fdd59d201466a23d67d0bceb284c5e6d9e79/sdk/src/sysvars/rent.rs#L102) | Clock fields 43; Clock macro 86; Rent fields 102; Rent macro 319 |
| Pinocchio 0.11.1 | [sysvars/mod.rs](https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/sysvars/mod.rs#L70), [clock.rs](https://github.com/anza-xyz/pinocchio/blob/a2ba6529b58d201ce91be5d2bd937e56569ec17a/sdk/src/sysvars/clock.rs#L39) | Generic macro 70; Clock fields 39; Clock macro 82 |
| Solana Sysvar 3.1.1 | [lib.rs](https://github.com/anza-xyz/solana-sdk/blob/a5ecbeb813096b11c63cca476acf9b4d49e27475/sysvar/src/lib.rs#L163) | Typed macro 163; `Default` 166; selected callback 170/173; status conversion 175 |
| Solana Sysvar 3.1.1 | [clock.rs](https://github.com/anza-xyz/solana-sdk/blob/a5ecbeb813096b11c63cca476acf9b4d49e27475/sysvar/src/clock.rs#L132), [rent.rs](https://github.com/anza-xyz/solana-sdk/blob/a5ecbeb813096b11c63cca476acf9b4d49e27475/sysvar/src/rent.rs#L131) | Typed Clock instantiation 133; typed Rent instantiation 132 |

The shared tests check the generic status conversion, preserve callback state
on ordinary errors, unwind and terminal exits, and reject uninitialized success
and mixed good/bad successful providers. They distinguish an initialized but
invalid result, which remains admitted, and compose a stateful successful read
with a callback observing both its value and state. Converter controls show
that nonzero status classified as success still needs initialization, while
zero classified as an ordinary error does not. A separate valid-provider
control applies `get_success_valid`. Closed family references cover every
callback interpretation satisfying the minimal admission. Rust implementation,
target selection, ABI and runtime correspondence remain separate.

The typed getter tests additionally distinguish generic status 1 from typed
status 1 and check the request lengths and defaults.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:6d548314f765b20d -->
<a id="review-6d548314f765b20d"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Versioned public aggregate of the reviewed mathematical models.

Instantiate the shared mathematical operations for this exact SDK version; keep closed reference, precondition and execution witnesses in the public version namespace.

Versioned aggregate of the exact registered callable utility models; coverage is the listed API subset.

Generated typed capability catalog retains every complete registered family, exact Rust identity, source/build profile and closed reference witness.

The macro initializes the actual typed destination with Default, calls the Solana typed syscall or the selected replaceable host stub and returns that current value for status 0. It converts each nonzero status with ProgramError::from(u64), preserving exact builtin matching and unknown-status low-word truncation. Borsh tag 15 returns BorshIoError("Unknown"). The 1.15.2 table ends at tag 21; 1.18.26 at tag 24; program-error 2.2.2 at tag 26. No nonzero status is folded to UnsupportedSysvar in these profiles. The exact Borsh tag reaches an explicit literal-copy provider after the typed read. Its returned OwnedError retains a live String resource; StringReady for reached normal copies proves freshness at the post-read state and exact current contents "Unknown". ownedPost and the nonempty closed witness retain ordinary allocation effects. fromStatus remains a separate value facet; no error-buffer ownership is inferred from it.

Sysvar 3.1.1 constructs EpochSchedule::default(), passes a typed epoch-schedule destination to the target-selected syscall or host stub, returns its current value on SUCCESS = 0 and maps every nonzero status to UnsupportedSysvar. The reached EpochSchedule 3.0.0 and 3.2.0 fields and custom/default calculation agree, yielding (432000,432000,true,14,524256); serde/wincode/CloneZeroed derive differences do not alter this call. The impl is available without the optional bincode feature.
<!-- /registry -->

<!-- registry:review:dfa3fc92cc252bde -->
<a id="review-dfa3fc92cc252bde"></a>

Only 3.0.0 and 3.1.1 retain the complete typed-provider protocol: construct Clock::default(), pass its destination to the target-selected typed syscall or overridable host stub, return its resulting value for status 0, and fold every nonzero status to UnsupportedSysvar. Clock default fields and their widths remain unchanged throughout the reviewed 3.x dependency releases, including the 3.2.1 re-export of 4.0.0. solana-program-entrypoint SUCCESS remains 0 and ProgramError::UnsupportedSysvar is unchanged in the admitted dependency family. The earlier five real sysvar releases convert nonzero status with e.into(), so statuses such as 1 produce Custom(1). Release 3.1.0 is an actual hole: it requests the generic sysvar by ID into MaybeUninit rather than the default-initialized typed provider. 3.1.1 restores the typed macro. 4.0.0 goes back to the generic macro; 4.1.0 onward re-export GetSysvar and move its implementation into dependency crates. These later APIs exist, but differ in request, initialization and host/provider behavior. No successful empty reply is manufactured for uninitialized generic getters.
<!-- /registry -->

<!-- registry:review:6e17e39c3f9a7ac0 -->
<a id="review-6e17e39c3f9a7ac0"></a>

Only 3.0.0 and 3.1.1 retain the complete typed-provider protocol: construct Rent::default(), pass its destination to the target-selected typed syscall or overridable host stub, return its resulting value for status 0, and fold every nonzero status to UnsupportedSysvar. The reached Rent 3.0.0 and 3.1.0 defaults retain rate 3480, f64 threshold 2.0 and burn 50; logical initialized fields do not imply initialized padding bytes. solana-program-entrypoint SUCCESS remains 0 and ProgramError::UnsupportedSysvar is unchanged in the admitted dependency family. The earlier five real sysvar releases instead use e.into() for nonzero status. 3.1.0 uses a generic ID/offset/length request into MaybeUninit and is not admitted; 3.1.1 restores typed Default initialization. 4.0.0 uses the changed Rent 4 representation, explicitly zeroes seven trailing padding bytes, and requests the generic serialized data. 4.1.0 onward re-export GetSysvar and move the implementation to Rent/get-sysvar dependencies. The later public getter remains present; the old complete typed-provider model does not describe it.
<!-- /registry -->

<!-- registry:review:2319f09990511059 -->
<a id="review-2319f09990511059"></a>

The macro initializes the actual typed destination with Default, calls the Solana typed syscall or the selected replaceable host stub and returns that current value for status 0. It converts each nonzero status with ProgramError::from(u64), preserving exact builtin matching and unknown-status low-word truncation. Borsh tag 15 returns BorshIoError("Unknown"). The 1.15.2 table ends at tag 21; 1.18.26 at tag 24; program-error 2.2.2 at tag 26. No nonzero status is folded to UnsupportedSysvar in these profiles. The declared compatible range assumes preservation of default initialization before the call, successful value forwarding, the complete nonzero-status decoder with its owned String error, and the reached-state, unwind and terminal behavior of the call and error allocation.
<!-- /registry -->

<!-- registry:review:27503edfbc5ee6f4 -->
<a id="review-27503edfbc5ee6f4"></a>

The inspected 2.2.2/2.3.0 typed-getter files are identical. This incoming pre-2.3 range assumes the actual typed Default destination, status-zero forwarding and full ProgramError status decoder, including tag 15 BorshIoError("Unknown") and unknown low-word truncation. Provider effects and finite exits remain; existing 2.3.0 profiles and the bincode gate stay separate.
<!-- /registry -->

<!-- registry:review:af86c4ba96d8bec1 -->
<a id="review-af86c4ba96d8bec1"></a>

Preserve default-initialized EpochSchedule, the target-selected typed destination request, status-zero return of its current value and folding every nonzero status to UnsupportedSysvar. Keep the exact EpochSchedule, entrypoint and ProgramError dependency gates; no bincode gate is needed. The generic MaybeUninit/by-ID getter is a different protocol. Comparable 3.0.0 source is recorded as inspection evidence, not added to this selected profile. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->
