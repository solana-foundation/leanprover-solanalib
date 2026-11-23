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
