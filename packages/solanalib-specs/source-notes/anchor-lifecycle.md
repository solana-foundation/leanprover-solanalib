# Anchor account validation and lifecycle

The literal [source API rows](../source-map/anchor-lang.json) retain Anchor Lang
0.32.1 at revision `1ebbe58158d089a2a40b5e35ebead5a10db9090d`. The twenty
profiles also record inspected 0.32.0, 0.32.2 and 0.32.3 references and declare
compatibility in `[0.32.0, 0.33.0)` under their operation-specific preservation
assumptions. A complete-build match supplies the actual resolved version;
reference hashes, Rust names and source ABI evidence remain separate. Named and
erased lifetime spellings identify the same implementations.

The `Solanalib.Specs.AnchorLang.Lifecycle` module collects the public declarations; model
IDs follow the Rust receiver and operation. The existing AccountInfo-dependent profiles
declare `[2.1.0, 3.0.0)`, except close requires `[2.3.0, 3.0.0)` for resize. Their
ProgramError dependency declares `[2.1.0, 3.0.0)` and retains the legacy owned
String payload. Exact reference versions remain in the generated profile guide;
no other Anchor minor/major line is added by this declaration.

The additional `Account::reload`, InterfaceAccount operations and
`Sysvar::try_accounts` require AccountInfo `[2.3.0, 3.0.0)` and ProgramError
`[2.2.0, 3.0.0)`. `Interface::try_accounts` and
`UncheckedAccount::try_accounts` add no dependency-version requirements.

The selected 0.27.0 implementations retain revision
`d456168d82e2725eaefd2306b516ee201e990820`. Their separate
`[0.27.0, 0.28.0)` profiles keep the owned AccountInfo, inline-error
and cleanup distinctions below. Where required, their Solana provider
compatibility stops before 1.16.0.

The selected 0.29.0 implementations retain revision
`fc9fd6d24b9be84abb2f40e47ed3faf7b11864ae` and declare the separate range
`[0.29.0, 0.30.0)` under their recorded operation and provider contracts.
Their exact source, dependency and ABI references remain distinct.

The 1.0.2 additions retain revision
`1314a6b83b16e6a31947b372d57988fd0e81559c` from
`solana-foundation/anchor`. Their separate 1.0 profiles preserve the
recorded operation and provider contracts; the table below identifies
their source references. Existing modern ranges remain unchanged.

The 1.1.2 implementations retain revision
`24035e2b0035c87e321acc1c05f97793829a87f1`; the published package records
`otter-sec/anchor`. Their exact files, anchors, trait parameters and
dependency profiles remain in the registry. Named and erased lifetime
spellings identify the same implementations; they do not broaden source or
ABI selection. The 1.1.2 catalog profiles assume their recorded operations
through `[1.1.2, 1.2.1)`. The upper boundary precedes the new mutually exclusive
Solana provider cohorts; it is not a claim that every operation changes there.
Account/InterfaceAccount exit additionally gains an unowned-account path in
1.2.2. Existing exact source bindings and loader panic profiles are unchanged.

The 0.27.0 subset is:

| Receiver | Registered operations |
| --- | --- |
| `Account<T>` | `try_from`, `try_from_unchecked`, `try_accounts`, `reload`, `exit`, `close` |
| `Signer`, `SystemAccount`, `Program<T>`, `Sysvar<T>`, `AccountInfo` | `try_accounts` |
| `UncheckedAccount` | `try_from`, `try_accounts` |
| `Box<T>` | `try_accounts`, `exit` |
| `AccountsExit` | Provided `exit` |

The 0.29.0 subset is:

| Receiver | Registered operations |
| --- | --- |
| `Account<T>` | `try_from_unchecked`, `try_accounts`, `exit`, `close` |
| `InterfaceAccount<T>` | `try_accounts`, `exit` |
| `Program<T>` | `TryFrom::try_from`, `try_accounts` |
| `Signer` | `try_from`, `try_accounts` |
| `AccountInfo` | `try_accounts` |
| `Box<T>` | `try_accounts`, `exit`, `close` |
| `Option<T>` | `try_accounts`, `exit` |
| `AccountsExit` | Provided `exit` |

The 0.32.1 subset is:

| Receiver | Registered operations |
| --- | --- |
| `Account<T>` | `try_from_unchecked`, `try_accounts`, `reload`, `exit`, `close` |
| `InterfaceAccount<T>` | `try_accounts`, `reload`, `exit` |
| `Signer`, `Program<T>`, `Interface<T>`, `UncheckedAccount`, `Sysvar<T>`, `AccountInfo` | `try_accounts` |
| `Box<T>` | `try_accounts`, `exit`, `close` |
| `Option<T>` | `try_accounts`, `exit` |
| `AccountsExit` | Provided `exit` |

The 1.0.2 subset is:

| Receiver | Registered operations |
| --- | --- |
| `InterfaceAccount<T>` | `try_from_unchecked`, `try_accounts`, `exit` |
| `Signer`, `SystemAccount`, `Program<T>`, `Interface<T>`, `Sysvar<T>` | `try_accounts` |
| `UncheckedAccount` | `try_from`, `try_accounts` |
| `Box<T>`, `Option<T>` | `try_accounts`, `exit` |
| `AccountsExit` | Provided `exit` |

The 1.1.2 subset is:

| Receiver | Registered operations |
| --- | --- |
| `Account<T>` | `try_from_unchecked`, `try_accounts`, `exit`, `close` |
| `InterfaceAccount<T>` | `try_from_unchecked`, `try_accounts`, `reload`, `exit` |
| `Signer`, `Program<T>`, `Interface<T>` | `try_accounts` |
| `UncheckedAccount` | `try_from`, `try_accounts` |
| `Box<T>` | `try_accounts`, `exit` |
| `Option<T>` | `try_accounts` |
| `AccountsExit` | Provided `exit` |

At 0.27.0 the Account and simple validation wrappers own an AccountInfo.
Later selected Account, InterfaceAccount and simple wrappers store a borrowed
record; the selected AccountInfo trait implementations still clone the owner.
Anchor errors are inline at 0.27.0 and boxed in the later releases. The
0.27.0, 0.29.0 and 0.32.1 ProgramErrors retain the owned
`BorshIoError(String)` through the generic carrier and `programStrings`
projection, restricted to variants in the actual dependency release. The
1.0.2 and 1.1.2 ProgramErrors have a unit Borsh variant.
The 1.0.2 Anchor error is defined in Anchor Lang; 1.1.2 reexports it from the
defining `anchor-lang-error` crate. The
[shared error-construction boundary](../BINDINGS.md#callbacks-and-outcomes) applies.

## Account consumption and validation

An empty leaf account slice constructs `AccountNotEnoughKeys` without advancing
it. Otherwise the leaf consumes exactly one record before validation. Errors,
unwinds and callback effects retain the consumed tail; bumps, reallocations
and instruction data remain unchanged. Collection wrappers instead retain
the actual changes of their inner `Accounts` implementation.

`AccountReference` preserves the original record identity as well as metadata
and shared Rc cells. Different records may share those cells. Returned
borrowed wrappers retain the actual record; equal metadata does not identify
it. The selected 0.27.0, 0.29.0 and 0.32.1
`AccountInfo::try_accounts` clone their AccountInfo owner. The 0.27.0 simple
wrappers also clone the record after successful validation; Sysvar clones only
after its decoder succeeds. Later simple wrappers retain source references.
The direct 0.27.0 `UncheckedAccount::try_from` instead moves its supplied owner
without cloning. At 1.0.2 and 1.1.2 it retains the input reference. The selected
0.29.0 `Signer::try_from` and
`TryFrom<&AccountInfo> for Program<T>` validate the supplied reference directly;
they do not consume an Accounts slice. Their `try_accounts` callers first
consume the record as above.

Signer checks its flag. The selected 0.27.0 and 1.0.2 SystemAccounts check
the current owner against the System ID. Program calls the selected `Id::id`,
compares the key,
then checks executable. A mismatch constructs the Anchor error before a second
`Id::id` call for the diagnostic; if that call unwinds, the owned error is
destroyed. The 1.1.2 entry binds generic `Program<T: Id>`, not the distinct
`Program<()>` specialization that skips the ID check. The 1.0 profile
starts at 1.0.2: generic 1.0.0 and 1.0.1 make an extra `Id::id` call and skip the
key check when it is zero. This restriction leaves existing modern alternatives
intact. Interface calls the selected `CheckId`, then checks executable. The selected 0.27.0 and 0.32.1
Sysvars call `Sysvar::from_account_info`; 1.0.2 uses
`SysvarSerialize::from_account_info`. Each receives the original record. An error first
constructs `AccountSysvarMismatch` and then drops the discarded ProgramError,
including its String when present. A terminal factory invents no later drop.

## Decoding and reload

Account construction checks system ownership with zero lamports, then current
owner, then borrows data and calls the selected decoder. Checked and unchecked
constructors use `try_deserialize` and `try_deserialize_unchecked` respectively.
Their discriminator, cursor, error and state effects remain part of the actual
callback. The 0.27.0 constructors clone AccountInfo while the shared data guard
is held, before calling the decoder. A decoder error or unwind destroys that
clone before releasing the guard. Their direct `try_from` and
`try_from_unchecked` calls do not consume an Accounts slice. InterfaceAccount
uses `CheckOwner` and saves the owner after decoding.
A wrong Account owner allocates its diagnostic before reading the diagnostic
owner and making the second `Owner::owner` call.

At 0.27.0 and 0.32.1 reload performs no owner recheck; the selected 0.32.1
InterfaceAccount delegates to Account reload. The shared data guard remains
held through old-payload destruction and assignment. Plain assignment installs the decoded replacement
even if the old destructor unwinds, retaining the effects of that destructor.
A terminal destructor has no successor state. Decoder error leaves the old
payload in place and releases the guard.

The selected 1.1.2 InterfaceAccount reload rechecks `CheckOwner` and ends the
shared data-borrow block before `set_inner` destroys the old payload. A
destructor attempting a mutable data borrow therefore observes a different
borrow state from the 0.32.1 path. Assignment still installs the already
decoded replacement if the old destructor unwinds.

`InitReady`, `OwnerReady`, `DecoderReady` and `DecodeReplaceReady` apply at
actually reached reads and cleanup prefixes. They supply current typed data,
live diagnostic ownership and the retained guards used by continuation
lemmas. These conditions neither require a callback to terminate nor discard
error paths. Rc admission belongs at each reached primitive, even before a
later primitive that terminates.

## Exit and close

Account exit obtains `T::owner`; InterfaceAccount uses its saved owner. It
serializes only when that owner equals the program ID and the account is not
closed. The closed test compares current owner to the System ID before using
the actual shared data-length borrow. Serialization receives the real mutable
bytes and a BpfWriter at position zero. Partial writes remain after error or
unwind. No writable-flag test or rollback is added. `SerializeReady` retains
the identified exclusive guard and data length while allowing these writes.
The 0.27.0 and 0.29.0 helpers clone an AccountInfo after the owner/closed
checks and before borrowing data. Each mutable guard drops before its local
clone. The later helpers use the retained reference without this local Rc owner.

The 0.27.0, 0.29.0 and 0.32.1 close helpers read destination lamports before
source lamports, perform checked addition followed by `unwrap`, write the
destination, then
zero the source, assign System ownership and shrink data to zero. Overflow
and both write-borrow failures panic under the selected strategy.

The 1.0 loader-close profile keeps the destination-first
arithmetic and panic behavior of the 0.32.1 helper, but borrows the source without cloning it and
still drops the moved destination. Its range ends before 1.1. Loader clone is
separate: it copies the same AccountInfo reference and PhantomData without a
payload read, validation or Rc clone.

The 1.1.2 helper reads source lamports first and calls `add_lamports` on the
destination. Overflow and destination write-borrow failure return ordinary
ProgramErrors. The final source-zero write can still panic. Each version
retains its actual evaluation order and target-selected panic outcomes.

Aliases are permitted: closing to the same lamports cell finishes at zero.
A late resize error keeps earlier balance and owner changes. Shrinking retains
backing tail and original length; tail zeroing is unreachable. The 0.27.0,
0.29.0 and 0.32.1 wrappers clone the source for the common helper, which consumes
and drops destination before source. The 1.1.2 helper borrows both; the outer wrapper
still drops the moved destination. Reached-prefix admission imposes no resize
conditions on earlier errors.

## Generic wrappers and interpretation

`Box<T>::try_accounts` invokes the actual inner constructor and boxes only a
successful payload. `Option<T>::try_accounts` consumes a program-ID sentinel
once; otherwise it passes the original slice to the inner constructor. Its
empty-slice branch follows the `allow-missing-optionals`
feature of the defining crate. Unrelated derive/init features add no mathematical precondition.

Box and Option delegation reads the current inner payload. `None` has no inner
exit call. The `AccountsExit::exit` facade selects the provided `Ok(())`
implementation, not an override. Traits, allocations, errors, Rc and destructor
operations remain scoped assumed interfaces. Source argument/result layouts,
loans, ownership and target behavior require their separate
[binding interpretation](../BINDINGS.md); mathematical consistency and one
finite sample do not prove arbitrary callback termination or any Rust body.

The existing `AnchorLifecycle` conformance family exercises these selected
operations with the pinned `anchor-lifecycle-0_32_1` driver. Its Option
constructor cases cover both the program-ID sentinel and a different key whose
inner constructor returns an error or unwinds with effects. Replay controls
check consumed tails, partial writes, released guards, and the balance/owner
changes retained after close fails. The mathematical collection tests also
retain inner and allocator terminal outcomes without a returned state.
Use the existing runner with `--record --driver anchor-lifecycle-0_32_1 --offline`
and then `--model-only --registered-checkers --family AnchorLifecycle`, supplying
an evidence directory to each invocation. The selection receipt identifies any
native observations outside the twenty registered methods.
