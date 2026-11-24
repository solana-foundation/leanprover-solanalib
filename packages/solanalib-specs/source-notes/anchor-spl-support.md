# Anchor SPL values and supporting CPI wrappers

The [source registry](../source-map/anchor-spl.json) records the following
Anchor SPL operations with 0.32.1 reference bindings. The token value,
associated-token and metadata operations have inspected 0.32.0–0.32.3 references and declare
`[0.32.0, 0.33.0)` under their complete operation and dependency contracts.
The `token_interface::TokenAccount::deref` profile has its own
range below. Each operation keeps its source and feature conditions.

The 1.1.2 operations have exact source and dependency references.
Their catalog profiles assume the recorded dereference/ATA behavior through
`[1.1.2, 1.2.1)`, before the new Solana provider cohorts; their concrete source bindings and recorded native inputs stay exact. Other crate methods
are not registered.

The 0.29.0 subset is `token_interface::{TokenAccount::deref,
TokenInterface::ids}`. Its separate `[0.29.0, 0.30.0)` profiles retain the
exact source, dependency and feature gates.

The 0.27.0 subset is `token::TokenAccount::deref` and
`stake::{StakeAccount::deref, withdraw, deactivate_stake}`. Its separate
`[0.27.0, 0.28.0)` profiles retain the operation-specific nominal
providers, dependencies and feature gates.

The 0.32.1 subset is:

| Module | Registered operations |
| --- | --- |
| `token` | `Token::id`, `TokenAccount::deref` |
| `token_interface` | `TokenAccount::deref` |
| `associated_token` | `create` |
| `memo` | `build_memo` |
| `metadata` | `create_metadata_accounts_v3` |

For `memo::build_memo`, inspected Anchor SPL 0.32.0 through 0.32.3
support `0.32.0 ≤ v < 0.33.0` with the recorded `memo` feature, Anchor
Lang and Memo dependency ranges. Preserve the actual context resources,
ordered Memo construction, opaque invocation and cleanup. Other support
wrappers keep their separate profiles; native and exact source references
remain at 0.32.1.

The [source registry](../source-map/anchor-spl.json) selects
`anchor-spl::token_interface::TokenAccount::deref` with inspected references
0.32.1, 0.32.2 and 0.32.3 and declared range `[0.32.1, 0.33.0)`.
The complete wrapper/module files and relevant manifest requirements agree.
The profile retains `token_2022` and requires the complete decoded
`spl-token-2022` Account provider: reference 8.0.1, compatible range
`[8.0.1, 9.0.0)` under its recorded field and layout assumptions.
The concrete source entry selection and both native fixtures retain their exact
0.32.1 builds.

The 1.0.2 subset is `token::{Token::id, TokenAccount::deref}`,
`token_2022::Token2022::id`, `token_interface::TokenAccount::deref` and
`associated_token::create_idempotent`.

The 1.1.2 subset is `token_interface::TokenAccount::deref` and
`associated_token::{create, create_idempotent}`.

## Values and references

The selected TokenAccount dereferences select `&self.0`. They do not deserialize data,
check an account owner or acquire another borrow. `FieldReference.Access`
retains the existing parent, permission and current complete value; an expired
parent cannot be replaced by a saved pointee. The value includes both keys,
amount, delegate, state, native reserve, delegated amount and close authority,
including every optional payload. Its compiled Rust representation remains
distinct from the packed 165-byte account wire format. `Token::id` and
`Token2022::id` copy their distinct canonical 32-byte program keys.

The selected 0.27.0 `StakeAccount::deref` similarly returns the current
`StakeState` field under its existing parent loan. This is the legacy
Uninitialized, Initialized, Stake or RewardsPool value, with complete
authorities, lockup, delegation and binary64 fields; it is not StakeStateV2
with stake flags. No wire decoding occurs at this dereference.

The selected 0.29.0 `TokenInterface::ids` returns the borrowed static slice
`[spl_token::ID, spl_token_2022::ID]` in that order. It performs no allocation
or account-key validation. The source interpretation retains the actual
static storage and slice representation.

## Local requests and dependency boundaries

CPI wrappers compose instruction construction, the complete opaque
`invoke_signed` signature and cleanup. The invocation relation retains the
full request, ordinary result, state effects, unwind and terminal outcomes.
It supplies no callee success or unchanged-state guarantee.

Resource providers distinguish vector identities from current elements,
Strings, error boxes, AccountInfo clone/drop, serialization and PDA operations.
`Admission.Ready` applies at actual prefixes before local reads. Literal
construction retains ordered evaluation and owns the cleanup of each moved occurrence exactly once, including when allocation precedes expression evaluation.
Continuation conditions concern reached primitive exits; they do not require
a completed wrapper result or provider termination.

A returned invocation error retains the full ProgramError inside the actual
Anchor error, inline at 0.27.0 and boxed in the later releases. The 0.27.0
and 0.32.1 payloads include an owned `BorshIoError(String)`;
the 1.0.2 and 1.1.2 Borsh variants are unit. Anchor Lang defines the 1.0.2
error; `anchor-lang-error` defines it at 1.1.2. Absent origin and compared values remain absent. The
error owner is distinct from the input Strings of the metadata function. The shared
error-construction boundary in [BINDINGS.md](../BINDINGS.md) applies.

## Constructor and cleanup distinctions

The 0.27.0 stake wrappers use the `solana-program` 1.15.2 constructors.
Deactivation encodes tag 5 and passes stake, clock and staker. Withdrawal
encodes tag 4 followed by the little-endian `u64` amount; it passes stake,
destination, clock, stake history and withdrawer, appending the optional
custodian when present. The constructor also marks that custodian as a signer.
These tags are little-endian `u32`. The source account fields move into the
temporary array or vector in that order. The withdrawal vector drops before
the instruction and context; deactivation retains its tail-expression array
scope. Allocation and partial-construction cleanup retain actual owners and
reached effects, including duplicate account identities.

Associated-token creation uses fixed ATA and System IDs and ordered PDA seeds
wallet, token-program key, mint. The supplied associated AccountInfo is
forwarded even if its key differs from the derived instruction meta. Metas,
flags and the create or idempotent byte follow the real constructor. Remaining accounts
remain context owners and are not appended to this request.

The 0.32.1 profiles resolve ATA 7/client 2 with Pubkey 2.2.1 or 2.4.0. These
PDA implementations initialize the destination to zero and bump to 255.
Untouched bytes after a successful partial syscall write therefore remain
zero. This initialization is not an assumption of cryptographic success.

The 1.0.2 and 1.1.2 profiles resolve ATA interface 2 through Pubkey 3.0.0
and the Address 1.1.0 reexport, to defining Address 2.6.0 and 2.6.1
respectively. Their `MaybeUninit` destinations must be initialized at the
actual successful reply before the local read. A
zeroed-output family is not a substitute. Retain that full source edge even
when the whole dependency list is ambiguous to a name-based matcher.

The selected 0.32.1 memo construction preserves arbitrary input bytes and the ordered signer
keys, including duplicates, from remaining accounts. Its temporary key vector
drops before invocation. The request uses those same ordered AccountInfos.

The selected 0.32.1 metadata wrapper uses mpl-token-metadata 5.1.1. It allocates
metadata capacity seven and pushes six metas, using the fixed System ID and
absent rent. Its
AccountInfo list instead clones seven source fields, then appends remaining
accounts and the context program. Discriminator 33 and arguments are
serialized into separate byte vectors; the argument bytes are moved/appended
and their temporary vector is dropped. The model preserves complete UTF-8
Strings, optional creators, collection, uses, fee, mutability and both
CollectionDetails variants. Owned DataV2 fields drop in source order.

The 0.27.0 and 0.32.1 CPI contexts own a program AccountInfo; 1.0.2 and
1.1.2 store a copied program key. Rc cleanup follows each actual owner
occurrence and observes current resources; aliases are not deduplicated.
Each finite provider error or unwind carries its actual state into the
remaining cleanup. A terminal exit runs no later cleanup and has no
post-state. Exact source layouts, reference loans, allocator/Rc behavior and
frames remain binding obligations. These mathematical/source arguments are
separate from physical representation correspondence, native conformance and
proofs of the selected Rust bodies.

The [mathematical reference scenarios](../SolanalibTest/Specs/Core/AnchorSplSupport.lean)
check current-parent reads and expired-parent rejection. A source binding must retain complete optional fields; the returned reference remains a loan from the same parent, not an independent owner. The library
[test root](../SolanalibTest/Specs/AnchorSpl.lean) and existing `AnchorSplSupport`
conformance family cover these selected operations. Its two pinned native
drivers, `anchor-spl-support-v0321-interface` and
`anchor-spl-support-v0321-pubkey240`, retain their different dependency
profiles. See the [conformance guide](../../../tools/library-conformance/README.md)
for selected replay and fresh recording. Source entry selection, the complete source ABI,
representation coverage, and implementation correctness remain distinct obligations.
