# Anchor SPL token CPI operations

The [source registry](../source-map/anchor-spl.json) records inspected Anchor
SPL 0.32.0–0.32.3 for `token_2022::transfer_checked`, using the 0.32.1
reference binding. It declares `>=0.32.0, <0.33.0` with `token_2022` enabled
and the recorded constructor, context, AccountInfo and legacy error
assumptions. Constructor references are `spl-token-2022` 8.0.0 and 8.0.1,
with declared `>=8.0.0, <9.0.0` compatibility.

The additional wrappers below also have inspected 0.32.0–0.32.3 references
and declare `[0.32.0, 0.33.0)` under their complete operation and dependency
contracts. Their 0.32.1 source bindings, immutable selectors and native builds
remain exact. The feature of each module must be enabled in the actual build.

The selected 1.1.2 wrappers retain separate exact source and dependency
references. Their catalog profiles assume the recorded constructor, context,
modern error and cleanup behavior through `[1.1.2, 1.2.1)`, before the new
Solana provider cohorts. The exact call-specific Binding and native inputs
remain separate.

The 0.29.0 subset is `token_2022::transfer_checked`, using the resolved
`spl-token-2022` 0.9.0 constructor and `solana-program` 1.18.26. Its separate
`[0.29.0, 0.30.0)` profile retains the constructor, context, feature and
dependency conditions recorded for that operation.

The 0.27.0 subset is `token::{burn, mint_to, transfer}`, using the
recorded `spl-token` 3.5.0 and `solana-program` 1.15.2 references. Its
separate `[0.27.0, 0.28.0)` profiles retain the constructor, context,
feature and dependency conditions for each operation.

The 0.32.1 subset is:

| Module | Registered functions |
| --- | --- |
| `token` | `transfer` |
| `token_2022` | `burn`, `close_account`, `get_account_data_size`, `initialize_account3`, `initialize_immutable_owner`, `initialize_mint2`, `mint_to`, `set_authority`, `transfer_checked` |
| `token_2022_extensions` | Group-member pointer, group pointer, metadata pointer, mint-close authority, non-transferable mint, permanent delegate and transfer-hook initializers |

The 0.32.1 reference bindings use resolved `spl-token` 8.0.0 or
`spl-token-2022` 8.0.1 constructor
implementations. Equal instruction tags do not justify replacing a constructor
or its error type. The context owns its program AccountInfo; invocation-array
operands move the selected account fields. Error conversion allocates the
Anchor box and retains the full old ProgramError, including any owned
`BorshIoError(String)`. An error does not restore the input state.

The 1.0.2 subset is `token_2022::{initialize_account3, transfer_checked}`.
The former uses unsigned `invoke` with account and mint; the latter uses
`invoke_signed` with from, mint, to and authority. Both use the selected
`spl-token-2022-interface` 2.1.0 constructors. The context stores a copied
program key and moves the invocation-array fields. Its ProgramError
Borsh variant is unit; conversion allocates the Anchor Lang error box.
These 1.0 profiles keep their own dependency gates and do not replace
the modern alternatives. Errors retain effects already performed.

The 1.1.2 subset is `token_2022::{burn_checked, mint_to_checked, set_authority,
transfer_checked}`. Its constructors are from `spl-token-2022-interface`
2.1.0. That context stores a copied program key, and invocation-array
operands move the selected account fields. Its Borsh error is unit, and
conversion allocates the actual error box defined by `anchor-lang-error`.
An error does not restore input state.

The 0.29.0 context owns its program AccountInfo. Invocation-array operands
move the selected fields in declaration order. Its old ProgramError retains
any owned `BorshIoError(String)`, and conversion allocates the actual Anchor
Lang error box. An error preserves effects already performed.

At 0.27.0, invocation-array operands clone the selected AccountInfos
and both Rc fields while the context retains its original owners. The
context owns its program AccountInfo; error conversion retains the inline
Anchor payload and any `BorshIoError(String)`. Cleanup preserves effects
already performed.

The canonical 0.32.1 legacy transfer declaration is
[`Solanalib.Specs.AnchorSpl.token.transfer_with_program_owner_contract`](../Solanalib/Specs/AnchorSpl/token_2022.lean).
Its owned context program and boxed legacy error distinguish it from the
other registered transfer family. The checked-transfer declaration remains
[`Solanalib.Specs.AnchorSpl.token_2022.transfer_checked_contract`](../Solanalib/Specs/AnchorSpl/token_2022.lean).
The 0.29.0 wrapper retains the separately indexed
[`Solanalib.Specs.AnchorSpl.token_2022.transfer_checked_legacy_interface_contract`](../Solanalib/Specs/AnchorSpl/token_2022.lean).
Every wrapper keeps its own exact source/build admission.

## Requests and construction

| Operation | Invocation account order |
| --- | --- |
| Transfer | from, to, authority |
| Checked transfer | from, mint, to, authority |
| Burn and checked burn | from, mint, authority |
| Mint-to and checked mint-to | to, mint, authority |
| Close account | account, destination, authority |
| Set authority | owned account, current authority |
| Initialize account3 | account, mint; authority is a constructor argument |
| Initialize mint2, immutable owner, get size | mint/account only |
| Extension initializers | token program, mint |

This order need not match the declaration order of the account aggregate.
Metadata order and signer/writable flags come from the real constructor.
Legacy `token` uses its fixed ID even if the context has another key. Ordinary
2022 constructors accept either token ID where their source permits it;
extension initialization requires the Token-2022 key from the program account.
Remaining context accounts are destroyed but not appended to these arrays.
Duplicate identities, repeated owners and nested signer seeds retain order and
empty groups. Unsigned initializers do not read the borrowed signer reference.

Each constructor retains its own metadata/data allocation order and actual
compiled enum-size reservation. Pointer initializers use outer tags 36, 39,
40 and 41, subtag zero and the ordered 64-byte POD payload. Program admission
precedes metadata allocation. A present zero authority is rejected before the
second optional key, with the allocated metadata owner dropped on either
failure. Zero mint-close authority or permanent delegate is accepted where
the source accepts it. The 0.32.1 constructor authority and extension enums
retain their seventeen and twenty-eight variants respectively; each profile
keeps its actual compiled enum rather than substituting a sample layout.

## Size replies and local cleanup

The selected 0.32.1 size builder allocates metadata, copies the extension slice into its owned
temporary vector, constructs tag 21 followed by little-endian extension tags,
then drops that temporary before invoking. After a successful invocation its
statement-scoped account array drops before `get_return_data`; instruction and
context program remain live at the getter. On invocation error, ProgramError
conversion precedes array cleanup.

Missing return data yields `InvalidInstructionData`. For present data the
program key is checked before length: a wrong key yields `IncorrectProgramId`
even if length is wrong. A matching reply must have exactly eight bytes,
decoded as little-endian `u64`. Both failures and successful Vec-to-array
conversion release the returned byte vector before final conversion/return.
Edition-2021 cleanup drops instruction metadata, bytes, remaining temporary
array owners and then context accounts, remaining vector and, at 0.27.0,
0.29.0 and 0.32.1, the program owner in their source scopes. The 0.27.0
array clones and retained context owners each require their own cleanup.
Unwind retains the reached state; a terminal exit has no after-state or subsequent cleanup.

## Assumed providers and continuation

Invocation and return-data access stop at their complete opaque signatures.
Their explicit contracts supply actual effects and exit kinds. The local
wrapper never traverses the invoked program or assumes its success.

`Ready` supplies only reached observations: the extension copy, constructed
vectors and signed seed view after actual successful preparation, and the
returned byte owner when a matching-program reply is read. Seeds are read
from that prepared state. No blanket AccountInfo/heap validity or provider
termination condition replaces these facts. `Continuation` retains each
actual return, ordinary error, unwind and terminal path through cleanup;
a successful path does not excuse a second unreadable reached request.

The [binding obligations](../BINDINGS.md) retain the actual primitive and
callback contracts, source ownership, layouts, panic strategy and shared
error-construction allocation boundary. Closed mathematical executions do not
establish SDK body correctness or physical source coverage. Tests that replace
whole invocation/getter signatures are projected-wrapper observations, not
full linked-SDK or validator execution; host/Solana cfg does not prove SBF
layout equivalence.

## Checked-transfer scenarios and conformance

Checked transfer accepts the reviewed legacy or Token-2022 ID before
allocation. It packs tag 12, eight little-endian amount bytes and the decimals
byte, retaining the actual enum-size reservation. Metadata is source
(writable), mint (readonly), destination (writable), authority (readonly signer).
The selected `CheckedTransfer` cases in the
[mathematical tests](../SolanalibTest/Specs/Core/AnchorSplTokenOperations.lean)
check this request, the success result, full error payload and provider
effects, ordered cleanup, unwind and terminal exit. A constructor-rejection
witness is admitted with no available signer-seed view: it returns
`IncorrectProgramId` before instruction allocation or invocation and releases
the intact context. A source binding must separately reject a fabricated reached read and admit a coherent changed view. Source entry selection, the exact source ABI, representation coverage, and implementation correctness remain
distinct obligations.

The existing `AnchorSplTokenOperations` family now selects all registered
wrappers from the authenticated 188-record `anchor_spl_token_0_32_1` corpus.
Selected controls corrupt error, alias, cleanup, provider-effect,
constructor-rejection and terminal observations; the selection regression
checks that each selected mutation reaches its registered checker. Omitted
records and controls are reported separately. From the repository root:

```sh
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers --family AnchorSplTokenOperations --evidence-dir /tmp/slc-anchor-token-operations
python3.12 -B tools/library-conformance/run.py --record --offline --twice --no-write-corpus --driver anchor-spl-token-0-32-1 --evidence-dir /tmp/slc-anchor-token-operations-native
```

The driver retains its exact source projection, locks, feature selection and
authenticated `dev`/unwind, x86-64, Solana-cfg configuration. Fresh native
recordings and replay of the committed corpus are separate checks; neither
executes the Token processor or proves the SDK wrapper body.
