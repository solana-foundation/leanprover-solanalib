# Token byte views and checked parsers

The common model distinguishes raw borrowed storage from the validated copied
values of SPL. It adds no Rust body correctness, target-layout, validator or token-callee
claim. It uses the canonical Solana model for runtime vocabulary.

The Pinocchio sources are the registry packages `pinocchio-token 0.6.0` (git
`cc937fec77a9888a9d7e60aba59bd2dc16291413`, `programs/token`) and
`pinocchio-token-2022 0.3.1` (git
`d713b2d0baf9bb406eea34cd020c963078b8c56a`, `programs/token-2022`).
The [source registry](../source-map.json) records immutable revisions, complete
file hashes and exact source declaration anchors. The source audit checks those
files without claiming that Rust code was compiled or verified.

## Shared data and references

`Solanalib.Specs.Core.Token` uses canonical byte strings, fixed 32-byte public keys,
little-endian integers and named program errors. Its two token program IDs decode
the source Base58 declarations exactly. Every successful `readNat` or `readKey`
checks the complete range; truncated input is neither padded nor silently read.

`MintRaw` and `AccountRaw` are exact 82-byte and 165-byte storage views. Their
projections preserve invalid option tags, initialization bytes and state bytes.
This is necessary because all underlying Pinocchio fields are bytes, byte
arrays or addresses. Its `Account::state` performs a separate conversion:
0, 1 and 2 return the three enum values; every other byte panics.

The guard-backed parser shares the identified `Borrow.State Account Slice` of AccountView. It uses the common acquire, transfer, current and
release operations. A successful `Ref::map` retains the same lease identity,
advances its ghost generation and narrows the byte view. A field reference
retains that guard and a field offset; it does not create another lease or copy
a stale address snapshot. Later reads use current account contents. Releasing
the parent makes its field references unusable.

These identities are logical handles, not machine addresses. The generation
models consumption of a Rust guard value; it is not an added source field.
Physical pointer validity, the source lifetimes and the `repr(C)` alignment-1
casts remain explicit implementation-binding obligations. The model does not
claim that arbitrary direct cell replacements are authorized.

## Parser admission and error order

| Source operation | Ordered checks | Success |
| --- | --- | --- |
| Legacy Account, `account.rs:57` | length = 165; legacy owner; shared borrow | mapped raw base view |
| Legacy Mint, `mint.rs:45` | length = 82; legacy owner; shared borrow | mapped raw base view |
| Token-2022 Account, `account.rs:61` | token-2022 owner; shared borrow; layout | mapped raw base view |
| Token-2022 Mint, `mint.rs:48` | token-2022 owner; shared borrow; layout | mapped raw base view |

Length/layout failure returns `InvalidAccountData`. A wrong account owner also
returns `InvalidAccountData`; a wrong mint owner returns
`InvalidAccountOwner`. Borrow conflict and shared saturation return
`AccountBorrowFailed`, with the AccountView limit of 254.

The token-2022 layout helper is `state/mod.rs:19`. Exact base length succeeds.
Otherwise the length must differ from 355, exceed 165, and contain the requested
type byte at offset 165 (Account = 2; Mint = 1). Nonzero mint padding and arbitrary
extension bytes are admitted here. There is no initialized-account, COption-tag,
TLV-kind or neutral-extension restriction. If that layout check fails after
acquisition, Rust drops the temporary guard; the model releases it and keeps
its tombstone. Earlier independent guards and all account contents remain.

The parser contract records this complete mathematical computation with no
separate global account-validity gate. A missing mathematical cell keeps the
existing `InvalidAccountData` fallback and unchanged state; it is not thereby a
valid Rust AccountView input. Cell presence, account representation, the selected
borrow policy and source-width bounds remain implementation-binding obligations.
The local current-view and checked-range theorems retain the concrete premises
they use.

The typed getters cover Account::mint/owner/amount/state and Mint::decimals.
Mint and owner return references into the original guard; amount is the
little-endian word at offset 64, and decimals is the byte at offset 44. State
conversion has an explicit panic-provider family whose Empty result type
forbids a fabricated normal result. The provider can unwind with its actual
state or terminate; the sample abort policy is only one closed witness.

Mint/owner contract results construct field descriptors with the supplied guard
identity and offsets. Those equalities require no readability gate and grant no
new lease or permission to read through a retired guard. `currentKey` still
checks the current guard and complete range. The amount and decimal contracts
retain `AccountReadable` and `MintReadable`: their proofs use those premises to
identify the actual current bytes and exact values. The state-getter family
also requires `AccountReadable`. Its continuation theorem supplies the actual
decoded normal value or forwards every actual finite panic-provider exit with
its effects; it does not assume that a panic provider terminates. Unreadable or
retired references are rejected by admission, and the unchanged `stateRun` has
no outcome for them. Readable invalid state bytes remain admitted and retain
their original panic behavior.

## SPL and Pod validation

The copied-value helpers follow `spl-token-2022-interface 3.1.1/src/state.rs`:
Mint checks the mint-authority COption, Boolean initialization byte and
freeze-authority COption, in that order. Account checks delegate COption,
state enum, native COption and close-authority COption. The four-byte tag of a COption must encode exactly 0 or 1; absent options do not constrain ignored payload
bytes. The Boolean accepts exactly 0 or 1. The final initialized check of Pack
rejects an otherwise valid uninitialized value.

`unpackPodMint` models the different admission needed by account sizing.
PodMint uses its raw initialization byte as nonzero/zero and does not validate
COption tags. Its exact-size check is retained. Extension parsing, type-specific
layout and sizing build on these helpers in the separate extension modules.
The raw Pod representation is not silently replaced with Pack Mint.

## Mathematical evidence and limits

The versioned contracts have closed reference and satisfiability witnesses.
The state-conversion family additionally has a closed finite-execution witness.
General lemmas prove complete checked read bounds, preservation of every account
through parser paths, correct guard transfer, failed-parser retirement, and
field-reference agreement with the current byte view of the parent.

The two State test modules check nonzero amounts, distinct field addresses,
borrow conflict and saturation, exact error ordering, dropped temporary guards,
preserved older guards, consumed generations, exact-base and extended admission,
multisig/type rejection, nonzero mint padding, malformed state panic, and the
different Pack/Pod admission rules. A model consumer derives the amount from
the versioned contract alone. These are mathematical model controls, not
compiled Rust clients, native executions or token-program proofs.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:0a10af57146136f1 -->
<a id="review-0a10af57146136f1"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

The versioned ID is the declared legacy key. InitializeAccount3 and Transfer instantiate the common owned builder with the actual legacy-only program check, exact tags/data/metadata order and source capacity arguments. Value and operational contracts have precondition True; representable Rust scalars and capacity arithmetic remain source interpretation obligations. Separate _value_contract declarations observe the constructor result without allocation effects. Closed references, satisfiability and operational execution witnesses name the exact contracts and samples.

Import-only versioned roots collect the separately reviewed leaf modules. The listed module hashes seal their exact imports; each leaf retains its own source-facing contract and interpretation obligations.
<!-- /registry -->

<!-- registry:review:74c71ad71e0b68cd -->
<a id="review-74c71ad71e0b68cd"></a>

Import-only roots expose the selected versioned modules. Generated typed catalogs collect their exact registered contracts, source identities, profiles and closed reference witnesses. The generator check derives every catalog from the source registry without changing any model body.

Exact Base58 literals were decoded to 32-byte constants and compared with direct native id/check_id calls. Each mathematical function is a state-preserving constant copy or full equality; no allocation, hashing or syscall is introduced.

These complete families select the source-specific program check, enum domain and ordered plan. All native callback/state/resource indices remain explicit, and each family has a closed real execution at the two-ledger sample. Three unchanged Token-2022 constructors use the pre-existing complete families via explicit applicability profiles, with their own released source layout index.
<!-- /registry -->

<!-- registry:review:81c8fb73aa93f345 -->
<a id="review-81c8fb73aa93f345"></a>

Every API-bearing spl-token-interface release first rejects nonlegacy program IDs, packs tag 3 with one byte push and one eight-byte little-endian amount extension, then reserves 3 + signer count metadata entries and pushes source/destination/authority/signers in order. Authority signs exactly for the empty signer list; duplicates and lists beyond the multisig limit are retained. There is no execution-balance/signature validation. The selected body and pack arm are identical; unrelated new enum variants in 3.0.0 do not change this arm and enumSize remains an explicit layout parameter. Full allocation/unwind/terminal cleanup sequencing is preserved. The 0.0.0 builder is absent.
<!-- /registry -->

<!-- registry:review:91f5b81744dcf3e0 -->
<a id="review-91f5b81744dcf3e0"></a>

Every API-bearing spl-token-interface release first rejects nonlegacy program IDs, packs tag 3 with one byte push and one eight-byte little-endian amount extension, then reserves 3 + signer count metadata entries and pushes source/destination/authority/signers in order. Authority signs exactly for the empty signer list; duplicates and lists beyond the multisig limit are retained. There is no execution-balance/signature validation. The selected body and pack arm are identical; unrelated new enum variants in 3.0.0 do not change this arm and enumSize remains an explicit layout parameter. Full allocation/unwind/terminal cleanup sequencing is preserved. The 0.0.0 builder is absent. This entry is only the existing value observation; compatible releases share admission and returned values, while allocation, owned-resource lifecycle and abnormal exits remain covered by the separately registered full family.
<!-- /registry -->

<!-- registry:review:e749f1b22a7ddaa6 -->
<a id="review-e749f1b22a7ddaa6"></a>

The inspected 8.0.0 operation and reached helpers agree. The declared 8.x range assumes tag 9 and source/destination/authority/signers in order, checking the legacy token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:b8d9f75af270a939 -->
<a id="review-b8d9f75af270a939"></a>

The inspected 8.0.0 operation and reached helpers agree. The declared 8.x range assumes tag 7, little-endian amount and mint/destination/authority/signers in order, checking the legacy token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:b5e0bae5488e0e7c -->
<a id="review-b5e0bae5488e0e7c"></a>

The inspected 8.0.0 operation and reached helpers agree. The declared 8.x range assumes tag 15, amount and decimals bytes, source/mint/authority/signers in order, checking the legacy token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order. Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:26ac1cc24492af4f -->
<a id="review-26ac1cc24492af4f"></a>

The inspected 8.0.0 operation and reached helpers agree. The declared 8.x range assumes tag 6, the exact authority enum byte and optional key, 3 + N reserved but 2 + N initialized metadata slots, checking the legacy token ID before allocation, preserving actual enum-size reservation, duplicates/signers, owned vectors and allocation/cleanup order, including four authority variants and distinct None/Some(zero). Every finite primitive failure and partial state remains; native references are unchanged.
<!-- /registry -->

<!-- registry:review:cb8636f2f700a696 -->
<a id="review-cb8636f2f700a696"></a>

The inspected 8.0.0 operation and reached helpers agree. The declared 8.x range assumes comparison of every key byte with the fixed legacy native-mint ID, without allocation or state change. Source layout and any reached provider assumptions remain separate.
<!-- /registry -->
