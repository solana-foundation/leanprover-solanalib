# Interpreting the library models

This package proves properties of mathematical models for the functions in the
[source registry](source-map.json). [Source notes](source-notes) justify their
design against pinned library sources. A source anchor or a successful model
execution does not prove that a Rust body implements the contract.

Generated library capability structures collect these exact contracts as
ordinary propositional hypotheses. A client requests only the members and
generic indices it uses. Subset composition fixes the operation assignment;
it cannot replace one member by a different interpretation. Catalog references
prove mathematical consistency, not the source-call hypotheses.

An execution binding uses one static program and shared ownership
representation for its selected calls. Native model state types remain
distinct; their current-state projections, source identities, argument and
outcome representations must agree through that binding. Combining catalogs
alone establishes neither this agreement nor disjointness of resources.

Each catalog member lists its registered Rust identities: crate and version, the item through which a function is called and its resolved implementation. A concrete binding must establish the following obligations for the selected compilation:

- **Source and build identity.** Match the actual package, immutable source, target, features, dependency instance, trait or inherent implementation, concrete type arguments, monomorphization and ABI. The declared version of the source alone does not establish the version of the compiled function. Two different crate instances can have the same Rust item path. Preserve compiler and build metadata and justify its agreement with the program being interpreted.
- **Body or interface selection.** A retained body must be the selected implementation. An opaque or foreign interface must match the actual resolved function, signature, frame and symbol where applicable. Equal Rust item and implementation paths do not replace resolution evidence. If a boundary model supplies behavior for an external declaration, that behavior remains an explicit assumption. CPI invocation stays opaque at its actual signature.
- **One shared interpretation.** Use one static program, current-state representation, argument/outcome codecs and ownership interpretation across the selected calls. Relate all finite returns and unwinds from admitted, resource-satisfiable inputs to exact represented after-states and well-typed results. Establish jointly satisfiable ownership and exit resources. This representation coverage is separate from an implementation or heap-transition proof.
- **Exact generic indices.** Relate the index of each family to the source type arguments, callbacks and selected implementation. The function identities of the registry do not check that connection automatically. Members without a registered Rust identity supply mathematical assumptions only, not a source-call binding.
- **Faithful codecs and resources.** Prove that argument and outcome encodings, current-state projections, ownership predicates and callback frames describe the actual implementation. A satisfiable codec that represents a modeled result by the integer 42 while the callee returns 1 is still wrong. ABI agreement, representation coverage and model witnesses do not discharge this obligation.

Use identities from the generated catalog, a reviewed `forBuild` view or a catalog sum of those. Changing a catalog changes the identities being checked. Rust item and implementation paths in the registry exclude build-specific disambiguating suffixes. A binding must relate these paths to the exact dependency instances in its build; a matching path alone does not establish that identity. A consuming verification tool must discharge its own execution-binding obligations.

**Rust implementation and memory correspondence remain unproved by these models.** A usable input witness or a synthetic interpretation establishes mathematical consistency only. An implementation hypothesis includes the concrete representation and dependency choices and may be false when those choices are wrong.

## Selecting a reviewed build

The Pubkey Borsh and packed-length references use Borsh 0.10.4. Their general
profiles declare a compatible 0.10 range. A concrete source binding must retain
the exact compilation unit for each selected reader or writer. A dependency graph containing
several Borsh versions remains ambiguous to whole-build lookup. Preserve the
complete graph and use the actual trait implementation, concrete arguments,
reached Borsh callee and callback metadata to justify an individual source
selection. Finding a compatible dependency among several candidates is
insufficient.

The additional account models preserve shared Rc/RefCell identities, current
owner storage, source borrow order and retained realloc backing. Account views
preserve provenance and loan repayment; clone retains its payload and account
primitive contracts. Anchor context and diagnostic models retain actual owned
arguments, the selected error layout, callback effects and source cleanup order.
The optional-account index follows the allow-missing-optionals cfg of the defining crate; this lifecycle group adds no blanket debug-feature restriction.
Each profile fixes the relevant source and build choices. Physical layout
correspondence and the behavior of invoked library operations remain separate
source-interface obligations.

Each model has source/version/configuration profiles in
`applicability.json`. The installed tool requires only the standard
library of Python:

```sh
python3.12 packages/solanalib-specs/tools/lookup_applicability.py \
  --build model-build.json \
  --model 'solana-hash::Hash::to_bytes'
```

Run this from the solanalib repository root, or adjust the paths to the installed
package. Omit `--model` to list all matches; repeat it to select several model
IDs. The input describes one actual compiled package, for example:

```json
{
  "package": "solana-hash",
  "version": "4.4.0",
  "source": {
    "kind": "registry",
    "url": "https://github.com/rust-lang/crates.io-index",
    "revision": ""
  }
}
```

The complete input vocabulary is:

| Field | Meaning |
| --- | --- |
| `package`, `version` | Cargo package name and exact resolved version. |
| `source` | Registry index URL, or `kind: "git"`, repository URL and exact 40-character `revision`. A fork is not the registry release with the same version. |
| `target` | List of `{ "field": "os", "value": "solana" }` facts; other reviewed fields include architecture and pointer width. Omitted facts are unknown. |
| `features` | Cargo features enabled for the actual compilation unit of this package. `null` or omission means unknown; `[]` means known empty. |
| `target_features` | Enabled compiler target features, with the same unknown/empty distinction. |
| `dependencies` | Selected packages in the dependency closure of the function, each with `package`, `version` and `source`. Supply the actual instance, not every same-named alternative in the lockfile. |

Only facts constrained by a profile are required. A dependency constraint
records a behavior difference inside the modeled API; it does not ask a Pyth
caller, for example, to prove an additional Borsh contract. For a reexport,
the returned Rust identity names the actual defining dependency and version.

Every selected model must report `eligible`. `unresolved` names missing facts;
`unsupported` means no declared alternative matches. Exit codes are 0 when
at least one model is eligible, 1 when unsupported, 3 when unresolved and 2
for malformed input. Inspect each requested model, not just the aggregate
status. The result retains the scope of the model, profile conditions and shared
boundary. An eligible mathematical observation without a registered source
call still has no callable identity.

Use the same facts in `Solanalib.Contracts.Model.Versioning.Build` and select
`catalog.forBuild build` in Lean. Its fields follow the JSON schema, with
`targetFeatures` for `target_features`, and `some []`/`none` for known empty
or unknown features. This view retains the exact family and all its indices;
`Catalog.forBuild_spec_iff` preserves the mathematical specification. It
changes only the registered source identities. No separate versioned module
or duplicated proof is required for each reviewed release.

Match these facts to the compilation being interpreted. Captured dependency
resolution or reproducible Cargo metadata must agree with its lockfile, target
and feature selection. For constrained cfg/features, use the settings of the actual compiled
crate: metadata can merge features from separate compilation units,
and requested root features do not establish dependency features. Eligibility
uses the declared compatibility evidence and leaves the existing ownership, codec, provider
and Rust implementation obligations in place.

### Reference versions and compatible ranges

`releases` lists source-reviewed references. Optional `compatible_ranges`
extends selection under the explicit assumption that the relevant operations
preserve the reference contract at the used types. Exact test lockfiles remain
reproducible examples, not mandatory dependency resolutions for every caller.
SemVer is evidence for this assumption; it does not guarantee every detail the
model may specify, such as diagnostic text. Those details remain part of the
assumption and the model, and known differences require separate profiles.

For example, the Borsh dependency of the Pyth decoder is recorded as:

```json
{
  "package": "borsh",
  "source": {
    "kind": "registry",
    "url": "https://github.com/rust-lang/crates.io-index",
    "revision": ""
  },
  "releases": ["1.6.1"],
  "compatible_ranges": [{ "lower": "1.5.3", "upper": "2.0.0" }],
  "reason": "The selected Borsh 1 slice decoder is assumed to preserve values, success remainders and exact InvalidData diagnostics of the reference; no error remainder is required."
}
```

Every registered model follows this policy. Direct registry profiles declare
compatible ranges; shared helpers inherit applicability from their named
consumers. Exact git origins remain exact even when their registry dependencies
have compatible ranges. The following examples share their existing contracts:

| Function or behavior | Declared compatible releases | Relevant conditions retained |
| --- | --- | --- |
| Pyth `PriceUpdateV2::deserialize_reader` | Receiver `>=2.0.0, <3.0.0` | Anchor/derive `>=1.0.2, <2.0.0`, Borsh/derive `>=1.5.3, <2.0.0`, Pythnet `>=3.0.0, <4.0.0`. |
| Pyth `VerificationLevel::deserialize_reader` | Receiver `>=2.0.0, <3.0.0` | The same Anchor/derive and Borsh/derive ranges; no Pythnet dependency is required. |
| Pythnet `PriceFeedMessage::deserialize_reader` | `>=3.0.0, <4.0.0` | Direct Borsh and `solana-program`/Anchor paths remain separate profiles. |
| Borsh `u64::deserialize_reader`, `InvalidData` truncation | `>=1.0.0, <2.0.0` | Reader `R = &[u8]`; separate `std` and no-`std` profiles. |
| Borsh `u64::deserialize_reader`, `InvalidInput` truncation | `>=0.10.0, <0.11.0` | The same reader scope; older reviewed releases and `0.11.0` remain exact references. |

Bounds are inclusive below and exclusive above. The pre-1.0 rule of Cargo matters:
`0.10.x` does not imply `0.11.x` compatibility. Prereleases need explicit
reviewed entries, and git forks keep their exact source/revision profiles.
The `0.0.x` references and the yanked Borsh `0.11.0` reference stay exact; no
broader compatibility line is declared for them. Known changes split ranges
even within a major version: the sysvar `3.1.0` protocol change remains a hole,
Anchor loading stops before `1.2.0`, and the hook resolver range stops before
`0.11.4`. Reexports use the version and identity of the selected defining dependency.
The lookup requires actual compilation facts; it does not resolve Cargo or
certify that an arbitrary combination of versions builds.

## Members without source-call registration

The six `Solanalib.Specs.SolanaAccountView.AccountView.Observation` members
(`data_len`, `is_signer`, `lamports`, `set_lamports`, `try_borrow`,
`try_borrow_mut`) register the same Rust functions as their `AccountView.Pool`
counterparts. Acquisition returns a byte projection; subsequent guard lifecycle reasoning requires the pool model.

The following 41 catalog keys have no registered Rust identity and therefore
cannot supply a registered source-call binding. They remain available through
the mathematical `Capabilities.Spec` interface. This includes six common
supporting members and 35 members in library catalogs; catalog membership alone
does not make a member usable as a source-call contract.

| Catalog | Keys without source-call registration |
| --- | --- |
| `Solanalib.Specs.Core.SupportingCapabilities` | `Token_amountContract`, `Token_decimalsContract`, `Token_mintContract`, `Token_ownerContract`, `Token_stateFamily`, `Owned_Array_construction` |
| `Solanalib.Specs.AnchorLang.Capabilities` | `ToAccountInfo_to_account_info_observation`, `accounts_account_Account_try_from_observation`, `accounts_account_loader_AccountLoader_load_mut_observation`, `accounts_account_loader_AccountLoader_load_observation`, `accounts_account_loader_AccountLoader_try_from_observation`, `accounts_interface_account_InterfaceAccount_try_from_observation`, `context_CpiContext_new_with_signer_observation`, `error_Error_from_anchor_error_observation`, `error_Error_with_pubkeys_observation`, `error_Error_with_values_observation` |
| `Solanalib.Specs.AnchorSpl.Capabilities` | `token_accessor_amount_observation`, `token_transfer_observation` |
| `Solanalib.Specs.Pinocchio.Capabilities` | `sysvars_instructions_Instructions_load_current_index`, `sysvars_instructions_Instructions_load_instruction_at`, `sysvars_instructions_IntrospectedInstruction_get_instruction_data`, `sysvars_instructions_IntrospectedInstruction_get_program_id` |
| `Solanalib.Specs.SolanaAccountInfo.Capabilities` | `AccountInfo_clone_observation` |
| `Solanalib.Specs.SolanaAddress.Capabilities` | `Address_find_program_address`, `Address_is_on_curve`, `Address_try_find_program_address_solana` |
| `Solanalib.Specs.SolanaInstruction.Capabilities` | `Instruction_new_with_bincode`, `Instruction_new_with_wincode` |
| `Solanalib.Specs.SolanaSystemInterface.Capabilities` | `instruction_create_account`, `instruction_transfer` |
| `Solanalib.Specs.SplToken2022.Capabilities` | `onchain_invoke_transfer_checked_value` |
| `Solanalib.Specs.SplToken2022Interface.Capabilities` | `extension_transfer_fee_TransferFeeConfig_get_epoch_fee`, `instruction_close_account_value`, `instruction_initialize_account3_value`, `instruction_transfer_checked_value`, `instruction_withdraw_excess_lamports_value`, `extension_BaseStateWithExtensions_get_extension`, `extension_BaseStateWithExtensions_get_extension_types`, `extension_StateWithExtensions_unpack` |
| `Solanalib.Specs.SplTokenInterface.Capabilities` | `instruction_initialize_account3_value`, `instruction_transfer_value` |

The `Address_try_find_program_address_solana` member and the two
`solana_instruction` members have API records without `rust_names`;
the other listed members have no source-call API association. Where the
registry supplies a primary operational, owned or generic model, use that
member for its stated behavior. Adding a source registration must retain the scope and interpretation obligations of the
selected model; inventing an identity
or replacing the generated catalog does not supply that correspondence.

## State, references and resources

A Rust binding must relate modeled identities, headers, current contents and
views to the actual representation of the library. Preserve distinct cells where
the source distinguishes them and aliases where values share storage. A
reference read uses the state at that source read; an entry snapshot cannot
replace a later read across a callback.

Some shared representations use unbounded mathematical integers. Contracts
retain the bounds needed by their guarantees and established interfaces;
source representation obligations that those results do not consume stay
separate. The AccountView observation contracts specify their admitted inputs and prove validity preservation for subsequent calls. Sysvar getters
require initialized output; their separate `GetterValid` law establishes
properties such as the integer bounds of the returned clock.

A Rust binding must relate source values to their actual integer widths.
Every contract precondition must support a substantive mathematical result.
State preservation and cleanup claims need their own proved invariants.

The borrow protocol tracks guard identity, acquisition, release, generation
changes and mapped views. It does not itself prove pointer validity, lifetimes,
access permissions or correspondence to a physical borrow counter. The lease identity and returned target of a mapped guard are distinct: a generic callback can
select another permitted target. Its target permissions and callback frame
must be supplied explicitly.

A current-state reference model does not authorize mutation during a Rust
shared borrow. The source binding must justify both the lifetime of the reference
and each permitted state change. Value-only observations omit this identity
and access information; use their registered primary model when it is needed.

Owned dependency providers describe resource tokens, current contents, finite
outcomes and cleanup. Their local laws express allocation, ownership transfer
and destruction without assuming an allocator implementation proof. Progress,
freshness across lifetimes, exclusivity and framing are guaranteed only where
the model explicitly requires or proves them. Mutations before failure remain
visible to subsequent cleanup; a terminal exit skips later code.

## Callbacks and outcomes

**Error-construction boundary.** For every library modeled in this package,
custom-allocator failure while constructing an error or its diagnostic payload
is outside scope. Interpret those allocations as successful. Record this shared
boundary with version applicability; no per-function model of such failures is
required. Native probes that inject null allocator returns during error
construction are outside this boundary and do not exclude a library version.
The boundary concerns allocation failure during error construction; other
errors, panics and callback outcomes follow their stated contracts.

`Outcome.returned` includes ordinary errors. Unwinding carries the actual
state reached by the operation; a terminal outcome carries no post-state.
Divergence has no finite outcome. A return-only model needs a source argument
that its admitted domain excludes other exits.

Generic models retain the dependencies used at their source call sites, such
as `AsRef`, `Deref`, codecs, error construction, allocation and invocation.
Bindings must establish the supplied dependency contracts, legal inputs and
frame conditions. A callback cannot be replaced with a successful constant or
have its mutations, errors, unwind or terminal behavior silently discarded.
Panic strategy and other profile choices remain explicit where relevant.
For Anchor `with_values`, `AnchorErrorOwned.protectReturnPlace` admits both
return-place retention and cleanup when the destructor of a later local unwinds;
a binding of that relation must allow either outcome. Its retention case matches
the pinned rustc behavior recorded under rust-lang/rust#47949.
The Address Borsh reader family selects its exceptional return-place behavior
through `ReadIndex.unwindReturnPlace`. Its source binding must implement the
selected lowering: the pinned compiler retains the constructed replacement when destruction of the EOF error unwinds.

`Holds` states partial correctness for an explicit reference relation.
`Satisfiable` supplies an admissible input; `HasExecution` supplies a permitted
finite reference execution. For indexed families, correctness covers every
index, while the latter witnesses name one explicit sample. They do not prove
progress for every type or callback. The registry records and the audit checks
these exact identities.

Reference correctness alone does not show that a wrapper can continue from
every finite provider exit. Initialization, readable-memory and guard conditions
must support the corresponding defined-read or continuation result; otherwise
a relation can silently omit an actual callback outcome. Such results preserve
each reached provider exit without assuming provider termination. Conditions
used only to interpret physical storage remain separate binding obligations.

## Byte codecs and views

The Borsh models describe decoding from a byte slice, `R = &[u8]`, directly
over bytes. The behavior of the slice reader of std (`read_exact`, and `read`
returning the smaller of the buffer and the remaining length) is assumed rather
than modeled as a function, and decoding involves no `Write` model. On
success they fix the value and the remaining slice. After an error they fix
the error but leave the remaining slice open, because the slice reader in std
empties it while the `nostd_io` of borsh keeps it; the executable references
follow std. A binding must identify the borsh `std` feature of the program where
the remaining slice is observed, and relate the `io::Error` of Rust to the modeled
pair of error kind and message. Error kinds are fixed per crate version.
Serializers take the writer as a callback in the family index and model the
exact sequence of `write_all` chunks; the callback supplies the errors and effects of the writer. Without the `std` feature of borsh, that `write_all` can be the
provided `nostd_io::Write::write_all`, modeled over the `write` of the writer, the
panic of its slice index and the allocation of the `String` message of its `WriteZero` error. A binding must show that the program calls this provided
method rather than an override supplied by a writer, bind the panic callback to the panic strategy of the
program, and bind the allocation callback to the allocator of the program under that strategy. Before retrying an `Interrupted` error, borsh
drops that error; a custom error frees its `String` message. The `write_all`
model resumes from the state left by `write` without modeling this drop or
free. A binding with observable destructor or deallocation effects must account
for them separately. `Vec<T>` decoding reports its allocations to an
explicit provider; freeing a partial vector and destructors on error or unwind
paths are not modeled.

`hint::cautious` casts the actual element size to `u32` before division. The
helper and generic vector families include a division-panic callback, whose
empty return type permits only unwind or terminal exits. Bind this callback
to the panic strategy and effects of the program. For a vector it also receives
the slice after the length read; a positive size divisible by `2^32` reaches
it before allocation or element decoding when the length is nonzero. The
family imposes no upper size bound. Any interpretation restricted to returning vectors must separately establish that this panic is unreachable; that restriction is absent from the source contract.

The bytemuck models take the layout, the in-memory encoding and the decoding
of the selected type from the family index, and carry slice and reference
addresses explicitly. A binding must show that these agree with the compiled
type and target, and must establish the validity, provenance, lifetime and
aliasing of every returned reference.

The [library conformance suite](../../tools/library-conformance)
compares these executable references with recorded runs of the pinned Rust
crates, built natively for the host. It checks only observable results at
chosen instantiations. It is evidence for the models, not a proof of the
Rust implementation or of its compiled target behavior.

## Runtime and target interpretation

Signer and writable observations report metadata. Local writes do not perform
the authorization, conservation or synchronization of the runtime checks. Those
remain properties of the surrounding canonical Solana model with their own
premises. This package supplies no whole-program entrypoint theorem.

Instruction construction and local CPI preparation stop at the actual opaque
invocation signatures. External contracts supply callee behavior; opacity
guarantees neither success nor any state effect. Machine memory, request bytes,
call/return operations and runtime copyback need explicit execution correspondences
and composition arguments.

Source branch selection is not target equivalence. A binding must identify
layout, endianness, alignment, integer and floating-point behavior, panic
strategy and relevant features. Mathematical layout or arithmetic results do
not prove the implementation of the compiler or machine. Syscall admission,
metering and cryptographic primitives retain their separate interpretation
obligations.

The runtime model describes each syscall with plain values: for `sol_sha256`,
a list of byte strings in and a digest out. It does not describe how a Rust
program hands these over, which is through pointers and lengths in memory. To
use the model for a program that calls a syscall directly, we also have to
state how the inputs are read from the memory of the program and how the outputs
are written back to it. For `sol_sha256` that means reading the (pointer,
length) pairs and the bytes they point to, and writing the 32-byte digest to
the result pointer. When a program reaches a syscall only through a library
function, the model of that function covers it.

The [raw SHA-512 and multiscalar models](source-notes/raw-syscalls.md) follow the
same boundary. SHA-512 returns 64 bytes. Multiscalar multiplication consumes
paired 32-byte scalar and point encodings and writes a 32-byte point only on
status `0`; status `1` preserves the output buffer. Invalid encodings remain
admissible inputs. Their decoding and cryptographic meaning belong to the
primitive interpretation, not a caller precondition. The canonical multiscalar
instance uses a separate width law for successful supported operations within
the count limit. Catalog selection and representation coverage do not prove this law, the primitive algorithms or the assumed external implementation contract.

Rust body proofs and executable client correctness remain separate developments. These models are justified by their pinned library sources, mathematical proofs and conformance tests.

The [error and nullable value bindings](source-notes/error-nullable.md) use
complete by-value codecs and preserve the supplied execution state. A concrete binding must establish all-result representation coverage, exact generic source selection, ABI agreement and the library implementation contract.
Only the reviewed Address instance has a pure query and trivial drop.
