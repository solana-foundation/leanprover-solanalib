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

Each model has source/version/configuration profiles in the [source registry](source-map.json). Lookup in a checkout reads those reviewed inputs directly. `just generate-specs` also produces an ignored `applicability.json` export; a standalone bundle containing that file and the lookup tools needs only the Python standard library:

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
preserve the reference contract at the used types. Exact native recordings remain
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

## Registered binding clauses

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:binding:66f4d76aecf1d8fb -->
<a id="binding-66f4d76aecf1d8fb"></a>

This model requires the target_os = solana source branch and an explicit finite-exit syscall provider; a concrete binding must justify the selected cfg and does not assume a successful status.
<!-- /registry -->

<!-- registry:binding:aedf68b7ebcba974 -->
<a id="binding-aedf68b7ebcba974"></a>

Relate the provider to actual point/output memory, syscall admission, feature gates, metering and the cryptographic primitive separately.
<!-- /registry -->

<!-- registry:binding:2bdd10cfed4f63a1 -->
<a id="binding-2bdd10cfed4f63a1"></a>

Rust body, compiler, ABI, legal access and representation correspondence remain open.
<!-- /registry -->

<!-- registry:binding:7c831c1e0b4de3a2 -->
<a id="binding-7c831c1e0b4de3a2"></a>

Supplied callback relations must interpret the actual primitive or trait implementation, including error, unwind, termination and state effects.
<!-- /registry -->

<!-- registry:binding:d282988771a2fb4f -->
<a id="binding-d282988771a2fb4f"></a>

Current bytes, allocation identity, address range, native-load alignment, pointer provenance, reference validity and read permission require a source memory interpretation.
<!-- /registry -->

<!-- registry:binding:15c59e5e680dd420 -->
<a id="binding-15c59e5e680dd420"></a>

Current bytes, allocation identity, address range, pointer provenance, reference validity, read permission and little-endian target interpretation require a source memory interpretation. The reached eight-byte logical extent is checked by model admission; read_unaligned does not require an eight-byte-aligned pointer.
<!-- /registry -->

<!-- registry:binding:73cfb3cbae7ec412 -->
<a id="binding-73cfb3cbae7ec412"></a>

Rust body correctness, compiler correspondence and target memory/reference representation remain open; these mathematical witnesses are not Rust execution proofs.
<!-- /registry -->

<!-- registry:binding:157f977863257615 -->
<a id="binding-157f977863257615"></a>

Bind each actual dependency implementation to its local outcome/current-resource, ownership and frame laws, including partial effects and element destruction; primitive vector laws alone do not imply a frame or nested ownership.
<!-- /registry -->

<!-- registry:binding:94d82941a618889f -->
<a id="binding-94d82941a618889f"></a>

Use the published Pyth receiver 2.0.0 reference, complete update/message observations and the explicit panic strategy. The mathematical family has precondition True; fitting canonical Clock fields to Rust u64/i64 widths remains a source binding obligation expressed by Sysvar.clockValid, not a runtime check or family gate.
<!-- /registry -->

<!-- registry:binding:142c76ae14e92655 -->
<a id="binding-142c76ae14e92655"></a>

The getter does not authenticate signatures, authority or ownership; Anchor/error representation and Rust integer operations remain separate bindings.
<!-- /registry -->

<!-- registry:binding:462e2f49be94cd57 -->
<a id="binding-462e2f49be94cd57"></a>

Ready supplies protocol validity and a live readable byte view; these premises establish progress, final validity and retirement of the input token. Shared mode, a positive 64-bit slice address, isize-bounded length and nonoverflowing extent remain separate Rust argument bindings.
<!-- /registry -->

<!-- registry:binding:308202f8b78687ec -->
<a id="binding-308202f8b78687ec"></a>

Select the actual 8/16 alignment profile and justify Pod layout, bytemuck alignment primitive feature branch, physical references and typed-field observations separately.
<!-- /registry -->

<!-- registry:binding:28e35fd0e9f93d35 -->
<a id="binding-28e35fd0e9f93d35"></a>

64-bit usize and binary64 round-to-nearest ties-to-even with gradual underflow; integer overflow and panic profiles are explicit. Arithmetic NaN payloads are unobserved by the final u64 cast.
<!-- /registry -->

<!-- registry:binding:3be629903e979e7e -->
<a id="binding-3be629903e979e7e"></a>

V1 temporary descriptor writes are abstracted by preparation. The source interpretation of Box allocation/drop must cover every reachable partially initialized prefix, including later validation errors and unwind. Projecting private scratch out of State requires justification; drop may soundly overapproximate hidden-prefix effects. No precise byte-observing allocator/destructor correspondence or unchanged-state guarantee follows from this abstraction.
<!-- /registry -->

<!-- registry:binding:95ee659b5979b9c0 -->
<a id="binding-95ee659b5979b9c0"></a>

Interpret each source payload type and COption variant in the indexed logical representation; no physical enum-layout claim is made.
<!-- /registry -->

<!-- registry:binding:27ff7dfa299cd3f3 -->
<a id="binding-27ff7dfa299cd3f3"></a>

Interpret U64 as exactly eight initialized bytes and the result as the corresponding 64-bit unsigned integer; Rust core conversion correctness remains separate.
<!-- /registry -->

<!-- registry:binding:0eced3bcf8b962e4 -->
<a id="binding-0eced3bcf8b962e4"></a>

Rust implementation, compiler, representation and legal-access correspondence remain open.
<!-- /registry -->

<!-- registry:binding:7a8a551ef172114a -->
<a id="binding-7a8a551ef172114a"></a>

The supplied callee relation must preserve the finite outcomes and effects of the actual provider; no runtime admission or termination is assumed.
<!-- /registry -->

<!-- registry:binding:4a7190a81d148c5b -->
<a id="binding-4a7190a81d148c5b"></a>

The actual inputs are two immutable references to one-field 32-byte Address values; the source binding must check their complete ABI and ownership.
<!-- /registry -->

<!-- registry:binding:d340b5da13ec1c9e -->
<a id="binding-d340b5da13ec1c9e"></a>

The source binding must select the exact Address Ord implementation by full callable identity and ABI; generic artifacts must additionally agree on the recorded source and implementation arguments. The source compiler, Rust body, standard-library bodies and target equivalence remain explicit boundaries.
<!-- /registry -->

<!-- registry:binding:5f583f5855e8d5ee -->
<a id="binding-5f583f5855e8d5ee"></a>

Closed references and execution samples establish mathematical consistency only; no SDK body or Agave implementation is verified.
<!-- /registry -->

<!-- registry:binding:0e0734da409a4986 -->
<a id="binding-0e0734da409a4986"></a>

No general termination follows. Translation/compute failures have no ordinary postcondition; existing request-level terminal outcomes are not relabeled as successful returns.
<!-- /registry -->

<!-- registry:binding:d8520a9e72709815 -->
<a id="binding-d8520a9e72709815"></a>

Checked nonempty descriptor VM misalignment and typed destination VM misalignment are excluded by source admission without equating VM and translated-host alignment.
<!-- /registry -->

<!-- registry:binding:4288734bf7f8f1b2 -->
<a id="binding-4288734bf7f8f1b2"></a>

Separate input/output ownership is a sufficient source footprint, not a claim that Agave rejects all aliases. PDA early failures conservatively retain input/output ownership, while their answer contains no writes.
<!-- /registry -->

<!-- registry:binding:025d8e5631e6dc0b -->
<a id="binding-025d8e5631e6dc0b"></a>

Half-token recoloring proves simultaneous output/state representability only; it is not a client ghost update or a source/runtime initialization proof.
<!-- /registry -->

<!-- registry:binding:b5fa051f6f3ee7b5 -->
<a id="binding-b5fa051f6f3ee7b5"></a>

Rust body, compiler, target layout, legal access and representation correspondence remain open.
<!-- /registry -->

<!-- registry:binding:f8fdb012bb5e313a -->
<a id="binding-f8fdb012bb5e313a"></a>

The explicit provider interprets the actual runtime syscall, host stub or library operation with its normal results, state changes, unwind and terminal exits; no termination or validator implementation is assumed.
<!-- /registry -->

<!-- registry:binding:57a174b603247af7 -->
<a id="binding-57a174b603247af7"></a>

GetterReady consumes initialization of every actual reply classified as successful to retain its forwarding continuation; value validity is a separate provider interpretation and no provider termination is assumed. Defaults are zero Clock and Rent(rate 3480, threshold bits for 2.0, burn 50).
<!-- /registry -->

<!-- registry:binding:bd9bae7aff33eed6 -->
<a id="binding-bd9bae7aff33eed6"></a>

The concrete source values contain exactly 32 initialized bytes; references, slice descriptors, legal access, pointer widths and lifetimes are separate source/memory obligations.
<!-- /registry -->

<!-- registry:binding:5e39aac10a122ac0 -->
<a id="binding-5e39aac10a122ac0"></a>

Rust/SDK/standard-library bodies, compiler correctness, target-layout equivalence and runtime/cryptographic implementations remain open; source identity and native scripted checks do not prove them.
<!-- /registry -->

<!-- registry:binding:784d07d7dda8727b -->
<a id="binding-784d07d7dda8727b"></a>

Each indexed callback interprets the actual reached source operation with its full state, return, unwind and terminal outcomes; no termination or successful reply is assumed.
<!-- /registry -->

<!-- registry:binding:b792c49c5b1e749b -->
<a id="binding-b792c49c5b1e749b"></a>

When multiple Borsh generations are linked, bind the exact retained trait item and implementation (including its resolved arguments and disambiguating description) to the stated generation; bare display names and dependency presence do not establish this selection.
<!-- /registry -->

<!-- registry:binding:34997fb89ae90ad6 -->
<a id="binding-34997fb89ae90ad6"></a>

These are explicit assumed library interfaces; no SDK, core/alloc/std, compiler or application body correctness is supplied.
<!-- /registry -->

<!-- registry:binding:6c0671bb94c95d48 -->
<a id="binding-6c0671bb94c95d48"></a>

Bind reference/current-resource identities to legal source borrows and owned allocations in one shared memory interpretation, with the exact selected layouts and scalar/Boolean widths.
<!-- /registry -->

<!-- registry:binding:1e57e9a6f8c82faa -->
<a id="binding-1e57e9a6f8c82faa"></a>

Dependency relations represent actual Vec allocation/clone/push/drop, serializer and unwrap sites, including partial initialization cleanup, actual intermediate states and all finite failure/terminal outcomes.
<!-- /registry -->

<!-- registry:binding:e20913a2fdff6199 -->
<a id="binding-e20913a2fdff6199"></a>

Primitive exact-content/freshness laws and the needed resource frames are separate from the operational model. No allocator or serializer success, rollback or source preservation by an arbitrary provider is assumed.
<!-- /registry -->

<!-- registry:binding:885eb82897407338 -->
<a id="binding-885eb82897407338"></a>

A terminal exit has no post-state and skips subsequent cleanup. Only the explicit double-unwind relation can supply a terminal result after a second unwind.
<!-- /registry -->

<!-- registry:binding:b844ef86141ca458 -->
<a id="binding-b844ef86141ca458"></a>

Rust body correctness, physical memory layout, reference lifetimes, target correspondence and the source-call InterfaceSpec remain separate assumptions.
<!-- /registry -->

<!-- registry:binding:0ca3308c4a8c4733 -->
<a id="binding-0ca3308c4a8c4733"></a>

The logical source-loan store interprets live Rust receiver objects and references. AccountInfo RefCell cells, callback-accessible interiors and owned payload resources are interpreted in the auxiliary state.
<!-- /registry -->

<!-- registry:binding:dfecc70a526cdd36 -->
<a id="binding-dfecc70a526cdd36"></a>

Rust implementation, source reference/lifetime/alias interpretation, compiler layout and legal memory access remain explicit source-call assumptions.
<!-- /registry -->

<!-- registry:binding:b985857460252cc6 -->
<a id="binding-b985857460252cc6"></a>

Rust implementation, compiler, ABI, pointer provenance, legal reference access and allocator correspondence remain explicit interpretation obligations; mathematical witnesses and native differential tests are not Rust body proofs.
<!-- /registry -->

<!-- registry:binding:f80b845a6ce838b4 -->
<a id="binding-f80b845a6ce838b4"></a>

Bind keys to 32 bytes, amounts to u64, decimals to u8, the actual released authority enum and the reached usize arithmetic. The source TokenInstruction enum size is an explicit provider index, not the closed sample size.
<!-- /registry -->

<!-- registry:binding:340aca4748420ac8 -->
<a id="binding-340aca4748420ac8"></a>

Bind each actual vector allocation, literal, push, extend and drop to its outcome/current-content/ownership and needed frame laws. Resource identities and actual callback states are retained; primitive current-content laws alone do not supply freshness, framing or nested ownership.
<!-- /registry -->

<!-- registry:binding:624aee729d2ca0fe -->
<a id="binding-624aee729d2ca0fe"></a>

Interpret the indexed accessors, borrowed source ranges, vector allocation/push/drop, base Pack and owned-base destruction at their reached source call sites. Finite unwind and terminal exits retain their effects; no callback success or whole-call result is assumed.
<!-- /registry -->

<!-- registry:binding:5d949fd403669264 -->
<a id="binding-5d949fd403669264"></a>

The reviewed ordinary build excludes cfg(test) extension variants. Source type/layout, legal reference access and provider correspondence remain separate from these mathematical contracts.
<!-- /registry -->

<!-- registry:binding:a5f30773f618fd19 -->
<a id="binding-a5f30773f618fd19"></a>

Source field/layout and Rust implementation correspondence remain separate; no SDK, standard-library or application body is proved here.
<!-- /registry -->

<!-- registry:binding:c7d04bcad5003b3b -->
<a id="binding-c7d04bcad5003b3b"></a>

Bind the three moved String owners to their actual current UTF-8 strings at the reached serialization call, with source ownership preserved by intervening vector operations. Borsh serializes u32 little-endian byte lengths followed by UTF-8 bytes; the only local length-conversion error is InvalidData. The error callback denotes the whole consuming unwrap, including its unwind or terminal exit.
<!-- /registry -->

<!-- registry:binding:62c0aeb6d3e245ae -->
<a id="binding-62c0aeb6d3e245ae"></a>

The 64-bit little-endian aligned-loader input is one live, nonnull, eight-byte-aligned allocation containing every range decoded by EntryDeserialize.parse; every account data length is at most 10485760 bytes. Offsets, instruction lengths and the allocation end fit the selected pointer and signed slice bounds.
<!-- /registry -->

<!-- registry:binding:5e5a0ed2ab440ed4 -->
<a id="binding-5e5a0ed2ab440ed4"></a>

Every duplicate marker designates an earlier account slot, including duplicates of duplicates. A unique marker introduces distinct header storage even when keys are equal. Input storage is not concurrently accessed or invalidated during the call.
<!-- /registry -->

<!-- registry:binding:a91a3edc32684bd0 -->
<a id="binding-a91a3edc32684bd0"></a>

The model covers the named unsafe library interface under these loader-format conditions. Rust, core/alloc, compiler, loader and interpreter bodies remain assumed; this is not an implementation or startup proof.
<!-- /registry -->

<!-- registry:binding:1f54d6f6175ab591 -->
<a id="binding-1f54d6f6175ab591"></a>

MAX_ACCOUNTS and the input account count are at most 254; a nonempty input requires MAX_ACCOUNTS greater than zero because the source writes output slot zero before testing capacity.
<!-- /registry -->

<!-- registry:binding:c0681db98b1e8d03 -->
<a id="binding-c0681db98b1e8d03"></a>

The caller separately owns the disjoint mutable MaybeUninit<AccountInfo> array of exactly MAX_ACCOUNTS elements. Each initialized element is the same raw unique-header pointer, with its provenance retained; the unfilled suffix is unchanged.
<!-- /registry -->

<!-- registry:binding:b71285ec55ef5888 -->
<a id="binding-b71285ec55ef5888"></a>

Pinocchio Account has its reviewed repr(C) layout of 88 bytes and AccountInfo is a single pointer. Header offset 0 is the two-nibble borrow byte, offsets 1/2/3 raw flags, offset 4 the signed resize delta, and offsets 8/40/72/80 the key/owner/lamports/data length. Deserialization does not change any input byte.
<!-- /registry -->

<!-- registry:binding:34c704f8b299f2ae -->
<a id="binding-34c704f8b299f2ae"></a>

The unsafe source returns static references. The source binding must guarantee backing lifetime for every subsequent use of those references, or encapsulate them under a shorter scoped interface that prevents escape. Input and output uniqueness and the exposed-provenance alignment round-trip are explicit representation obligations.
<!-- /registry -->

<!-- registry:binding:9d269257abd5b59c -->
<a id="binding-9d269257abd5b59c"></a>

The input grants exclusive access to each lamports/data region and to the four-byte original-length word at unique-header offset 4, with legal shared key/owner/instruction/program references. RefCell/Rc aliases share the same original mutable borrow; no second independent mutable owner is manufactured.
<!-- /registry -->

<!-- registry:binding:a7315b2b44d1b238 -->
<a id="binding-a7315b2b44d1b238"></a>

The selected 64-bit AccountInfo layout has 48 bytes, and count * 48 is below 2^63. Existing modeled resources are coherent. Rc counts are fresh and bounded by this count, so neither Vec capacity nor Rc count overflow is admitted.
<!-- /registry -->

<!-- registry:binding:7456d774b115948a -->
<a id="binding-7456d774b115948a"></a>

The explicit index provider interprets Global allocation at Vec reservation, then lamports Rc and data Rc for each unique entry. It preserves existing resources and input bytes, never unwinds, and may return, terminate or have no finite outcome. Data allocation follows the original-length write; terminals have no invented post-state.
<!-- /registry -->

<!-- registry:binding:f93c6474e7d2034a -->
<a id="binding-f93c6474e7d2034a"></a>

Returned Vec/Rc allocations own actual fresh live storage in the execution representation. Logical vector/cell IDs record identity, not physical ownership. All input references live for the source lifetime a, and returned owners obey the ordinary destruction and borrowing protocol.
<!-- /registry -->

<!-- registry:binding:f15afa8677b4b8c2 -->
<a id="binding-f15afa8677b4b8c2"></a>

Each index operation denotes the actual reached vector allocation, slice extension, Rc clone/drop, collection work, local panic or PDA syscall. The model composes their actual return, unwind and terminal outcomes; no allocator or callback termination or success is assumed.
<!-- /registry -->

<!-- registry:binding:d7227cf23647c204 -->
<a id="binding-d7227cf23647c204"></a>

Borrow cell IDs, Ref slots and current vector resources represent the same source account aliases and owners. Source representation supplies valid typed cells, live retained views and current prefix reads, exact constructor counts/cleanup permutations, and resource/borrow frames at each actual primitive outcome.
<!-- /registry -->

<!-- registry:binding:90832d83de9cd52d -->
<a id="binding-90832d83de9cd52d"></a>

The two caller vectors are lent mutable resources; additional accounts are a borrowed slice and four named AccountInfos are moved owners. Rust bindings must retain caller instruction data/program, Rc multiplicities and all surviving frames at the actual after-world, including partial copyback mutation on unwind.
<!-- /registry -->

<!-- registry:binding:cc5c6bc062c36cdd -->
<a id="binding-cc5c6bc062c36cdd"></a>

Choose the zero-initialized Pubkey 2.2.1 target syscall provider and the actual compilation panic/double-unwind policy. Cryptographic correctness is separate; this helper never invokes CPI.
<!-- /registry -->

<!-- registry:binding:a147ebec4789a003 -->
<a id="binding-a147ebec4789a003"></a>

Rust SDK/standard-library bodies, compiler/target layout and source memory correspondence remain explicit assumed interfaces. Mathematical reference, execution and satisfiability theorems do not discharge source-call coverage.
<!-- /registry -->

<!-- registry:binding:8eb0270e4a85336e -->
<a id="binding-8eb0270e4a85336e"></a>

Interpret the selected account through its current alias-aware borrow cells and each vector through the actual allocation world. The Vec providers describe with_capacity, push, to_vec and drop, including allocation identity, contents, abnormal exits and double-unwind termination. No source allocation or ownership is manufactured by an observation.
<!-- /registry -->

<!-- registry:binding:172619708ef1bcc9 -->
<a id="binding-172619708ef1bcc9"></a>

Hash.Value interprets a valid source array of exactly 32 bytes; the operation is a pure value copy.
<!-- /registry -->

<!-- registry:binding:a5b548f00e55295a -->
<a id="binding-a5b548f00e55295a"></a>

Interpret usize as 64 bits and binary64 with round-to-nearest ties-to-even and gradual underflow. Preserve the selected checked/wrapping integer overflow and unwind/abort profile; NaN payloads are unobserved by the final saturating u64 cast.
<!-- /registry -->

<!-- registry:binding:a172ad168dd1c2c6 -->
<a id="binding-a172ad168dd1c2c6"></a>

Interpret the returned canonical Pubkey as the pinned SDK address value; physical macro expansion and Rust representation remain separate.
<!-- /registry -->

<!-- registry:binding:16af5e6b4a95e14a -->
<a id="binding-16af5e6b4a95e14a"></a>

Concrete Rust/SDK implementation, compiler and memory correspondence remain open.
<!-- /registry -->

<!-- registry:binding:5353be6e65af8112 -->
<a id="binding-5353be6e65af8112"></a>

This is the concrete Mint with COption<Address>, u64, u8 and bool fields, not generic Clone<T>. Interpret every field including None versus Some(zero), and retain legal shared access to the caller-owned record.
<!-- /registry -->

<!-- registry:binding:32d8ceaf1167419a -->
<a id="binding-32d8ceaf1167419a"></a>

The mathematical model is an unconditional complete value copy. Source representation, compiler and Rust implementation correspondence remain separate; no account-parser or initialized-mint condition is imposed.
<!-- /registry -->

<!-- registry:binding:dc0f7b4297946370 -->
<a id="binding-dc0f7b4297946370"></a>

The source reference, lifetime and projected field are related to the corresponding mathematical value.
<!-- /registry -->

<!-- registry:binding:c5a5ab9a475a2643 -->
<a id="binding-c5a5ab9a475a2643"></a>

AsRef and the two non-unwinding Global Rc dependencies are bound to the actual implementations and aliases.
<!-- /registry -->

<!-- registry:binding:73d1e352efeac332 -->
<a id="binding-73d1e352efeac332"></a>

The primary family requires AnchorConstructOwned.Ready. InitReady excludes only a malformed lamports observation on the actual system-owner branch; checked borrow failures, zero balances and the non-system bypass remain admitted. At each successful initialization prefix, OwnerCheckReady protects the reached wrong-owner Error allocation through the diagnostic Owner call and local store.
<!-- /registry -->

<!-- registry:binding:971d048c4454f471 -->
<a id="binding-971d048c4454f471"></a>

After each actual successful owner check, DecodeReady supplies selected typed data and admission for every actual decoder exit. account_retain extends that exit through checked release to the complete constructor. The owner-mismatch continuation results retain the current Box and exact normal or unwind cleanup after actual allocation and callback exits.
<!-- /registry -->

<!-- registry:binding:edd1d70e566ad18d -->
<a id="binding-edd1d70e566ad18d"></a>

Raw operations and posts are unchanged. Admission supplies local continuation without assuming callback, allocation or destructor termination. Concrete trait, resource, reference, lifetime and target interpretations remain separate bindings; a consumed guard receives no fabricated cleanup.
<!-- /registry -->

<!-- registry:binding:a2d03a509453fd58 -->
<a id="binding-a2d03a509453fd58"></a>

The primary family requires AnchorLoadingOwned.Admission. A successful selected data acquisition must expose actual current bytes; earlier writable or checked-borrow errors remain admitted. A reached discriminator-error factory must retain the held token at every actual name, message and Box allocation return through FactoryReady.
<!-- /registry -->

<!-- registry:binding:b1f8df6a81c33ec6 -->
<a id="binding-b1f8df6a81c33ec6"></a>

local_continuations derives current-data availability, cleanup availability at each primitive prefix and the exact outer continuation of each finite complete factory exit. Mapping keeps its size, bounds and alignment panic/abort paths; successful mapping exposes the current byte range and consumes the input guard. Legacy Ready.retain remains a separate stronger result.
<!-- /registry -->

<!-- registry:binding:ddd61db6d06104a0 -->
<a id="binding-ddd61db6d06104a0"></a>

The primary family requires AnchorConstructOwned.Ready. OwnerCheckReady protects the reached wrong-owner allocation, diagnostic callback, current Error payload and ordinary store. After every successful owner-check prefix, the selected data cell is typed and LoaderReady admits each reached guarded discriminator or error-factory exit.
<!-- /registry -->

<!-- registry:binding:b7895fba7ea669ee -->
<a id="binding-b7895fba7ea669ee"></a>

loader_input derives actual current data and guarded-check admission. loader_retain extends each actual guarded-check exit through release to the full constructor. Owner-mismatch continuation results retain actual returned errors, unwind cleanup and terminal exits.
<!-- /registry -->

<!-- registry:binding:77c8cd70b6b3a584 -->
<a id="binding-77c8cd70b6b3a584"></a>

The primary family requires AnchorConstructOwned.Ready. InitReady applies only to the system-owner lamports observation. After every actual successful initialization and CheckOwner prefix, DecodeReady supplies the selected typed data and admission for every actual decoder exit.
<!-- /registry -->

<!-- registry:binding:e5d80a11a22900c1 -->
<a id="binding-e5d80a11a22900c1"></a>

interface_retain extends each actual decoder exit through checked release and the final current-owner observation. Initialization borrow failures, zero balances, ordinary errors, unwind state and terminal reasons are retained; unrelated account fields and target-width equalities are not gates.
<!-- /registry -->

<!-- registry:binding:7785cb37cddc871d -->
<a id="binding-7785cb37cddc871d"></a>

EmptyReady requires only that the actual empty-provider output has current contents [] and an owner absent from the input state. realizes consumes both pointwise facts to prove the current-empty and freshness postconditions of the constructor; no law for an uncalled vector operation is required.
<!-- /registry -->

<!-- registry:binding:6aad66efe7123dd4 -->
<a id="binding-6aad66efe7123dd4"></a>

Source resource identity, representation and lifetime correspondence remain implementation bindings.
<!-- /registry -->

<!-- registry:binding:171bc0a14bd71af9 -->
<a id="binding-171bc0a14bd71af9"></a>

The primary family requires live, distinct input payload Strings and exactly Ops.BoxingLaws: returned Box contents, freshness of its identity, and preservation of existing String observations. These three facts establish the fresh/current payload and returned Ready postcondition without assuming allocation success.
<!-- /registry -->

<!-- registry:binding:a17197a536f01649 -->
<a id="binding-a17197a536f01649"></a>

The shared Types index carries no full Ops.Laws certificate. Laws for uncalled String allocation, retirement, Box deallocation or payload stores are not part of the admission of this family; concrete source resource and lifetime interpretation remains separate.
<!-- /registry -->

<!-- registry:binding:d8fef6fa3cd5bbb9 -->
<a id="binding-d8fef6fa3cd5bbb9"></a>

The primary family requires input Ready, the four Ops.ComparisonLaws used by replacement, and ComparisonStoreReady for this receiver and key-pair update. String drops preserve other Strings and Box descriptors; actual stores establish current payloads and preserve String observations. These capabilities prove the unchanged normal identity/payload/Ready post.
<!-- /registry -->

<!-- registry:binding:56aabcf45cb87f53 -->
<a id="binding-56aabcf45cb87f53"></a>

ComparisonStoreReady supplies an actual writeBox result only after a reached normal old-comparison cleanup. withPubkeys_family_cleanup_continues constructs that exact local assignment continuation or passes through the same terminal cleanup exit. It does not assert opaque destructor termination or require unrelated allocation/Box-retirement laws. Physical ownership and source correspondence remain external bindings.
<!-- /registry -->

<!-- registry:binding:3cef9da0767b99f3 -->
<a id="binding-3cef9da0767b99f3"></a>

The primary family requires input Ready, the four Ops.ComparisonLaws used by replacement, and ValuesCallbacks.CallReady at this initial call. ReturnedAdmissible remains a component proving the normal same-identity Ready post; reached unwind and destructor premises additionally retain the current error resources required by later local cleanup.
<!-- /registry -->

<!-- registry:binding:1b29f8a5e1d0ec4b -->
<a id="binding-1b29f8a5e1d0ec4b"></a>

A left ToString unwind leaves a Ready current error. A right unwind also retains the actual first returned String live and disjoint from the current error fields. At each actual operand-cleanup entry, returned drops and a first unwind retain Ready whenever cleanup continues. Terminal and double-unwind exits impose no later resource condition. Changes to unrelated captured state and changed but Ready unwind payloads remain allowed.
<!-- /registry -->

<!-- registry:binding:d57ca1955ec077f8 -->
<a id="binding-d57ca1955ec077f8"></a>

CallReady.assignment requires ComparisonStoreReady after each actual pair of returning conversions: every normal old-comparison cleanup reaches an available ordinary writeBox assignment. Family assignment/unwind continuation theorems construct exact raw continuations from supplied finite dependency exits; they do not require opaque callbacks or destructors to terminate. Actual resource ownership, lifetimes, provider semantics and Rust correspondence remain separate source bindings.
<!-- /registry -->

<!-- registry:binding:adcdae24dbcc6084 -->
<a id="binding-adcdae24dbcc6084"></a>

The source cfg and actual syscall sink interpretation are supplied; no logging success or display encoding is invented.
<!-- /registry -->

<!-- registry:binding:6f280571909d7252 -->
<a id="binding-6f280571909d7252"></a>

Both amount contracts require AccountInfo.DataBorrow.Ready for the selected shared data borrow. An actual borrow failure is admitted; after a successful borrow, its actual current cell must contain data. This reached-read admission yields the bytes used by the complete local read continuation, and actual acquisition proves release on return or unwind. Every actual checked-error conversion exit and its state changes is retained. Source AccountInfo/reference representation and concrete dependency correctness remain separate bindings; no whole-AccountInfo Valid, owner, full-token-codec or scalar-width condition is added.
<!-- /registry -->

<!-- registry:binding:40d8a3ff30ef5912 -->
<a id="binding-40d8a3ff30ef5912"></a>

No owner or full-token-codec check is present. Short data retains its configured panic behavior; malformed mathematical cells receive no invented reference or cleanup outcomes.
<!-- /registry -->

<!-- registry:binding:ae0c03b89cc57426 -->
<a id="binding-ae0c03b89cc57426"></a>

The primary family requires BuildReady: every actual successful fixed-ID instruction-builder return leaves its constructed metadata and byte vectors readable in that returned state. This condition is exactly actual request availability; it imposes no requirement on an unreached request after construction unwind or terminal exits.
<!-- /registry -->

<!-- registry:binding:da3bc674a1a68c4b -->
<a id="binding-da3bc674a1a68c4b"></a>

BuildReady.after_build and BuildReady.builder_continuation form the actual current request and preserve each supplied invocation, ProgramError conversion and source-ordered cleanup continuation. They assume neither finite dependency execution nor CPI success, rollback, allocation success or destructor return. No full VectorOps.Laws, initial whole-world validity or hidden no-unwind certificate is required.
<!-- /registry -->

<!-- registry:binding:daf69c9b1a706e33 -->
<a id="binding-daf69c9b1a706e33"></a>

Target reservation size, vector contents, resource representation, Rust ownership/frame correspondence and the actual Vec/Rc/error implementations remain source bindings. Remaining-vector destruction must use the same AccountInfo Rc interpretation. Conditional cleanup results retain their explicit destructor non-unwind premises.
<!-- /registry -->

<!-- registry:binding:05ae94e8a0aab82d -->
<a id="binding-05ae94e8a0aab82d"></a>

Pinned Anchor SPL 1.0.2 selects Rust edition 2021. Cleanup destroys instruction metadata then bytes, the moved accounts of the tail-expression temporary, and finally the remaining vector of the context.
<!-- /registry -->

<!-- registry:binding:bb8ed50904536916 -->
<a id="binding-bb8ed50904536916"></a>

The reviewed Rust profile selects target_os = solana; identifying the model target with that branch and proving cfg/features, output representation and syscall ABI remain source-binding obligations. The host pointer-status fallback is outside the reviewed profile.
<!-- /registry -->

<!-- registry:binding:4127ac8d33558d84 -->
<a id="binding-4127ac8d33558d84"></a>

GetterValid is a separate law about present successful values, consumed by get_success_valid. It is not part of initialization admission; a present value is forwarded without a value-validity gate.
<!-- /registry -->

<!-- registry:binding:537ecccf4f4b28a5 -->
<a id="binding-537ecccf4f4b28a5"></a>

To interpret the pinned Solana source branch, a binding must justify target_os = solana, destination initialization and representation, and the syscall ABI. The mathematical family itself has no target gate.
<!-- /registry -->

<!-- registry:binding:1aee417e4d5a09d4 -->
<a id="binding-1aee417e4d5a09d4"></a>

The two Global Rc dependencies have no user unwind callback; count and ownership correctness are separately bound.
<!-- /registry -->

<!-- registry:binding:bb350415a16a3490 -->
<a id="binding-bb350415a16a3490"></a>

ObservationReady requires only the selected present cell and its defined typed projection; observe_reference_exists consumes this premise to exclude the malformed branch and produce a finite getter outcome.
<!-- /registry -->

<!-- registry:binding:c37367abb942f927 -->
<a id="binding-c37367abb942f927"></a>

The source interpretation relates the selected cell policy and explicit panic strategy to Rust RefCell behavior. Other account cells and unused target-width bounds are not mathematical getter preconditions.
<!-- /registry -->

<!-- registry:binding:9e176e56efb52170 -->
<a id="binding-9e176e56efb52170"></a>

DataBorrowReady requires a protocol-valid world and an actual selected data cell. Its proof uses both premises to preserve after.Valid and expose typed current data through every successfully returned guard.
<!-- /registry -->

<!-- registry:binding:d58e18c6548503f5 -->
<a id="binding-d58e18c6548503f5"></a>

The source binding relates cell identities, the actual current cell policy, counter bounds and ownership to Rust RefCell behavior. Whole-AccountInfo validity, the unrelated lamports cell and profile-width equalities are not premises of this mathematical borrow contract.
<!-- /registry -->

<!-- registry:binding:560e8905b27a4063 -->
<a id="binding-560e8905b27a4063"></a>

The index provider interprets the answers of the actual syscall environment and terminal exits for .hash .sha256 slices, with slices the bytes that the vals descriptors point to, in order, and its terminal exits for .abort as the abort of the runtime of a call that fails the slice-count check or the alignment check of vals.
<!-- /registry -->

<!-- registry:binding:05320ac747e596af -->
<a id="binding-05320ac747e596af"></a>

The law Index.hashShape of the index gives every answer of the environment to this request the hash shape: status below 2^64, one 32-byte digest on status 0 and no bytes otherwise; the call has no precondition. The canonical runtime meets the law by the width law of Solanalib.Runtime.Prims (sha256_length), so a canonical return is a 32-byte digest with no premise on the world (canonical_sha256_post_iff).
<!-- /registry -->

<!-- registry:binding:e6648f74d71cff46 -->
<a id="binding-e6648f74d71cff46"></a>

The argument aligned is whether vals is 8-aligned as Agave checks it, on its host translation; where the index checks alignment, a call with a slice and aligned = false does not return (Sha256Args.unaligned), as Agave aborts it before reading a descriptor.
<!-- /registry -->

<!-- registry:binding:6cde058747336a99 -->
<a id="binding-6cde058747336a99"></a>

The limit of the index Index.maxHashSlices, if any, is the limit of the environment on val_len; a call with more slices does not return (Sha256Args.overLimit), whatever its alignment, as Agave checks the count before any other check and aborts with TooManySlices. The limit of the canonical runtime is the maxHashSlices of the profile.
<!-- /registry -->

<!-- registry:binding:3d52d811cf8553b3 -->
<a id="binding-3d52d811cf8553b3"></a>

The family precondition is True; entry metaVec.Live is not assumed. Stronger current-value observations use their explicit vector, serializer and frame laws.
<!-- /registry -->

<!-- registry:binding:8931a46059c86d18 -->
<a id="binding-8931a46059c86d18"></a>

The raw family has precondition True. length_exact separately uses a 64-bit length bound to prove equality of the forwarded word and mathematical length; Rust slice width, pointer translation, provenance, permissions and target cfg remain source bindings.
<!-- /registry -->

<!-- registry:binding:21b05b239226caa6 -->
<a id="binding-21b05b239226caa6"></a>

target_os=solana selects the syscall helper; other targets select the separately overridable host stub. BPF architecture alone does not select Solana.
<!-- /registry -->

<!-- registry:binding:2900f113aa317f4f -->
<a id="binding-2900f113aa317f4f"></a>

The wrapper applies no 1024-byte check or truncation. canonical_step states that limit and the current-program tag only for the separately interpreted canonical runtime provider.
<!-- /registry -->

<!-- registry:binding:5f764e88f3097a6a -->
<a id="binding-5f764e88f3097a6a"></a>

This model requires the target_os = solana or target_arch = bpf source branch; host SHA2 and host no-feature panic are outside this profile. A concrete binding must justify the selected cfg and syscall ABI.
<!-- /registry -->

<!-- registry:binding:19cfbc7ec1a14203 -->
<a id="binding-19cfbc7ec1a14203"></a>

The family imposes no count bound. Bounded is the separate premise of request_count, which proves exactness of the forwarded u64 count. Rust slice representation and the physical validity of both the slices and the destination remain source bindings.
<!-- /registry -->

<!-- registry:binding:099a0f46db32ce3b -->
<a id="binding-099a0f46db32ce3b"></a>

The family requires EveryReturnInitialized at this input: every normal provider reply, including nonzero status, initializes all 32 bytes. initialized_return_has_run consumes that premise to retain each normal return; it does not assume that any provider return occurs.
<!-- /registry -->

<!-- registry:binding:e88a3b632a4bc3ed -->
<a id="binding-e88a3b632a4bc3ed"></a>

The returned hash is the actual initialized output of the provider. Cryptographic projection additionally requires the explicit NormalHashAgreement law for the supplied canonical SHA-256 primitive; its implementation is not proved.
<!-- /registry -->

<!-- registry:binding:130167e488cfa028 -->
<a id="binding-130167e488cfa028"></a>

GetterReady requires every actual provider reply classified as success to carry an initialized destination. It imposes no target or value-validity predicate. get_retains and get_hasOutcome_iff preserve every actual finite provider exit through the unchanged forwarding relation without assuming provider termination. GetterValid is separate and used by get_success_valid; initialized abstract values outside the validity predicate remain admitted.
<!-- /registry -->

<!-- registry:binding:9df96e55b3af729d -->
<a id="binding-9df96e55b3af729d"></a>

The supplied target selects the Solana typed syscall or the actual host stub; the logical initial value is Default.
<!-- /registry -->

<!-- registry:binding:b065eabd4fb4eef2 -->
<a id="binding-b065eabd4fb4eef2"></a>

The family precondition is True. Actual program-ID checks and capacity arguments remain in the operation; Rust scalar/key widths, capacity arithmetic and the explicit enumSize layout parameter require separate source bindings.
<!-- /registry -->

<!-- registry:binding:6dd560d8c31dbd2c -->
<a id="binding-6dd560d8c31dbd2c"></a>

The public entry fixes fee to None and retains argument/account ordering and duplicates. Source 64-bit target widths, AccountInfo representation and fixed-width amounts/decimals remain explicit binding obligations; the mathematical families impose no unused whole-argument validity gate.
<!-- /registry -->

<!-- registry:binding:5ba95e0cf972fe77 -->
<a id="binding-5ba95e0cf972fe77"></a>

The primary family chooses one collection protocol and requires Admission.Admitted, ResourceReady and BorrowReady at the actual input. These conditions cover used primitive guards/data, current owned locals and five reached authority/mint/validation/collection borrow sites. Retained-Ref success supplies protocol validity and current data; checked errors and early program rejection need no success-only facts. The authority getter excludes only its malformed selected result.
<!-- /registry -->

<!-- registry:binding:8739f5d15cd09c48 -->
<a id="binding-8739f5d15cd09c48"></a>

ResourceReady covers actual returned constructor contents, used mutations and authority-slot assignment, other-live-local retention and post-CPI cleanup owners. family_borrow_continue and family_mint_primitive_retain consume the reached input admission to derive the actual mint read/release scope after finite primitive exits.
<!-- /registry -->

<!-- registry:binding:217415a22f6b26e7 -->
<a id="binding-217415a22f6b26e7"></a>

LiteralAdmission.Ready constrains actual evaluate/finish commands at the four/five source counts and the cleanup permutation before each actual cleanup exit. The raw ordered clone/move trace is unchanged; initialInfos_success_current separately uses CurrentLaw for the exact four account values.
<!-- /registry -->

<!-- registry:binding:15dbec1574e60ded -->
<a id="binding-15dbec1574e60ded"></a>

PdaInputs.Bounded remains at each actual Types.findPda call. PdaAdmission.Ready requires initialized address output on each actual bounded status-zero reply, yielding its local decode continuation. Nonzero replies retain each actual panic exit, and direct unwind/terminal exits bypass decode. Concrete syscall, source-width and retained-slice interpretations remain bindings.
<!-- /registry -->

<!-- registry:binding:7dcb1abdf69804b6 -->
<a id="binding-7dcb1abdf69804b6"></a>

The same selected protocol supplies collection conformance, finish-current, guard/data/iterator/resource frames and finite-prefix cleanup-order admission. CleanupSite.extend retains actual cleanup exits in that protocol Trace. One-way Conforms does not prove arbitrary collection-provider completeness; opaque downstream destructor/provider outcomes remain premises, not termination assumptions.
<!-- /registry -->

<!-- registry:binding:0debfffaff7181c9 -->
<a id="binding-0debfffaff7181c9"></a>

The final actual CPI relation is opaque and outcome-carrying; no invoked-program body is inspected or modeled by this wrapper.
<!-- /registry -->

<!-- registry:binding:a94eadb779c2b078 -->
<a id="binding-a94eadb779c2b078"></a>

Bind the isNone provider to the selected Nullable::is_none implementation, including the equality and NONE-temporary cleanup of the default method if that default is selected. Do not assume the query is pure or is a zero comparison.
<!-- /registry -->

<!-- registry:binding:f470a5fa36573684 -->
<a id="binding-f470a5fa36573684"></a>

Interpret payloads as retained identities and put mutable interior contents in State. Bind dropValue and doubleUnwind to the actual destructor and panic runtime, including their cleanup and terminal outcomes.
<!-- /registry -->

<!-- registry:binding:0ac56aa3bf041d7f -->
<a id="binding-0ac56aa3bf041d7f"></a>

A runtime binding must use one fixed world and invocation context for the operation, including release, registration and feature behavior; SDK versions do not change runtime profiles.
<!-- /registry -->

<!-- registry:binding:9116059b71b2645c -->
<a id="binding-9116059b71b2645c"></a>

A source execution binding must initialize and maintain the runtime half of the shared invocation-state ghost token against the live runtime. The caller half alone cannot select or update the current state. Each call equates its fixed request buffer snapshot with actual before.buf, and its actual after.buf includes ordered source output stores; all non-buffer fields follow the selected request result.
<!-- /registry -->

<!-- registry:binding:370bc3d5960180c3 -->
<a id="binding-370bc3d5960180c3"></a>

Applying these contracts to Rust assumes the reviewed source call implements the derived partial-correctness interface, with representable 64-bit register/pointer values and the stated memory layout. Translation, compute exhaustion, deployment and compiler correctness are not proved.
<!-- /registry -->

<!-- registry:binding:d217979acc183d04 -->
<a id="binding-d217979acc183d04"></a>

Copying-mode runtime interpretation is retained. Directly mapped account memory may have additional state effects and is outside this physical memory interpretation.
<!-- /registry -->

<!-- registry:binding:93ea59c34453d56e -->
<a id="binding-93ea59c34453d56e"></a>

The exact Borsh tag reaches an explicit literal-copy provider after the typed read. Its returned OwnedError retains a live String resource; StringReady for reached normal copies proves freshness at the post-read state and exact current contents "Unknown". ownedPost and the nonempty closed witness retain ordinary allocation effects. fromStatus remains a separate value facet; no error-buffer ownership is inferred from it.
<!-- /registry -->

<!-- registry:binding:564171134c0cf409 -->
<a id="binding-564171134c0cf409"></a>

Only target_os = solana is selected. Interpret the nested slice descriptors, u64 count and initialized 32-byte destination with actual memory and lifetime; the provider reply is the final complete buffer. Cryptographic agreement is an additional provider law.
<!-- /registry -->

<!-- registry:binding:99216bc9e8f4347d -->
<a id="binding-99216bc9e8f4347d"></a>

Always allocate three metadata entries; copy the borrowed seed into an owned temporary String before moving metadata into bincode construction, then drop the temporary String after the builder call.
<!-- /registry -->

<!-- registry:binding:7f72c118c05ff7ce -->
<a id="binding-7f72c118c05ff7ce"></a>

The seed bytes interpret the entire Rust str (valid UTF-8), including NUL/long seeds; the function performs no seed-length or derived-address check. The source u64/string-length representation is separate from the True mathematical precondition.
<!-- /registry -->

<!-- registry:binding:c41ef833cfea176c -->
<a id="binding-c41ef833cfea176c"></a>

Bind T::clone to the actual source-reference callback, including pointer identity, interior effects and all finite exits. For owned AccountInfo bind both non-unwinding Global Rc operations in declaration order.
<!-- /registry -->

<!-- registry:binding:7a6faca29e2214a8 -->
<a id="binding-7a6faca29e2214a8"></a>

Select debug from the actual anchor-debug feature. Bind the logging and panic dependencies to their complete actual finite outcomes.
<!-- /registry -->

<!-- registry:binding:76e1f0b5a6c2ddb6 -->
<a id="binding-76e1f0b5a6c2ddb6"></a>

The supplied FieldReference.Access describes the same existing live parent and its current complete pointee.
<!-- /registry -->

<!-- registry:binding:f2e36a141d24d78c -->
<a id="binding-f2e36a141d24d78c"></a>

Bind the runtime index to the separately pinned Agave 4.3.2 configuration with pointerChecks enabled and the actual current invocation context/state. Crate version compatibility does not admit another validator release or runtime configuration.
<!-- /registry -->

<!-- registry:binding:60f74de8272cb6ae -->
<a id="binding-60f74de8272cb6ae"></a>

The callee relation is the explicit processing contract of the invoked program. The canonical instance uses Solanalib.Runtime.ProcInstr and retains its preparation, synchronization, privilege/error order, account frame and balance results. No SDK invocation or callee implementation is proved or executed.
<!-- /registry -->

<!-- registry:binding:9535b5cea863a10d -->
<a id="binding-9535b5cea863a10d"></a>

Decode the complete instruction, account-info array and nested signer tree from initialized, live source memory, preserving order, repeated keys, pointer aliases, empty seeds and signer groups. Every translated pointer and the copyback destination must match the separate physical memory interpretation.
<!-- /registry -->

<!-- registry:binding:037a85cf2ef8669f -->
<a id="binding-037a85cf2ef8669f"></a>

Only a successful canonical runtime invocation returns. Runtime, metering and callee errors terminate the caller; no unchanged post-state is asserted for a failed stage. Nonzero-returning host stubs are not this profile.
<!-- /registry -->

<!-- registry:binding:c244dadca533135a -->
<a id="binding-c244dadca533135a"></a>

Bind the three thin pointer arguments and two u64 counts in their declared order. The C and Rust names select different instruction/account/seed data layouts; both declarations have extern-C function calling convention.
<!-- /registry -->

<!-- registry:binding:5420f9893b14614c -->
<a id="binding-5420f9893b14614c"></a>

Only the dynamic external declaration is bound. Exclude static-syscalls; for define-syscall 5.1.0 also exclude unstable-static-syscalls on BPF. No raw implementation body is traversed.
<!-- /registry -->

<!-- registry:binding:26c74514c7c8de9e -->
<a id="binding-26c74514c7c8de9e"></a>

Use the actual AccountInfo RefCell identities in one shared Borrow.State with the 64-bit RefCell policy. Probe the first matching info per instruction meta, lamports before data, and release each temporary borrow before the next check. Local AccountBorrowFailed is an ordinary Result error; missing infos remain runtime checks.
<!-- /registry -->

<!-- registry:binding:b0d8fe177aeb03d4 -->
<a id="binding-b0d8fe177aeb03d4"></a>

The result codec represents only Ok(()) or the local AccountBorrowFailed variant in the exact compiled ProgramResult layout. Older BorshIoError string payloads and later enum variants are not silently equated; they cannot occur as ordinary results of this canonical on-chain signature.
<!-- /registry -->

<!-- registry:binding:ac3d616cd1e7a922 -->
<a id="binding-ac3d616cd1e7a922"></a>

Bind caller pointers, provenance, layout, lifetimes, allowed interior mutation and returned memory to the exact compiled types. Source cfg selection on a native compilation target is not proof of SBF layout equivalence.
<!-- /registry -->

<!-- registry:binding:ed72514c57e1145f -->
<a id="binding-ed72514c57e1145f"></a>

The signature borrows instruction buffers throughout. For solana-invoke the temporary stable header uses ManuallyDrop and must not acquire ownership of or destroy the source Vec buffers; monolithic 1.15.2 passes the original instruction layout. These distinct pointer origins are separate physical memory interpretations.
<!-- /registry -->

<!-- registry:binding:20074908a0bc516b -->
<a id="binding-20074908a0bc516b"></a>

Bind the owned storage provider to Instruction::clone, StableInstruction::from and destruction at the selected source release. It returns a fresh owner with the exact ordered instruction, retains the current allocator state, and destroys that owner after successful CPI. Allocation and cleanup terminal outcomes are preserved; no custom allocator success is assumed.
<!-- /registry -->

<!-- registry:binding:24ab93f48eddb4cc -->
<a id="binding-24ab93f48eddb4cc"></a>

OwnerRef identifies the actual writable owner storage behind the shared reference. The finite store bound establishes the new current value through every alias; runtime reassignment authorization is separate.
<!-- /registry -->

<!-- registry:binding:f94a9b8b313cea65 -->
<a id="binding-f94a9b8b313cea65"></a>

ResizeReady provides the selected typed cell and original-length/backing representation; its reached capacity condition proves the requested slice length. Local data and spare bytes jointly describe the complete backing. A source binding must validate key-4 u32 original length, data-8 u64 length, pointer width, alignment, allocation and legal volatile/raw writes.
<!-- /registry -->

<!-- registry:binding:7bf35fb4da09cb81 -->
<a id="binding-7bf35fb4da09cb81"></a>

The Solana memory syscall writes exactly the reached new tail on a normal return and may terminate without a post-state. Legacy replaceable host SyscallStubs are outside this profile.
<!-- /registry -->

<!-- registry:binding:04db13a4e8e37593 -->
<a id="binding-04db13a4e8e37593"></a>

The explicit zero_init flag is retained; false preserves stale bytes on shrink/regrow.
<!-- /registry -->

<!-- registry:binding:c1d55f0616719a4c -->
<a id="binding-c1d55f0616719a4c"></a>

LamportsBorrowReady supplies a typed selected cell and protocol-valid lease world. The current cell policy, guard lifetime and counter bounds interpret the actual RefCell. No account writability or unrelated-cell condition is assumed.
<!-- /registry -->

<!-- registry:binding:406d4ce455251844 -->
<a id="binding-406d4ce455251844"></a>

ObservationReady supplies only the selected current typed data projection and excludes malformed mathematical paths; borrow conflicts map to AccountBorrowFailed and a successful temporary shared guard is released.
<!-- /registry -->

<!-- registry:binding:7bdf23307ec95f9e -->
<a id="binding-7bdf23307ec95f9e"></a>

A Rust binding must establish the actual value layouts, borrowed references and moved owners at the same native before/after states. Generic indices do not certify Rust trait implementations.
<!-- /registry -->

<!-- registry:binding:d43fca11b888da6c -->
<a id="binding-d43fca11b888da6c"></a>

Explicit primitive allocation, formatting, vector and callback interfaces retain their source effects and finite exits. Bind only the operations actually reached by this function; no whole-function callback is assumed.
<!-- /registry -->

<!-- registry:binding:8de5a33352ee0296 -->
<a id="binding-8de5a33352ee0296"></a>

Error construction follows the shared diagnostic-allocation boundary. A finite reference sample is not evidence that a source dependency terminates.
<!-- /registry -->

<!-- registry:binding:e35b1a90c208ac41 -->
<a id="binding-e35b1a90c208ac41"></a>

Bind constructor allocation, bincode serialization, Vec/Rc cleanup, current resource reads and error conversion to the exact resolved dependency providers.
<!-- /registry -->

<!-- registry:binding:7913f80c9d1a90ec -->
<a id="binding-7913f80c9d1a90ec"></a>

Invocation is an explicit opaque whole invoke_signed signature. Error, unwind, terminal and account effects are retained; neither invocation implementation correctness nor successful callee execution is assumed.
<!-- /registry -->

<!-- registry:binding:e7201e629bb160d4 -->
<a id="binding-e7201e629bb160d4"></a>

Use one fixed Types interpretation and actual shared before/after state for the Vec, Rc, remaining-vector, owned error, invocation and return-data primitives. Remaining destruction uses the same AccountInfo Rc owners.
<!-- /registry -->

<!-- registry:binding:7b66a53dd366f823 -->
<a id="binding-7b66a53dd366f823"></a>

Ready requires current metadata/bytes and the borrowed seed view only at every actual successful builder and array-preparation prefix. Earlier error, unwind and terminal exits stay admitted; it assumes no allocation, callback or CPI termination.
<!-- /registry -->

<!-- registry:binding:878dfd6fedb5efd2 -->
<a id="binding-878dfd6fedb5efd2"></a>

Source bindings provide concrete resource identities, current vector contents/capacities, actual AccountInfo Rc aliases and nested seed references, scalar widths and result/error layout. Error conversion preserves an old owned Borsh String and uses the release-specific inline or boxed representation.
<!-- /registry -->

<!-- registry:binding:fed0ddcfeaff0f89 -->
<a id="binding-fed0ddcfeaff0f89"></a>

Every supplied invocation/getter result and effect is retained. No token processor, rollback, CPI success, global heap validity or arbitrary final-state premise is supplied by opacity. Cleanup uses actual finite destructor exits and retains terminal outcomes without an after state.
<!-- /registry -->

<!-- registry:binding:b7304d1788b346af -->
<a id="binding-b7304d1788b346af"></a>

Bind DispatchTypes.current to the actual source receiver field, inner to the selected T trait method and the result type to the Anchor Result of this release. Mutable callbacks return their actual successor state; a stale payload snapshot is not a valid current accessor.
<!-- /registry -->

<!-- registry:binding:213c482f0e460f33 -->
<a id="binding-213c482f0e460f33"></a>

ValidationReady requires IdReady only for Program: each reached boxed wrong-ID error survives the actual second Id callback, whose returned path admits its diagnostic update. Signer, System, Interface, Unchecked, AccountInfo and Sysvar impose no unused Id premise.
<!-- /registry -->

<!-- registry:binding:c1d2deb536a81191 -->
<a id="binding-c1d2deb536a81191"></a>

ConstructReady uses InitReady only at the reached system-owner lamports observation. Reached owner mismatches require the actual live boxed diagnostic resource and store; a bypass or earlier error has no decoder precondition.
<!-- /registry -->

<!-- registry:binding:c42ca0543b805cfc -->
<a id="binding-c42ca0543b805cfc"></a>

DecodePayloadReady and DecoderReady supply typed current data and guard frames at the reached clone, decoder and failed-result cleanup primitives. The resulting continuation retains every actual finite decoder exit and releases that same guard; it does not assume callback termination.
<!-- /registry -->

<!-- registry:binding:ed08aa3fef0d35ca -->
<a id="binding-ed08aa3fef0d35ca"></a>

Bind the actual T::try_accounts and Box::new interfaces. A successful inner return is consumed by the allocator; failed and unwinding inner outcomes retain their actual state without calling it.
<!-- /registry -->

<!-- registry:binding:4cec0de093505962 -->
<a id="binding-4cec0de093505962"></a>

CommonCloseReady applies at the reached common helper after any actual source clone. CloseCoreReady checks typed observations and only the reached credit, source-zero, owner-assignment and zero-resize prefix. Earlier errors and panics require no later resize precondition.
<!-- /registry -->

<!-- registry:binding:8f5cb700b0a2c045 -->
<a id="binding-8f5cb700b0a2c045"></a>

The lawful SDK focus retains actual balances, owners, backing buffers and borrow state. Zero resize never invokes a zero-initialization callback. The actual source and moved-destination Rc cleanup outcomes remain explicit; aliasing and earlier mutations on late failure are retained.
<!-- /registry -->

<!-- registry:binding:5a1947e55baf63a8 -->
<a id="binding-5a1947e55baf63a8"></a>

ExitReady constrains only the reached is_closed observation and actual serialization branch. SerializeReady frames the identified exclusive data guard and fixed selected-data length, while permitting serializer writes, auxiliary mutations, errors and unwind.
<!-- /registry -->

<!-- registry:binding:f246563e54a0e50c -->
<a id="binding-f246563e54a0e50c"></a>

ReloadReady covers only reached owner checks and data decoding. DecodeReplaceReady preserves the held Account data guard through each actual decoder and old-payload destructor exit; modern InterfaceAccount releases its decoder guard before replacement.
<!-- /registry -->

<!-- registry:binding:b76b36ba6162dce4 -->
<a id="binding-b76b36ba6162dce4"></a>

The lawful payload focus selects the current receiver field. Its actual old-payload destructor outcome is retained, and a returned or unwinding destructor installs the decoded replacement in the successor state. Terminal outcomes have no invented successor.
<!-- /registry -->

<!-- registry:binding:3369cad7447b6afa -->
<a id="binding-3369cad7447b6afa"></a>

Empty slices retain their position while constructing AccountNotEnoughKeys; nonempty slices consume the first AccountReference before validation. Every finite result retains the actual remaining slice, bumps and reallocations; original record identity is passed to Sysvar.
<!-- /registry -->

<!-- registry:binding:f50c4eeed67fa378 -->
<a id="binding-f50c4eeed67fa378"></a>

The actual serializer is called with the current payload, held mutable data guard and BpfWriter position zero. Old local AccountInfo clones are retained and dropped in source order; the interface wrapper uses its saved owner.
<!-- /registry -->

<!-- registry:binding:04e532375f9ed040 -->
<a id="binding-04e532375f9ed040"></a>

Ready requires the branch-specific is_closed read domain only after an actual matching Owner return, and the selected exclusive-data domain only after an actual non-closed result. No writable, payload-layout or discriminator-capacity success gate is added.
<!-- /registry -->

<!-- registry:binding:2bc6a93830b86448 -->
<a id="binding-2bc6a93830b86448"></a>

Ready requires typed data only after a successful selected acquisition and CodeReady only at a reached nonzero-prefix error. Each actual name/message/Box return retains the held token for real cleanup; terminal exits have no post-state. No zero-prefix, payload-size, alignment-success or Owner gate is imposed.
<!-- /registry -->

<!-- registry:binding:4e0e900ac3ac2d45 -->
<a id="binding-4e0e900ac3ac2d45"></a>

AccountsReady applies the existing selected typed-data, protocol-validity and factory continuation domain at the reached head; it places no account condition on the empty slice. Current resource and trait interpretation remain source-binding obligations.
<!-- /registry -->

<!-- registry:binding:68d588ceb884c6ae -->
<a id="binding-68d588ceb884c6ae"></a>

Only the reached mismatch diagnostic needs OwnerCheckReady: every actual Box allocation and second Owner exit must leave the current error resources required by store/drop. This is not a whole-call termination premise.
<!-- /registry -->

<!-- registry:binding:9abc704a0f62b73f -->
<a id="binding-9abc704a0f62b73f"></a>

For owned AccountInfo bind both non-unwinding Global Rc operations. Program and Interface PhantomData do not invoke T::clone.
<!-- /registry -->

<!-- registry:binding:3e36dc5ce0fbd225 -->
<a id="binding-3e36dc5ce0fbd225"></a>

The supplied primitive providers interpret reached allocation, move, clone, current-read, serialization, cleanup and panic operations at the same state. Admission.Ready contains exact prefix-local current/frame and literal-control conditions, not a completed-wrapper or termination premise.
<!-- /registry -->

<!-- registry:binding:402fd412934b25f9 -->
<a id="binding-402fd412934b25f9"></a>

The complete invocation signature is an explicit CpiRequest.Invocation boundary with actual request, return/error/unwind/terminal state effects. No invocation body is traversed.
<!-- /registry -->

<!-- registry:binding:5ea795acd8ef5611 -->
<a id="binding-5ea795acd8ef5611"></a>

At every actual matching-program getter return, the returned byte owner is current. Nonmatching program IDs need no byte read. Key comparison precedes exact eight-byte validation, and both error and success paths drop the owned return vector at the source site.
<!-- /registry -->

<!-- registry:binding:d82b6ea87f65b5b1 -->
<a id="binding-d82b6ea87f65b5b1"></a>

Interpret the COption discriminant and nominal payload identities in the source values. For borrowed operations, the observed values refer to the actual live shared borrows. This is a source representation obligation, not a mathematical precondition.
<!-- /registry -->

<!-- registry:binding:0a812cb901d5b6a2 -->
<a id="binding-0a812cb901d5b6a2"></a>

The index supplies the actual reached callbacks, their state and finite outcomes. A FnOnce provider consumes its closure and payload and includes their internal cleanup. Empty callback relations admit no finite exit and do not fabricate a result.
<!-- /registry -->

<!-- registry:binding:efb215d4a04efa9e -->
<a id="binding-efb215d4a04efa9e"></a>

For the frozen nightly-2026-05-01 lowering, select ReturnPlace.retain: a payload moved into the return place remains live if the unused fallback destructor unwinds (rust-lang/rust#47949). ReturnPlace.drop separately represents a lowering that cleans that value and double-unwind remains terminal. Do not choose the policy independently of the compiled cleanup paths.
<!-- /registry -->

<!-- registry:binding:55c845bff490db1c -->
<a id="binding-55c845bff490db1c"></a>

Reference.id denotes the same existing shared AccountInfo reference; no Rc operation, pointee snapshot or independent ownership is introduced.
<!-- /registry -->

<!-- registry:binding:8f5901777e64d651 -->
<a id="binding-8f5901777e64d651"></a>

Bind the actual AsRef and panic callbacks and the selected AccountInfo lamports cell. The reached typed-cell premise excludes malformed interpretations but admits borrow conflicts.
<!-- /registry -->

<!-- registry:binding:976de49ba44eab42 -->
<a id="binding-976de49ba44eab42"></a>

The unsafe Pinocchio signature performs no borrow preflight; establish the Rust access and lifetime obligations of the caller separately. The reviewed body passes accounts.len() in full, despite an adjacent documentation sentence about a required-account prefix. Its normal return is unit.
<!-- /registry -->

<!-- registry:binding:8996044f28fdcf44 -->
<a id="binding-8996044f28fdcf44"></a>

ObservationReady supplies only the selected current typed data projection. RefCell conflict or saturation follows the explicit panic strategy, with no invented ordinary error return.
<!-- /registry -->

<!-- registry:binding:3bb5a093b983c27b -->
<a id="binding-3bb5a093b983c27b"></a>

Interpret the returned Address in the canonical 32-byte key model and bind the exact macro provider, target layout and source result ABI.
<!-- /registry -->

<!-- registry:binding:f42beb0eef8280a3 -->
<a id="binding-f42beb0eef8280a3"></a>

Ready checks selected typed lamports reads at their reached source prefixes, then the source owner and resize storage only after nonoverflow and both actual balance writes. Destination cleanup and error allocation retain each actual dependency outcome; neither is assumed to terminate.
<!-- /registry -->

<!-- registry:binding:04ca1585f63163ad -->
<a id="binding-04ca1585f63163ad"></a>

Interpret the transparent OptionalNonZeroPubkey wrapper and its resolved Pubkey/Address provider as the same canonical 32-byte key. Byte equality and the zero Default key are the reviewed dependency operations; no general address API model is claimed.
<!-- /registry -->

<!-- registry:binding:b23d9639abd9c98d -->
<a id="binding-b23d9639abd9c98d"></a>

The consumed receiver is owned and has no outstanding source loan. Bind destruction of owned AccountInfo Rc fields, including terminal allocation-owner behavior.
<!-- /registry -->

<!-- registry:binding:b2c7d07a74177c94 -->
<a id="binding-b2c7d07a74177c94"></a>

Bind the actual old-field destructor and replacement owner. Its source field identity and auxiliary effects are preserved; no destructor success or non-unwind premise is assumed.
<!-- /registry -->

<!-- registry:binding:da9292f98b753337 -->
<a id="binding-da9292f98b753337"></a>

Clone reads its borrowed source once, then clones accounts before data. The metadata clone owner is dropped on byte-clone unwind, while the borrowed source is never dropped.
<!-- /registry -->

<!-- registry:binding:a3d9aa5aca9ad251 -->
<a id="binding-a3d9aa5aca9ad251"></a>

After successful local preflight, bind the runtime index to the separately pinned Agave 4.3.2 configuration with pointerChecks enabled and the actual invocation context/state. Local AccountBorrowFailed needs no runtime correspondence. Crate compatibility does not admit another validator release or runtime configuration.
<!-- /registry -->

<!-- registry:binding:d58882f488884798 -->
<a id="binding-d58882f488884798"></a>

The signature borrows the original instruction buffers throughout and directly forwards their native layout. CpiLegacyFields retains those source fields; conditional runtime entry separately checks the literal raw address words against the decoded request. No StableInstruction clone or AccountInfo clone is modeled for this version.
<!-- /registry -->

<!-- registry:binding:4687a26157d25733 -->
<a id="binding-4687a26157d25733"></a>

The frozen nightly-2026-05-01 Solana-cfg native layout has Vec words [capacity,pointer,length] and legacy AccountInfo fields rent/key/lamports/data/owner, while the pinned Agave decoder reads [pointer,capacity,length] and key/lamports/data/owner/unused. Actual source calls remain representable. General nonempty forwarding has no established decoded-request and VM-mapping correspondence for this build; the numeric disagreement alone predicts no runtime fault.
<!-- /registry -->

<!-- registry:binding:6365458673055eb5 -->
<a id="binding-6365458673055eb5"></a>

Rust body correctness, representation, references, lifetimes and target correspondence remain open.
<!-- /registry -->

<!-- registry:binding:1b225f24050e4109 -->
<a id="binding-1b225f24050e4109"></a>

Bind explicit dependency/callback operations and resource observations to the actual source implementations; prove their required frames and live-result properties.
<!-- /registry -->

<!-- registry:binding:17a03b289e0ff9cd -->
<a id="binding-17a03b289e0ff9cd"></a>

Bind the reader to R = &[u8] with the default std feature of borsh; the reference follows <&[u8] as Read>::read_exact in the toolchain, which empties the slice on a short read, while the contract leaves the remaining slice after an error unconstrained.
<!-- /registry -->

<!-- registry:binding:a2417f2e879712bf -->
<a id="binding-a2417f2e879712bf"></a>

Bind the index callback to Self::deserialize_reader; an implementation that overrides deserialize needs its own model.
<!-- /registry -->

<!-- registry:binding:5190a32e6baa1ea3 -->
<a id="binding-5190a32e6baa1ea3"></a>

Rust source-body, compiler, ABI and runtime correspondence are separate open obligations; no executable Rust client or implementation proof is supplied.
<!-- /registry -->

<!-- registry:binding:f2d1a89f467a17ae -->
<a id="binding-f2d1a89f467a17ae"></a>

Bind the index callback to Self::deserialize of the actual Self.
<!-- /registry -->

<!-- registry:binding:c057a58384ccd687 -->
<a id="binding-c057a58384ccd687"></a>

Bind the element size to its actual target layout and the division-panic callback to the program panic policy at the post-length slice; the generic family includes every size and both unwind and terminal panic exits.
<!-- /registry -->

<!-- registry:binding:2bc46c3a684818c5 -->
<a id="binding-2bc46c3a684818c5"></a>

Bind size_of::<T>() to the actual target layout and the division-panic callback to the program panic policy, retaining its unwind state or terminal reason.
<!-- /registry -->

<!-- registry:binding:223a82755f573ca2 -->
<a id="binding-223a82755f573ca2"></a>

Bind the write callback to the write of the writer and the panic callback to the panic of the slice index under the panic strategy of the program.
<!-- /registry -->

<!-- registry:binding:79637d167eaeecdf -->
<a id="binding-79637d167eaeecdf"></a>

Bind the allocate callback to the global allocator of the program, under its panic strategy, at the String allocation of the message of the WriteZero error.
<!-- /registry -->

<!-- registry:binding:a12e3b881a4024a7 -->
<a id="binding-a12e3b881a4024a7"></a>

Applies only where the called implementation is this provided method: a writer that overrides write_all (&mut W, &mut [u8] and Vec<u8>, the write_all methods at nostd_io.rs 674, 700 and 727) is a different implementation.
<!-- /registry -->

<!-- registry:binding:806ff9d3f58588e0 -->
<a id="binding-806ff9d3f58588e0"></a>

Bind the index writer to W::write_all; the u8 element path covers [u8; 32] (Address) and [u8; 16] (WrappedI80F48).
<!-- /registry -->

<!-- registry:binding:49a16c6a1bbf1e3d -->
<a id="binding-49a16c6a1bbf1e3d"></a>

Bind the index writer to W::write_all and the element callback to <T as BorshSerialize>::serialize::<W>.
<!-- /registry -->

<!-- registry:binding:1a7c81de7b33e146 -->
<a id="binding-1a7c81de7b33e146"></a>

Bind the index writer to the actual W::write_all.
<!-- /registry -->

<!-- registry:binding:e8ced30d0e6c882f -->
<a id="binding-e8ced30d0e6c882f"></a>

Relate the returned slice to the same borrowed storage as the argument.
<!-- /registry -->

<!-- registry:binding:38e494d8c0515f05 -->
<a id="binding-38e494d8c0515f05"></a>

Rust body, compiler layout, reference representation and runtime correspondence remain open.
<!-- /registry -->

<!-- registry:binding:c1e02d524da98b55 -->
<a id="binding-c1e02d524da98b55"></a>

Bind the index to the actual size_of::<T>(), align_of::<T>() and decoding of the selected AnyBitPattern type, the argument to the actual slice address and bytes, the is_aligned_to feature branch, and the returned reference, lifetime and aliasing to the input slice.
<!-- /registry -->

<!-- registry:binding:7c5d7e8595bb66f2 -->
<a id="binding-7c5d7e8595bb66f2"></a>

Rust body, compiler layout and runtime correspondence remain open; core::mem::zeroed is described only by its effect on bytes.
<!-- /registry -->

<!-- registry:binding:0c093ec8744042a4 -->
<a id="binding-0c093ec8744042a4"></a>

Justify the Zeroable safety contract and the use of the default method for the selected impl, and bind the index decoding to its all-zero pattern.
<!-- /registry -->

<!-- registry:binding:8cce10fdf9b17bf4 -->
<a id="binding-8cce10fdf9b17bf4"></a>

Bind the index to the actual size_of::<T>(), align_of::<T>() and in-memory bytes of the selected NoUninit type, and the returned slice reference, lifetime and aliasing to the input reference.
<!-- /registry -->

<!-- registry:binding:01c6d2d5b808f2d9 -->
<a id="binding-01c6d2d5b808f2d9"></a>

Bind the macro instance impl_borsh_stake_state_v2!(borsh) (line 217) and the derived Meta, Authorized, Lockup, Stake, Delegation and StakeFlags decoders to this model; source anchors alone do not prove macro-generated or derive-generated bodies.
<!-- /registry -->

<!-- registry:binding:4e52a781d31ad796 -->
<a id="binding-4e52a781d31ad796"></a>

Bind the borsh 1.6.1 primitive decoders and the solana-address 2.6.0 Address decoder to their models.
<!-- /registry -->

<!-- registry:binding:328106abb4b8d9fb -->
<a id="binding-328106abb4b8d9fb"></a>

Relate the mathematical value, reference and outcome observations to the pinned Rust implementation and storage.
<!-- /registry -->

<!-- registry:binding:df7a30e351ddaf98 -->
<a id="binding-df7a30e351ddaf98"></a>

No ATA callee implementation, existing-account success, address validation, account creation or rollback follows from request preparation.
<!-- /registry -->

<!-- registry:binding:f1d104e35bf8ce2e -->
<a id="binding-f1d104e35bf8ce2e"></a>

Bind entry address observations and local request construction separately. No System program implementation, authorization or postcondition is inferred from this helper.
<!-- /registry -->

<!-- registry:binding:98a12e8e457dbf24 -->
<a id="binding-98a12e8e457dbf24"></a>

Relate mathematical space and its existing u64 byte encoding to the actual Rust u64 argument; source width is not a family entry restriction.
<!-- /registry -->

<!-- registry:binding:c8e824b432162c0e -->
<a id="binding-c8e824b432162c0e"></a>

Relate mathematical lamports and its existing u64 byte encoding to the actual Rust u64 argument; source width is not a family entry restriction.
<!-- /registry -->

<!-- registry:binding:a65f2b8ba6347d52 -->
<a id="binding-a65f2b8ba6347d52"></a>

Prove the frozen Rust body/refinement to this mathematical operation.
<!-- /registry -->

<!-- registry:binding:a1ae3bded4c69f65 -->
<a id="binding-a1ae3bded4c69f65"></a>

Bind source AccountView metadata, borrows, casts, references, layout and lifetimes to the shared state and guard interpretation.
<!-- /registry -->

<!-- registry:binding:08c2dff6463367ba -->
<a id="binding-08c2dff6463367ba"></a>

Bind the selected target panic behavior to the supplied nonreturning outcome provider.
<!-- /registry -->

<!-- registry:binding:3510e1039942260a -->
<a id="binding-3510e1039942260a"></a>

Rust source/body/compiler correspondence and client correctness remain open; mathematical execution is not an implementation proof.
<!-- /registry -->

<!-- registry:binding:c1d5441431680255 -->
<a id="binding-c1d5441431680255"></a>

Interpret live AccountView references, source lifetimes, physical CpiAccount fields/flag bytes/padding, initialized storage and exclusive buffer separation.
<!-- /registry -->

<!-- registry:binding:7bf3d56b29ba7e4b -->
<a id="binding-7bf3d56b29ba7e4b"></a>

Establish the three PrefixReady premises for the actual committed source slices. Separately bind private Batch invariants, source widths and representable additions, retained references, callback/provider behavior and buffer separation; the local progress result supplies no runtime/CPI execution or termination guarantee.
<!-- /registry -->

<!-- registry:binding:29f34a97ff0bf250 -->
<a id="binding-29f34a97ff0bf250"></a>

Bind source u64/u8 arguments and target slice/counter widths, including representable source additions; justify actual callback/provider behavior and buffer separation separately. The mathematical contracts impose no unused width/readiness gate and establish no runtime/CPI body correctness or admission.
<!-- /registry -->

<!-- registry:binding:f876e3949ed46c08 -->
<a id="binding-f876e3949ed46c08"></a>

Bind the #[account]/AnchorDeserialize-generated body to the Address, VerificationLevel, PriceFeedMessage and Borsh u64 decoder models; source anchors alone do not prove generated derive or std I/O bodies.
<!-- /registry -->

<!-- registry:binding:113c1721b1564bb7 -->
<a id="binding-113c1721b1564bb7"></a>

Bind the generated deserialize_reader and EnumExt::deserialize_variant bodies to these models; source anchors alone do not prove generated derive, format! or std I/O bodies.
<!-- /registry -->

<!-- registry:binding:65023296818b9f48 -->
<a id="binding-65023296818b9f48"></a>

Bind the generated derive body to the Borsh 1.6.1 decoder models; source anchors alone do not prove generated derive or std I/O bodies.
<!-- /registry -->

<!-- registry:binding:7e9928471a7d1a58 -->
<a id="binding-7e9928471a7d1a58"></a>

Bind the exact source version, target/profile, RuntimeAccount representation and legitimate handle/guard flow to the mathematical state.
<!-- /registry -->

<!-- registry:binding:ffb0ea7cfe813e99 -->
<a id="binding-ffb0ea7cfe813e99"></a>

Prove the selected Rust implementation and its pointer/reference access obligations separately; no Rust body, compiler or validator correspondence is supplied here.
<!-- /registry -->

<!-- registry:binding:d4e64798f6f30395 -->
<a id="binding-d4e64798f6f30395"></a>

For this source API, establish the actual AccountView account/guard storage, the applicable AccountView lease policy, source integer/byte representation and Rust reference/lifetime permissions. These are source-binding obligations, not extra premises of the mathematical contract.
<!-- /registry -->

<!-- registry:binding:3018289608ff30ae -->
<a id="binding-3018289608ff30ae"></a>

The exact source receiver is &self; discharge its access obligations without inferring global uniqueness across AccountView aliases.
<!-- /registry -->

<!-- registry:binding:495415022682de5f -->
<a id="binding-495415022682de5f"></a>

Track owner-reference invalidation independently of data leases, including owner writes performed by code outside these selected operations.
<!-- /registry -->

<!-- registry:binding:9ec21d0f219399d7 -->
<a id="binding-9ec21d0f219399d7"></a>

The branch contract requires an existing account cell and a defined source i32 update (CloseArithmetic); every ResizeValid header satisfies it. Separate pool preservation uses Ready; signed-counter preservation uses account presence and ResizeValid. Relate the physical source representation and owner-reference validity independently.
<!-- /registry -->

<!-- registry:binding:63f7c42455f06fca -->
<a id="binding-63f7c42455f06fca"></a>

The branch contract requires an existing account cell and defined source i32 arithmetic (ResizeArithmetic); every ResizeValid header satisfies it. Separate pool preservation uses Ready, and signed-domain preservation uses account presence and ResizeValid. Mathematical backing may extend; fixed backing length needs the actual capacity inequality. Relate Rust usize arguments and runtime-created storage to the state; signed conversion remains an operation check.
<!-- /registry -->

<!-- registry:binding:459397f6c2991bb0 -->
<a id="binding-459397f6c2991bb0"></a>

Relate the supplied generic target descriptor, captured storage and reference interpretation to the source reference types.
<!-- /registry -->

<!-- registry:binding:392e62a99c1ab2f1 -->
<a id="binding-392e62a99c1ab2f1"></a>

Justify the callback relation and source ManuallyDrop cleanup order for every finite exit; retainLease is explicit on unwind, terminal exits supply no state, and no termination is assumed.
<!-- /registry -->

<!-- registry:binding:f3467ba3fb126b2e -->
<a id="binding-f3467ba3fb126b2e"></a>

The exact source receiver is &mut self; discharge its access obligations without inferring global uniqueness across AccountView aliases.
<!-- /registry -->

<!-- registry:binding:2ce51d6689c731a9 -->
<a id="binding-2ce51d6689c731a9"></a>

Bind the selected cell to the AccountView 254-share policy. The shared byte-projection helper uses cell presence and that policy; the raw acquisition contract has no Ready premise.
<!-- /registry -->

<!-- registry:binding:df2792cf6c83a826 -->
<a id="binding-df2792cf6c83a826"></a>

The mutable byte-projection helper needs the selected cell, while the raw acquisition contract has no Ready premise. Valid Rust references and source representation remain separate.
<!-- /registry -->

<!-- registry:binding:2462ae15b6a5c71f -->
<a id="binding-2462ae15b6a5c71f"></a>

Justify the input reference of the callback separately; CallbackSafe supplies the protocol frame and exit-specific validity used by the mathematical post.
<!-- /registry -->

<!-- registry:binding:7c7750c30e9bae67 -->
<a id="binding-7c7750c30e9bae67"></a>

Bind the generated derive body to the Borsh 1.6.1 [u8; 32] decoder model; source anchors alone do not prove generated derive or std I/O bodies.
<!-- /registry -->

<!-- registry:binding:a476936476993e94 -->
<a id="binding-a476936476993e94"></a>

Bind the provider to the actual syscall, including memory admission, metering, partial writes, current state and target failure policy. Establish the universal SuccessInitialized law before assume_init; it supplies the mathematical initialization admission used by the local progress results, not syscall termination.
<!-- /registry -->

<!-- registry:binding:d6c9ed9aa195ae1a -->
<a id="binding-d6c9ed9aa195ae1a"></a>

Bind borrowed seed/program references and both output destinations to their physical storage. None denotes output not established as fully initialized, not a null address pointer.
<!-- /registry -->

<!-- registry:binding:1431ead4405387b8 -->
<a id="binding-1431ead4405387b8"></a>

This model uses the target_os = solana or target_arch = bpf source branch. A concrete binding must justify the cfg/features, target widths/layouts, syscall ABI and compiler/execution profile; selecting a source branch alone does not establish target equivalence.
<!-- /registry -->

<!-- registry:binding:e9939193ee58385c -->
<a id="binding-e9939193ee58385c"></a>

Bind the local panic provider, including target panic strategy and any internal machinery/cleanup; there are no owned host vectors in this selected source branch.
<!-- /registry -->

<!-- registry:binding:2d787b40d0676452 -->
<a id="binding-2d787b40d0676452"></a>

Bind the actual null-output syscall signature, borrowed point storage, runtime admission/metering, current state, return register and finite failure policy. No scratch allocation/output or concrete curve implementation is supplied.
<!-- /registry -->

<!-- registry:binding:a8e15f73222da86d -->
<a id="binding-a8e15f73222da86d"></a>

This mathematical family uses the Solana/bpf source branch. A concrete binding must justify its cfg/features, target widths/layouts, syscall ABI and compiler/execution profile.
<!-- /registry -->

<!-- registry:binding:de4fe6c902f18cc2 -->
<a id="binding-de4fe6c902f18cc2"></a>

Bind the generated derive body to the Borsh 1.6.1 [u8; 32] serializer model and the writer index; source anchors alone do not prove generated derive or std I/O bodies.
<!-- /registry -->

<!-- registry:binding:bb9edf5e161a23ee -->
<a id="binding-bb9edf5e161a23ee"></a>

Bind the explicit primitive provider to the actual syscall, including memory admission, metering, successful output initialization, partial output writes, current state and target failure policy. No runtime or Rust implementation proof is supplied.
<!-- /registry -->

<!-- registry:binding:4bdc0963b6a7b8b1 -->
<a id="binding-4bdc0963b6a7b8b1"></a>

The family requires SuccessInitialized at the actual before-state and seed/program inputs: every actual status-zero provider reply must contain an initialized address. Nonzero replies and unwind or terminal exits have no address-initialization requirement. A source binding must establish this provider law for the actual output storage.
<!-- /registry -->

<!-- registry:binding:df0747ec2c3f2597 -->
<a id="binding-df0747ec2c3f2597"></a>

The selected source binding uses target_os = solana or target_arch = bpf and represents slice counts as u64. The mathematical family has no target/width gate; its initialization admission is SuccessInitialized.
<!-- /registry -->

<!-- registry:binding:9e1e7876a64e7643 -->
<a id="binding-9e1e7876a64e7643"></a>

Bind the dynamic extern-C ABI under assumed InterfaceSpec. Valid within-limit calls own paired input arrays and a separate 32-byte result, even on failure; early rejections need no memory. See source-notes/raw-syscalls.md.
<!-- /registry -->

<!-- registry:binding:401acecbe6991f00 -->
<a id="binding-401acecbe6991f00"></a>

Bind the dynamic extern-C ABI under assumed InterfaceSpec. Within the slice limit, own descriptors/inputs and a separate 64-byte output, including for empty input. See source-notes/raw-syscalls.md.
<!-- /registry -->

<!-- registry:binding:c290248368f11032 -->
<a id="binding-c290248368f11032"></a>

Bind the provider to the syscall environment of the program.
<!-- /registry -->

<!-- registry:binding:fa3b72d31a81bd91 -->
<a id="binding-fa3b72d31a81bd91"></a>

The models cover the extern "C" declaration of define_syscall! without the static-syscalls target feature.
<!-- /registry -->

<!-- registry:binding:f7b63a436d462d41 -->
<a id="binding-f7b63a436d462d41"></a>

Bind the provider to the syscall environment of the program, and read the message from the memory of the program: the len bytes at message.
<!-- /registry -->

<!-- registry:binding:521ee5e5e48db40b -->
<a id="binding-521ee5e5e48db40b"></a>

Bind the provider to the syscall environment of the program, and read the file name from the memory of the program: the filename_len bytes at filename.
<!-- /registry -->

<!-- registry:binding:44ae024359492a59 -->
<a id="binding-44ae024359492a59"></a>

Bind the provider to the syscall environment of the program. For an admitted call within the slice limit of the index, read val_len (ptr, len) descriptors of 16 bytes at vals, 8-aligned where the index checks alignment, and the bytes they point to; write the 32 bytes of a status-0 answer at hash_result. Only a call over the slice limit has an empty memory precondition, regardless of alignment, since val_len is a register argument checked before memory translation. In the Agave request model, aligned denotes the alignment of the translated host address. A binding that sets this argument from the VM address must, within the limit, exclude nonempty calls at a VM-unaligned vals where the index checks alignment; callers cannot use that admission restriction to prove that these calls never return. No host/VM alignment agreement is assumed: a VM-aligned call may abort on an unaligned host address, which the partial-correctness contract permits. An empty descriptor list skips the vals alignment check but, within the limit, still requires the 32-byte result buffer.
<!-- /registry -->

<!-- registry:binding:49956dedf07d5306 -->
<a id="binding-49956dedf07d5306"></a>

Bind the actual unchecked unit-returning invocation, not an arbitrary SDK Result provider. Local checked-wrapper behavior is modeled; concrete runtime/callee correctness remains separate.
<!-- /registry -->

<!-- registry:binding:89f26d9c076e3598 -->
<a id="binding-89f26d9c076e3598"></a>

Discharge the pinned Rust compile-time assertion ACCOUNTS <= 64 at the concrete const instantiation. The mathematical array carrier retains exact extent equality without a capacity field or added runtime rejection.
<!-- /registry -->

<!-- registry:binding:8159938e2f16bac2 -->
<a id="binding-8159938e2f16bac2"></a>

Bind each provider to the pinned allocation, serialization, unwrap and destruction dependency, including partial construction, error destruction and target panic strategy; this is not a proof of core/alloc/std implementations.
<!-- /registry -->

<!-- registry:binding:8a2855591da273cc -->
<a id="binding-8a2855591da273cc"></a>

Bind resource handles/current tables to live Rust Vec storage and establish the local primitive laws, serializer encoding and resource frames needed for returned-byte/value observations.
<!-- /registry -->

<!-- registry:binding:ded97d06a9e14daa -->
<a id="binding-ded97d06a9e14daa"></a>

Establish the selected source feature configuration. The mathematical Format parameter does not assert which serialization feature was compiled in a recorded binary.
<!-- /registry -->

<!-- registry:binding:61fd13001748e776 -->
<a id="binding-61fd13001748e776"></a>

Both value and operational contracts have precondition True. Relate mathematical lamports and space to Rust u64 values and establish the actual encoding of the selected serializer; the contracts do not impose those width bounds.
<!-- /registry -->

<!-- registry:binding:37df194093da7bee -->
<a id="binding-37df194093da7bee"></a>

Both value and operational contracts have precondition True. Relate mathematical lamports to Rust u64 values and establish the actual encoding of the selected serializer; the contracts do not impose those width bounds.
<!-- /registry -->

<!-- registry:binding:cc436e49cb47751c -->
<a id="binding-cc436e49cb47751c"></a>

Relate source integer and record representations to these decoded mathematical values.
<!-- /registry -->

<!-- registry:binding:0060e01c0d962eea -->
<a id="binding-0060e01c0d962eea"></a>

Supply Rust-body correctness and justify the modeled ordinary return restriction separately.
<!-- /registry -->

<!-- registry:binding:fbf81f4c44a54a96 -->
<a id="binding-fbf81f4c44a54a96"></a>

Relate the selected fee value to the source immutable field reference, including lifetime, alias identity and permissions.
<!-- /registry -->

<!-- registry:binding:91c4a3a012f1311d -->
<a id="binding-91c4a3a012f1311d"></a>

Bind the logical parent to the original existing shared borrow, and Access.live to its current valid lifetime and permissions. Reused storage does not revive an expired borrow identity.
<!-- /registry -->

<!-- registry:binding:830324794a48dbe7 -->
<a id="binding-830324794a48dbe7"></a>

Bind Access.current to current decoded source fields and the retained selector to the same field location. The pinned alignment-one layout places the 18-byte older/newer records at offsets 72/90 within the 108-byte configuration; physical layout and access proofs remain separate.
<!-- /registry -->

<!-- registry:binding:95a1b202c370de32 -->
<a id="binding-95a1b202c370de32"></a>

Justify any state transition between field observations under the rules of the source borrow. The model does not grant write permission during an active shared borrow.
<!-- /registry -->

<!-- registry:binding:1c3a4cd8155ee3c4 -->
<a id="binding-1c3a4cd8155ee3c4"></a>

No new borrow acquisition or Ref-guard consumption is part of the modeled &self to &TransferFee projection.
<!-- /registry -->

<!-- registry:binding:c1ed1feba88a5615 -->
<a id="binding-c1ed1feba88a5615"></a>

The family requires GetterReady at the actual before-state: every actual provider reply classified as success by the configured status converter has a present destination. Classified errors, unwind and termination need no initialized destination. A source binding must establish this provider law for the actual destination storage.
<!-- /registry -->

<!-- registry:binding:dee4822ceae1b1a1 -->
<a id="binding-dee4822ceae1b1a1"></a>

Establish GetterReady for every actual reply classified as success, matching the destination read by the source. Initialization permits local continuation; the separate GetterValid law is needed for get_success_valid. Neither law supplies provider termination or physical memory correspondence.
<!-- /registry -->

<!-- registry:binding:78d99e79273e336f -->
<a id="binding-78d99e79273e336f"></a>

The selected profile uses 64-bit usize/isize and little-endian native u16, metadata size 33 and Address size 32/alignment 1. Bind these layouts and the numeric checked accesses to actual source allocation, provenance and reference permissions.
<!-- /registry -->

<!-- registry:binding:31821ab46e517f2b -->
<a id="binding-31821ab46e517f2b"></a>

The model requires a 64-bit usize representation for the source data length; a concrete binding must justify this width.
<!-- /registry -->

<!-- registry:binding:55a3a875a96efabf -->
<a id="binding-55a3a875a96efabf"></a>

Bind the exact pinned Rust body and compiler execution to this mathematical model.
<!-- /registry -->

<!-- registry:binding:727a4fdff0331ec6 -->
<a id="binding-727a4fdff0331ec6"></a>

Resolve get_extension_bytes/get_tlv_data, bind live source references and source Pod size/alignment/value representation.
<!-- /registry -->

<!-- registry:binding:8a6121a88bd9ac44 -->
<a id="binding-8a6121a88bd9ac44"></a>

The operational family has precondition True. Relate supplied Pod layout, current reference bytes and actual pointer/slice access to Rust; the modeled size/alignment checks supply the success geometry.
<!-- /registry -->

<!-- registry:binding:5d3abe86daa1ac06 -->
<a id="binding-5d3abe86daa1ac06"></a>

Bind the actual vector allocation, push and destructor operations, resource ownership, the original source reference and byte-read permissions.
<!-- /registry -->

<!-- registry:binding:ccebd22c9a7f08b0 -->
<a id="binding-ccebd22c9a7f08b0"></a>

Derive any desired immutability/frame specialization separately; collector frame does not frame the accessor or empty construction.
<!-- /registry -->

<!-- registry:binding:e6e2c373a6bc0657 -->
<a id="binding-e6e2c373a6bc0657"></a>

The operational family has precondition True. The separate successful-current-value theorem uses only the direct push_current capability and ExtensionReadFrame. Rust slice bounds and legal access remain source bindings. The reader retains fixed length metadata; Rust slice bounds and legal access impose no additional mathematical admission condition.
<!-- /registry -->

<!-- registry:binding:6c9ff93b9e18915d -->
<a id="binding-6c9ff93b9e18915d"></a>

Bind the shared PodMint codec, target integer widths, production extension layouts and source slices.
<!-- /registry -->

<!-- registry:binding:b7ead47d29726221 -->
<a id="binding-b7ead47d29726221"></a>

The contract has precondition True. Rust input widths remain source bindings; actual account-kind and PodMint initialization checks, saturation and sizing determine the result.
<!-- /registry -->

<!-- registry:binding:597b7adb38e705aa -->
<a id="binding-597b7adb38e705aa"></a>

Resolve S::SIZE_OF, S::ACCOUNT_TYPE, S::unpack and S destruction; bind owned values/resources and input/subrange permissions and lifetimes.
<!-- /registry -->

<!-- registry:binding:238eebbfdb8383bb -->
<a id="binding-238eebbfdb8383bb"></a>

The operational family has precondition True. Rust input/layout/pointer representation remains separately bound; actual parser, layout checks and destructor outcomes determine successful geometry and cleanup.
<!-- /registry -->

<!-- registry:binding:d6e262b172cb3892 -->
<a id="binding-d6e262b172cb3892"></a>

Exact Rust body correctness, compiler lowering, ABI, ownership and source-memory correspondence remain explicit assumed interfaces; the mathematical witnesses do not prove the SDK implementation.
<!-- /registry -->

<!-- registry:binding:00e8e1acec00ca35 -->
<a id="binding-00e8e1acec00ca35"></a>

This source-reference row preserves the exact reviewed defining crate, version and Rust item. A successful complete-build applicability match supplies the actual resolved source identity within the declared compatible range, under its recorded behavior assumptions. The dynamic-dispatch, target and resolved-dependency gates still apply; source-name registration alone does not discharge them.
<!-- /registry -->

<!-- registry:binding:44ec9cf7d1127c04 -->
<a id="binding-44ec9cf7d1127c04"></a>

A source execution binding must initialize and maintain the runtime half of the shared invocation-state ghost token against the live runtime. The caller half alone cannot select or update the current state.
<!-- /registry -->

<!-- registry:binding:d32627554f3ea10c -->
<a id="binding-d32627554f3ea10c"></a>

Source implementation, target layout, legal references, actual callback/resource interpretation and compiler correspondence remain assumed interfaces, not Rust body proofs.
<!-- /registry -->

<!-- registry:binding:7679e14f11acd2fe -->
<a id="binding-7679e14f11acd2fe"></a>

The serializer index is the actual selected T::serialize behavior interacting with Write, including writer-error handling, catch_unwind and owned cleanup; a finite fuel replay supplies evidence only for terminating executions.
<!-- /registry -->

<!-- registry:binding:a42f266e82ec9f63 -->
<a id="binding-a42f266e82ec9f63"></a>

Bind wordBits and checkedOverflow to the target usize width and overflow-check configuration. A checked overflow uses the selected panic callback before updating the count; unchecked addition wraps. Keep serializer IO error resources and external state.
<!-- /registry -->

<!-- registry:binding:421a7d13239ccda1 -->
<a id="binding-421a7d13239ccda1"></a>

Bind the actual complete input allocation and returned Cow::Borrowed slice at byte offset 56 with preserved provenance, contents and lifetime. No address storage allocation occurs; the numeric address in the pure model is an observation, not an ownership proof.
<!-- /registry -->

<!-- registry:binding:9d59b6137c60e939 -->
<a id="binding-9d59b6137c60e939"></a>

Bind the selected bincode decoder and owned Box<ErrorKind> destructor, including normal allocation, diagnostic resources, deallocation, unwind and terminal effects. map_err drops the error before returning InvalidAccountData. Successful decoding and the four-byte Uninitialized case do not allocate an error. The pure byte decoder is only a value facet.
<!-- /registry -->

<!-- registry:binding:72f98d8373dbe5e1 -->
<a id="binding-72f98d8373dbe5e1"></a>

Allocator allocation, reallocation and deallocation obey the GlobalAlloc no-unwind requirement of Rust. For errors reached by this fixed decoder, bind their normal owned-resource destruction; generic cleanup-unwind witnesses do not establish a source destructor unwind. Allocation failure follows the selected terminal policy.
<!-- /registry -->

<!-- registry:binding:885b1f50e60bedcb -->
<a id="binding-885b1f50e60bedcb"></a>

Source correctness remains an explicit assumed call interface. Bind exact emitted argument/result types, generic arguments, lifetimes, pointer provenance and current source ownership; no Rust implementation or SBF layout refinement is proved.
<!-- /registry -->

<!-- registry:binding:e16d15b95e89229f -->
<a id="binding-e16d15b95e89229f"></a>

This exact defining crate/version is registered for automatic candidate discovery. Its separately reviewed build profile and Rust binding remain required; this alias supplies no body proof or retained-route evidence.
<!-- /registry -->

<!-- registry:binding:939a0f8a1b615b3a -->
<a id="binding-939a0f8a1b615b3a"></a>

Interpret CpiContext, AccountInfo aliases, nested signer slices, owned vector/string/box resources and Result with actual source layouts and lifetimes. BuildReady constrains only reached constructor returns.
<!-- /registry -->

<!-- registry:binding:8ea6e053311768a9 -->
<a id="binding-8ea6e053311768a9"></a>

Admit only ProgramError variants present in the selected dependency release, retaining the current owned legacy Borsh String rather than only its numeric status.
<!-- /registry -->

<!-- registry:binding:79725b0208189d1c -->
<a id="binding-79725b0208189d1c"></a>

Target-unit dependency edges are source binding evidence, not target-layout equivalence. Ambiguous whole-build lookup stays unresolved; do not substitute a filtered build for an exact source-owned per-call dependency edge.
<!-- /registry -->

<!-- registry:binding:d3dcbfa680d90541 -->
<a id="binding-d3dcbfa680d90541"></a>

Bind current AccountInfo metadata, owner references, typed lamports/data cells and source record identities to the selected source arguments and lifetime. Equal Rc handles do not identify equal AccountInfo records. Source output codecs retain the input record identity or the fresh owned field as appropriate.
<!-- /registry -->

<!-- registry:binding:d57b4cd5d9cd5cfa -->
<a id="binding-d57b4cd5d9cd5cfa"></a>

The selected trait and primitive operations are explicit assumed interfaces for the actual source methods. Retain their actual returned, error, unwind and terminal effects; mathematical sample callbacks do not establish concrete callback or allocator success.
<!-- /registry -->

<!-- registry:binding:3ce052ba6dc22289 -->
<a id="binding-3ce052ba6dc22289"></a>

Bind the source panic policy, pointer width and physical layout separately. Solana cfg selection alone does not establish target-memory equivalence.
<!-- /registry -->

<!-- registry:binding:d36321e8c288593f -->
<a id="binding-d36321e8c288593f"></a>

Bind the source Error enum, actual String/Box operations and fixed builtin ProgramError injection. This source reference uses boxed Error storage. Legacy ProgramError values obey the selected release availability predicate and retain owned BorshIoError Strings; errors.programStrings lists exactly their owned String resources.
<!-- /registry -->

<!-- registry:binding:5c08b6f53fa5df2d -->
<a id="binding-5c08b6f53fa5df2d"></a>

Bind PayloadTypes.deserialize to the actual AccountDeserialize::try_deserialize_unchecked implementation of this call, including its discriminator checks or deliberate unchecked behavior, complete errors and state effects. Do not substitute an always-success decoder.
<!-- /registry -->

<!-- registry:binding:c42d54f89cb867a6 -->
<a id="binding-c42d54f89cb867a6"></a>

OptionalTypes.allowMissing is true exactly when the defining anchor-lang build enables allow-missing-optionals. Both source branches are represented; no unrelated derive/init-if-needed feature constraint is imposed.
<!-- /registry -->

<!-- registry:binding:f092c860a2393f1d -->
<a id="binding-f092c860a2393f1d"></a>

Bind PayloadTypes.deserialize to the actual AccountDeserialize::try_deserialize implementation of this call, including its discriminator checks or deliberate unchecked behavior, complete errors and state effects. Do not substitute an always-success decoder.
<!-- /registry -->

<!-- registry:binding:b57fed0af6329e80 -->
<a id="binding-b57fed0af6329e80"></a>

This source identity denotes the provided default implementation, not a user override. The unit Result representation is related to the actual source result.
<!-- /registry -->

<!-- registry:binding:625decc1cefdca14 -->
<a id="binding-625decc1cefdca14"></a>

Bind the actual checked try_deserialize callback and the lawful current-payload focus of the receiver; the source mode fixes owner checking and guard release relative to payload destruction.
<!-- /registry -->

<!-- registry:binding:2db78db6ef5614e1 -->
<a id="binding-2db78db6ef5614e1"></a>

Bind the source Error enum, actual String/Box operations and fixed builtin ProgramError injection. The facade fixes inline storage for 0.27 and boxed storage for later releases. Legacy ProgramError values obey the selected release availability predicate and retain owned BorshIoError Strings; errors.programStrings lists exactly their owned String resources.
<!-- /registry -->

<!-- registry:binding:591d954cc9feb4c8 -->
<a id="binding-591d954cc9feb4c8"></a>

Represent the stored source record reference and its legal returned reference permission; no data or owner read is imposed.
<!-- /registry -->

<!-- registry:binding:31125d2759b105b2 -->
<a id="binding-31125d2759b105b2"></a>

Bind Owner and associated discriminator, current owner/data storage, BpfWriter prefix mutation and actual checked guard. The payload layout is not inspected.
<!-- /registry -->

<!-- registry:binding:5a5fe323ce2fe23d -->
<a id="binding-5a5fe323ce2fe23d"></a>

Bind the reached io::Error::new(WriteZero, "failed to write whole buffer"), borrowed Result::unwrap formatting/panic, destruction of that same error owner, and double-unwind policy to their actual auxiliary effects and selected panic profile. The data guard remains held until error cleanup completes. A Rust binding must transfer a separate local error-ownership footprint through these primitive calls; no callback termination or library-body proof is supplied.
<!-- /registry -->

<!-- registry:binding:8fa75c78cbe2ffb2 -->
<a id="binding-8fa75c78cbe2ffb2"></a>

The associated discriminator, ZeroCopy byte size/alignment and checked-overflow/panic profile instantiate the mathematical index. Bind the actual acquired/mapped guard; never derive its identity from bytes or counters.
<!-- /registry -->

<!-- registry:binding:8b42335fdb02a1ef -->
<a id="binding-8b42335fdb02a1ef"></a>

Bind the mutable source slice and bump/realloc resources, the head record, associated discriminator, Owner callback and actual held data guard. Payload size/alignment is not inspected.
<!-- /registry -->

<!-- registry:binding:9a689cae46364eff -->
<a id="binding-9a689cae46364eff"></a>

Bind the Owner callback and current owner storage, actual error resources and the stored AccountInfo record reference. Neither payload layout nor discriminator is read.
<!-- /registry -->

<!-- registry:binding:01f446c1a31aea21 -->
<a id="binding-01f446c1a31aea21"></a>

The Sysvar callback receives the original source AccountInfo record and the selected trait implementation; discarded legacy ProgramError Strings are dropped after constructing the replacement Anchor error.
<!-- /registry -->

<!-- registry:binding:cc7613826bb60e52 -->
<a id="binding-cc7613826bb60e52"></a>

The API identity preserves this exact defining crate and reviewed version. Its applicability profile supplies the dynamic-dispatch, target and resolved-dependency conditions; source-name registration alone does not discharge them.
<!-- /registry -->

<!-- registry:binding:d715096aaf855717 -->
<a id="binding-d715096aaf855717"></a>

Ordinary dependency compilation with cfg(test) unset; no test-only extension enum variants.
<!-- /registry -->

<!-- registry:binding:971a9ce7a19fa561 -->
<a id="binding-971a9ce7a19fa561"></a>

Interpret the immutable source enum slice, actual Vec<&ExtensionType> empty/current/push/drop operations, the value projection and exact reached operands of its first-occurrence references, and the resolved S::SIZE_OF associated constant. The source primitive interpretation manages internal iterator/vector child borrowing and repays the original input region on continuing outcomes; equal addresses do not supply child access permission. The concrete Mint and Account bindings use 82 and 165 respectively. This method does not parse or destroy a base-state value.
<!-- /registry -->

<!-- registry:binding:91fcbbf990282b6f -->
<a id="binding-91fcbbf990282b6f"></a>

Bind the returned Pubkey bytes to the source ID and actual ABI.
<!-- /registry -->

<!-- registry:binding:0ade6b5645dc71a1 -->
<a id="binding-0ade6b5645dc71a1"></a>

A separate binding to the Rust implementation must establish the fresh-invocation and finite-address-space profile: explicit input and retained allocation graph, space for at most 128 bytes per account after that graph, and fresh physical outputs. These requirements do not prove the selected GlobalAlloc implementation or extension of an unrepresented arbitrary heap frame. See source-notes/entry-deserialize.md.
<!-- /registry -->

<!-- registry:binding:04b7c89022dbabb7 -->
<a id="binding-04b7c89022dbabb7"></a>

Bind actual pointer provenance, lifetimes, target integer and aggregate layouts, and source result representation separately. These contracts are assumed SDK interfaces, not Rust implementation proofs.
<!-- /registry -->

<!-- registry:binding:c22857d940544e9c -->
<a id="binding-c22857d940544e9c"></a>

The capacity is the actual BUFFER const argument. Retain initialized-prefix and full backing-storage representation, receiver identity and permissions.
<!-- /registry -->

<!-- registry:binding:75353d3818144d47 -->
<a id="binding-75353d3818144d47"></a>

Instantiate Log::write_with_args at the empty argument slice and the actual by-value destructor. The unsafe Log trait law requires a truthful initialized-byte count within the supplied tail and preserves its extent; source callback effects and cleanup remain explicit.
<!-- /registry -->

<!-- registry:binding:2bcee7d9be9f2c81 -->
<a id="binding-2bcee7d9be9f2c81"></a>

Use the 88-byte repr(C) RuntimeAccount header with separate low-nibble data and high-nibble lamports leases, initially FF. Duplicate AccountInfo pointers denote the same header and cells; the common guard ledger must represent the actual byte and live tokens.
<!-- /registry -->

<!-- registry:binding:ba004bf07d76abfb -->
<a id="binding-ba004bf07d76abfb"></a>

Interpret the generic target descriptor at the actual input and output types, including sized, slice and trait-object metadata. The source lease field and the mapped reference target are distinct; dereferencing reads current storage, never a saved copy.
<!-- /registry -->

<!-- registry:binding:bed8d41f4f7e6beb -->
<a id="binding-bed8d41f4f7e6beb"></a>

Bind the closure and captured-state effects to the universal CallbackFrame condition. ManuallyDrop is established before the call; an unwind does not execute the original guard destructor.
<!-- /registry -->

<!-- registry:binding:8f761522110cd8cc -->
<a id="binding-8f761522110cd8cc"></a>

Bind current/entry lengths and signed resize_delta to the actual loader allocation and 10240 spare bytes. Apply the separate arithmetic lemma to the i32 intermediates and bind zeroRange to the reached sol_memset_ destination after both header writes. Lamport leases do not restrict data resize.
<!-- /registry -->

<!-- registry:binding:f15ae3c683af93cd -->
<a id="binding-f15ae3c683af93cd"></a>

Bind the actual dynamic sol_log_ provider. Normal completion gives no UTF-8 validity or runtime success guarantee; the provider may terminate.
<!-- /registry -->

<!-- registry:binding:731a6fe39089b8a7 -->
<a id="binding-731a6fe39089b8a7"></a>

The model address is the borrowed source reference, with source field order separately interpreted.
<!-- /registry -->

<!-- registry:binding:00e2ec0455cb764c -->
<a id="binding-00e2ec0455cb764c"></a>

Instantiate the dedicated typed Clock provider and actual five-field C representation. Status-zero output must initialize a valid Clock; the pointer-valued host fallback and later generic sol_get_sysvar error mapping are outside this profile.
<!-- /registry -->

<!-- registry:binding:e446da9f7dfd35d4 -->
<a id="binding-e446da9f7dfd35d4"></a>

Use the actual SIZE const parameter and retain input array reference provenance, including zero-sized arrays.
<!-- /registry -->

<!-- registry:binding:6ae128044d9262fe -->
<a id="binding-6ae128044d9262fe"></a>

A Rust binding must establish the actual mutable slice receiver, nominal Self and result layouts, and every outcome of the actual unchecked callback at the same native state.
<!-- /registry -->

<!-- registry:binding:49f3244e0b0817b6 -->
<a id="binding-49f3244e0b0817b6"></a>

Only implementations inheriting this provided default are admitted. Generic indices do not certify a different or overriding Rust implementation.
<!-- /registry -->

<!-- registry:binding:8161a44a31a89b8a -->
<a id="binding-8161a44a31a89b8a"></a>

This identity is the generic Program<T: Id> implementation. The separate Program<()> specialization is not admitted by this source binding.
<!-- /registry -->

<!-- registry:binding:ccdce1908d62a564 -->
<a id="binding-ccdce1908d62a564"></a>

Represent the stored source reference and PhantomData exactly; cloning does not require a payload, discriminator, owner callback or borrow operation.
<!-- /registry -->

<!-- registry:binding:7fbbd71f025e07c4 -->
<a id="binding-7fbbd71f025e07c4"></a>

Bind the actual shared lamports/data cells, current owner and complete resize backing, original/current length words, and the owned destination Rc fields. No Owner, discriminator or payload-layout operation is invoked.
<!-- /registry -->

<!-- registry:binding:c47dd6f1c4622b17 -->
<a id="binding-c47dd6f1c4622b17"></a>

Interpret the immutable source enum slice and the reached Vec empty/push/drop operations, retaining each finite unwind or terminal exit and the same live result owner. This method has no base parser or base destructor.
<!-- /registry -->

<!-- registry:binding:3eeb3b16ebf78c63 -->
<a id="binding-3eeb3b16ebf78c63"></a>

The unqualified build remains partial with no automatic profile. CpiLegacyAdapter separately admits actual native source fields and ordered preflight; successful preflight additionally requires CpiLegacyFields.DecodedRequest and the existing runtime CopybackAdmission. Local borrow-error returns require neither runtime condition. The empty-slice consistency instance retains real allocated Vec buffers.
<!-- /registry -->

<!-- registry:binding:2734a87244893ad2 -->
<a id="binding-2734a87244893ad2"></a>

Preserve the legacy four-variant StakeState representation and every copied integer, key and binary64 bit. No decoder, float validation or allocation is performed.
<!-- /registry -->

<!-- registry:binding:0bc30535466a8072 -->
<a id="binding-0bc30535466a8072"></a>

Resolve Self::unpack_unchecked, Self::is_initialized and Self drop for the actual type, with its complete state, error (including owned BorshIoError payload), unwind and terminal representations. Use defaultUnchecked only if source resolution selects that provided method; the generic Pack method does not impose LEN itself.
<!-- /registry -->

<!-- registry:binding:68eaaf680c94cf24 -->
<a id="binding-68eaaf680c94cf24"></a>

Interpret the index providers as the actual metadata vectors, bincode bytes, outer fixed array/vector storage, selected allocator, panic strategy and destructors, retaining aliases, caller ownership and every callback state transition.
<!-- /registry -->

<!-- registry:binding:cbbf6d1458a6671e -->
<a id="binding-cbbf6d1458a6671e"></a>

Bincode framing uses the reviewed fixed bytes, while size/serialize, byte buffer allocation, metadata push, outer allocation and cleanup effects remain indexed interfaces. The emitted instructions do not execute CPI.
<!-- /registry -->
