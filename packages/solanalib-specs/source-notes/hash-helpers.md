# Hash value and selected SHA-256 wrapper models

The `Hash::to_bytes` value-copy contract also covers solana-hash 4.3.0 and
4.4.0. All three releases use the same transparent 32-byte representation and
return `self.0`, with no callees or feature branch in this function. Separate
versioned roots instantiate the shared contract. See the
[version review](../VERSION_COMPATIBILITY.md#hash-to-bytes); this does not extend
the version scope of any hashing operation.

These are mathematical function models. Their reference and execution witnesses
prove consistency of the stated models, without a Rust implementation, compiler,
memory or cryptographic implementation theorem. The
[source registry](../source-map.json) records the exact `Hash::to_bytes` and
`hashv` models and their source anchors.

The ordinary sources are pinned separately:

| Package | Source | Revision | SHA-256 |
| --- | --- | --- | --- |
| solana-hash 4.5.0 | `hash/src/lib.rs` | `e33d4eacfc252f0f8bd82ca208c53db8e93f0e24` | `321fbfcad19137ca7bbc9ca0f32c0748fc9679db0a1c44e79e51962d3789286d` |
| solana-sha256-hasher 3.1.0 | `sha256-hasher/src/lib.rs` | `5da94053da7b81dcd04c62ff4df7eb6bfc20a398` | `10388c2d6943cfbdca396e653e83507b5b6112a84933e754744dcfb06dee3df2` |
| solana-define-syscall 4.0.1 | `define-syscall/src/definitions.rs` | `6fde52632b91530f2492abd9e8f6062509173a75` | `958fc42c0c792cd01d20fbeb12faad1e01220dc2f785e55c9ccf60625f3a99d5` |

The reviewed hasher 3.1.0 dependency profile uses Hash 4.5.0 and
define-syscall 4.0.1. These exact source revisions define the review scope;
other resolutions of the dependency ranges require their own correspondence.
The source audit checks each pinned file without rebuilding Rust packages.

## Exact hash value

[`Hash::to_bytes`](https://github.com/anza-xyz/solana-sdk/blob/e33d4eacfc252f0f8bd82ca208c53db8e93f0e24/hash/src/lib.rs#L167)
returns `self.0`. The same file defines `HASH_BYTES = 32` at line 34 and the
transparent array wrapper at lines 58–59. The common `Hash.Value` therefore
contains exactly 32 bytes, separately from account addresses. `Hash.toArray`
preserves the existing byte order and width, with inverse and injectivity
theorems. The versioned `to_bytes_contract` has a total reference and a closed
satisfiable input. The nonuniform test value detects a reversed copy.

This is a pure value operation. Binding a Rust shared receiver to that value,
its array layout and its legal read permissions remains a consumer obligation.

## Selected `hashv`

[`hashv`](https://github.com/anza-xyz/solana-sdk/blob/5da94053da7b81dcd04c62ff4df7eb6bfc20a398/sha256-hasher/src/lib.rs#L44)
uses the syscall branch when either `target_os = "solana"` or
`target_arch = "bpf"`. Lines 64–72 create an uninitialized 32-byte destination,
pass the original slice-of-slices pointer and its count, ignore the `u64` status of the syscall, then call `assume_init`. The syscall declaration is at
[`definitions.rs:21`](https://github.com/anza-xyz/solana-sdk/blob/6fde52632b91530f2492abd9e8f6062509173a75/define-syscall/src/definitions.rs#L21).
The host SHA2 and host no-feature panic branches are outside this selected-target
contract. Merely selecting a source cfg does not establish an SBF memory layout.

`Hash.Syscall.request` retains the ordered slice boundaries, empty slices and
duplicates. It records the forwarded `u64` count and the initially uninitialized
destination. `request_count` separately uses an outer count bound to prove that
the forwarded word equals the mathematical count; the family does not impose
that bound. Individual source slice
lengths, pointer arrays, pointer width, provenance,
alignment, slice validity, source and destination permissions, and VM translation
still require a physical representation binding.

The provider relation supplies its actual finite outcome. Ordinary replies keep
status and initialized output separate; callback state can include partial writes.
`EveryReturnInitialized` is a mandatory precondition on **every normal reply**,
including nonzero status. One uninitialized normal branch invalidates the
precondition even if another branch initialized the destination. The wrapper then
returns exactly the written hash. `initialized_return_has_run` proves that this
precondition retains every normal provider return; the finite-exit factor also
forwards every unwind with its state and every terminal reason. An uninitialized
provider return lies outside the safe model domain and is not converted into an
ordinary error or silently treated as a valid execution.

`NormalHashAgreement` separately states that each normally returned hash agrees
with the supplied `CryptoPrimitives.sha256` of the canonical model on the concatenated
bytes. `returned_hash_projection` uses precisely that premise. The reference
family itself preserves provider behavior and does not prove the SHA-256
algorithm, supply the agreement premise, assert output access, or guarantee
runtime admission. `canonical_hash_reply` exposes the existing canonical count
limit and digest projection independently of source provider interpretation.
The constant digest used by consistency controls is only a mathematical sample.

Controls cover a nonempty repeated input with an empty slice, a nonzero initialized
return, a mixed initialized/uninitialized provider, unwind state, terminal runtime
failure, count-limit success and failure, and the fact that initialized transport
alone cannot prove the optional cryptographic agreement. All model relations are
partial-correctness descriptions of finite exits; their closed sample executions
do not assert termination for every provider.

## Registered source reviews

The crate records reference the following exact clauses by their stable identifiers.

<!-- registry:review:36a587963d1dc0f8 -->
<a id="review-36a587963d1dc0f8"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Represent the exact 32-byte array separately from account addresses; copying preserves every byte, with inverse and injectivity laws.

In every listed release, Hash is repr(transparent) over [u8; 32], HASH_BYTES is 32, and to_bytes(&self) returns self.0. The function has no callees, allocation, error or configuration branch. The unrelated Hash trait implementation and feature-gated derives changed; they are not used by to_bytes. All versions share the entire original value-copy contract and its legal-access and representation obligations. Other hash methods and versions outside this window have not been assessed.
<!-- /registry -->

<!-- registry:review:fb64f1077c204b66 -->
<a id="review-fb64f1077c204b66"></a>

Typed selections collect the exact existing model families at every index; nongeneric contracts use a singleton embedding. A fixed operation assignment is shared by subset restriction and union. Tagged catalog composition retains native model state types, identities and scope. Each member lists the Rust identities derived from its APIs: source crate name and version, called item path and registered implementation path. Generated reference_spec theorems consume the already registered closed reference witnesses. Conditional clients derive read-after-write and mapped-guard cleanup from requested assumptions, including a real Err callback effect; negative controls reject incorrect observations and a mismatched generic index. Per-function applicability profiles separate exact reviewed references from declared registry compatibility ranges, retaining source origins, behavior-changing build constraints and known exceptions. Range eligibility assumes preservation of the reference operation and its relevant dependency behavior; it does not turn the exact test lockfile into a caller requirement. forBuild preserves the entire family and its indices while selecting eligible source identities; reexports use their actual defining dependency, and source-less or unregistered observations stay unbound. The independent matcher requires known constrained facts and does not infer Cargo resolution or implementation correctness. The common definitions live in Solanalib.Contracts; these modules publicly import them for use throughout the SDK models.

Forward the ordered slice collection and uninitialized destination; require every normal provider return to initialize all bytes, including nonzero status, then return those bytes. Preserve abnormal exits and state. Keep primitive and canonical count laws separate.

Versioned aggregate of the exact registered callable utility models; coverage is the listed API subset.

Generated typed capability catalog retains every complete registered family, exact Rust identity, source/build profile and closed reference witness.

The selected Solana branch creates [0;32], passes that initialized output and the exact ordered input slices and count to sol_sha256, ignores its returned integer status and wraps the actual final 32 bytes as Hash. A normal provider reply may leave some or all bytes unchanged; no all-normal full-write premise is imposed. hash(val) performs exactly hashv(&[val]), including one empty slice for empty input. Host SHA2 is a different profile and is not admitted here.

The versioned hash wrapper reindexes the reviewed hashv source family at one exact slice.
<!-- /registry -->

<!-- registry:review:728de313fd1dc37e -->
<a id="review-728de313fd1dc37e"></a>

In every listed release, Hash is repr(transparent) over [u8; 32], HASH_BYTES is 32, and to_bytes(&self) returns self.0. The function has no callees, allocation, error or configuration branch. The unrelated Hash trait implementation and feature-gated derives changed; they are not used by to_bytes. All versions share the entire original value-copy contract and its legal-access and representation obligations. Other hash methods and versions outside this window have not been assessed.
<!-- /registry -->

<!-- registry:review:655e626ff7893c13 -->
<a id="review-655e626ff7893c13"></a>

Every direct real release has HASH_BYTES=32, transparent [u8;32] storage and returns self.0 without callees or cfg branches. Releases through 3.0.0 consume self (3.0.0 adds const); 4.x borrow &self. Both realize the unchanged pure value-copy contract, while their physical receiver bindings differ. 3.1.0 reexports Hash from solana-hash ^4.0, whose entire published 4.0.0–4.7.0 resolution set is reviewed. 0.0.1 is a placeholder with no Hash API.
<!-- /registry -->

<!-- registry:review:00094bae31eaa266 -->
<a id="review-00094bae31eaa266"></a>

3.1.0 builds MaybeUninit<[u8;32]>, forwards the original slice-array pointer/count, ignores status and returns the provider-initialized output. The selected request records uninitialized output (none), with all provider finite exits/effects retained. Every earlier real hashv initializes [0;32], so its initial provider request is different; an arbitrary provider can distinguish that initial request while fully writing every normal reply. Equal digest samples or a projection erasing the initial request cannot establish equality of the complete family. Legacy no-write returns are outside EveryReturnInitialized and are not claimed as premise-satisfying counterexamples. Only 3.1.0 also selects this branch under BPF without Solana OS. 0.0.1 has no hashv API.
<!-- /registry -->

<!-- registry:review:d67302287a6118cb -->
<a id="review-d67302287a6118cb"></a>

The selected Solana branch creates [0;32], passes that initialized output and the exact ordered input slices and count to sol_sha256, ignores its returned integer status and wraps the actual final 32 bytes as Hash. A normal provider reply may leave some or all bytes unchanged; no all-normal full-write premise is imposed. hash(val) performs exactly hashv(&[val]), including one empty slice for empty input. Host SHA2 is a different profile and is not admitted here. The declared compatible range assumes preservation of the zero-filled 32-byte destination, ordered slice descriptors, ignored returned status, complete final buffer and provider state or exceptional exit; the selected Hash provider preserves every returned byte.
<!-- /registry -->

<!-- registry:review:60050e25608b2520 -->
<a id="review-60050e25608b2520"></a>

The selected Solana branch creates [0;32], passes that initialized output and the exact ordered input slices and count to sol_sha256, ignores its returned integer status and wraps the actual final 32 bytes as Hash. A normal provider reply may leave some or all bytes unchanged; no all-normal full-write premise is imposed. hash(val) performs exactly hashv(&[val]), including one empty slice for empty input. Host SHA2 is a different profile and is not admitted here. The declared compatible range assumes preservation of the zero-filled 32-byte destination, ordered slice descriptors, ignored returned status, complete final buffer and provider state or exceptional exit; the selected Hash provider preserves every returned byte. The hash wrapper keeps exactly one input slice, including an empty one.
<!-- /registry -->

<!-- registry:review:57cded8fdf371ffd -->
<a id="review-57cded8fdf371ffd"></a>

Preserve hashv(&[val]), including a singleton empty slice, the uninitialized output request, ignored status after every normal reply initializes all 32 bytes, and all provider effects/exits. Earlier hashv starts from zeroed output, which a valid provider can distinguish. Host SHA2 and the host no-feature panic remain outside both syscall profiles. The declared range is a complete-operation preservation assumption; inspected releases, native runs, exact ABI observations and source-call implementation obligations remain separate.
<!-- /registry -->
