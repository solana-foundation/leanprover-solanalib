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
