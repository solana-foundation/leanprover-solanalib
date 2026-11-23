# Anchor System wrappers

This note covers `system_program::{allocate, assign, create_account, transfer}`
using the 0.32.1 reference family. The
[source registry](../source-map/libraries.json) records inspected Anchor Lang
0.32.0–0.32.3 and declares `>=0.32.0, <0.33.0` under the per-function
constructor, serialization, AccountInfo, Pubkey and legacy ProgramError
assumptions.

The note also covers the exact 1.1.2 reference families for the same four
wrappers. Their catalog profiles assume the unit-Borsh error, copied-program
and cleanup behavior through `[1.1.2, 1.2.1)`, before the new Solana provider
cohorts; concrete source bindings and native reference versions stay exact.
`System::id` retains its separate 0.32.1 reference selection; the whole
System module is not registered.

The 1.0.2 additions select the same four System wrappers with their own
copied-program and unit-Borsh profiles, preserving their exact source
and dependency references. Their 1.0 compatibility assumptions are
separate from both existing ranges.

The 0.29.0 additions select those four wrappers with their own owned-program,
legacy ProgramError and constructor profiles in `[0.29.0, 0.30.0)`. Their
source and dependency references remain exact; `System::id` keeps its
separate 0.32.1 selection.

The 0.27.0 additions select the same four wrappers with separate
`[0.27.0, 0.28.0)` profiles. Their owned program AccountInfo, cloned
invocation fields, inline errors and exact constructor references remain
distinct from the later families.

The four wrapper `_contract` declarations and `System::id` live together in
[`Solanalib.Specs.AnchorLang.system_program`](../Solanalib/Specs/AnchorLang/system_program.lean).

`System::id` was inspected at Anchor Lang 0.32.0 through 0.32.3 and
declares `0.32.0 ≤ v < 0.33.0` for the same 32-byte constant copy. Its
exact source/native reference remains 0.32.1. The four wrappers retain their
existing construction, dependency, opaque-CPI and cleanup profiles.

Each wrapper first constructs the ordinary System instruction, then moves its
account fields into the temporary invocation array. Instruction metadata is
independent of the input AccountInfo flags. The program of the context and remaining
accounts do not change the fixed System program ID or the invocation list.

| Wrapper | Instruction data, in order | Ordered metadata | Invocation accounts |
| --- | --- | --- | --- |
| `allocate` | tag 8, space | account: signer, writable | account |
| `assign` | tag 1, owner | account: signer, writable | account |
| `create_account` | tag 0, lamports, space, owner | from: signer, writable; to: signer, writable | from, to |
| `transfer` | tag 2, lamports | from: signer, writable; to: writable | from, to |

Tags are bincode little-endian `u32`; lamports and space are little-endian
`u64`; an owner contributes all 32 bytes. Constructor providers retain the
actual metadata and data allocations, serialization and partial cleanup.
`BuildReady` requires a successfully reached constructor return to expose its
current vectors. It requires neither construction success nor an invocation
outcome. Nested signer seeds preserve order, duplicates, empty groups and
empty seeds.

The complete `invoke_signed` signature is an explicit opaque provider over the
wrapper state. Its account effects, returned errors, unwind and terminal exits
remain visible. The wrapper converts a returned ProgramError to
ProgramErrorWithOrigin with origin and compared values initialized to `None`.
The Anchor error stores that payload inline at 0.27.0 and in a box in the
later releases. The 0.27.0, 0.29.0 and 0.32.1 ProgramErrors retain the owned
`BorshIoError(String)`; numeric status alone is insufficient. Their available
variants must match the actual dependency release. In 1.0.2 and 1.1.2 the Borsh variant is unit. Conversion
is defined in Anchor Lang 1.0.2 and reexported from the defining
`anchor-lang-error` 1.1.2 crate.

Edition-2021 temporary scopes matter. After invocation and error conversion,
cleanup drops instruction metadata, instruction data, the tail-expression
account array, then the remaining-accounts vector. The 0.27.0, 0.29.0 and
0.32.1 contexts also own a program AccountInfo, which drops last. The 1.0.2 and
1.1.2 contexts contain a copied program key instead. Each AccountInfo drops its lamports Rc before its
data Rc. Aliases retain separate owner occurrences, and destructors use current
resource contents. Construction unwind cleans the intact context; invocation
unwind skips error conversion and cleans the moved array. Terminal exits stop
at the reached provider, with no invented after-state or subsequent cleanup.

`System::id` returns the fixed 32-byte zero key without reading account state.
This value operation does not supply a CPI outcome.

The 0.27.0 and 0.29.0 profiles select the System constructors in
`solana-program` 1.15.2 and 1.18.26 respectively. The reviewed 1.0.2 and 1.1.2
direct source edges select `solana-system-interface` 2.0.0 and `solana-pubkey` 3.0.0. Other versions can coexist as separate target units;
those exact call edges do not make a whole ambiguous build eligible.

The [binding obligations](../BINDINGS.md) apply, including the shared
error-construction allocation boundary. Exact constructor and invocation
providers, layouts, source ownership and callback frames remain explicit.
A build containing multiple candidate dependency versions does not identify
the provider used at this call. Keep automatic whole-build rejection when the
evidence is ambiguous; a filtered dependency list cannot replace the actual
source edge. Mathematical references and source comparisons do not prove an
invocation body, SDK body, allocator or application execution.

The [mathematical tests](../SolanalibTest/Specs/Core/AnchorSystem.lean) exercise
exact wire fields, alias occurrences, current-resource reads, String-bearing
errors, unwind, terminal exits and providers with no finite exit. A source binding must establish the specified resource fragments. Source entry selection, argument/result ABI agreement, representation coverage and implementation correctness remain separate obligations; the mathematical tests do not prove an SDK implementation.

The `AnchorSystem` conformance family selects the four wrapper keys and
`System::id`, covering all 31 observations in `anchor_system_0_32_1`. Its selected negative controls corrupt requests,
aliases, errors, provider effects, cleanup and terminal observations at the
same 0.32.1 rows. From the repository root, reproduce the committed replay and
separately record the pinned native driver with the existing runner:

```sh
python3.12 -B tools/library-conformance/run.py --model-only --registered-checkers --family AnchorSystem --evidence-dir /tmp/slc-anchor-system
python3.12 -B tools/library-conformance/run.py --record --offline --twice --no-write-corpus --driver anchor-system-0-32-1 --evidence-dir /tmp/slc-anchor-system-native
```

The native driver projects the exact four wrapper spans and scripts the whole
invocation signature. Its authenticated `dev`/unwind, x86-64, Solana-cfg build
does not execute an invocation body or establish sBPF layout equivalence.
