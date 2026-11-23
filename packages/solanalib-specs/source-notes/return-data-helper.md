# Program return-data wrapper model

This mathematical function model covers
`solana_program::program::set_return_data` in solana-program 4.0.0. Its closed
reference, satisfiability and execution witnesses concern the model; Rust body,
compiler, memory and runtime-provider correspondence remain open.

The ordinary sources are pinned separately:

| Package | Source | Revision | SHA-256 |
| --- | --- | --- | --- |
| solana-program 4.0.0 | `program/src/program.rs` | `12b63164cc1854b798362190583de5d1f2fe8091` | `8cbc87ca75b5fb67c3dbdcae53144d77a5a3dcd9e983e0d1e19b7c3434b35e6b` |
| solana-cpi 3.1.0 | `cpi/src/lib.rs` | `a8ef5986f7e2178b020b49ca47ed05e39712d08a` | `65a38d3dc33ad069186c1c8d8b618264d0e41bb5c696efa4b89e3b07e1f538de` |
| solana-define-syscall 4.0.1 | `define-syscall/src/definitions.rs` | `6fde52632b91530f2492abd9e8f6062509173a75` | `958fc42c0c792cd01d20fbeb12faad1e01220dc2f785e55c9ccf60625f3a99d5` |

The reviewed profile follows the call in solana-program 4.0.0 through
solana-cpi 3.1.0 to define-syscall 4.0.1 for this return-data helper. That chain
must be distinguished from the direct define-syscall dependency of program 4.0.0.
The [source registry](../source-map.json) pins the supporting files and anchors.
Only ordinary return-data helpers and the syscall signature are reviewed here;
invocation bodies remain opaque.

[`program.rs:103–111`](https://github.com/anza-xyz/solana-sdk/blob/12b63164cc1854b798362190583de5d1f2fe8091/program/src/program.rs#L103)
dispatches to `solana_cpi::set_return_data(data)` under `target_os = "solana"`;
other targets call the overridable program stub. A BPF architecture alone does not
select the Solana path. The selected
[`cpi/src/lib.rs:340–345`](https://github.com/anza-xyz/solana-sdk/blob/a8ef5986f7e2178b020b49ca47ed05e39712d08a/cpi/src/lib.rs#L340)
passes the data pointer and `data.len() as u64` to the
[`void syscall`](https://github.com/anza-xyz/solana-sdk/blob/6fde52632b91530f2492abd9e8f6062509173a75/define-syscall/src/definitions.rs#L8).
Neither wrapper checks `MAX_RETURN_DATA`, truncates the payload, or converts a
status to a source `Result`.

The common model retains the selected target, complete bytes and the Solana
length word in `ReturnData.Request`. The family imposes no length precondition;
`length_exact` separately proves equality of the forwarded word and mathematical
length when that length fits in 64 bits. The host request retains its own identity
and has no implicit canonical syscall interpretation. A caller supplies the callee or stub
relation, including every normal return, unwind with its actual state, and
terminal reason. Provider memory accesses, compute charges, output visibility,
and host override behavior are not synthesized by the wrapper.

`ReturnData.canonical_step` separately exposes the canonical runtime provider
rule: payloads longer than 1,024 bytes fail with `ProgramFailedToComplete`;
accepted bytes are tagged with the key of the executing program and replace return
data, preserving the rest of the modeled invocation state. This is a theorem
about `Solanalib.Runtime.sysStep`, not an assertion that every supplied provider is that
runtime. Binding it to a source provider still requires byte-slice translation,
legal access, target selection, error correspondence and compute admission.

The controls keep these two rules distinct: a recording provider receives and
returns normally from a complete 1,025-byte payload, while the canonical runtime
rejects that same payload and accepts the exact 1,024-byte limit. Other controls
check explicit host dispatch, unwind effects, terminal failure and forwarding an
empty slice. The closed reference execution establishes model nonvacuity without
asserting liveness or validator success for arbitrary providers.
