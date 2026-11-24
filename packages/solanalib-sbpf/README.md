# sBPF instruction-set semantics (exploration)

This package is an exploration. It is a Lean port of the Isabelle/HOL formalisation of the Solana eBPF (sBPF) instruction set from [*A Complete Formal Semantics of eBPF Instruction Set Architecture for Solana*](https://dl.acm.org/doi/10.1145/3720414) (Yuan et al., OOPSLA 2025). It is kept apart from the runtime, contract and crate models, and nothing in those libraries depends on it.

Treat it as a starting point for work on deployed bytecode, not as a reviewed model:

- No theorem connects `Solanalib.SBPF` to `Solanalib.Runtime`. The [gap index](../../docs/model-gaps.md) records this as `execution:sbpf-runtime`.
- It has no source-correspondence registry and no recorded native observations. The standards in [CONTRIBUTING.md](../../CONTRIBUTING.md) for the model packages do not yet apply here.
- Its declarations depend only on `propext`, `Classical.choice` and `Quot.sound`, which the [axiom audit](SolanalibTest/SBPF/AxiomAudit.lean) checks when `just test-sbpf` builds it. The audit also rejects `implemented_by`, `extern`, `partial`, `unsafe` and `opaque` in the model, so `sbpf-oracle` runs the interpreter the theorems describe. The interpreter and lifting regressions evaluate with `decide +kernel`, so they do not trust the Lean compiler.
- The x86-64 JIT of the paper is not ported.
- Names, layout and statements may change, and the package is left out of the generated documentation site.

## Contents

| Module | Contents |
| --- | --- |
| [CommType](Solanalib/SBPF/CommType.lean) | `BitVec` machine words and little-endian byte conversion. |
| [Syntax](Solanalib/SBPF/Syntax.lean) | Registers, operations, the 22 instruction forms and the sBPF version. |
| [Value](Solanalib/SBPF/Value.lean), [Memory](Solanalib/SBPF/Memory.lean) | Memory values, byte-addressed memory, `loadv` and `storev`. |
| [Decoder](Solanalib/SBPF/Decoder.lean) | Bytecode to instructions, over the full opcode table. |
| [State](Solanalib/SBPF/State.lean) | Registers, call stack and the result state. |
| [Interpreter](Solanalib/SBPF/Interpreter.lean) | `step` and the fuel-bounded `bpfInterp`. |
| [Verifier](Solanalib/SBPF/Verifier.lean) | `verifyInstr` and `step_ne_err`: an instruction accepted by the verifier does not step to the error state (Lemma 6.4 of the paper). |

The machine words are bit-precise `BitVec` values, unlike the `Nat` balances of the runtime model, because signed division, sign extension and shifts are part of what the bytecode means.

## Use and test

Import `Solanalib.SBPF`, or one module such as `Solanalib.SBPF.Interpreter`. From the repository root:

```sh
just test-sbpf
```

This builds the library, the [regressions](SolanalibTest/SBPF.lean) and `sbpf-oracle` with warnings as errors. [`sbpf-oracle`](SolanalibTest/SBPFOracle.lean) is a command-line front end to `bpfInterp`: it reads one test vector per line and prints the result, so that the Lean interpreter can be compared with an external sBPF virtual machine. Its module description gives the input format.

The sources use Lean core and Std only.
