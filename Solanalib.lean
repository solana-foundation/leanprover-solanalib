/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType
import Solanalib.SBPF.Decoder
import Solanalib.SBPF.Interpreter
import Solanalib.SBPF.Memory
import Solanalib.SBPF.State
import Solanalib.SBPF.Syntax
import Solanalib.SBPF.Value
import Solanalib.SBPF.Verifier

/-!
![Solanalib][banner]

[banner]: https://github.com/solana-foundation/leanprover-solanalib/raw/main/docs/assets/banner-github-light.png

# Solanalib

A library of formal models and verified results for Solana programs in Lean 4.

Solanalib provides reusable models of the Solana runtime and of the Rust crates
Solana programs are built on, together with theorems about their behaviour.
This root library holds the model of the **sBPF instruction set** that deployed
bytecode runs on; the runtime, contract and crate models are separate libraries
of the same package.

The intent is that downstream verification work on Anchor or Pinocchio
programs can reuse these definitions rather than redefining them per project.

## Organisation

Modules are organised by Solana concept, not by framework. Framework-specific
results (Anchor account validation, Pinocchio entrypoint patterns, …) layer on
top of the core primitives and live in their own subdirectories.

* `Solanalib.Runtime`    — Solana public keys, accounts, instructions and execution,
  including conservation for the checked System transfer path.
* `Solanalib.Contracts`  — the shared contract vocabulary.
* `Solanalib.Specs`      — contracts for SDK and framework crates.
* `Solanalib.SBPF`       — the sBPF ISA semantics (machine layer).
-/
