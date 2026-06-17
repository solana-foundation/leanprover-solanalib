/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Account.Basic
import Solanalib.Account.Transfer
import Solanalib.Finance.CompoundInterest
import Solanalib.Finance.Decay
import Solanalib.Finance.Growth
import Solanalib.Finance.LinearDecay
import Solanalib.Finance.MonotoneSequence
import Solanalib.Finance.WithdrawalCap
import Solanalib.Instruction.Basic
import Solanalib.Numeric.Fraction
import Solanalib.Primitives.Lamports
import Solanalib.Primitives.Pubkey
import Solanalib.Primitives.Time
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

Solanalib provides reusable type-level models of Solana primitives — lamports,
accounts, instructions, programs — together with theorems about their
behaviour. It also models the **sBPF instruction set** that deployed bytecode
actually runs on, giving a single Lean library that spans both the high-level
domain shapes and the machine those shapes ultimately compile down to.

The intent is that downstream verification work on Anchor or Pinocchio
programs can reuse these definitions rather than redefining them per project.

## Organisation

Modules are organised by Solana concept, not by framework. Framework-specific
results (Anchor account validation, Pinocchio entrypoint patterns, …) layer on
top of the core primitives and live in their own subdirectories.

* `Solanalib.Primitives` — atomic on-chain types (`Pubkey`, `Lamports`, `Timestamp`).
* `Solanalib.Numeric`    — fixed-point arithmetic (`Fraction`, Q68.60).
* `Solanalib.Account`    — the account model and operations over it.
* `Solanalib.Instruction` — instruction + account-meta shapes.
* `Solanalib.Finance`    — domain abstractions: decay, growth, compounding, caps.
* `Solanalib.SBPF`       — the sBPF ISA semantics (machine layer).
-/
