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
# sBPF instruction-set semantics

An exploratory Lean port of the Isabelle/HOL formalisation of the Solana eBPF
instruction set by Yuan et al. (OOPSLA 2025): machine words, syntax, decoder,
memory, interpreter and verifier. No theorem connects this machine model to
`Solanalib.Runtime`. See the [package guide](../README.md).
-/
