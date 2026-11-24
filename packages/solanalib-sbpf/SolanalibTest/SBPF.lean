/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.SBPF.DecoderTest
import SolanalibTest.SBPF.InterpreterTest
import SolanalibTest.SBPF.LiftTest
import SolanalibTest.SBPF.MemoryTest
import SolanalibTest.SBPF.SyntaxTest
import SolanalibTest.SBPF.VerifierTest

/-!
# sBPF regressions

Decoder, memory, syntax, interpreter and verifier checks for the exploratory
sBPF model. The interpreter and lifting tests evaluate with `native_decide`.
-/
