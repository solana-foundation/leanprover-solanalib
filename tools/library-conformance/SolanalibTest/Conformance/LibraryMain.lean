/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Registry
import SolanalibTest.Conformance.Library.Runner

/-!
# `solanalib-library-conformance CORPUS_DIRECTORY [--only CORPUS,...]`

Runs `SolanalibTest.Conformance.Library.runMain` over the generated registry of every family
module (`SolanalibTest/Conformance/Library/Families/*.lean`).
-/

def main (args : List String) : IO UInt32 :=
  SolanalibTest.Conformance.Library.runMain SolanalibTest.Conformance.Library.registry args
