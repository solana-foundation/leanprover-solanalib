/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Runner

/-! Synthetic runner controls only; this fixture makes no SDK conformance claim. -/

open SolanalibTest.Conformance.Library Lean

namespace SolanalibTest.Conformance.Selection

def selectedChecker : Checker where
  function := "fixture::read"
  generics := [("T", "u64")]
  reference := "synthetic selected checker"
  decides := ["synthetic"]
  check := fun record => do
    let result ← (← field record.outcome "result").getNat?
    pure ⟨result == 7, toJson (7 : Nat)⟩

end SolanalibTest.Conformance.Selection

def main (args : List String) : IO UInt32 :=
  runMain [("selection_fixture", [SolanalibTest.Conformance.Selection.selectedChecker])] args
