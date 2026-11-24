/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Interpreter

/-!
# Regression test for `spinoza lift` output

Mirrors the `BpfBin` literal format emitted by `spinoza lift` (`<byte>#8` list)
and runs it through `bpfInterp`, confirming the lift → decode → execute path
composes: the emitted bytes decode and evaluate to the expected result.
-/

namespace SolanalibTest.SBPF.Lift

open Solanalib.SBPF

/-- A lifted `mov64 r0, 5; exit`, in the exact shape `spinoza lift` emits. -/
def programBytes : BpfBin :=
  [183#8, 0#8, 0#8, 0#8, 5#8, 0#8, 0#8, 0#8,
   149#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]

/-- The lifted bytes decode and run to `5`. -/
example :
    (match bpfInterp 8 programBytes
        (.ok 0 initRegMap initMem initStackState .v2 initFuncMap 0 8) true 0x100000000 with
      | .success v => v
      | _ => 0) = 5 := by native_decide

end SolanalibTest.SBPF.Lift
