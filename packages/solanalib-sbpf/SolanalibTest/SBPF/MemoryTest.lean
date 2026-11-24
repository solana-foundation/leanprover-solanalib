/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.Memory

/-!
# Regression tests for `Solanalib.SBPF.Memory`

Pins the store-then-load round-trip at each access width and the tag/width
mismatch behaviour of `storev`.
-/

namespace SolanalibTest.SBPF.Memory

open Solanalib.SBPF

/-- Store-then-load round-trips at the given address, for each width. -/
example :
    (storev .m8 initMem 0x1000 (.vbyte 0x2a)).bind (fun m => loadv .m8 m 0x1000)
      = some (.vbyte 0x2a) := by decide

example :
    (storev .m16 initMem 0x1000 (.vshort 0xBEEF)).bind (fun m => loadv .m16 m 0x1000)
      = some (.vshort 0xBEEF) := by decide

example :
    (storev .m32 initMem 0x1000 (.vint 0xDEADBEEF)).bind (fun m => loadv .m32 m 0x1000)
      = some (.vint 0xDEADBEEF) := by decide

example :
    (storev .m64 initMem 0x20 (.vlong 0x0123456789ABCDEF)).bind
        (fun m => loadv .m64 m 0x20)
      = some (.vlong 0x0123456789ABCDEF) := by decide

/-- A load from empty memory is unmapped. -/
example : (loadv .m32 initMem 0x1000).isNone := by decide

/-- Storing a value whose tag does not match the access width fails. -/
example : (storev .m32 initMem 0 (.vlong 5)).isNone := by decide

end SolanalibTest.SBPF.Memory
