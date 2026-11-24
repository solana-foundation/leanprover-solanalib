/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType
import Solanalib.SBPF.Syntax

/-!
# Regression tests for `Solanalib.SBPF` syntax and machine words

Pins the data-layer behaviour ported from `rBPFCommType.thy` / `rBPFSyntax.thy`:
the register ↔ 4-bit-field bridge and the little-endian byte (de)serialisation
used by the memory model.
-/

namespace SolanalibTest.SBPF.Syntax

open Solanalib.SBPF

/-! ## Register encoding -/

/-- Every register round-trips through its 4-bit index field. -/
example : ∀ r : BpfIReg, BpfIReg.ofU4 r.toU4 = some r := by
  intro r; cases r <;> decide

/-- Out-of-range 4-bit fields decode to no register. -/
example : BpfIReg.ofU4 11 = none := by decide

/-! ## Byte (de)serialisation -/

/-- 16-bit serialisation is little-endian. -/
example : u8ListOfU16 0xBEEF = [0xEF, 0xBE] := by decide

/-- 16-bit serialisation round-trips. -/
example : u16OfU8List (u8ListOfU16 0xBEEF) = some 0xBEEF := by decide

/-- 32-bit serialisation round-trips. -/
example : u32OfU8List (u8ListOfU32 0xDEADBEEF) = some 0xDEADBEEF := by decide

/-- 64-bit serialisation round-trips. -/
example : u64OfU8List (u8ListOfU64 0x0123456789ABCDEF) = some 0x0123456789ABCDEF := by decide

end SolanalibTest.SBPF.Syntax
