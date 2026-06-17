/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType

/-!
# SBPF.Memory — the sBPF memory model

Byte-addressable memory and access widths for the sBPF semantics, ported from
`Mem.thy`. This module currently provides the address space and access-width
type; the `loadv` / `storev` operations (which depend on the value type) land
alongside `Solanalib.SBPF.Value`.

## Main definitions
* `Solanalib.SBPF.MemoryChunk` — access width (`M8` … `M64`).
* `Solanalib.SBPF.Mem` — the byte-addressable address space.
-/

namespace Solanalib.SBPF

/-- Access width for a memory operation (the source theory's `memory_chunk`). -/
inductive MemoryChunk
  | m8
  | m16
  | m32
  | m64
  deriving DecidableEq, Repr

/-- Byte-addressable memory: a partial map from 64-bit address to byte.

Modelled as a total function into `Option U8` (`none` = unmapped), matching the
source theory's `(u64, u8) map`. -/
abbrev Mem := U64 → Option U8

end Solanalib.SBPF
