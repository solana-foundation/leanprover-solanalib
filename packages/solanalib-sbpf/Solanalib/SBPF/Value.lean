/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.SBPF.CommType

/-!
# SBPF.Value — the CompCert-style memory value

The value type read from and written to memory (`Val.thy`'s `val`). A memory
access at a given `MemoryChunk` width yields one of these tagged values.

Scope note: `Val.thy` additionally defines a large suite of CompCert-style
arithmetic on `val` (`add32`, `divmod64s`, `bswap32`, `cmpu`, …). Those operate
on the *x86-64 JIT's* value-typed registers and are out of scope here — the sBPF
interpreter operates on raw `U64` registers directly. Only the value type, which
the memory model needs, is ported.

## Main definitions
* `Solanalib.SBPF.Val` — a tagged memory value (`Vundef` / byte / short / int / long).
-/

namespace Solanalib.SBPF

/-- A CompCert-style memory value: either undefined or a tagged machine word. -/
inductive Val
  | vundef
  | vbyte (b : U8)
  | vshort (s : U16)
  | vint (i : U32)
  | vlong (l : U64)
  deriving DecidableEq, Repr

end Solanalib.SBPF
