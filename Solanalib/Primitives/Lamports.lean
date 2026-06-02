/-!
# Lamports

The native unit of value on Solana. One SOL equals one billion lamports.

This module defines `Lamports` as a transparent alias for `Nat`. The real
on-chain representation is `u64`, so values exceeding `2 ^ 64 - 1` cannot
occur on a live cluster; that bound belongs in a higher-level wrapper and
is deliberately *not* enforced here, so this module can stay small and the
first theorems can stay focused on the algebraic content rather than the
representation.
-/

namespace Solanalib

/-- A lamport count: the smallest unit of native Solana value.

`1 SOL = 10^9 lamports`. Implemented as `Nat` so arithmetic is exact and
`omega` can decide linear questions about it. -/
abbrev Lamports : Type := Nat

namespace Lamports

/-- The number of lamports in one SOL. -/
def perSol : Lamports := 1_000_000_000

end Lamports
end Solanalib
