/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/

/-!
# Lamports

The native unit of value on Solana. One SOL equals one billion lamports.

`Lamports` is exposed as a *parse-time notation* for `Nat`, not as an `abbrev`
or wrapper structure. Decision procedures like `omega` are sensitive to the
type they see in hypotheses; with `notation`, `(amount : Lamports)` is
elaborated as `(amount : Nat)` from the start, so no unfolding ceremony is
needed in proofs. The semantic name is preserved in signatures and rendered
docs.

The real on-chain representation is `u64`, so values exceeding `2 ^ 64 - 1`
cannot occur on a live cluster; that bound belongs in a higher-level wrapper
and is deliberately not enforced here.

## Main definitions

* `Lamports` — a parse-time notation for `Nat`. Use this name in signatures
  to mark "this is a lamport count".
* `Solanalib.Lamports.perSol` — the number of lamports in one SOL.
-/

namespace Solanalib.Lamports

/-- The number of lamports in one SOL. -/
def perSol : Nat := 1_000_000_000

end Solanalib.Lamports

/-- A lamport count: the smallest unit of native Solana value.

`1 SOL = 10^9 lamports`. Implemented as a parse-time `notation` over `Nat`
so that `omega` and other decision procedures see `Nat` directly without
reducibility ceremony. -/
notation "Lamports" => Nat
