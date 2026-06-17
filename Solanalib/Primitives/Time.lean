/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# Time: unix-second timestamps as a parse-time alias for `UInt64`

Solana's runtime exposes wall-clock time via the `Clock` sysvar
(`unix_timestamp : i64`) and slots via `Clock.slot : u64`. Both are
64-bit integers on chain. For Solanalib we expose the unsigned
`Timestamp` (= `UInt64`) — the natural shape for "seconds since epoch"
— alongside its unbounded `Nat` companion for spec-layer reasoning.

The two-name discipline mirrors `Lamports` / `LamportsUnchecked`:
strict `UInt64` for on-chain semantics; unbounded `Nat` for `omega`-
friendly proofs about elapsed time, window arithmetic, accumulators.

## Main definitions

* `Timestamp`           — unsigned 64-bit seconds since epoch.
* `TimestampUnchecked`  — unbounded `Nat` for proof-level arithmetic.

Bridge via `.toNat` (UInt64 → Nat) and `UInt64.ofNat` (Nat → UInt64,
wraps on overflow).
-/

/-- A unix-seconds timestamp, with the strict on-chain `u64`
representation. Use this in signatures that talk about real on-chain
time (`Clock.unix_timestamp`, last-update slots cast to seconds, …). -/
notation "Timestamp" => UInt64

/-- An unbounded timestamp for abstract reasoning where the u64 bound
isn't relevant. `omega` and the `Nat` simp set apply without
unfolding ceremony. Bridge to `Timestamp` via `UInt64.ofNat` /
`.toNat`. -/
notation "TimestampUnchecked" => Nat
