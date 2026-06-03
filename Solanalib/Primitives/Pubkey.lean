/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Init

/-!
# Pubkey

A Solana public key — a 32-byte identifier used as the address of every
account on the cluster. Real on-chain pubkeys are interpreted in two
ways depending on context: as compressed Ed25519 curve points (regular
wallet/program addresses) or as off-curve hashes (Program Derived
Addresses). This module captures the raw byte-array shape; the curve /
PDA distinction is layered on in `Solanalib.Pda`.

## Main definitions

* `Solanalib.Pubkey` — the 32-byte identifier wrapper.

## Implementation notes

The 32-byte length constraint is not yet enforced in the type. A later
refinement will replace `ByteArray` with a length-indexed `Vector UInt8 32`
once we have a use site that actually needs the bound. For algebraic
theorems about pubkey equality, the current shape is sufficient.
-/

-- `ByteArray` ships without a `Repr` instance in Lean core; derive one
-- here so anything containing a `ByteArray` (Pubkey, Account.data, …) can
-- itself derive `Repr`.
deriving instance Repr for ByteArray

namespace Solanalib

/-- A Solana public key: a 32-byte identifier serving as an account
address. Equality is byte-wise; `@[ext]` lets `ext` reduce a pubkey
equation to a byte-array equation. -/
@[ext]
structure Pubkey where
  /-- The raw bytes of the pubkey. Conceptually length 32. -/
  bytes : ByteArray
  deriving Repr, DecidableEq

end Solanalib
