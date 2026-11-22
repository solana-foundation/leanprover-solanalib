/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Profile

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Runtime

/-- A lease on the data of an account. -/
inductive Lease where
  | free
  | shared (n : Nat)
  | exclusive
  deriving DecidableEq, Repr

/-- An account of the store. The field `copy` holds the snapshot of an exclusive lease
under copy-back, and is unused in place. -/
structure Cell where
  owner : Pubkey
  lamports : Nat
  data : Bytes
  /-- The data length at the start of the instruction, which bounds growth. -/
  entryLen : Nat
  lease : Lease
  copy : Option Bytes
  deriving DecidableEq, Repr

/-- The account store, by transaction index. -/
def Store := Nat → Cell

/-- The store with the cell at `i` replaced. -/
def Store.upd (S : Store) (i : Nat) (c : Cell) : Store := fun j => if j = i then c else S j

@[simp] theorem Store.upd_self (S : Store) (i : Nat) (c : Cell) : S.upd i c i = c := by
  simp [Store.upd]

@[simp] theorem Store.upd_ne (S : Store) (i j : Nat) (c : Cell) (h : j ≠ i) : S.upd i c j = S j :=
  by
  simp [Store.upd, h]

end Solanalib.Runtime
