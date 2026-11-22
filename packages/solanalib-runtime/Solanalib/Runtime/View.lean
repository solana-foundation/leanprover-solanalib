/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.AccountState

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Runtime

/-- The observations justified by the resources left in an account pool.
An exclusive borrower owns the current data, so that data observation is absent. -/
structure PartialCell where
  owner : Pubkey
  lamports : Nat
  dataLen : Nat
  entryLen : Nat
  lease : Lease
  data : Option Bytes
  deriving DecidableEq, Repr

/-- A complete in-place account agrees with every available observation. -/
def Completes (p : PartialCell) (c : Cell) : Prop :=
  p.owner = c.owner ∧ p.lamports = c.lamports ∧ p.dataLen = c.data.length ∧
    p.entryLen = c.entryLen ∧ p.lease = c.lease ∧
    (match p.data with | none => True | some bytes => bytes = c.data) ∧ c.copy = none

/-- The complete observation of a cell whose data are available. -/
def PartialCell.ofCell (c : Cell) : PartialCell :=
  ⟨c.owner, c.lamports, c.data.length, c.entryLen, c.lease, some c.data⟩

theorem completes_ofCell {c : Cell} (h : c.copy = none) :
    Completes (.ofCell c) c :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, h⟩

/-- A local balance update preserves the relation for every possible current
content of data held by a borrower. -/
theorem completes_setLamports {p : PartialCell} {c : Cell}
    (h : Completes p c) (value : Nat) :
    Completes { p with lamports := value } { c with lamports := value } := by
  rcases h with ⟨ho, _, hn, he, hl, hd, hc⟩
  exact ⟨ho, rfl, hn, he, hl, hd, hc⟩

theorem completes_assign {p : PartialCell} {c : Cell}
    (h : Completes p c) (owner : Pubkey) :
    Completes { p with owner } { c with owner } := by
  rcases h with ⟨_, hb, hn, he, hl, hd, hc⟩
  exact ⟨rfl, hb, hn, he, hl, hd, hc⟩

theorem hidden_data_may_vary {p : PartialCell} {c : Cell}
    (h : Completes p c) (hidden : p.data = none) (bytes : Bytes)
    (hlen : bytes.length = c.data.length) : Completes p { c with data := bytes } := by
  rcases h with ⟨ho, hb, hn, he, hl, _, hc⟩
  exact ⟨ho, hb, hn.trans hlen.symm, he, hl, by simp [hidden], hc⟩

/-- Program-visible header metadata. Authentication of runtime privileges is
a separate relation established at invocation entry and synchronization. -/
structure AccountMeta where
  address : Pubkey
  signer : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

end Solanalib.Runtime
