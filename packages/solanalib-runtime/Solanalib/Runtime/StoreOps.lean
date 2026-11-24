/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.AccountState

@[expose] public section

/-!
# Abstract account-store operations

The data-lease protocol represents the limit of 254 shared leases in
solana-account-view 2.0.0. Direct lamport and owner stores remain separate
operations. These definitions do not give a complete contract for every account
interface; in particular, they do not represent the separate lamport-borrow
protocol of solana-account-info 3.1.1. The source scope and the premises needed by
implementation proofs are in
[library state and derived
proofs](../../source-notes/agave-4.3.2.md#library-state-and-derived-proofs).
-/

set_option autoImplicit false

namespace Solanalib.Runtime

/-- The represented operations on the abstract account store. -/
inductive StoreOp where
  | borrow (i : Nat)
  | borrowMut (i : Nat)
  | release (i : Nat)
  | write (i off : Nat) (bs : Bytes)
  | resize (i n : Nat)
  | setLamports (i v : Nat)
  | assign (i : Nat) (o : Pubkey)
  /-- A read of the account by the runtime: a CPI or the end of the instruction. -/
  | observe (i : Nat)
  deriving Repr

/-- The lease after taking a shared data borrow, with the shared-borrow limit of
solana-account-view 2.0.0. -/
def Lease.addShared : Lease → Option Lease
  | .free => some (.shared 1)
  | .shared n => if n < 254 then some (.shared (n + 1)) else none
  | .exclusive => none

/-- The lease after a release, if there is a borrow to release. -/
def Lease.release : Lease → Option Lease
  | .shared (n + 2) => some (.shared (n + 1))
  | .shared 1 => some .free
  | .exclusive => some .free
  | _ => none

/-- The lease part of an operation, common to both semantics. -/
def leaseStep (c : Cell) : StoreOp → Option Lease
  | .borrow _ => c.lease.addShared
  | .borrowMut _ => if c.lease = .free then some .exclusive else none
  | .release _ => c.lease.release
  | _ => some c.lease

/-- The account an operation acts on. -/
def StoreOp.target : StoreOp → Nat
  | .borrow i | .borrowMut i | .release i | .write i _ _ | .resize i _ | .setLamports i _
  | .assign i _ | .observe i => i

/-- A step with writes in place. The result carries the data that an observation reads. -/
def stepInPlace (S : Store) (op : StoreOp) : Option (Store × Option Bytes) :=
  let c := S op.target
  match op with
  | .borrow i | .borrowMut i | .release i =>
    (leaseStep c op).map fun l => (S.upd i { c with lease := l }, none)
  | .write i off bs =>
    if c.lease = .exclusive ∧ off + bs.length ≤ c.data.length then
      some (S.upd i { c with data := writeAt c.data off bs }, none)
    else none
  | .resize i n =>
    if c.lease = .exclusive ∧ n ≤ c.entryLen + MAX_PERMITTED_DATA_INCREASE then
      some (S.upd i { c with data := resizeZero c.data n }, none)
    else none
  | .setLamports i v => some (S.upd i { c with lamports := v }, none)
  | .assign i o => some (S.upd i { c with owner := o }, none)
  | .observe _ => some (S, some c.data)

end Solanalib.Runtime
