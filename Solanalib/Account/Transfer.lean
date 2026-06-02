import Solanalib.Account.Basic

/-!
# Lamport transfers

A transfer moves lamports from one account to another. Its defining property
is **conservation**: the total lamports across the two accounts is invariant.
This is the Solana analogue of "conservation of mass" and is the first
property any state-transition system over accounts should respect — every
richer invariant in the library will eventually reduce, in part, to this one.
-/

namespace Solanalib.Account

/-- The result of a `transfer`: the source and destination accounts after
the lamports have moved. -/
structure TransferResult where
  /-- The source account, with `amount` lamports debited. -/
  source : Account
  /-- The destination account, with `amount` lamports credited. -/
  destination : Account
  deriving Repr

/-- Move `amount` lamports from `src` to `dst`.

Requires a proof `h` that the source holds at least `amount` lamports, so a
transfer is total: there is no failure mode and no underflow. -/
def transfer (src dst : Account) (amount : Lamports) (h : amount ≤ src.lamports) :
    TransferResult :=
  { source := src.debit amount h, destination := dst.credit amount }

/-- **Lamport conservation.** A transfer neither creates nor destroys lamports:
the total balance across source and destination is preserved. -/
theorem transfer_preserves_total
    (src dst : Account) (amount : Lamports) (h : amount ≤ src.lamports) :
    (transfer src dst amount h).source.lamports
      + (transfer src dst amount h).destination.lamports
      = src.lamports + dst.lamports := by
  simp [transfer, debit, credit]
  omega

end Solanalib.Account
