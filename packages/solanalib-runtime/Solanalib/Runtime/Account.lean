/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Ids
public import Solanalib.Runtime.Profile

@[expose] public section

/-!
# Accounts and rent

The account record represents the observable fields of an account; the transaction
context keeps its address separately. The current source correspondence and numeric
premises are in [accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent).
-/

namespace Solanalib.Runtime

/-- An account. -/
structure Account where
  lamports : Nat
  data : Bytes
  owner : Pubkey
  executable : Bool
  rentEpoch : Nat
  deriving DecidableEq, Repr

namespace Account

/-- The account that loading creates for a missing address: zero lamports, empty
data, the System program as owner and rent epoch `u64::MAX`.
See `load_transaction_account` in the current
[loading analysis](../../source-notes/agave-4.3.2.md#transaction-admission-and-loading). -/
def missing : Account :=
  { lamports := 0, data := [], owner := Ids.systemProgram, executable := false,
    rentEpoch := U64_MAX }

/-- The integers of the account fit the types of the runtime, and the data length
respects the 10 MiB limit. -/
def WF (a : Account) : Prop :=
  a.lamports < U64_LIMIT ∧ a.data.length ≤ MAX_ACCOUNT_DATA_LEN ∧ a.rentEpoch < U64_LIMIT

end Account

instance : Inhabited Account := ⟨Account.missing⟩

namespace RentParams

/-- The mathematical rent-exempt minimum balance of an account with `len` data bytes.
For the integer thresholds 1 and 2, this agrees with `Rent::try_minimum_balance`
in solana-rent 4.4.0 when the length and rate satisfy its checked bounds.
`RentParams.WF` alone does not impose those bounds; see
[accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/
def minBalance (r : RentParams) (len : Nat) : Nat :=
  (128 + len) * r.lamportsPerByte * r.thresholdNum / r.thresholdDen

/-- Whole-account rent is at least its effective per-byte amount, including
profiles whose threshold is represented by integer division. -/
theorem perByte_le_minBalance (rent : RentParams) (len : Nat) :
    rent.lamportsPerByte * rent.thresholdNum / rent.thresholdDen ≤ rent.minBalance len := by
  unfold minBalance
  apply Nat.div_le_div_right
  have bound : 1 ≤ 128 + len := by omega
  simpa only [Nat.one_mul, Nat.mul_assoc] using
    Nat.mul_le_mul_right (rent.lamportsPerByte * rent.thresholdNum) bound

/-- `Rent::is_exempt`. -/
def isExempt (r : RentParams) (lamports len : Nat) : Bool :=
  decide (r.minBalance len ≤ lamports)

end RentParams

/-- `RentState` in Agave 4.3.2, `svm/src/rent_calculator.rs`. -/
inductive RentState where
  | uninitialized
  | rentPaying (lamports dataSize : Nat)
  | rentExempt
  deriving DecidableEq, Repr

/-- The static rent classification of an account, as used by
`get_pre_exec_account_rent_state` in `svm/src/rent_calculator.rs`. -/
def rentState (r : RentParams) (a : Account) : RentState :=
  if a.lamports = 0 then .uninitialized
  else if r.isExempt a.lamports a.data.length then .rentExempt
  else .rentPaying a.lamports a.data.length

/-- `transition_allowed` in Agave 4.3.2, `svm/src/rent_calculator.rs`.
See [accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/
def transitionAllowed : RentState → RentState → Bool
  | _, .uninitialized => true
  | _, .rentExempt => true
  | .rentPaying preLamports preSize, .rentPaying postLamports postSize =>
    postSize == preSize && decide (postLamports ≤ preLamports)
  | _, .rentPaying _ _ => false

/-- The minimum-balance condition implemented by Agave 4.3.2 through
`TransactionAccountStateInfo::new_pre_exec`, `new_post_exec` and `verify_changes`,
with `get_post_exec_account_rent_state` and `transition_allowed`.
The floor is the rent-exempt minimum at the final size, lowered to the balance before
execution when the account held lamports, did not grow and kept its owner.
See [accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/
def relaxedMinBalanceOk (r : RentParams) (pre post : Account) : Bool :=
  let floor := r.minBalance post.data.length
  let minAllowed :=
    if 0 < pre.lamports ∧ post.data.length ≤ pre.data.length ∧ post.owner = pre.owner then
      min floor pre.lamports
    else floor
  post.lamports == 0 || decide (minAllowed ≤ post.lamports)

/-- The balance condition of the post-execution rent check of one writable account.
`rentCheck` adds the incinerator exemption retained by Agave 4.3.2 in
`check_rent_state_with_account`.
See [accounts and rent](../../source-notes/agave-4.3.2.md#accounts-and-rent). -/
def rentCheckCore (p : Profile) (pre post : Account) : Bool :=
  if p.features.relaxPostExecMinBalance then relaxedMinBalanceOk p.rent pre post
  else transitionAllowed (rentState p.rent pre) (rentState p.rent post)

def rentCheck (p : Profile) (key : Pubkey) (pre post : Account) : Bool :=
  key == Ids.incinerator || rentCheckCore p pre post

/-- Fee-payer validation in Agave 4.3.2 uses
`check_static_account_rent_state_transition`, which
does not exempt the incinerator. Fee deduction preserves owner and data length.
Earlier profiles retain their existing account-key-aware check. -/
def feePayerRentCheck (p : Profile) (key : Pubkey) (pre post : Account) : Bool :=
  if p.release = .agave_4_3_2 then rentCheckCore p pre post else rentCheck p key pre post

/-- An account that keeps its lamports, data length and owner passes the check:
under the old rule its rent state is unchanged, and under SIMD-0392 its floor is at
most its balance. -/
theorem rentCheck_of_unchanged (p : Profile) (key : Pubkey) (pre post : Account)
    (hl : post.lamports = pre.lamports) (hd : post.data.length = pre.data.length)
    (ho : post.owner = pre.owner) : rentCheck p key pre post = true := by
  unfold rentCheck rentCheckCore
  cases p.features.relaxPostExecMinBalance with
  | true =>
    simp only [relaxedMinBalanceOk, hl, hd, ho]
    by_cases h0 : pre.lamports = 0
    · simp [h0]
    · have : 0 < pre.lamports := Nat.pos_of_ne_zero h0
      simp [this, Nat.min_le_right]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
    right
    have hs : rentState p.rent post = rentState p.rent pre := by
      simp [rentState, hl, hd]
    rw [hs]
    cases rentState p.rent pre <;> simp [transitionAllowed]

end Solanalib.Runtime
