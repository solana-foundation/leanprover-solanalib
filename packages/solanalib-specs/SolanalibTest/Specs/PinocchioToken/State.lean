/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioToken.State

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioToken.State

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

/-- Structural decidability used only by the finite model controls. -/
def exceptEq {E A : Type} [DecidableEq E] [DecidableEq A] :
    DecidableEq (Except E A)
  | .ok x, .ok y => if same : x = y then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (Except.ok.inj equal))
  | .error x, .error y => if same : x = y then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (Except.error.inj equal))
  | .ok _, .error _ => isFalse (by intro equal; cases equal)
  | .error _, .ok _ => isFalse (by intro equal; cases equal)

local instance {E A : Type} [DecidableEq E] [DecidableEq A] :
    DecidableEq (Except E A) := exceptEq

/-- The concrete parser starts with an existing free account. -/
def accountInput : ViewState := viewWitnessState legacyProgramId accountWitness.bytes

/-- Uninitialized bytes are accepted and the returned guard has been transferred,
not copied or fabricated independently of the lease registry. -/
theorem account_parse_success :
    fromAccountView .legacy .account accountInput ⟨0⟩ =
      (.ok accountWitnessRef, accountWitnessState) := by
  decide +kernel

/-- Whole-data generation zero was consumed by the typed-view projection. -/
theorem original_generation_consumed :
    accountWitnessState.resolve ⟨0, 0⟩ = none ∧
      accountWitnessState.resolve accountWitnessRef.guard =
        some ⟨⟨0⟩, .shared, 1, ⟨0, accountLength⟩⟩ := by
  decide +kernel

/-- A nontrivial account with distinct mint/owner keys, balance 37, and state Frozen. -/
def observedBytes : Bytes :=
  legacyProgramId.bytes ++ token2022ProgramId.bytes ++ Solanalib.Runtime.u64le 37 ++
    List.replicate 36 0 ++ [2] ++ List.replicate 56 0

/-- The byte fixture is a complete token account, rather than an arbitrary prefix. -/
def observedRaw : AccountRaw := ⟨observedBytes, by
  simp [observedBytes, Solanalib.Runtime.u64le, legacyProgramId.length_eq,
    token2022ProgramId.length_eq, accountLength]⟩

/-- The actual post-parser state for the nonzero byte fixture. -/
def observedState : ViewState :=
  (fromAccountView .legacy .account (viewWitnessState legacyProgramId observedBytes) ⟨0⟩).2

/-- The live view reads the exact current parsed bytes. -/
theorem observed_current : currentAccount observedState accountWitnessRef = .ok observedRaw := by
  decide +kernel

/-- Amount decoding is little-endian and retains the full account/guard state. -/
theorem amount_37 : amountReference observedState accountWitnessRef = (37, observedState) := by
  decide +kernel

/-- The nonzero amount is decoded from the actual bytes of the fixture. -/
theorem observedRaw_amount : observedRaw.amount = 37 := by decide +kernel

/-- Both address references retain the same guard, with distinct field offsets. -/
theorem field_references :
    (mintReference observedState accountWitnessRef).1 = ⟨accountWitnessRef.guard, 0⟩ ∧
    (ownerReference observedState accountWitnessRef).1 = ⟨accountWitnessRef.guard, 32⟩ ∧
    currentKey observedState (mintReference observedState accountWitnessRef).1 =
      .ok legacyProgramId ∧
    currentKey observedState (ownerReference observedState accountWitnessRef).1 =
      .ok token2022ProgramId := by
  decide +kernel

/-- Releasing the typed guard also invalidates both previously borrowed fields. -/
theorem released_field_rejected :
    currentKey (Borrow.release observedState accountWitnessRef.guard).2
      (mintReference observedState accountWitnessRef).1 = .error .InvalidAccountData := by
  decide +kernel

/-- A complete amount guarantee is available through the source contract alone. -/
theorem amount_of_contract
    {run : ViewState → Token.Ref → Nat × ViewState}
    (correct : Solanalib.Specs.PinocchioToken.state.account.Account.amount_contract.RealizedBy run)
      :
    run observedState accountWitnessRef = (37, observedState) := by
  have post := correct observedState accountWitnessRef ⟨observedRaw, observed_current⟩
  obtain ⟨unchanged, raw, current, amount⟩ := post
  rw [observed_current] at current
  have same : raw = observedRaw := (Except.ok.inj current).symm
  rw [same] at amount
  apply Prod.ext
  · exact Eq.trans (b := observedRaw.amount) amount observedRaw_amount
  · dsimp only
    exact unchanged

/-- A valid exclusive lease competes with the checked shared borrow of the parser. -/
def exclusivelyBorrowed (bytes : Bytes) (owner : Solanalib.Runtime.Pubkey) : ViewState :=
  { viewWitnessState owner bytes with
    slots := [some ⟨⟨0⟩, .exclusive, 0, ⟨0, bytes.length⟩⟩] }

/-- Legacy length failure precedes both owner failure and borrow conflict. -/
theorem length_before_owner_and_borrow :
    fromAccountView .legacy .mint (exclusivelyBorrowed [] .zero) ⟨0⟩ =
      (.error .InvalidAccountData, exclusivelyBorrowed [] .zero) := by
  decide +kernel

/-- With a complete mint, wrong ownership is the mint-specific error before borrowing. -/
theorem mint_owner_before_borrow :
    fromAccountView .legacy .mint (exclusivelyBorrowed mintWitness.bytes .zero) ⟨0⟩ =
      (.error .InvalidAccountOwner, exclusivelyBorrowed mintWitness.bytes .zero) := by
  decide +kernel

/-- A valid complete account reaches and reports the actual borrow conflict. -/
theorem complete_account_borrow_conflict :
    fromAccountView .legacy .account
      (exclusivelyBorrowed accountWitness.bytes legacyProgramId) ⟨0⟩ =
      (.error .AccountBorrowFailed,
        exclusivelyBorrowed accountWitness.bytes legacyProgramId) := by
  decide +kernel

/-- Exact-size legacy mint acquisition accepts an uninitialized base and the
subsequent source-facing getter reads its nonzero decimal byte without effects. -/
theorem mint_parse_and_decimals :
    let bytes : Bytes := List.replicate 44 0 ++ [9, 0] ++ List.replicate 36 0
    let before := viewWitnessState legacyProgramId bytes
    let after := (Solanalib.Specs.PinocchioToken.state.mint.Mint.from_account_view_reference
      before ⟨0⟩).2
    (Solanalib.Specs.PinocchioToken.state.mint.Mint.from_account_view_reference before ⟨0⟩).1 =
      .ok mintWitnessRef ∧
    Solanalib.Specs.PinocchioToken.state.mint.Mint.decimals_reference after mintWitnessRef =
      (9, after) := by
  decide +kernel

/-- Legacy rejects an extended account even when its type byte is correct. -/
theorem legacy_extension_rejected :
    (fromAccountView .legacy .account
      (viewWitnessState legacyProgramId (accountWitness.bytes ++ [2])) ⟨0⟩).1 =
        .error .InvalidAccountData := by
  decide +kernel

/-- A structurally accepted raw account can contain an invalid state discriminant. -/
def invalidStateBytes : Bytes := List.replicate 108 0 ++ [255] ++ List.replicate 56 0

/-- The invalid-state fixture is still a complete 165-byte raw account. -/
def invalidStateRaw : AccountRaw := ⟨invalidStateBytes, by
  simp [invalidStateBytes, accountLength]⟩

/-- Its real parser post-state retains the acquired guard. -/
def invalidStateWorld : ViewState :=
  (fromAccountView .legacy .account
    (viewWitnessState legacyProgramId invalidStateBytes) ⟨0⟩).2

/-- Raw view acquisition does not smuggle in an initialized/valid-state premise. -/
theorem invalid_state_parse_success :
    (fromAccountView .legacy .account
      (viewWitnessState legacyProgramId invalidStateBytes) ⟨0⟩).1 =
        .ok accountWitnessRef ∧
    currentAccount invalidStateWorld accountWitnessRef = .ok invalidStateRaw := by
  decide +kernel

/-- The later state projection forwards the explicit panic, rather than returning an enum. -/
theorem invalid_state_panics :
    stateRun stateAbortPolicy.panic invalidStateWorld accountWitnessRef
      (.terminated (255 : UInt8)) := by
  have current := invalid_state_parse_success.2
  have bad : decodeAccountState invalidStateRaw.stateByte = none := by decide +kernel
  simp only [stateRun, current, bad, Callback.map]
  exact ⟨.terminated (255 : UInt8), rfl, rfl⟩

/-- A supplied panic policy can expose both an actual unwinding state change
and a terminal alternative; neither outcome becomes an ordinary enum value. -/
def invalidStatePolicy : StatePolicy where
  Unwind := Nat
  Terminal := UInt8
  panic := fun before byte outcome =>
    outcome = .unwound 7 { before with slots := [] } ∨ outcome = .terminated byte

-- Instantiating the continuation with this 165-byte fixture exceeds the
-- default reduction recursion depth; the generic theorem uses default limits.
set_option maxRecDepth 2048 in
/-- Readable invalid bytes remain admitted, and the general continuation
theorem retains both actual panic exits with their exact effects. -/
theorem invalid_state_family_outcomes :
    (stateFamily.contract invalidStatePolicy).requires invalidStateWorld accountWitnessRef ∧
    stateFamilyRun invalidStatePolicy invalidStateWorld accountWitnessRef
      (.unwound (7 : Nat) { invalidStateWorld with slots := [] }) ∧
    stateFamilyRun invalidStatePolicy invalidStateWorld accountWitnessRef
      (.terminated (255 : UInt8)) := by
  have readable : AccountReadable invalidStateWorld accountWitnessRef :=
    ⟨invalidStateRaw, invalid_state_parse_success.2⟩
  obtain ⟨raw, current, continues⟩ := stateFamily_continues invalidStatePolicy readable
  have same : raw = invalidStateRaw :=
    Except.ok.inj (current.symm.trans invalid_state_parse_success.2)
  subst raw
  have bad : decodeAccountState invalidStateRaw.stateByte = none := by decide +kernel
  rw [bad] at continues
  dsimp only at continues
  refine ⟨readable, ?_, ?_⟩
  · have forwarded := continues
      (.unwound 7 { invalidStateWorld with slots := [] } : Outcome ViewState Empty Nat UInt8)
      (Or.inl rfl)
    simpa only [Outcome.map] using forwarded
  · have byte : invalidStateRaw.stateByte = (255 : UInt8) := by decide +kernel
    have ran : invalidStatePolicy.panic invalidStateWorld invalidStateRaw.stateByte
        (.terminated (255 : UInt8)) := Or.inr (by rw [byte]; rfl)
    have forwarded := continues (.terminated (255 : UInt8)) ran
    simpa only [Outcome.map] using forwarded

/-- The same malformed state bytes remain a decoding error for SPL Pack. -/
theorem spl_rejects_invalid_state :
    unpackAccount invalidStateBytes = .error .InvalidAccountData := by
  decide +kernel

/-- Pinocchio and Pack intentionally differ on an uninitialized exact-size account. -/
theorem spl_rejects_uninitialized :
    unpackAccount accountWitness.bytes = .error .UninitializedAccount := by
  decide +kernel

/-- A mathematical missing-cell input, outside the Rust AccountView binding. -/
def missingCellState : ViewState := ⟨[], []⟩

/-- The broadened parser contract retains the already defined missing-cell
error and unchanged state; it does not assert that this is a valid Rust handle. -/
theorem missing_cell_parser_error :
    Solanalib.Specs.PinocchioToken.state.account.Account.from_account_view_contract.requires
      missingCellState ⟨0⟩ ∧
    Solanalib.Specs.PinocchioToken.state.account.Account.from_account_view_reference
      missingCellState ⟨0⟩ = (.error .InvalidAccountData, missingCellState) :=
  ⟨True.intro, rfl⟩

/-- The real release consumes the only token of the previously parsed account. -/
def retiredState : ViewState := (Borrow.release observedState accountWitnessRef.guard).2

/-- Neither a widened field-descriptor contract nor its returned offset
resurrects the consumed parent token or grants a current-value read. -/
theorem retired_field_descriptors :
    Solanalib.Specs.PinocchioToken.state.account.Account.mint_contract.requires
      retiredState accountWitnessRef ∧
    Solanalib.Specs.PinocchioToken.state.account.Account.owner_contract.requires
      retiredState accountWitnessRef ∧
    Solanalib.Specs.PinocchioToken.state.account.Account.mint_contract.ensures
      retiredState accountWitnessRef ⟨accountWitnessRef.guard, 0⟩ retiredState ∧
    Solanalib.Specs.PinocchioToken.state.account.Account.owner_contract.ensures
      retiredState accountWitnessRef ⟨accountWitnessRef.guard, 32⟩ retiredState ∧
    currentKey retiredState ⟨accountWitnessRef.guard, 0⟩ = .error .InvalidAccountData ∧
    currentKey retiredState ⟨accountWitnessRef.guard, 32⟩ = .error .InvalidAccountData :=
  ⟨True.intro, True.intro, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    by decide +kernel, by decide +kernel⟩

/-- The substantive readable-current-value premise of Amount still rejects the
retired guard, so the fallback zero of the helper is not a proved token balance. -/
theorem retired_amount_not_admitted :
    ¬ Solanalib.Specs.PinocchioToken.state.account.Account.amount_contract.requires
      retiredState accountWitnessRef := by
  have unreadable : currentAccount retiredState accountWitnessRef =
      .error .InvalidAccountData := by decide +kernel
  change ¬ AccountReadable retiredState accountWitnessRef
  simp only [AccountReadable, unreadable, reduceCtorEq, exists_false, not_false_eq_true]

/-- A retired guard is outside the readable domain of the state getter. The raw
operation still has no ordinary, panic or terminal exit for that reference. -/
theorem retired_state_has_no_exit :
    ¬ (stateFamily.contract stateAbortPolicy).requires retiredState accountWitnessRef ∧
    ∀ outcome, ¬ stateFamilyRun stateAbortPolicy retiredState accountWitnessRef outcome := by
  have unreadable : currentAccount retiredState accountWitnessRef =
      .error .InvalidAccountData := by decide +kernel
  constructor
  · change ¬ AccountReadable retiredState accountWitnessRef
    simp only [AccountReadable, unreadable, reduceCtorEq, exists_false, not_false_eq_true]
  · intro outcome
    change ¬ stateRun stateAbortPolicy.panic retiredState accountWitnessRef outcome
    simp only [stateRun, unreadable, not_false_eq_true]

end SolanalibTest.Specs.PinocchioToken.State
