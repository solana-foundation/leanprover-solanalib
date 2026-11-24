/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Init
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Construct
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Exit

/-! Kernel controls for admission failures that the typed native record reader
cannot construct. They use the same executable decisions as the checkers. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor
open Anchor.RequiresCheck (illTyped illInfo ownerScript)

theorem init_rejects_illTyped (layout : LoadIndex) (address : Nat) :
    ¬ (accounts.account_loader.AccountLoader.load_init_contract.contract
      (Anchor.Loading.types layout)).requires (illTyped, Anchor.Loading.heap0)
        ⟨profile, ⟨illInfo⟩, address⟩ := by
  intro required
  have rejects : Init.readyB layout (illTyped, Anchor.Loading.heap0)
      ⟨profile, ⟨illInfo⟩, address⟩ = false := rfl
  exact Bool.false_ne_true (rejects.symm.trans ((Init.readyB_iff _ _ _).mpr required))

theorem init_observation_rejects_illTyped (layout : LoadIndex) (address : Nat) :
    ¬ (accounts.account_loader.AccountLoader.load_init_observation_contract.contract
      layout).requires illTyped ⟨profile, ⟨illInfo⟩, address⟩ := by
  intro required
  have rejects : Init.observationReadyB layout illTyped
      ⟨profile, ⟨illInfo⟩, address⟩ = false := rfl
  exact Bool.false_ne_true (rejects.symm.trans ((Init.observationReadyB_iff _ _ _).mpr required))

def badAccounts : AnchorLoader.AccountsState (Construct.accountsTypes ownerScript) :=
  ⟨(illTyped, (Anchor.Construct.heap0, ⟨[.zero], []⟩)), [⟨0, illInfo⟩], (0 : Nat), []⟩

theorem accounts_rejects_illTyped :
    ¬ (accounts.account_loader.AccountLoader.try_accounts_contract.contract
      (Construct.accountsTypes ownerScript)).requires badAccounts ⟨profile, .zero, []⟩ := by
  intro required
  have rejects : Construct.accountsReadyB ownerScript badAccounts ⟨profile, .zero, []⟩ = false := by
    decide +kernel
  exact Bool.false_ne_true (rejects.symm.trans ((Construct.accountsReadyB_iff _ _ _).mpr required))

def badExitWorld : Anchor.Construct.W :=
  (illTyped, (Anchor.Construct.heap0, ⟨[⟨List.replicate 32 1, by decide⟩], []⟩))

theorem exit_rejects_illTyped :
    ¬ (accounts.account_loader.AccountLoader.exit_contract.contract
      (Exit.types ownerScript)).requires badExitWorld ⟨profile, ⟨⟨0, illInfo⟩⟩, .zero⟩ := by
  intro required
  have rejects : Exit.readyB ownerScript badExitWorld ⟨profile, ⟨⟨0, illInfo⟩⟩, .zero⟩ = false := by
    decide +kernel
  exact Bool.false_ne_true (rejects.symm.trans ((Exit.readyB_iff _ _ _).mpr required))

def diagnosticWorld : Anchor.Construct.W :=
  (AccountInfo.sampleState,
    (⟨[some "name", some "message"], [some (Anchor.RequiresAccounts.payload3 ⟨0⟩ ⟨1⟩)], 0, []⟩,
      ⟨[.zero], []⟩))

/-- This is the exact inner decision used after the second Owner call.
The native script preserves the heap; an arbitrary callback losing the held
error Box must instead be rejected, even if it returns a diagnostic key. -/
theorem unchecked_diagnostic_loss_rejected :
    Anchor.RequiresAccounts.ownerExitReadyB ⟨profile, AccountInfo.sampleInfo⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩
      diagnosticWorld (.returned .zero
        (AccountInfo.sampleState, (Anchor.Construct.heap0, ⟨[.zero], []⟩))) = false := by
  decide +kernel

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Requires
