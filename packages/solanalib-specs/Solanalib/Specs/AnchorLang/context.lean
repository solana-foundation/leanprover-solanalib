/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorContext
public import Solanalib.Specs.Core.AnchorContextOwned
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorLang.context

abbrev CpiContext (Accounts AccountInfo : Type) :=
  Solanalib.Specs.Core.AnchorContext.Value Accounts AccountInfo

namespace CpiContext

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorContext

abbrev SignerSeeds := AnchorContext.SignerSeeds
abbrev NewWithSignerArgs (Accounts : Type) := AnchorContext.NewWithSignerArgs Accounts

/-- `T`, account handles, and ambient state are independent model parameters.
The Rust constructor does not call its `ToAccountMetas` or `ToAccountInfos`
trait bounds, so the value contract needs no behavioral premise for them. -/
structure ObservationIndex where
  State : Type
  Accounts : Type
  AccountInfo : Type

def new_with_signer_observation_contract (index : ObservationIndex) :
    Solanalib.Contracts.Model index.State (NewWithSignerArgs index.Accounts)
      (CpiContext index.Accounts index.AccountInfo) :=
  newWithSignerContract index.State index.Accounts index.AccountInfo

def new_with_signer_observation_family : Family where
  Index := ObservationIndex
  State := ObservationIndex.State
  Args := fun index => NewWithSignerArgs index.Accounts
  Value := fun index => CpiContext index.Accounts index.AccountInfo
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := new_with_signer_observation_contract

def new_with_signer_observation_run : FamilyRun new_with_signer_observation_family :=
  fun _ => returnsOf newWithSignerReference

theorem new_with_signer_observation_reference :
    FamilyReference new_with_signer_observation_family new_with_signer_observation_run := by
  intro index
  exact (realized_iff_holds _ _).mp
    (newWithSignerReference_realizes index.State index.Accounts index.AccountInfo)

/-- A concrete inhabited payload witnesses the constructor precondition.
Universal reference correctness above covers every model account type. -/
def new_with_signer_observation_sample : new_with_signer_observation_family.Index :=
  ⟨Unit, _root_.Solanalib.Runtime.Pubkey × _root_.Solanalib.Runtime.Pubkey,
    _root_.Solanalib.Runtime.Pubkey⟩

private def sampleArgs : NewWithSignerArgs
    (_root_.Solanalib.Runtime.Pubkey × _root_.Solanalib.Runtime.Pubkey) :=
  ⟨.ofNat 9, (.ofNat 1, .ofNat 2), [[[1, 2], [255]], [[3]]]⟩

theorem new_with_signer_observation_satisfiable :
    FamilySatisfiable new_with_signer_observation_family new_with_signer_observation_sample :=
  ⟨(), sampleArgs, trivial⟩

theorem new_with_signer_observation_has_execution :
    FamilyHasExecution new_with_signer_observation_family new_with_signer_observation_run
      new_with_signer_observation_sample :=
  ⟨(), sampleArgs, .returned (newWithSigner sampleArgs) (), trivial, rfl⟩

/-- Primary source model: preserve the moved payload and borrowed values while
creating one fresh empty remaining-vector resource through the infallible
dependency. The observation family above forgets that resource identity. -/
def new_with_signer_contract : Family := AnchorContextOwned.family

def new_with_signer_run : FamilyRun new_with_signer_contract := AnchorContextOwned.reference

def new_with_signer_sample : new_with_signer_contract.Index := AnchorContextOwned.sample

theorem new_with_signer_reference :
    FamilyReference new_with_signer_contract new_with_signer_run :=
      AnchorContextOwned.reference_holds

theorem new_with_signer_satisfiable :
    FamilySatisfiable new_with_signer_contract new_with_signer_sample :=
      AnchorContextOwned.sample_satisfiable

theorem new_with_signer_has_execution :
    FamilyHasExecution new_with_signer_contract new_with_signer_run new_with_signer_sample :=
  AnchorContextOwned.sample_execution

end CpiContext

end Solanalib.Specs.AnchorLang.context
