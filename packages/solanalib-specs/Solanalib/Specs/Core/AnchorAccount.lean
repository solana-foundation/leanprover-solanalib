/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoContracts
public import Solanalib.Specs.Core.AnchorError
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorAccount

abbrev Error := AnchorError.Value ProgramError.Value

/-- The account-validation errors used by the selected Anchor 1.0.2 functions.
Codes and messages are the declared ErrorCode values of the version. -/
inductive Code where
  | discriminatorNotFound
  | discriminatorMismatch
  | notMutable
  | ownedByWrongProgram
  | notInitialized
  deriving DecidableEq, Repr

def Code.payload : Code → AnchorError.AnchorValue
  | .discriminatorNotFound =>
    ⟨"AccountDiscriminatorNotFound", 3001, "No discriminator was found on the account", none, none⟩
  | .discriminatorMismatch =>
    ⟨"AccountDiscriminatorMismatch", 3002,
      "Account discriminator did not match what was expected", none, none⟩
  | .notMutable =>
    ⟨"AccountNotMutable", 3006, "The given account is not mutable", none, none⟩
  | .ownedByWrongProgram =>
    ⟨"AccountOwnedByWrongProgram", 3007,
      "The given account is owned by a different program than expected", none, none⟩
  | .notInitialized =>
    ⟨"AccountNotInitialized", 3012,
      "The program expected this account to be already initialized", none, none⟩

def error (code : Code) : Error := .anchor code.payload

/-- Program errors retain their exact payload and initially have no diagnostic
origin or compared-values field. -/
def programError (error : ProgramError.Value) : Error := .program ⟨error, none, none⟩

/-- Account owns a decoded value and refers to an AccountInfo alias. The model
does not identify the decoded value with live bytes until a codec is supplied. -/
structure Account (Payload : Type) where
  value : Payload
  info : AccountInfo.Value
  deriving DecidableEq, Repr

/-- InterfaceAccount also remembers the owner present at construction. -/
structure InterfaceAccount (Payload : Type) where
  account : Account Payload
  owner : _root_.Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- the generic parameter of Program is a Rust phantom; no value of that type is
created or observed by the dereference of Interface. -/
structure Program (Tag : Type) where
  info : AccountInfo.Value
  deriving DecidableEq, Repr

structure Interface (Tag : Type) where
  program : Program Tag
  deriving DecidableEq, Repr

/-- Loader stores an alias, not a decoded account or a persistent data borrow. -/
structure Loader (Payload : Type) where
  info : AccountInfo.Value
  deriving DecidableEq, Repr

structure Signer where
  info : AccountInfo.Value
  deriving DecidableEq, Repr

/-- These shared-reference projections observe the selected field value. Their
Rust binding must relate the returned reference and lifetime to that field. -/
def accountDeref {Payload : Type} (account : Account Payload) : Payload := account.value
def interfaceAccountDeref {Payload : Type} (account : InterfaceAccount Payload) : Payload :=
  account.account.value
def interfaceDeref {Tag : Type} (value : Interface Tag) : AccountInfo.Value := value.program.info
def loaderKey {Payload : Type} (loader : Loader Payload) : _root_.Solanalib.Runtime.Pubkey :=
  loader.info.key
def signerKey (signer : Signer) : _root_.Solanalib.Runtime.Pubkey := signer.info.key
def infoKey (info : AccountInfo.Value) : _root_.Solanalib.Runtime.Pubkey := info.key

/-- Type-valued parameters for the six pure projection families. -/
structure ProjectionIndex where
  State : Type
  Payload : Type

def projectionContract {State Args Result : Type} (project : Args → Result) :
    Solanalib.Contracts.Model State Args Result :=
  .returning (fun _ _ => True)
    (fun before args result after => result = project args ∧ after = before)

def projectionFamily (Args Result : Type → Type)
    (project : (Payload : Type) → Args Payload → Result Payload) : Family where
  Index := ProjectionIndex
  State := fun i => i.State
  Args := fun i => Args i.Payload
  Value := fun i => Result i.Payload
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun i => projectionContract (project i.Payload)

def projectionRun (Args Result : Type → Type)
    (project : (Payload : Type) → Args Payload → Result Payload) :
    FamilyRun (projectionFamily Args Result project) :=
  fun i => returnsOf (fun before args => (project i.Payload args, before))

theorem projection_reference (Args Result : Type → Type)
    (project : (Payload : Type) → Args Payload → Result Payload) :
    FamilyReference (projectionFamily Args Result project) (projectionRun Args Result project) := by
  intro i
  apply (realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl⟩

def projectionSample : ProjectionIndex := ⟨Unit, Nat⟩

/-- Both generic type parameters remain arbitrary in the correctness theorem;
this particular state and argument only witness nonvacuity. -/
theorem projection_execution (Args Result : Type → Type)
    (project : (Payload : Type) → Args Payload → Result Payload) (arg : Args Nat) :
    FamilyHasExecution (projectionFamily Args Result project)
      (projectionRun Args Result project) projectionSample := by
  exact ⟨(), arg, .returned (project Nat arg) (), trivial, rfl⟩

end Solanalib.Specs.Core.AnchorAccount
