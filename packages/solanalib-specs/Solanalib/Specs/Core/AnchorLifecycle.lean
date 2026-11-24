/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorConstructOwned
public import Solanalib.Specs.Core.AnchorOwnedSamples
public import Solanalib.Specs.Core.OwnedFocusFacts
public import Solanalib.Specs.Core.AnchorErrorOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World ConstructorUnwind ConstructorTerminal)

/-- The AccountInfo of the wrapper is owned in Anchor 0.27, and borrowed in the
reviewed later versions. This is an ownership distinction, not a copy of the
lamport/data cells: both representations retain their alias identities. -/
inductive InfoStorage where
  | owned
  | borrowed
  deriving DecidableEq, Repr

/-- Validation errors introduced by the account wrappers. Diagnostic text and
numeric codes are the declared Anchor errors in every reviewed release. -/
inductive Code where
  | notEnoughKeys
  | invalidProgramId
  | invalidProgramExecutable
  | notSigner
  | notSystemOwned
  | sysvarMismatch
  deriving DecidableEq, Repr

def Code.payload : Code → AnchorError.AnchorValue
  | .notEnoughKeys =>
    ⟨"AccountNotEnoughKeys", 3005, "Not enough account keys given to the instruction", none, none⟩
  | .invalidProgramId =>
    ⟨"InvalidProgramId", 3008, "Program ID was not as expected", none, none⟩
  | .invalidProgramExecutable =>
    ⟨"InvalidProgramExecutable", 3009, "Program account is not executable", none, none⟩
  | .notSigner =>
    ⟨"AccountNotSigner", 3010, "The given account did not sign", none, none⟩
  | .notSystemOwned =>
    ⟨"AccountNotSystemOwned", 3011, "The given account is not owned by the system program", none,
      none⟩
  | .sysvarMismatch =>
    ⟨"AccountSysvarMismatch", 3015, "The given public key does not match the required \
      sysvar",
      none, none⟩

/-- The owned error dependencies are scoped to their real primitive calls.
They may terminate and alter auxiliary state; no allocation success is built
into a wrapper contract. -/
structure Base where
  Aux : Type
  Unwind : Type
  Terminal : Type
  StringResource : Type
  BoxResource : Type
  Program : Type
  errorStorage : AnchorErrorOperations.Storage
  errors : AnchorErrorOperations.Ops (World Aux) Program StringResource BoxResource Terminal
  /-- Interpret the fixed builtin errors raised by these local SDK operations.
  The source binding supplies the enum representation of the exact release. -/
  programValue : ProgramError.Value → Program

abbrev Base.Error (base : Base) :=
  AnchorErrorOperations.Error base.errorStorage base.Program base.StringResource base.BoxResource
abbrev Base.Unw (base : Base) := ConstructorUnwind base.Unwind
abbrev Base.Term (base : Base) := ConstructorTerminal base.Terminal
abbrev Base.Run (base : Base) (Args Value : Type) :=
  Callback.Run (World base.Aux) Args Value base.Unw base.Term

def Base.ofConstructor (types : AnchorConstructOwned.Types) : Base :=
  ⟨types.Aux, types.Unwind, types.Terminal, types.StringResource, types.BoxResource,
    ProgramError.Value, .boxed, AnchorErrorOperations.Ops.fromOwned types.errors, id⟩

/-- Widen the non-unwinding Global/error dependency without adding an exit. -/
def dependency (base : Base) {Args Value : Type}
    (run : Callback.Run (World base.Aux) Args Value Empty base.Terminal) :
    base.Run Args Value := AnchorAccount.widenCallback (AccountInfoRc.lift run)

def code (base : Base) (failure : Code) : base.Run Unit base.Error :=
  fun before _ => dependency base (AnchorErrorOperations.fromCode base.errorStorage base.errors)
    before
    ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩

def programError (base : Base) (failure : ProgramError.Value) : base.Run Unit base.Error :=
  fun before _ => dependency base (AnchorErrorOperations.fromProgram base.errorStorage base.errors)
    before (base.programValue failure)

def fail {Value : Type} (base : Base) (failure : Code) :
    base.Run Unit (Except base.Error Value) := Callback.map Except.error (code base failure)

def dropError (base : Base) (error : base.Error) :
    Owned.DropAction (World base.Aux) base.Unw base.Term :=
  fun before => dependency base
    (fun state (_ : Unit) => AnchorErrorOperations.drop base.errorStorage base.errors state error)
      before ()

/-- The fixed Global Rc and error destructors do not unwind. An unrelated
double-unwind terminal is therefore not fabricated by this policy. -/
def noDoubleUnwind (base : Base) : Owned.DoubleUnwind (World base.Aux) base.Unw base.Term :=
  fun _ _ _ _ => False

def cloneInfo (base : Base) (rc : AccountInfoRc.Ops (World base.Aux) base.Terminal) :
    base.Run AccountInfo.Value AccountInfo.Value := dependency base (AccountInfoRc.cloneCall rc)

def dropInfo (base : Base) (rc : AccountInfoRc.Ops (World base.Aux) base.Terminal)
    (info : AccountInfo.Value) : Owned.DropAction (World base.Aux) base.Unw base.Term :=
  fun state => dependency base (AccountInfoRc.dropCall rc) state info

/-- Borrowed wrappers create no Rc owner; old owned wrappers clone the same
two cell identities in declaration order. -/
def retainInfo (storage : InfoStorage) (base : Base)
    (rc : AccountInfoRc.Ops (World base.Aux) base.Terminal) :
    base.Run AccountInfo.Value AccountInfo.Value :=
  match storage with
  | .borrowed => Callback.ofFunction fun state info => .returned info state
  | .owned => cloneInfo base rc

/-- Sysvar has the same mathematical payload and AccountInfo fields as an
Account. Its validation dependency and ownership profile remain separate. -/
abbrev Sysvar (Payload : Type) := AnchorAccount.Account Payload

/-- A source AccountInfo record identity is independent of the Rc aliases in
its fields. Equal contents never imply equal addresses. Input references are
represented by the live slice/reference interpretation of the caller. -/
structure AccountReference where
  identity : Nat
  info : AccountInfo.Value
  deriving DecidableEq, Repr

structure ReferenceArgs where
  profile : AccountInfo.Profile
  reference : AccountReference
  deriving DecidableEq, Repr

def ReferenceArgs.info (args : ReferenceArgs) : AccountInfo.Value := args.reference.info

def ReferenceArgs.toAccountInfoArgs (args : ReferenceArgs) : AccountInfo.Args :=
  ⟨args.profile, args.info⟩

/-- Source arguments unaffected by consuming the account slice. The bump type
is an index: the map in 0.27 and later generated bump structs are not identified. -/
structure AccountsArgs where
  profile : AccountInfo.Profile
  programId : Solanalib.Runtime.Pubkey
  instructionData : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

/-- All mutable source arguments to `Accounts::try_accounts` are retained.
The account slice is a sequence of aliases, so order and duplicates matter. -/
structure AccountsState (Bumps : Type) where
  remaining : List AccountReference
  bumps : Bumps
  reallocs : List Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- Lift a leaf constructor into the account-consumption world. Only the
first alias is removed before calling it; its errors/unwinds retain that tail.
The failure factory runs before consumption when the slice is empty. -/
def consume {Aux Bumps Error Value Unwind Terminal : Type}
    (missing : Callback.Run (World Aux) Unit Error Unwind Terminal)
    (construct : Callback.Run (World Aux) ReferenceArgs (Except Error Value) Unwind Terminal) :
    Callback.Run (World Aux × AccountsState Bumps) AccountsArgs
      (Except Error Value) Unwind Terminal :=
  fun before args outcome =>
    match before.2.remaining with
    | [] => Owned.Focus.fst.lift (Callback.map Except.error missing) before () outcome
    | info :: rest => Owned.Focus.fst.lift construct
        (before.1, { before.2 with remaining := rest }) ⟨args.profile, info⟩ outcome

/-- The generic collection wrappers pass these exact arguments to their inner
Accounts callback. They do not summarize it as an arbitrary successful value. -/
structure CollectionTypes where
  Aux : Type
  Bumps : Type
  Payload : Type
  BoxResource : Type
  Error : Type
  Unwind : Type
  Terminal : Type
  missing : Callback.Run (World Aux × AccountsState Bumps) Unit Error Unwind Terminal
  inner : Callback.Run (World Aux × AccountsState Bumps) AccountsArgs
    (Except Error Payload) Unwind Terminal
  newBox : Callback.Run (World Aux × AccountsState Bumps) Payload BoxResource Empty Terminal

def optionAccounts (allowMissing : Bool) (types : CollectionTypes) :
    Callback.Run (World types.Aux × AccountsState types.Bumps) AccountsArgs
      (Except types.Error (Option types.Payload)) types.Unwind types.Terminal :=
  fun before args outcome =>
    match before.2.remaining with
    | [] => if allowMissing then outcome = .returned (.ok none) before
        else Callback.map Except.error types.missing before () outcome
    | info :: rest =>
      if info.info.key = args.programId then
        outcome = .returned (.ok none) (before.1, { before.2 with remaining := rest })
      else Callback.map (Except.map some) types.inner before args outcome

/-- Box allocation runs only after an actual successful inner constructor.
Global allocation is terminal-only on failure, so there is no invented unwind
or destructor continuation for the moved payload. -/
def boxedAccounts (types : CollectionTypes) :
    Callback.Run (World types.Aux × AccountsState types.Bumps) AccountsArgs
      (Except types.Error types.BoxResource) types.Unwind types.Terminal :=
  AnchorEffects.resultBind types.inner fun value state =>
    Callback.map Except.ok (AccountInfoRc.lift types.newBox) state value

/-- The default trait method is a genuine no-op. This family binds only the
provided implementation; overridden implementations are separate identities. -/
structure DefaultExitTypes where
  State : Type
  Receiver : Type
  Error : Type

def defaultExitFamily : Family where
  Index := DefaultExitTypes
  State := DefaultExitTypes.State
  Args := fun types => types.Receiver × Solanalib.Runtime.Pubkey
  Value := fun types => Except types.Error Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => Solanalib.Contracts.Model.returning (fun _ _ => True)
    (fun before _ result after => result = .ok () ∧ after = before)

def defaultExitRun : FamilyRun defaultExitFamily :=
  fun _ => returnsOf fun state _ => (.ok (), state)

theorem defaultExit_reference : FamilyReference defaultExitFamily defaultExitRun := by
  intro types
  apply (realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl⟩

def defaultExitSample : DefaultExitTypes := ⟨Unit, AccountInfo.Value, Unit⟩

theorem defaultExit_execution :
    FamilyHasExecution defaultExitFamily defaultExitRun defaultExitSample := by
  exact ⟨(), (AccountInfo.sampleInfo, .zero), .returned (.ok ()) (), trivial, rfl⟩

/-- A borrowed Box dispatches through its current payload. The lookup is a
source-representation obligation, not permission to choose another receiver. -/
structure DispatchTypes where
  State : Type
  Payload : Type
  BoxResource : Type
  Arg : Type
  Error : Type
  Unwind : Type
  Terminal : Type
  current : State → BoxResource → Option Payload
  call : Callback.Run State (Payload × Arg) (Except Error Unit) Unwind Terminal

def boxedDispatch (types : DispatchTypes) :
    Callback.Run types.State (types.BoxResource × types.Arg)
      (Except types.Error Unit) types.Unwind types.Terminal :=
  fun before (box, args) outcome =>
    ∃ value, types.current before box = some value ∧ types.call before (value, args) outcome

def optionDispatch (types : DispatchTypes) :
    Callback.Run types.State (Option types.Payload × types.Arg)
      (Except types.Error Unit) types.Unwind types.Terminal :=
  fun before (value, args) outcome =>
    match value with
    | none => outcome = .returned (.ok ()) before
    | some value => types.call before (value, args) outcome

end Solanalib.Specs.Core.AnchorLifecycle
