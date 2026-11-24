/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleRead
public import Solanalib.Specs.Core.AccountInfoResize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

/-- Local panic causes in the reviewed Anchor close implementations. -/
inductive ClosePanic where
  | borrowFailed
  | arithmeticOverflow
  deriving DecidableEq, Repr

/-- 1.1.2 reads the source first and uses checked add_lamports. Earlier
versions read the destination first and use checked_add(...).unwrap(). -/
inductive CloseMode where
  | legacy
  | checked
  deriving DecidableEq, Repr

structure CloseArgs where
  profile : AccountInfo.Profile
  info : AccountInfo.Value
  destination : AccountInfo.Value
  deriving DecidableEq, Repr

abbrev CloseOutcome (Value : Type) := Outcome AccountInfoSdk.State Value ClosePanic ClosePanic

def closePanic {Value : Type} (profile : AccountInfo.Profile) (state : AccountInfoSdk.State)
    (reason : ClosePanic) : CloseOutcome Value :=
  if profile.aborts then .terminated reason else .unwound reason state

/-- Option excludes malformed model storage. Rust panics/errors are explicit
finite outcomes; a pending unwind or abort bypasses the next local statement. -/
def closeBind {First Last : Type} (first : Option (CloseOutcome First))
    (next : First → AccountInfoSdk.State → Option (CloseOutcome Last)) : Option (CloseOutcome Last)
      :=
  match first with
  | none => none
  | some (.returned value after) => next value after
  | some (.unwound reason after) => some (.unwound reason after)
  | some (.terminated reason) => some (.terminated reason)

def closeResultBind {First Last : Type} (first : Option (CloseOutcome (Except ProgramError.Value
  First)))
    (next : First → AccountInfoSdk.State → Option (CloseOutcome (Except ProgramError.Value Last))) :
    Option (CloseOutcome (Except ProgramError.Value Last)) :=
  closeBind first fun result after => match result with
    | .error error => some (.returned (.error error) after)
    | .ok value => next value after

def closeRead (profile : AccountInfo.Profile) (state : AccountInfoSdk.State) (info :
  AccountInfo.Value) :
    Option (CloseOutcome Nat) :=
  match AccountInfo.observe .lamports state.borrow info with
  | (.malformed, _) => none
  | (.value value, after) => some (.returned value { state with borrow := after })
  | (.borrowFailed, after) => some (closePanic profile { state with borrow := after } .borrowFailed)

/-- A successful assignment borrows exclusively, writes through the actual
guard and releases that temporary. Checked failure is used only by the 1.1.2
destination add; the source-zero assignment remains borrow_mut and can panic. -/
def closeWrite (checked : Bool) (profile : AccountInfo.Profile) (state : AccountInfoSdk.State)
    (info : AccountInfo.Value) (amount : Nat) : Option (CloseOutcome (Except ProgramError.Value
      Unit)) :=
  let (borrowed, during) := AccountInfo.tryBorrow .exclusive info.lamports state.borrow
  match borrowed with
  | .error failure =>
    if checked then some (.returned (.error failure) { state with borrow := during })
    else some (closePanic profile { state with borrow := during } .borrowFailed)
  | .ok guard =>
    let (written, changed) := Borrow.write during guard (.lamports (UInt64.ofNat amount))
    match written with
    | .error _ => none
    | .ok () =>
      let (released, after) := Borrow.release changed guard
      match released with
      | .error _ => none
      | .ok () => some (.returned (.ok ()) { state with borrow := after })

/-- Both realloc(0,false) and resize(0) have this same reached SDK path:
exclusive borrow, unchanged-length shortcut or shrink, then guard release.
Zeroing is unreachable at length zero. The preserved backing remains in the
shared SDK buffer state, so a later nonzeroing growth can observe its tail. -/
def closeResize (state : AccountInfoSdk.State) (info : AccountInfo.Value) :
    Option (CloseOutcome (Except ProgramError.Value Unit)) :=
  match AccountInfoSdk.prepareResize state ⟨info, 0, false⟩ with
  | .finished result after => some (.returned result after)
  | .malformed | .zero _ _ _ _ => none

def closeAfterBalances (mode : CloseMode) (args : CloseArgs) (state : AccountInfoSdk.State)
    (sourceBalance destinationBalance : Nat) : Option (CloseOutcome (Except ProgramError.Value
      Unit)) :=
  let total := sourceBalance + destinationBalance
  if 2^64 ≤ total then
    match mode with
    | .legacy => some (closePanic args.profile state .arithmeticOverflow)
    | .checked => some (.returned (.error .arithmeticOverflow) state)
  else closeResultBind (closeWrite (mode == .checked) args.profile state args.destination total)
    (fun _ credited => closeResultBind (closeWrite false args.profile credited args.info 0)
      (fun _ zeroed =>
        let assigned := (AccountInfoSdk.assign zeroed (args.info, AnchorAccount.systemProgramId)).2
        closeResize assigned args.info))

/-- The exact local state machine, including distinct aliases, self-close,
read order, partial mutation and the resize error after owner/lamport changes.
It performs no runtime authorization or conservation check absent from source. -/
def commonCloseCore (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs) :
    Option (CloseOutcome (Except ProgramError.Value Unit)) :=
  match mode with
  | .legacy => closeBind (closeRead args.profile state args.destination)
      (fun destinationBalance afterDestination => closeBind (closeRead args.profile
        afterDestination args.info)
        (fun sourceBalance afterSource => closeAfterBalances mode args afterSource sourceBalance
          destinationBalance))
  | .checked => closeBind (closeRead args.profile state args.info)
      (fun sourceBalance afterSource => closeBind (closeRead args.profile afterSource
        args.destination)
        (fun destinationBalance afterDestination => closeAfterBalances mode args afterDestination
          sourceBalance destinationBalance))

structure CloseTypes extends Base where
  sdk : Owned.Focus (AnchorAccount.World Aux) AccountInfoSdk.State
  /-- Local AccountInfo borrowing and SDK resize share the same store. -/
  borrow_eq : ∀ state, (sdk.get state).borrow = state.1
  rc : AccountInfoRc.Ops (AnchorAccount.World Aux) Terminal

abbrev CloseUnwind (types : CloseTypes) := ClosePanic ⊕ types.toBase.Unw
abbrev CloseTerminal (types : CloseTypes) := ClosePanic ⊕ types.toBase.Term

def closeLift {State Value Unwind Terminal : Type} :
    Outcome State Value Unwind Terminal → Outcome State Value (ClosePanic ⊕ Unwind) (ClosePanic ⊕
      Terminal)
  | .returned value after => .returned value after
  | .unwound reason after => .unwound (.inr reason) after
  | .terminated reason => .terminated (.inr reason)

def closeLiftCall {State Args Value Unwind Terminal : Type}
    (run : Callback.Run State Args Value Unwind Terminal) :
    Callback.Run State Args Value (ClosePanic ⊕ Unwind) (ClosePanic ⊕ Terminal) :=
  fun before args outcome => ∃ produced, run before args produced ∧ closeLift produced = outcome

/-- Convert only an actually returned ProgramError, in its actual failure
state. Local panic outcomes retain their own reason and are never Error values. -/
def commonClose (mode : CloseMode) (types : CloseTypes) :
    Callback.Run (AnchorAccount.World types.Aux) CloseArgs (Except types.toBase.Error Unit)
      (CloseUnwind types) (CloseTerminal types) :=
  fun before args outcome =>
    match commonCloseCore mode (types.sdk.get before) args with
    | none => False
    | some (.unwound reason after) => outcome = .unwound (.inl reason) (types.sdk.set before after)
    | some (.terminated reason) => outcome = .terminated (.inl reason)
    | some (.returned (.ok ()) after) => outcome = .returned (.ok ()) (types.sdk.set before after)
    | some (.returned (.error failure) after) =>
      closeLiftCall (Callback.map Except.error (programError types.toBase failure))
        (types.sdk.set before after) () outcome

/-- Old common::close owns its cloned source and moved destination (dropped
destination first). New common::close borrows both; only the moved destination of the outer wrapper
is dropped. Guard cleanup has already happened in the core. -/
def wrapperClose (cloneSource : Bool) (mode : CloseMode) (types : CloseTypes) :
    Callback.Run (AnchorAccount.World types.Aux) CloseArgs (Except types.toBase.Error Unit)
      (CloseUnwind types) (CloseTerminal types) :=
  fun before args outcome =>
    let drops (source : Option AccountInfo.Value) :=
      (fun state => closeLiftCall (fun state (_ : Unit) =>
        dropInfo types.toBase types.rc args.destination state) state ()) ::
      (source.toList.map fun info state => closeLiftCall (fun state (_ : Unit) =>
        dropInfo types.toBase types.rc info state) state ())
    if cloneSource then Callback.bind (closeLiftCall (cloneInfo types.toBase types.rc))
      (fun info afterClone => Owned.scope (fun _ _ _ _ => False) (drops (some info))
        (commonClose mode types) afterClone { args with info := info })
      before args.info outcome
    else Owned.scope (fun _ _ _ _ => False) (drops none) (commonClose mode types) before args
      outcome

/-- Admission at the reached post-balance prefix. Overflow or an earlier
borrow error needs no owner/header premise. The resize input is the actual
state after both assignments and source owner assignment. -/
def CloseBalancesReady (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs)
    (sourceBalance destinationBalance : Nat) : Prop :=
  sourceBalance + destinationBalance < 2^64 →
  ∀ credited, closeWrite (mode == .checked) args.profile state args.destination
    (sourceBalance + destinationBalance) = some (.returned (.ok ()) credited) →
  ∀ zeroed, closeWrite false args.profile credited args.info 0 = some (.returned (.ok ()) zeroed) →
    args.info.ownerRef.id < zeroed.owners.length ∧
    AccountInfoSdk.ResizeReady
      (AccountInfoSdk.assign zeroed (args.info, AnchorAccount.systemProgramId)).2 ⟨args.info, 0,
        false⟩

/-- Read admission follows the actual source order and current state. The
selected typed getter cannot erase a reached local source continuation. -/
def CloseCoreReady (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs) : Prop :=
  match mode with
  | .legacy => AccountInfo.ObservationReady .lamports state.borrow args.destination ∧
      ∀ destinationBalance afterDestination,
        closeRead args.profile state args.destination = some (.returned destinationBalance
          afterDestination) →
        AccountInfo.ObservationReady .lamports afterDestination.borrow args.info ∧
        ∀ sourceBalance afterSource,
          closeRead args.profile afterDestination args.info = some (.returned sourceBalance
            afterSource) →
          CloseBalancesReady mode afterSource args sourceBalance destinationBalance
  | .checked => AccountInfo.ObservationReady .lamports state.borrow args.info ∧
      ∀ sourceBalance afterSource,
        closeRead args.profile state args.info = some (.returned sourceBalance afterSource) →
        AccountInfo.ObservationReady .lamports afterSource.borrow args.destination ∧
        ∀ destinationBalance afterDestination,
          closeRead args.profile afterSource args.destination = some (.returned destinationBalance
            afterDestination) →
          CloseBalancesReady mode afterDestination args sourceBalance destinationBalance

def CommonCloseReady (types : CloseTypes) (before : AnchorAccount.World types.Aux)
    (args : CloseArgs) (mode : CloseMode := .legacy) : Prop :=
  CloseCoreReady mode (types.sdk.get before) args

def closeFamily (cloneSource : Bool) (mode : CloseMode) : Family where
  Index := CloseTypes
  State := fun types => AnchorAccount.World types.Aux
  Args := fun _ => CloseArgs
  Value := fun types => Except types.toBase.Error Unit
  Unwind := CloseUnwind
  Terminal := CloseTerminal
  contract := fun types => {
    requires := fun before args =>
      if cloneSource then ∀ info after,
        cloneInfo types.toBase types.rc before args.info (.returned info after) →
          CommonCloseReady types after { args with info := info } mode
      else CommonCloseReady types before args mode
    post := wrapperClose cloneSource mode types }

def closeRun (cloneSource : Bool) (mode : CloseMode) : FamilyRun (closeFamily cloneSource mode) :=
  wrapperClose cloneSource mode

theorem close_reference (cloneSource : Bool) (mode : CloseMode) :
    FamilyReference (closeFamily cloneSource mode) (closeRun cloneSource mode) := by
  intro _ _ _ _ _ called
  exact called

end Solanalib.Specs.Core.AnchorLifecycle
