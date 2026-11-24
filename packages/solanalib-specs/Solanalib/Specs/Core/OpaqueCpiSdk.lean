/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpi
public import Solanalib.Specs.Core.BorrowFacts
public import Solanalib.Specs.Core.ProgramError

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Sdk

open Solanalib.Runtime

/-- Source account infos retain both independently shared RefCell identities.
The translated info carries the runtime pointer facts; source representation is
checked separately. Repeated keys do not imply equal RefCell identities. -/
structure Account where
  info : CpiAccountInfo
  lamports : Borrow.Handle
  data : Borrow.Handle
  deriving DecidableEq, Repr

/-- Only leases are stored here. Account values remain in the canonical current
invocation state, so mutable data is not duplicated in a stale borrow snapshot. -/
abbrev BorrowState := Borrow.State Unit Unit

/-- SDK runtime state and one shared lease world across every AccountInfo alias. -/
structure State where
  invocation : InvState
  borrows : BorrowState

/-- Unsigned source arguments have no hidden signer-tree parameter. -/
structure UnsignedArgs where
  instruction : CpiInstruction
  accounts : List Account
  infosBelowInput : Bool
  deriving DecidableEq, Repr

/-- Signed source arguments retain every signer group and every seed, including
empty groups, empty seeds and repeated bytes. -/
structure Args extends UnsignedArgs where
  signers : List (List Bytes)
  deriving DecidableEq, Repr

/-- An unsigned invocation is exactly the signed request with no PDA signers. -/
def UnsignedArgs.signed (args : UnsignedArgs) : Args := ⟨args, []⟩

/-- The existing generic request vocabulary, before runtime pointer facts are
added. Lists retain source account order and multiplicity. -/
def Args.request (args : Args) : CpiRequest.Request Account :=
  CpiRequest.signed args.instruction args.accounts args.signers

/-- Pointer facts accompany the same complete ordered request. -/
def Args.runtimeRequest (args : Args) : CpiReq :=
  ⟨args.request.instruction, args.request.accounts.map Account.info,
    args.infosBelowInput, args.request.signers⟩

@[simp] theorem Args.accounts_preserved (args : Args) :
    args.runtimeRequest.infos = args.accounts.map Account.info := rfl

@[simp] theorem Args.signers_preserved (args : Args) :
    args.runtimeRequest.signers = args.signers := rfl

@[simp] theorem UnsignedArgs.no_signers (args : UnsignedArgs) :
    args.signed.runtimeRequest.signers = [] := rfl

/-- A temporary SDK borrow is acquired and released immediately. Released
identity tombstones are retained in the common resource vocabulary. -/
def probe (mode : Borrow.Mode) (handle : Borrow.Handle) (before : BorrowState) :
    Bool × BorrowState :=
  let (borrowed, during) := Borrow.acquire before handle mode ()
  match borrowed with
  | .error _ => (false, during)
  | .ok guard =>
    let (released, after) := Borrow.release during guard
    (released.isOk, after)

/-- Required lamports borrowing precedes required data borrowing. A failed
first probe never attempts the second; both source errors are AccountBorrowFailed. -/
def probeAccount (writable : Bool) (account : Account) (before : BorrowState) :
    Bool × BorrowState :=
  let mode := if writable then Borrow.Mode.exclusive else .shared
  let (lamports, afterLamports) := probe mode account.lamports before
  if lamports then probe mode account.data afterLamports
  else (false, afterLamports)

/-- Metas are inspected in instruction order. The first matching supplied
AccountInfo is probed, including when later infos share its key but not its
cells. Absent infos remain a runtime MissingAccount check. -/
def preflight (accounts : List Account) :
    BorrowState → List CpiMeta → Bool × BorrowState
  | before, [] => (true, before)
  | before, item :: metas =>
    match accounts.find? (fun account => account.info.key == item.key) with
    | none => preflight accounts before metas
    | some account =>
      let (result, after) := probeAccount (item.writableByte == 1) account before
      if result then preflight accounts after metas else (false, after)

/-- The checked signature contract: local borrow failure returns ordinarily;
otherwise canonical CPI success returns Ok and canonical failure terminates.
These are explicit on-chain interface assumptions, not a proof of an SDK body. -/
def checkedRun (index : OpaqueCpi.Index) (before : State) (args : Args) :
    Outcome State (Except ProgramError.Value Unit) Empty InstrError → Prop :=
  let (checked, borrows) := preflight args.accounts before.borrows args.instruction.metas
  if checked then fun outcome => match outcome with
    | .returned value after =>
        value = .ok () ∧ after.borrows = borrows ∧
          OpaqueCpi.run index before.invocation args.runtimeRequest
            (.returned () after.invocation)
    | .unwound reason _ => nomatch reason
    | .terminated error =>
        OpaqueCpi.run index before.invocation args.runtimeRequest (.terminated error)
  else fun outcome =>
    outcome = .returned (.error .accountBorrowFailed) ⟨before.invocation, borrows⟩

/-- Metering can also terminate while the source checks its local borrows. -/
def run (index : OpaqueCpi.Index) (before : State) (args : Args)
    (outcome : Outcome State (Except ProgramError.Value Unit) Empty InstrError) : Prop :=
  outcome = .terminated .ComputationalBudgetExceeded ∨ checkedRun index before args outcome

def signedFamily : Family where
  Index := OpaqueCpi.Index
  State := fun _ => State
  Args := fun _ => Args
  Value := fun _ => Except ProgramError.Value Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => InstrError
  contract := fun index => { requires := fun _ _ => True, post := run index }

def signedRun : FamilyRun signedFamily := run

theorem signedReference : FamilyReference signedFamily signedRun := by
  intro _ _ _ _ _ execution
  exact execution

def unsignedFamily : Family where
  Index := OpaqueCpi.Index
  State := fun _ => State
  Args := fun _ => UnsignedArgs
  Value := fun _ => Except ProgramError.Value Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => InstrError
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args => run index before args.signed }

def unsignedRun : FamilyRun unsignedFamily := fun index before args =>
  run index before args.signed

theorem unsignedReference : FamilyReference unsignedFamily unsignedRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- A failed local borrow cannot be converted into success or a runtime call. -/
theorem borrow_failure {index : OpaqueCpi.Index} {before : State} {args : Args}
    {borrows : BorrowState}
    (failed : preflight args.accounts before.borrows args.instruction.metas =
      (false, borrows)) (outcome : Outcome State (Except ProgramError.Value Unit)
        Empty InstrError) :
    run index before args outcome ↔
      outcome = .terminated .ComputationalBudgetExceeded ∨
        outcome = .returned (.error .accountBorrowFailed) ⟨before.invocation, borrows⟩ := by
  simp only [run, checkedRun, failed, Bool.false_eq_true, ↓reduceIte]

/-- Returning Ok proves the actual canonical stage contract, including account
synchronization. No PDA or runtime authorization is inferred from a signer flag. -/
theorem success {index : OpaqueCpi.Index} {before after : State} {args : Args}
    (returned : run index before args (.returned (.ok ()) after)) :
    OpaqueCpi.run index before.invocation args.runtimeRequest
      (.returned () after.invocation) := by
  rcases returned with stopped | returned
  · cases stopped
  cases checked : preflight args.accounts before.borrows args.instruction.metas with
  | mk result borrows =>
    cases result with
    | false => simp [checkedRun, checked] at returned
    | true =>
      have actual : after.borrows = borrows ∧
          OpaqueCpi.run index before.invocation args.runtimeRequest
            (.returned () after.invocation) := by
        simpa [checkedRun, checked] using returned
      exact actual.2

/-- All ordinary errors originate in the local preflight; a runtime error from a callee does not
turn into a recoverable source Result::Err. -/
theorem error_before_runtime {index : OpaqueCpi.Index} {before after : State}
    {args : Args} {error : ProgramError.Value}
    (returned : run index before args (.returned (.error error) after)) :
    error = .accountBorrowFailed ∧ ∃ borrows,
      preflight args.accounts before.borrows args.instruction.metas =
        (false, borrows) ∧ after.invocation = before.invocation := by
  rcases returned with stopped | returned
  · cases stopped
  cases checked : preflight args.accounts before.borrows args.instruction.metas with
  | mk result borrows =>
    cases result with
    | false =>
      have same : (.returned (.error error) after :
          Outcome State (Except ProgramError.Value Unit) Empty InstrError) =
          .returned (.error .accountBorrowFailed) ⟨before.invocation, borrows⟩ :=
        by simpa [checkedRun, checked] using returned
      cases same
      exact ⟨rfl, borrows, rfl, rfl⟩
    | true =>
      simp [checkedRun, checked] at returned

end Solanalib.Specs.Core.OpaqueCpi.Sdk
