/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorEffects
public import Solanalib.Specs.Core.AnchorSpl
public import Solanalib.Specs.Core.AnchorErrorOwned
public import Solanalib.Specs.Core.AnchorErrorOwnedTransport

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplAmountOwned

structure Types where
  Aux : Type
  Terminal : Type
  StringResource : Type
  BoxResource : Type
  errors : AnchorErrorOwned.Ops (AnchorAccount.World Aux) StringResource BoxResource Terminal

abbrev Error (types : Types) := AnchorErrorOwned.Error types.BoxResource
abbrev Terminal (types : Types) := AnchorSpl.AmountPanic ⊕ types.Terminal

/-- The accessor boxes a checked borrow error through the actual Anchor
conversion. Fixed-source Global allocation has no unwind callback, but its
terminal outcome is retained. -/
def program (types : Types) (failure : ProgramError.Value) :
    Callback.Run (AnchorAccount.World types.Aux) Unit (Error types)
      AnchorSpl.AmountPanic (Terminal types) :=
  fun before _ outcome => ∃ produced,
    AnchorErrorOwned.fromProgram types.errors before failure produced ∧
    (match produced with
      | .returned value after => outcome = .returned value after
      | .unwound impossible _ => nomatch impossible
      | .terminated reason => outcome = .terminated (.inr reason))

/-- Read the actual shared data guard at bytes 64..72. A short slice still
panics; successful reads release the guard. Only checked borrow failure calls
the boxed-error conversion, so the model adds no owner or full-codec check. -/
def run (types : Types) :
    Callback.Run (AnchorAccount.World types.Aux) AccountInfo.Args (Except (Error types) Nat)
      AnchorSpl.AmountPanic (Terminal types) :=
  fun before args outcome =>
    let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
    match borrowed with
    | .error failure => Callback.map Except.error (program types failure) (during, before.2) ()
      outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) =>
        match Token.readNat bytes 64 8 with
        | some value => match Borrow.release during guard with
          | (.ok (), after) => outcome = .returned (.ok value) (after, before.2)
          | (.error _, _) => False
        | none =>
          if args.profile.aborts then outcome = .terminated (.inl .sliceBounds)
          else match Borrow.release during guard with
            | (.ok (), after) => outcome = .unwound .sliceBounds (after, before.2)
            | (.error _, _) => False

/-- A checked borrow error forwards every actual error-conversion exit and
its effects. No data guard was acquired, so this branch adds no cleanup. -/
theorem run_borrow_error {types : Types} {before : AnchorAccount.World types.Aux}
    {args : AccountInfo.Args} {during : AccountInfo.State} {failure : ProgramError.Value}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.error failure, during))
    {produced : Outcome (AnchorAccount.World types.Aux) (Error types)
      AnchorSpl.AmountPanic (Terminal types)}
    (converted : program types failure (during, before.2) () produced) :
    run types before args (Outcome.map Except.error produced) := by
  simp only [run, acquired]
  exact ⟨produced, converted, rfl⟩

/-- The local read has no error allocation. Ordinary success and slice unwind
release the actual acquired guard; terminal slice panic has no post-state. -/
def readOutcome (types : Types) (auxiliary : types.Aux) (profile : AccountInfo.Profile)
    (during : AccountInfo.State) (guard : Borrow.Guard) (bytes : _root_.Solanalib.Runtime.Bytes) :
    Outcome (AnchorAccount.World types.Aux) (Except (Error types) Nat)
      AnchorSpl.AmountPanic (Terminal types) :=
  match Token.readNat bytes 64 8 with
  | some value => .returned (.ok value) ((Borrow.release during guard).2, auxiliary)
  | none =>
    if profile.aborts then .terminated (.inl .sliceBounds)
    else .unwound .sliceBounds ((Borrow.release during guard).2, auxiliary)

/-- Actual current data suffices for the complete local read/cleanup branch;
release availability follows from acquisition rather than an extra premise. -/
theorem run_read {types : Types} {before : AnchorAccount.World types.Aux}
    {args : AccountInfo.Args} {during : AccountInfo.State} {guard : Borrow.Guard}
    {bytes : _root_.Solanalib.Runtime.Bytes}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    (current : Borrow.current during guard = .ok (.whole, .data bytes)) :
    run types before args (readOutcome types before.2 args.profile during guard bytes) := by
  have released := AnchorSpl.amount_release acquired
  cases read : Token.readNat bytes 64 8 with
  | none =>
    by_cases aborts : args.profile.aborts = true <;>
      simp [run, readOutcome, acquired, current, read, aborts, released]
  | some value => simp [run, readOutcome, acquired, current, read, released]

/-- After an admitted successful borrow the data read and cleanup cannot
filter the local outcome. This uses no whole-store or source-width predicate. -/
theorem run_after_borrow {types : Types} {before : AnchorAccount.World types.Aux}
    {args : AccountInfo.Args} {during : AccountInfo.State} {guard : Borrow.Guard}
    (ready : AccountInfo.DataBorrow.Ready .shared before.1 args.info.data)
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      run types before args (readOutcome types before.2 args.profile during guard bytes) := by
  obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current ready acquired
  exact ⟨bytes, current, run_read acquired current⟩

def family : Family where
  Index := Types
  State := fun types => AnchorAccount.World types.Aux
  Args := fun _ => AccountInfo.Args
  Value := fun types => Except (Error types) Nat
  Unwind := fun _ => AnchorSpl.AmountPanic
  Terminal := Terminal
  contract := fun types => {
    requires := fun before args => AccountInfo.DataBorrow.Ready .shared before.1 args.info.data
    post := run types }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ step
  exact step

end Solanalib.Specs.Core.AnchorSplAmountOwned
