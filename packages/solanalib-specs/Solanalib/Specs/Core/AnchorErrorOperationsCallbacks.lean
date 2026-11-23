/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperations
public import Solanalib.Specs.Core.AnchorErrorOwnedCallbacks

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- Selected storage and the exact String/Box dependencies for one source
instantiation. Program remains the full resource-bearing value of the dependency. -/
structure Types where
  State : Type
  Program : Type
  StringResource : Type
  BoxResource : Type
  Terminal : Type
  storage : Storage
  ops : Ops State Program StringResource BoxResource Terminal

abbrev Types.Error (types : Types) :=
  AnchorErrorOperations.Error types.storage types.Program types.StringResource types.BoxResource

/-- A retained error is dropped through the same generic representation on
the actual cleanup state, with no invented unwind of String/Box destruction. -/
def dropLift (types : Types) {Unwind : Type} (error : types.Error) :
    Owned.DropAction types.State Unwind types.Terminal :=
  fun before outcome => AnchorErrorOwned.lift (drop types.storage types.ops) before error outcome

/-- Finish the locals of the function and moved return place. For inline errors the
returned value is the updated payload, so a cleanup unwind must not redrop the
old origin/comparison captured on entry. On the pinned rustc return-place leak
path (rust-lang/rust#47949), the existing owned model also admits retaining that
returned value; this choice applies only after the body has returned normally. -/
def finishMoved (types : Types) {Unwind : Type}
    (double : Owned.DoubleUnwind types.State Unwind types.Terminal)
    (locals : List (Owned.DropAction types.State Unwind types.Terminal))
    (original : types.Error)
    (pending final : Outcome types.State types.Error Unwind types.Terminal) : Prop :=
  ∃ cleaned, Owned.cleanup double locals pending cleaned ∧
    match pending with
    | .returned value _ =>
      Owned.onUnwind double [dropLift types value] cleaned final ∨
        (∃ reason after, cleaned = .unwound reason after ∧ final = cleaned)
    | .unwound _ _ => Owned.onUnwind double [dropLift types original] cleaned final
    | .terminated _ => final = cleaned

/-- The two ordinary ToString callbacks and their operand destructors are the
existing generic callback vocabulary. Both conversions return String owners. -/
structure ValuesTypes extends Types where
  Left : Type
  Right : Type
  Unwind : Type
  callbacks : AnchorErrorOwned.ValuesCallbacks State StringResource Left Right Unwind Terminal

structure ValuesArgs (Error Left Right : Type) where
  error : Error
  left : Left
  right : Right

/-- The RHS is evaluated left-to-right. If the second conversion unwinds,
the completed first String is destroyed before the operand and receiver scopes. -/
def valuesBody (types : ValuesTypes) (args : ValuesArgs types.toTypes.Error types.Left types.Right)
  :
    Callback.Run types.State Unit types.toTypes.Error types.Unwind types.Terminal :=
  fun before _ => Callback.bind types.callbacks.left
    (fun left middle => Callback.bind
      (Owned.protect types.callbacks.double
        [fun state outcome => AnchorErrorOwned.lift types.ops.dropString state left outcome]
        types.callbacks.right)
      (fun right actual => AnchorErrorOwned.lift
        (withCompared types.storage types.ops (some (.values left right))) actual args.error)
      middle args.right) before args.left

/-- The complete generic with_values operation, including ordinary-result
cleanup, first/second conversion failure, and a destructor during unwinding. -/
def valuesRun (types : ValuesTypes) : Callback.Run types.State
    (ValuesArgs types.toTypes.Error types.Left types.Right) types.toTypes.Error types.Unwind
      types.Terminal :=
  fun before args final => ∃ pending, valuesBody types args before () pending ∧
    finishMoved types.toTypes types.callbacks.double
      [fun state outcome => types.callbacks.dropLeft state args.left outcome,
       fun state outcome => types.callbacks.dropRight state args.right outcome]
      args.error pending final

def valuesFamily : Family where
  Index := ValuesTypes
  State := fun types => types.State
  Args := fun types => ValuesArgs types.toTypes.Error types.Left types.Right
  Value := fun types => types.toTypes.Error
  Unwind := ValuesTypes.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := valuesRun types }

theorem values_reference : FamilyReference valuesFamily valuesRun := fun _ _ _ _ _ run => run

/-- A single borrowed ToString invocation followed by the destructor of the consumed operand. The
storage layout of the receiver is kept by the common base index. -/
structure NameTypes extends Types where
  Name : Type
  Unwind : Type
  toString : Callback.Run State Name StringResource Unwind Terminal
  dropName : Callback.Run State Name Unit Unwind Terminal
  double : Owned.DoubleUnwind State Unwind Terminal

def nameBody (types : NameTypes) (args : types.toTypes.Error × types.Name) :
    Callback.Run types.State Unit types.toTypes.Error types.Unwind types.Terminal :=
  fun before _ => Callback.bind types.toString
    (fun name after => AnchorErrorOwned.lift
      (withOrigin types.storage types.ops (some (.accountName name))) after args.1)
    before args.2

def nameRun (types : NameTypes) : Callback.Run types.State (types.toTypes.Error × types.Name)
    types.toTypes.Error types.Unwind types.Terminal :=
  fun before args final => ∃ pending, nameBody types args before () pending ∧
    finishMoved types.toTypes types.double
      [fun state outcome => types.dropName state args.2 outcome] args.1 pending final

def nameFamily : Family where
  Index := NameTypes
  State := fun types => types.State
  Args := fun types => types.toTypes.Error × types.Name
  Value := fun types => types.toTypes.Error
  Unwind := NameTypes.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := nameRun types }

theorem name_reference : FamilyReference nameFamily nameRun := fun _ _ _ _ _ run => run

/-- BorshIoError conversion delegates to the selected ProgramError conversion.
That dependency consumes the full IoError, including its formatting and drop;
the resulting ProgramError is moved unchanged into the selected wrapper of Anchor. -/
structure IoTypes extends Types where
  IoError : Type
  Unwind : Type
  fromIo : Callback.Run State IoError Program Unwind Terminal

def ioRun (types : IoTypes) : Callback.Run types.State types.IoError
    types.toTypes.Error types.Unwind types.Terminal :=
  fun before input => Callback.bind types.fromIo
    (fun program actual => AnchorErrorOwned.lift
      (fromProgram types.storage types.ops) actual program) before input

def ioFamily : Family where
  Index := IoTypes
  State := fun types => types.State
  Args := IoTypes.IoError
  Value := fun types => types.toTypes.Error
  Unwind := IoTypes.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := ioRun types }

theorem io_reference : FamilyReference ioFamily ioRun := fun _ _ _ _ _ run => run

/-- A terminal first conversion calls neither the right callback nor any
cleanup action. This statement is independent of what those providers allow. -/
theorem valuesBody_first_terminal (types : ValuesTypes)
    (args : ValuesArgs types.toTypes.Error types.Left types.Right) (before : types.State)
    (reason : types.Terminal) (called : types.callbacks.left before args.left (.terminated reason))
      :
    valuesBody types args before () (.terminated reason) :=
  ⟨.terminated reason, called, rfl⟩

/-- A terminal body never performs local or receiver destruction. -/
theorem finishMoved_terminal (types : Types) {Unwind : Type}
    (double : Owned.DoubleUnwind types.State Unwind types.Terminal)
    (locals : List (Owned.DropAction types.State Unwind types.Terminal))
    (original : types.Error) (reason : types.Terminal) :
    finishMoved types double locals original (.terminated reason) (.terminated reason) := by
  refine ⟨.terminated reason, ?_, rfl⟩
  exact (Owned.cleanup_terminated double locals reason _).2 rfl

end Solanalib.Specs.Core.AnchorErrorOperations
