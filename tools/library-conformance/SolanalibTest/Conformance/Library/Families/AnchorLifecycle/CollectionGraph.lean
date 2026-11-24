/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.ValidationGraph

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (pgraph_ite effectsBind_graph
  resultK)

abbrev CW := W × AccountsState Nat
abbrev COut (Value : Type) := Outcome CW Value (AnchorAccount.ConstructorUnwind String)
  (AnchorAccount.ConstructorTerminal Unit)

def reallocKey : Solanalib.Runtime.Pubkey := ⟨List.replicate 32 0x32, by decide⟩

def insertRealloc (keys : List Solanalib.Runtime.Pubkey) : List Solanalib.Runtime.Pubkey :=
  if reallocKey ∈ keys then keys
  else (keys ++ [reallocKey]).mergeSort (fun left right => compare left.bytes right.bytes != .gt)

def innerAccountsFn (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : CW) (args : AccountsArgs) : Option (COut (Except (Error storage) Nat)) := do
  let (step, logged) ← begin script.inner target
    (.innerAccounts args.programId args.instructionData state.2.remaining.length) state.1
  let current : CW := (logged, { state.2 with
    remaining := state.2.remaining.drop 1,
    bumps := state.2.bumps + 1, reallocs := insertRealloc state.2.reallocs })
  let callback := (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    if step.panic then some (.unwound "script inner" after)
    else (returnedFn storage after step).map (Outcome.map (Except.map fun _ => step.value)))
  pure ((Owned.Focus.fst : Owned.Focus CW W).liftOutcome current (AnchorAccount.widen (← callback)))

def payloadBoxFn (state : CW) (value : Nat) : Outcome CW Nat Empty Unit :=
  let resource := state.1.2.payloadBoxes.length
  .returned resource ((state.1.1, { state.1.2 with
    payloadBoxes := state.1.2.payloadBoxes ++ [some value], extraLive := state.1.2.extraLive + 1
      }), state.2)

def collectionTypes (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value) :
    AccountCollectionTypes where
  toBase := base storage
  Bumps := Nat
  Payload := Nat
  PayloadBox := Nat
  inner := fun state args outcome => innerAccountsFn storage script target state args = some outcome
  newBox := Callback.ofFunction payloadBoxFn

def optionTypes (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (allowMissing : Bool) : OptionalTypes := ⟨collectionTypes storage script target, allowMissing⟩

def optionAccountsFn (allowMissing : Bool) (storage : AnchorErrorOperations.Storage) (script :
  Script)
    (target : AccountInfo.Value) (state : CW) (args : AccountsArgs) : Option (COut (Except (Error
      storage) (Option Nat))) :=
  match state.2.remaining with
  | [] => if allowMissing then some (.returned (.ok none) state)
      else (failFn storage state.1 .notEnoughKeys).map (Owned.Focus.fst.liftOutcome state)
  | info :: rest => if info.info.key = args.programId then
      some (.returned (.ok none) (state.1, { state.2 with remaining := rest }))
    else (innerAccountsFn storage script target state args).map (Outcome.map (Except.map some))

theorem optionAccounts_graph (allowMissing : Bool) (storage : AnchorErrorOperations.Storage)
  (script : Script)
    (target : AccountInfo.Value) (state : CW) (args : AccountsArgs) :
    PGraph (optionalRun (optionTypes storage script target allowMissing) state args)
      (optionAccountsFn allowMissing storage script target state args) := by
  unfold optionalRun collectionOptionRun optionAccounts optionAccountsFn
  dsimp only [optionTypes, collectionTypes, AccountCollectionTypes.operations]
  cases state.2.remaining with
  | nil =>
    apply pgraph_ite _ (PGraph.eq_left _)
    apply PGraph.congr (PGraph.focusLift Owned.Focus.fst (fail_graph storage state.1
      .notEnoughKeys))
    intro outcome
    constructor
    · rintro ⟨middle, ⟨built, called, rfl⟩, rfl⟩
      exact ⟨Outcome.map Except.error built, ⟨built, called, rfl⟩, by cases built <;> rfl⟩
    · rintro ⟨middle, ⟨built, called, rfl⟩, rfl⟩
      exact ⟨Owned.Focus.fst.liftOutcome state built, ⟨built, called, rfl⟩, by cases built <;> rfl⟩
  | cons info rest => exact pgraph_ite _ (PGraph.eq_left _) (PGraph.map _ (PGraph.ofOption _))

def boxAccountsFn (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : CW) (args : AccountsArgs) : Option (COut (Except (Error storage) Nat)) :=
  (innerAccountsFn storage script target state args).bind (PGraph.bindK (resultK fun value after =>
    (((some (payloadBoxFn after value)).map collectionBoxOutcome).map AccountInfoRc.liftOutcome).map
      (Outcome.map Except.ok)))

theorem boxAccounts_graph (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : CW) (args : AccountsArgs) :
    PGraph (collectionBoxedRun (collectionTypes storage script target) state args)
      (boxAccountsFn storage script target state args) := by
  apply effectsBind_graph (PGraph.ofOption _)
  intro value after
  have graph : PGraph
      (AccountInfoRc.lift (Unwind := AnchorAccount.ConstructorUnwind String)
        (collectionTypes storage script target).operations.newBox after value)
      (((some (payloadBoxFn after value)).map collectionBoxOutcome).map AccountInfoRc.liftOutcome)
        :=
    PGraph.exists_eq AccountInfoRc.liftOutcome
      (PGraph.exists_eq collectionBoxOutcome (PGraph.ofFunction payloadBoxFn after value))
  exact PGraph.map (Except.ok (ε := Error storage)) graph

def innerExitFn (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : W) (args : Nat × Solanalib.Runtime.Pubkey) : Option (Out (Except (Error storage)
      Unit)) :=
  (checkFn storage script.inner target (.innerExit args.1 args.2) "script inner" state).map
    AnchorAccount.widen

def innerCloseFn (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : W) (args : Nat × AccountInfo.Value) : Option (Out (Except (Error storage) Unit)) :=
  ((checkFn storage script.inner target
    (.innerClose args.1 { args.2 with owner := ownerAt state.2 args.2.ownerRef })
      "script inner"
      state).map
      AnchorAccount.widen).bind (PGraph.cleanupFn noDouble [dropInfoFn args.2])

def dispatchTypes {Arg : Type} (storage : AnchorErrorOperations.Storage)
    (fn : W → Nat × Arg → Option (Out (Except (Error storage) Unit))) : DispatchTypes where
  State := W
  Payload := Nat
  BoxResource := Nat
  Arg := Arg
  Error := Error storage
  Unwind := AnchorAccount.ConstructorUnwind String
  Terminal := AnchorAccount.ConstructorTerminal Unit
  current := fun state resource => state.2.payloadBoxes[resource]?.join
  call := fun state args outcome => fn state args = some outcome

def boxDispatchFn {Arg : Type} (storage : AnchorErrorOperations.Storage)
    (fn : W → Nat × Arg → Option (Out (Except (Error storage) Unit)))
    (state : W) (args : Nat × Arg) : Option (Out (Except (Error storage) Unit)) :=
  state.2.payloadBoxes[args.1]?.join.bind fun value => fn state (value, args.2)

theorem boxDispatch_graph {Arg : Type} (storage : AnchorErrorOperations.Storage)
    (fn : W → Nat × Arg → Option (Out (Except (Error storage) Unit))) (state : W) (args : Nat ×
      Arg) :
    PGraph (boxedDispatch (dispatchTypes storage fn) state args) (boxDispatchFn storage fn state
      args) :=
  PGraph.exists_step (PGraph.ofOption _) fun _ => PGraph.ofOption _

def optionDispatchFn {Arg : Type} (storage : AnchorErrorOperations.Storage)
    (fn : W → Nat × Arg → Option (Out (Except (Error storage) Unit)))
    (state : W) (args : Option Nat × Arg) : Option (Out (Except (Error storage) Unit)) :=
  match args.1 with
  | none => some (.returned (.ok ()) state)
  | some value => fn state (value, args.2)

theorem optionDispatch_graph {Arg : Type} (storage : AnchorErrorOperations.Storage)
    (fn : W → Nat × Arg → Option (Out (Except (Error storage) Unit))) (state : W) (args : Option
      Nat × Arg) :
    PGraph (optionDispatch (dispatchTypes storage fn) state args) (optionDispatchFn storage fn
      state args) := by
  rcases args with ⟨value, args⟩
  cases value
  · exact PGraph.eq_left _
  · exact PGraph.ofOption _

def optionCloseTypes (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value) :
    OptionCloseTypes where
  toBase := base storage
  Payload := Nat
  rc := rc
  close := fun state args outcome => innerCloseFn storage script target state args = some outcome

def optionCloseFn (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : W) (args : Option Nat × AccountInfo.Value) : Option (Out (Except (Error storage)
      Unit)) :=
  match args.1 with
  | some value => innerCloseFn storage script target state (value, args.2)
  | none => PGraph.cleanupFn noDouble [dropInfoFn args.2] (.returned (.ok ()) state)

theorem optionClose_graph (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (state : W) (args : Option Nat × AccountInfo.Value) :
    PGraph (optionClose (optionCloseTypes storage script target) state args)
      (optionCloseFn storage script target state args) := by
  rcases args with ⟨value, destination⟩
  cases value
  · exact PGraph.cleanup (noDouble_graph storage) _ _
      (PGraph.DropsGraph.cons (dropInfo_graph storage destination) PGraph.DropsGraph.nil) _
  · exact PGraph.ofOption _

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
