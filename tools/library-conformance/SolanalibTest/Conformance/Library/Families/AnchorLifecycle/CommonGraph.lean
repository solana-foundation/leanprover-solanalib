/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Callbacks
import SolanalibTest.Conformance.Library.Families.Anchor.Construct

/-! Executable graphs of local reads, diagnostics and slice consumption. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (pgraph_ite effectsBind_graph
  resultK withGuard_graph)

def noDouble : W → AnchorAccount.ConstructorUnwind String → AnchorAccount.ConstructorUnwind String →
    Option (AnchorAccount.ConstructorTerminal Unit) := fun _ _ _ => none

theorem noDouble_graph (storage : AnchorErrorOperations.Storage) (state : W)
    (first second : AnchorAccount.ConstructorUnwind String) :
    PGraph (noDoubleUnwind (base storage) state first second) (noDouble state first second) :=
      PGraph.false

def observeFn (field : AccountInfo.Observation) (state : W) (args : AccountInfo.Args) : Option (Out
  Nat) :=
  match AccountInfo.observe field state.1 args.info with
  | (.malformed, _) => none
  | (.value value, after) => some (.returned value (after, state.2))
  | (.borrowFailed, after) => some (if args.profile.aborts then .terminated (.inl .borrowFailed)
      else .unwound (.inl .borrowFailed) (after, state.2))

theorem observe_graph (field : AccountInfo.Observation) (state : W) (args : AccountInfo.Args) :
    PGraph (observe (Unwind := String) (Terminal := Unit) field state args) (observeFn field state
      args) := by
  unfold observe observeFn
  rcases AccountInfo.observe field state.1 args.info with ⟨value, after⟩
  cases value
  · exact PGraph.eq_left _
  · dsimp only
    split <;> exact PGraph.eq_left _
  · exact PGraph.false

def isClosedFn (state : W) (args : AccountInfo.Args) : Option (Out Bool) :=
  if ownerAt state.2 args.info.ownerRef = AnchorAccount.systemProgramId then
    (observeFn .dataLen state args).map (Outcome.map fun length => length == 0)
  else some (.returned false state)

theorem isClosed_graph (state : W) (args : AccountInfo.Args) :
    PGraph (isClosed (Unwind := String) (Terminal := Unit) ownerAt state args) (isClosedFn state
      args) :=
  pgraph_ite _ (PGraph.map _ (observe_graph .dataLen state args)) (PGraph.eq_left _)

def initializedFn (storage : AnchorErrorOperations.Storage) (state : W) (args : AccountInfo.Args) :
    Option (Out (Except (Error storage) Unit)) :=
  if ownerAt state.2 args.info.ownerRef = AnchorAccount.systemProgramId then
    (observeFn .lamports state args).bind (PGraph.bindK fun balance after =>
      if balance = 0 then (accountCodeFn storage after .notInitialized).map (Outcome.map
        Except.error)
      else some (.returned (.ok ()) after))
  else some (.returned (.ok ()) state)

theorem initialized_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AccountInfo.Args) :
    PGraph (initialized (payloadTypes storage script target checked) state args) (initializedFn
      storage state args) :=
  pgraph_ite _ (PGraph.bind (observe_graph .lamports state args) fun _ after =>
    pgraph_ite _ (PGraph.map _ (accountCode_graph storage after .notInitialized)) (PGraph.eq_left
      _))
    (PGraph.eq_left _)

def idCheckFn (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : AccountInfo.Args) :
    Option (Out (Except (Error storage) Unit)) :=
  ((keyFn script.id target .id "script id" state).map AnchorAccount.widen).bind
    (PGraph.bindK fun expected after =>
      if args.info.key = expected then some (.returned (.ok ()) after)
      else (codeFn storage after .invalidProgramId).bind (PGraph.bindK fun error allocated =>
        (((keyFn script.id target .id "script id" allocated).map AnchorAccount.widen).bind
          (PGraph.bindK fun diagnostic afterId =>
            (withPubkeysFn storage afterId error args.info.key diagnostic).map (Outcome.map
              Except.error))).bind
              (PGraph.onUnwindFn noDouble [dropErrorFn storage error])))

theorem idCheck_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (legacy : Bool) (state : W) (args : AccountInfo.Args) :
    PGraph (idCheck (validationTypes storage script target legacy) state args)
      (idCheckFn storage script target state args) := by
  apply PGraph.bind (widened_graph (PGraph.ofOption _))
  intro expected after
  apply pgraph_ite _ (PGraph.eq_left _)
  apply PGraph.bind (code_graph storage after .invalidProgramId)
  intro error allocated
  apply PGraph.protect (noDouble_graph storage)
    (PGraph.DropsGraph.cons (dropError_graph storage error) PGraph.DropsGraph.nil)
  exact PGraph.bind (widened_graph (PGraph.ofOption _)) fun diagnostic afterId =>
    PGraph.map Except.error (withPubkeys_graph storage afterId error args.info.key diagnostic)

def ownerCheckFn (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : AccountInfo.Args) :
    Option (Out (Except (Error storage) Unit)) :=
  ((keyFn script.owner target .owner "script owner" state).map AnchorAccount.widen).bind
    (PGraph.bindK fun expected after =>
      if ownerAt after.2 args.info.ownerRef = expected then some (.returned (.ok ()) after)
      else (accountCodeFn storage after .ownedByWrongProgram).bind (PGraph.bindK fun error
        allocated =>
        (((keyFn script.owner target .owner "script owner" allocated).map AnchorAccount.widen).bind
          (PGraph.bindK fun diagnostic afterOwner =>
            (withPubkeysFn storage afterOwner error (ownerAt allocated.2 args.info.ownerRef)
              diagnostic).map
              (Outcome.map Except.error))).bind (PGraph.onUnwindFn noDouble [dropErrorFn storage
                error])))

theorem ownerCheck_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AccountInfo.Args) :
    PGraph (ownerCheck (payloadTypes storage script target checked) state args)
      (ownerCheckFn storage script target state args) := by
  apply PGraph.bind (widened_graph (PGraph.ofOption _))
  intro expected after
  apply pgraph_ite _ (PGraph.eq_left _)
  apply PGraph.bind (accountCode_graph storage after .ownedByWrongProgram)
  intro error allocated
  apply PGraph.protect (noDouble_graph storage)
    (PGraph.DropsGraph.cons (dropError_graph storage error) PGraph.DropsGraph.nil)
  exact PGraph.bind (widened_graph (PGraph.ofOption _)) fun diagnostic afterOwner =>
    PGraph.map Except.error (withPubkeys_graph storage afterOwner error
      (ownerAt allocated.2 args.info.ownerRef) diagnostic)

def consumeFn {Value : Type} (storage : AnchorErrorOperations.Storage)
    (leaf : W → ReferenceArgs → Option (Out (Except (Error storage) Value)))
    (state : W × AccountsState Nat) (args : AccountsArgs) :
    Option (Outcome (W × AccountsState Nat) (Except (Error storage) Value)
      (AnchorAccount.ConstructorUnwind String) (AnchorAccount.ConstructorTerminal Unit)) :=
  match state.2.remaining with
  | [] => ((codeFn storage state.1 .notEnoughKeys).map (Outcome.map Except.error)).map
      (Owned.Focus.fst.liftOutcome state)
  | reference :: rest => (leaf state.1 ⟨args.profile, reference⟩).map
      (Owned.Focus.fst.liftOutcome (state.1, { state.2 with remaining := rest }))

theorem consume_graph {Value : Type} (storage : AnchorErrorOperations.Storage)
    {leaf : Callback.Run W ReferenceArgs (Except (Error storage) Value)
      (AnchorAccount.ConstructorUnwind String) (AnchorAccount.ConstructorTerminal Unit)}
    {fn : W → ReferenceArgs → Option (Out (Except (Error storage) Value))}
    (graph : ∀ state args, PGraph (leaf state args) (fn state args))
    (state : W × AccountsState Nat) (args : AccountsArgs) :
    PGraph (consume (code (base storage) .notEnoughKeys) leaf state args) (consumeFn storage fn
      state args) := by
  unfold consume consumeFn
  cases state.2.remaining
  · exact PGraph.focusLift _ (PGraph.map Except.error (code_graph storage state.1 .notEnoughKeys))
  · exact PGraph.focusLift _ (graph _ _)

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
