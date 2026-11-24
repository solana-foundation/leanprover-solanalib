/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.CommonGraph

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (pgraph_ite withGuard_graph)

def serializeAccountFn (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (account : AnchorAccount.Account Nat)
    (profile : AccountInfo.Profile) : Option (Out (Except (Error storage) Unit)) :=
  match AccountInfo.tryBorrowMutData state.1 ⟨profile, account.info⟩ with
  | (.error failure, during) => (programFn storage (during, state.2) (.plain failure)).map
    (Outcome.map Except.error)
  | (.ok guard, during) => match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      ((serializeFn storage script target (during, state.2) ⟨account.value, account.info, guard,
        bytes, 0⟩).map
        AnchorAccount.widen).bind (AccountInfo.GuardCallback.releaseOutcome guard)

theorem serializeAccount_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (account : AnchorAccount.Account Nat)
    (profile : AccountInfo.Profile) :
    PGraph (serializeAccount (exitTypes storage script target) state (account, profile))
      (serializeAccountFn storage script target state account profile) := by
  unfold serializeAccount serializeAccountFn
  dsimp only
  rcases AccountInfo.tryBorrowMutData state.1 ⟨profile, account.info⟩ with ⟨borrowed, during⟩
  cases borrowed with
  | error failure => exact PGraph.map _ (program_graph storage _ failure)
  | ok guard =>
    dsimp only
    rcases Borrow.current during guard with _ | ⟨view, content⟩
    · exact PGraph.false
    · cases content
      · exact PGraph.false
      · exact withGuard_graph guard (widened_graph (PGraph.ofOption _))

def serializeScopedFn (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage) (script :
  Script)
    (target : AccountInfo.Value) (state : W) (account : AnchorAccount.Account Nat)
    (profile : AccountInfo.Profile) : Option (Out (Except (Error storage) Unit)) :=
  if cloneLocal then (cloneFn state account.info).bind (PGraph.bindK fun info afterClone =>
    (serializeAccountFn storage script target afterClone ⟨account.value, info⟩ profile).bind
      (PGraph.cleanupFn noDouble [dropInfoFn info]))
  else serializeAccountFn storage script target state account profile

theorem serializeScoped_graph (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage) (script
  : Script)
    (target : AccountInfo.Value) (state : W) (account : AnchorAccount.Account Nat)
    (profile : AccountInfo.Profile) :
    PGraph (serializeScoped cloneLocal (exitTypes storage script target) state (account, profile))
      (serializeScopedFn cloneLocal storage script target state account profile) :=
  pgraph_ite _ (PGraph.bind (clone_graph storage state account.info) fun info afterClone =>
    PGraph.scope (noDouble_graph storage)
      (PGraph.DropsGraph.cons (dropInfo_graph storage info) PGraph.DropsGraph.nil)
      (serializeAccount_graph storage script target afterClone ⟨account.value, info⟩ profile))
    (serializeAccount_graph storage script target state account profile)

def exitExpectedFn (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (account : AnchorAccount.Account Nat) (profile :
      AccountInfo.Profile)
    (program expected : Solanalib.Runtime.Pubkey) (state : W) : Option (Out (Except (Error storage)
      Unit)) :=
  if expected = program then (isClosedFn state ⟨profile, account.info⟩).bind
    (PGraph.bindK fun closed after => if closed then some (.returned (.ok ()) after)
      else serializeScopedFn cloneLocal storage script target after account profile)
  else some (.returned (.ok ()) state)

theorem exitExpected_graph (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage) (script :
  Script)
    (target : AccountInfo.Value) (account : AnchorAccount.Account Nat) (profile :
      AccountInfo.Profile)
    (program expected : Solanalib.Runtime.Pubkey) (state : W) :
    PGraph (exitExpected cloneLocal (exitTypes storage script target) account profile program
      expected state ())
      (exitExpectedFn cloneLocal storage script target account profile program expected state) :=
  pgraph_ite _ (PGraph.bind (isClosed_graph state ⟨profile, account.info⟩) fun _ after =>
    pgraph_ite _ (PGraph.eq_left _) (serializeScoped_graph cloneLocal storage script target after
      account profile))
    (PGraph.eq_left _)

def exitFn (kind : PayloadKind) (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (state : W) (args : ExitArgs kind Nat) :
    Option (Out (Except (Error storage) Unit)) :=
  match kind with
  | .account => ((keyFn script.owner target .owner "script owner" state).map
    AnchorAccount.widen).bind
      (PGraph.bindK fun expected after =>
        exitExpectedFn cloneLocal storage script target args.wrapper args.profile args.programId
          expected after)
  | .interfaceAccount => exitExpectedFn cloneLocal storage script target args.wrapper.account
    args.profile
      args.programId args.wrapper.owner state

theorem exit_graph (kind : PayloadKind) (cloneLocal : Bool) (storage :
  AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (state : W) (args : ExitArgs kind Nat) :
    PGraph (exit kind cloneLocal (exitTypes storage script target) state args)
      (exitFn kind cloneLocal storage script target state args) := by
  cases kind
  · exact PGraph.bind (widened_graph (PGraph.ofOption _)) fun _ _ => exitExpected_graph _ _ _ _ _ _
      _ _ _
  · exact exitExpected_graph _ _ _ _ _ _ _ _ _

abbrev CloseOut (Value : Type) := Outcome W Value (ClosePanic ⊕ AnchorAccount.ConstructorUnwind
  String)
  (ClosePanic ⊕ AnchorAccount.ConstructorTerminal Unit)

def commonCloseFn (mode : CloseMode) (storage : AnchorErrorOperations.Storage) (state : W) (args :
  CloseArgs) :
    Option (CloseOut (Except (Error storage) Unit)) :=
  match commonCloseCore mode (sdk.get state) args with
  | none => none
  | some (.unwound reason after) => some (.unwound (.inl reason) (sdk.set state after))
  | some (.terminated reason) => some (.terminated (.inl reason))
  | some (.returned (.ok ()) after) => some (.returned (.ok ()) (sdk.set state after))
  | some (.returned (.error failure) after) =>
    ((programFn storage (sdk.set state after) (.plain failure)).map (Outcome.map Except.error)).map
      closeLift

theorem commonClose_graph (mode : CloseMode) (storage : AnchorErrorOperations.Storage) (state : W)
  (args : CloseArgs) :
    PGraph (commonClose mode (closeTypes storage) state args) (commonCloseFn mode storage state
      args) := by
  unfold commonClose commonCloseFn
  dsimp only [closeTypes]
  rcases commonCloseCore mode (sdk.get state) args with _ | produced
  · exact PGraph.false
  · cases produced with
    | unwound _ _ => exact PGraph.eq_left _
    | terminated _ => exact PGraph.eq_left _
    | returned value _ =>
      cases value
      · exact PGraph.exists_eq closeLift (PGraph.map Except.error (program_graph storage _ _))
      · exact PGraph.eq_left _

def closeDropFn (info : AccountInfo.Value) (state : W) : Option (CloseOut Unit) :=
  (dropInfoFn info state).map closeLift

theorem closeDrop_graph (storage : AnchorErrorOperations.Storage) (info : AccountInfo.Value) (state
  : W) :
    PGraph (closeLiftCall (fun current (_ : Unit) => dropInfo (base storage) rc info current) state
      ())
      (closeDropFn info state) := PGraph.exists_eq closeLift (dropInfo_graph storage info state)

def closeFn (cloneSource : Bool) (mode : CloseMode) (storage : AnchorErrorOperations.Storage)
    (state : W) (args : CloseArgs) : Option (CloseOut (Except (Error storage) Unit)) :=
  if cloneSource then ((cloneFn state args.info).map closeLift).bind (PGraph.bindK fun info
    afterClone =>
    (commonCloseFn mode storage afterClone { args with info := info }).bind
      (PGraph.cleanupFn (fun _ _ _ => none) [closeDropFn args.destination, closeDropFn info]))
  else (commonCloseFn mode storage state args).bind
    (PGraph.cleanupFn (fun _ _ _ => none) [closeDropFn args.destination])

theorem close_graph (cloneSource : Bool) (mode : CloseMode) (storage :
  AnchorErrorOperations.Storage)
    (state : W) (args : CloseArgs) :
    PGraph (wrapperClose cloneSource mode (closeTypes storage) state args) (closeFn cloneSource
      mode storage state args) := by
  apply pgraph_ite
  · apply PGraph.bind (PGraph.exists_eq closeLift (clone_graph storage state args.info))
    intro info afterClone
    exact PGraph.scope (fun _ _ _ => PGraph.false)
      (PGraph.DropsGraph.cons (closeDrop_graph storage args.destination)
        (PGraph.DropsGraph.cons (closeDrop_graph storage info) PGraph.DropsGraph.nil))
      (commonClose_graph mode storage afterClone { args with info := info })
  · exact PGraph.scope (fun _ _ _ => PGraph.false)
      (PGraph.DropsGraph.cons (closeDrop_graph storage args.destination) PGraph.DropsGraph.nil)
      (commonClose_graph mode storage state args)

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
