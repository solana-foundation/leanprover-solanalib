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
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (pgraph_ite effectsBind_graph
  resultK)

def failFn {Value : Type} (storage : AnchorErrorOperations.Storage) (state : W) (failure : Code) :
    Option (Out (Except (Error storage) Value)) :=
  (codeFn storage state failure).map (Outcome.map Except.error)

theorem fail_graph {Value : Type} (storage : AnchorErrorOperations.Storage) (state : W) (failure :
  Code) :
    PGraph (fail (Value := Value) (base storage) failure state ()) (failFn storage state failure) :=
  PGraph.map Except.error (code_graph storage state failure)

def validationFn (kind : ValidationKind) (ownership : InfoStorage)
    (storage : AnchorErrorOperations.Storage) (script : Script) (target : AccountInfo.Value)
    (legacy : Bool) (state : W) (args : ReferenceArgs) :
    Option (Out (Except (Error storage) (kind.Value Nat))) :=
  match kind with
  | .signer =>
    if args.info.isSigner then (retainFn ownership state args.info).map
      (Outcome.map fun info => Except.ok (AnchorAccount.Signer.mk info))
    else failFn storage state .notSigner
  | .system =>
    if ownerAt state.2 args.info.ownerRef = AnchorAccount.systemProgramId then
      (retainFn ownership state args.info).map (Outcome.map Except.ok)
    else failFn storage state .notSystemOwned
  | .program => (idCheckFn storage script target state args.toAccountInfoArgs).bind
    (PGraph.bindK (resultK fun _ checked =>
      if args.info.executable then (retainFn ownership checked args.info).map
        (Outcome.map fun info => Except.ok (AnchorAccount.Program.mk info))
      else failFn storage checked .invalidProgramExecutable))
  | .interface => ((checkFn storage script.checkId target (.checkId args.info.key)
      "script check_id" state).map AnchorAccount.widen).bind (PGraph.bindK (resultK fun _ checked =>
      if args.info.executable then (retainFn ownership checked args.info).map
        (Outcome.map fun info => Except.ok (AnchorAccount.Interface.mk (AnchorAccount.Program.mk
          info)))
      else failFn storage checked .invalidProgramExecutable))
  | .unchecked => (retainFn ownership state args.info).map (Outcome.map Except.ok)
  | .accountInfo => (cloneFn state args.info).map (Outcome.map Except.ok)
  | .sysvar => ((sysvarFn legacy script target state args.reference).map AnchorAccount.widen).bind
    (PGraph.bindK fun decoded after => match decoded with
      | .error error => (failFn storage after .sysvarMismatch).bind
        (PGraph.cleanupFn noDouble [fun current => (dropStringsFn current error.strings).map
          depLift])
      | .ok value => (retainFn ownership after args.info).map
        (Outcome.map fun info => Except.ok (AnchorAccount.Account.mk value info)))

theorem validation_graph (kind : ValidationKind) (ownership : InfoStorage)
    (storage : AnchorErrorOperations.Storage) (script : Script) (target : AccountInfo.Value)
    (legacy : Bool) (state : W) (args : ReferenceArgs) :
    PGraph (validate kind ownership (validationTypes storage script target legacy) state args)
      (validationFn kind ownership storage script target legacy state args) := by
  cases kind with
  | signer =>
    exact pgraph_ite _ (PGraph.map _ (retain_graph ownership storage state args.info))
      (fail_graph storage state .notSigner)
  | system =>
    exact pgraph_ite _ (PGraph.map _ (retain_graph ownership storage state args.info))
      (fail_graph storage state .notSystemOwned)
  | program =>
    exact effectsBind_graph (idCheck_graph storage script target legacy state
      args.toAccountInfoArgs)
      fun _ checked => pgraph_ite _ (PGraph.map _ (retain_graph ownership storage checked
        args.info))
        (fail_graph storage checked .invalidProgramExecutable)
  | interface =>
    exact effectsBind_graph (widened_graph (PGraph.ofOption _)) fun _ checked =>
      pgraph_ite _ (PGraph.map _ (retain_graph ownership storage checked args.info))
        (fail_graph storage checked .invalidProgramExecutable)
  | unchecked => exact PGraph.map _ (retain_graph ownership storage state args.info)
  | accountInfo => exact PGraph.map _ (clone_graph storage state args.info)
  | sysvar =>
    apply PGraph.bind (widened_graph (PGraph.ofOption _))
    intro decoded after
    cases decoded with
    | error error =>
      apply PGraph.scope (noDouble_graph storage)
        (PGraph.DropsGraph.cons (fun current => dependency_graph storage (dropStrings_graph current
          error.strings))
          PGraph.DropsGraph.nil)
      exact fail_graph storage after .sysvarMismatch
    | ok value => exact PGraph.map _ (retain_graph ownership storage after args.info)

def validationAccountsTypes (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (legacy : Bool) : ValidationAccountsTypes :=
  ⟨validationTypes storage script target legacy, Nat⟩

theorem validationAccounts_graph (kind : ValidationKind) (ownership : InfoStorage)
    (storage : AnchorErrorOperations.Storage) (script : Script) (target : AccountInfo.Value)
    (legacy : Bool) (state : W × AccountsState Nat) (args : AccountsArgs) :
    PGraph (validationAccountsRun kind ownership (validationAccountsTypes storage script target
      legacy) state args)
      (consumeFn storage (validationFn kind ownership storage script target legacy) state args) :=
  consume_graph storage (validation_graph kind ownership storage script target legacy) state args

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
