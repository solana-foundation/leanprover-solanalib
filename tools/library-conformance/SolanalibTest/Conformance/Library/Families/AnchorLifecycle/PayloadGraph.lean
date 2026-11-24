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
  resultK withGuard_graph)

def decoderCleanupFn (storage : AnchorErrorOperations.Storage) (info : AccountInfo.Value)
    (pending : Out (AnchorConstructOwned.Decoded (Error storage) Nat)) :
    Option (Out (AnchorConstructOwned.Decoded (Error storage) Nat)) :=
  match pending with
  | .returned decoded _ => match decoded.result with
    | .ok _ => some pending
    | .error _ => PGraph.cleanupFn noDouble [dropInfoFn info] pending
  | .unwound _ _ => PGraph.cleanupFn noDouble [dropInfoFn info] pending
  | .terminated _ => some pending

theorem decoderCleanup_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (checked : Bool) (info : AccountInfo.Value)
    (pending : Out (AnchorConstructOwned.Decoded (Error storage) Nat)) :
    PGraph (decoderCleanup (payloadTypes storage script target checked) info pending)
      (decoderCleanupFn storage info pending) := by
  cases pending with
  | terminated _ => exact PGraph.eq_left _
  | unwound _ _ =>
    exact PGraph.cleanup (noDouble_graph storage) _ _
      (PGraph.DropsGraph.cons (dropInfo_graph storage info) PGraph.DropsGraph.nil) _
  | returned decoded after =>
    cases eq : decoded.result
    · unfold Solanalib.Specs.Core.AnchorLifecycle.decoderCleanup
      simp only [decoderCleanupFn, eq]
      exact PGraph.cleanup (noDouble_graph storage) _ _
        (PGraph.DropsGraph.cons (dropInfo_graph storage info) PGraph.DropsGraph.nil) _
    · unfold Solanalib.Specs.Core.AnchorLifecycle.decoderCleanup
      simp only [decoderCleanupFn, eq]
      exact PGraph.eq_left _

def decoderFn (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AnchorAccount.DecodeArgs) :
    Option (Out (AnchorConstructOwned.Decoded (Error storage) Nat)) :=
  match ownership with
  | .borrowed => (decodeFn storage script target checked state args).map AnchorAccount.widen
  | .owned => (cloneFn state args.info).bind (PGraph.bindK fun info afterClone =>
      ((decodeFn storage script target checked afterClone args).map AnchorAccount.widen).bind
        (decoderCleanupFn storage info))

theorem decoder_graph (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage) (script :
  Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AnchorAccount.DecodeArgs) :
    PGraph (decoder ownership (payloadTypes storage script target checked) state args)
      (decoderFn ownership storage script target checked state args) := by
  cases ownership
  · exact PGraph.bind (clone_graph storage state args.info) fun info _ =>
      PGraph.exists_step (widened_graph (PGraph.ofOption _)) (decoderCleanup_graph storage script
        target checked info)
  · exact widened_graph (PGraph.ofOption _)

def decodePayloadFn (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage) (script :
  Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AccountInfo.Args) :
    Option (Out (Except (Error storage) Nat)) :=
  match AccountInfo.tryBorrowData state.1 args with
  | (.error failure, during) => (programFn storage (during, state.2) (.plain failure)).map
    (Outcome.map Except.error)
  | (.ok guard, during) => match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      ((decoderFn ownership storage script target checked (during, state.2) ⟨args.info, guard,
        bytes⟩).map
        (Outcome.map AnchorConstructOwned.Decoded.result)).bind
          (AccountInfo.GuardCallback.releaseOutcome guard)

theorem decodePayload_graph (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage)
  (script : Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AccountInfo.Args) :
    PGraph (decodePayload ownership (payloadTypes storage script target checked) state args)
      (decodePayloadFn ownership storage script target checked state args) := by
  unfold decodePayload decodePayloadFn
  rcases AccountInfo.tryBorrowData state.1 args with ⟨borrowed, during⟩
  cases borrowed with
  | error failure => exact PGraph.map _ (program_graph storage _ failure)
  | ok guard =>
    dsimp only
    cases Borrow.current during guard with
    | error _ => exact PGraph.false
    | ok content =>
      rcases content with ⟨view, value⟩
      cases value with
      | lamports _ => exact PGraph.false
      | data bytes =>
        exact withGuard_graph guard (PGraph.map AnchorConstructOwned.Decoded.result
          (decoder_graph ownership storage script target checked _ _))

def payloadFn (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (state : W) (args :
      AccountInfo.Args) :
    Option (Out (Except (Error storage) (kind.constructor.Result Nat))) :=
  (initializedFn storage state args).bind (PGraph.bindK (resultK fun _ after =>
    (match kind with
      | .account => ownerCheckFn storage script target after args
      | .interfaceAccount => (checkFn storage script.checkOwner target (.checkOwner
        args.info.ownerRef.id)
          "script check_owner" after).map AnchorAccount.widen).bind
        (PGraph.bindK (resultK fun _ validated =>
          (decodePayloadFn ownership storage script target checked validated args).bind
            (PGraph.bindK fun decoded final => match kind with
              | .account => some (.returned (decoded.map fun value => AnchorAccount.Account.mk
                value args.info) final)
              | .interfaceAccount => some (.returned
                (decoded.map fun value => AnchorAccount.InterfaceAccount.mk ⟨value, args.info⟩
                  (ownerAt final.2 args.info.ownerRef)) final))))))

theorem payload_graph (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (state : W) (args :
      AccountInfo.Args) :
    PGraph (construct kind ownership (payloadTypes storage script target checked) state args)
      (payloadFn kind ownership storage script target checked state args) := by
  apply effectsBind_graph (initialized_graph storage script target checked state args)
  intro _ after
  cases kind with
  | account =>
    exact effectsBind_graph (ownerCheck_graph storage script target checked after args) fun _
      validated =>
      PGraph.bind (decodePayload_graph ownership storage script target checked validated args) fun
        _ _ => PGraph.eq_left _
  | interfaceAccount =>
    exact effectsBind_graph (widened_graph (PGraph.ofOption _)) fun _ validated =>
      PGraph.bind (decodePayload_graph ownership storage script target checked validated args) fun
        _ _ => PGraph.eq_left _

def payloadAccountsTypes (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) : PayloadAccountsTypes := ⟨payloadTypes storage script target
      true, Nat⟩

theorem payloadAccounts_graph (kind : PayloadKind) (ownership : InfoStorage)
    (storage : AnchorErrorOperations.Storage) (script : Script) (target : AccountInfo.Value)
    (state : W × AccountsState Nat) (args : AccountsArgs) :
    PGraph (payloadAccountsRun kind ownership (payloadAccountsTypes storage script target) state
      args)
      (consumeFn storage (fun current refArgs =>
        payloadFn kind ownership storage script target true current refArgs.toAccountInfoArgs)
          state args) :=
  consume_graph storage (fun current refArgs =>
    payload_graph kind ownership storage script target true current refArgs.toAccountInfoArgs)
      state args

def replacePayloadFn (script : Script) (target : AccountInfo.Value) (state : W) (replacement : Nat)
  :
    Option (Out Unit) :=
  ((dropPayloadFn script target state (payloadFocus.get state)).map AnchorAccount.widen).map
    (AnchorViewsAssignment.replaceAfter payloadFocus.set replacement)

theorem replacePayload_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (replacement : Nat) :
    PGraph (replacePayload (reloadTypes storage script target) state replacement)
      (replacePayloadFn script target state replacement) :=
  PGraph.exists_eq _ (widened_graph (PGraph.ofOption _))

def decodeReplaceFn (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : AccountInfo.Args) : Option (Out (Except (Error
      storage) Unit)) :=
  match AccountInfo.tryBorrowData state.1 args with
  | (.error failure, during) => (programFn storage (during, state.2) (.plain failure)).map
    (Outcome.map Except.error)
  | (.ok guard, during) => match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      ((((decodeFn storage script target true (during, state.2) ⟨args.info, guard, bytes⟩).map
        AnchorAccount.widen).map (Outcome.map AnchorConstructOwned.Decoded.result)).bind
          (PGraph.bindK (resultK fun replacement after =>
            (replacePayloadFn script target after replacement).map (Outcome.map Except.ok)))).bind
              (AccountInfo.GuardCallback.releaseOutcome guard)

theorem decodeReplace_graph (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : AccountInfo.Args) :
    PGraph (decodeReplace (reloadTypes storage script target) state args)
      (decodeReplaceFn storage script target state args) := by
  unfold decodeReplace decodeReplaceFn
  rcases AccountInfo.tryBorrowData state.1 args with ⟨borrowed, during⟩
  cases borrowed with
  | error failure => exact PGraph.map _ (program_graph storage _ failure)
  | ok guard =>
    dsimp only
    cases Borrow.current during guard with
    | error _ => exact PGraph.false
    | ok content =>
      rcases content with ⟨view, value⟩
      cases value with
      | lamports _ => exact PGraph.false
      | data bytes =>
        exact withGuard_graph guard (effectsBind_graph
          (PGraph.map AnchorConstructOwned.Decoded.result (widened_graph (PGraph.ofOption _)))
          fun replacement after => PGraph.map _ (replacePayload_graph storage script target after
            replacement))

def reloadFn (mode : ReloadMode) (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : AccountInfo.Args) : Option (Out (Except (Error
      storage) Unit)) :=
  match mode with
  | .legacy => decodeReplaceFn storage script target state args
  | .account => (ownerCheckFn storage script target state args).bind
      (PGraph.bindK (resultK fun _ after => decodeReplaceFn storage script target after args))
  | .interfaceAccount =>
    ((checkFn storage script.checkOwner target (.checkOwner args.info.ownerRef.id)
      "script check_owner" state).map AnchorAccount.widen).bind (PGraph.bindK (resultK fun _
        checked =>
        (decodePayloadFn .borrowed storage script target true checked args).bind
          (PGraph.bindK (resultK fun replacement after =>
            (replacePayloadFn script target after replacement).map (Outcome.map Except.ok)))))

theorem reload_graph (mode : ReloadMode) (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : AccountInfo.Args) :
    PGraph (reload mode (reloadTypes storage script target) state args) (reloadFn mode storage
      script target state args) := by
  cases mode with
  | legacy => exact decodeReplace_graph storage script target state args
  | account =>
    exact effectsBind_graph (ownerCheck_graph storage script target true state args)
      fun _ after => decodeReplace_graph storage script target after args
  | interfaceAccount =>
    exact effectsBind_graph (widened_graph (PGraph.ofOption _))
      fun _ checked => effectsBind_graph (decodePayload_graph .borrowed storage script target true
        checked args)
        fun replacement after => PGraph.map _ (replacePayload_graph storage script target after
          replacement)

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
