/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresAccounts
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.PayloadGraph
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.ValidationGraph
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.ExitGraph

/-! Computable admission of the concrete native providers. Every Boolean
below is proved equivalent to the registered precondition. Quantifiers are
checked at each actual reached exit, including primitive Rc calls and the
state in which a diagnostic or destructor runs. A separate graph check is
still required to establish the observed finite execution. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Ready

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Families.Anchor.Decide
open SolanalibTest.Conformance.Library.Families.Anchor.RequiresAccounts (dataTypedB dataTypedB_iff)

theorem whenB_iff {condition : Prop} [Decidable condition] {check : Bool} {required : Prop}
    (correct : check = true ↔ required) :
    (if condition then check else true) = true ↔ condition → required := by
  by_cases reached : condition <;> simp [reached, correct]

def onUnitB {S U T : Type} (step : Option (Outcome S Unit U T)) (check : S → Bool) : Bool :=
  onReturnedB step fun _ after => check after

theorem onUnit_iff {S U T : Type} {run : Outcome S Unit U T → Prop}
    {step : Option (Outcome S Unit U T)} (graph : PGraph run step)
    (condition : S → Prop) (check : S → Bool) (correct : ∀ after, check after = true ↔ condition
      after) :
    onUnitB step check = true ↔ ∀ after, run (.returned () after) → condition after := by
  have all := onReturned_iff graph (fun _ after => condition after) (fun _ after => check after)
    (fun _ after => correct after)
  constructor
  · intro admitted after called
    exact all.mp admitted () after called
  · intro admitted
    exact all.mpr (fun _ after called => admitted after called)

def rcReadyB (increment : Bool) (before : W) (info : AccountInfo.Value) (guard : Borrow.Guard) :
  Bool :=
  allExitsB (rcStep increment before (.lamports, info.lamports)) (frameB before guard) &&
    onUnitB (rcStep increment before (.lamports, info.lamports)) fun middle =>
      allExitsB (rcStep increment middle (.data, info.data)) (frameB middle guard)

theorem rcReadyB_iff (increment : Bool) (before : W) (info : AccountInfo.Value) (guard :
  Borrow.Guard) :
    rcReadyB increment before info guard = true ↔
      RcReady (fun state argument outcome => rcStep increment state argument = some outcome) before
        info guard := by
  unfold rcReadyB RcReady
  rw [Bool.and_eq_true]
  exact and_congr (admissible_iff (PGraph.ofOption _))
    (onUnit_iff (PGraph.ofOption _) _ _ fun _ => admissible_iff (PGraph.ofOption _))

def decoderDropReadyB (guard : Borrow.Guard) (info : AccountInfo.Value)
    {storage : AnchorErrorOperations.Storage} : Out (AnchorConstructOwned.Decoded (Error storage)
      Nat) → Bool
  | .returned decoded after => match decoded.result with
    | .ok _ => true
    | .error _ => rcReadyB false after info guard
  | .unwound _ after => rcReadyB false after info guard
  | .terminated _ => true

theorem decoderDropReadyB_iff (guard : Borrow.Guard) (info : AccountInfo.Value)
    {storage : AnchorErrorOperations.Storage} (produced : Out (AnchorConstructOwned.Decoded (Error
      storage) Nat)) :
    decoderDropReadyB guard info produced = true ↔
      match produced with
      | .returned decoded after => match decoded.result with
        | .ok _ => True
        | .error _ => RcReady rc.dropRc after info guard
      | .unwound _ after => RcReady rc.dropRc after info guard
      | .terminated _ => True := by
  cases produced with
  | terminated _ => simp [decoderDropReadyB]
  | unwound _ after => exact rcReadyB_iff false after info guard
  | returned decoded after =>
    cases found : decoded.result <;> simp only [decoderDropReadyB, found]
    exact rcReadyB_iff false after info guard

def decoderReadyB (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (before : W)
    (args : AnchorAccount.DecodeArgs) : Bool :=
  match ownership with
  | .borrowed => allExitsB ((decodeFn storage script target checked before args).map
    AnchorAccount.widen)
      (frameB before args.guard)
  | .owned => rcReadyB true before args.info args.guard &&
      onReturnedB (cloneFn before args.info) fun info afterClone =>
        allExitsB ((decodeFn storage script target checked afterClone args).map AnchorAccount.widen)
          (frameB afterClone args.guard) &&
        allExitsB ((decodeFn storage script target checked afterClone args).map AnchorAccount.widen)
          (decoderDropReadyB args.guard info)

theorem decoderReadyB_iff (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (before : W)
    (args : AnchorAccount.DecodeArgs) :
    decoderReadyB ownership storage script target checked before args = true ↔
      DecoderReady ownership (payloadTypes storage script target checked) before args := by
  cases ownership with
  | borrowed => exact admissible_iff (widened_graph (PGraph.ofOption _))
  | owned =>
    unfold decoderReadyB DecoderReady
    rw [Bool.and_eq_true]
    apply and_congr (rcReadyB_iff true before args.info args.guard)
    apply onReturned_iff (clone_graph storage before args.info)
    intro info afterClone
    rw [Bool.and_eq_true]
    exact and_congr (admissible_iff (widened_graph (PGraph.ofOption _)))
      (allExits_iff (widened_graph (PGraph.ofOption _)) _ _ fun produced => by
        cases produced with
        | terminated _ => simp [decoderDropReadyB]
        | unwound _ after => exact rcReadyB_iff false after info args.guard
        | returned decoded after =>
          cases selected : decoded.result <;> simp only [decoderDropReadyB, selected]
          exact rcReadyB_iff false after info args.guard)

/-- The same reached-borrow shape is used for decode, replacement and
serialization; the callback check remains specific to that operation. -/
def dataGuardB
    (borrow : AccountInfo.State → AccountInfo.Args → Except ProgramError.Value Borrow.Guard ×
      AccountInfo.State)
    (check : W → AnchorAccount.DecodeArgs → Bool) (before : W) (args : AccountInfo.Args) : Bool :=
  dataTypedB before.1 args.info.data &&
    match borrow before.1 args with
    | (.ok guard, during) => match Borrow.current during guard with
      | .ok (_, .data bytes) => check (during, before.2) ⟨args.info, guard, bytes⟩
      | _ => true
    | _ => true

theorem dataGuardB_iff
    (borrow : AccountInfo.State → AccountInfo.Args → Except ProgramError.Value Borrow.Guard ×
      AccountInfo.State)
    (condition : W → AnchorAccount.DecodeArgs → Prop) (check : W → AnchorAccount.DecodeArgs → Bool)
    (correct : ∀ state args, check state args = true ↔ condition state args)
    (before : W) (args : AccountInfo.Args) :
    dataGuardB borrow check before args = true ↔
      ((∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
        ∀ guard during, borrow before.1 args = (.ok guard, during) →
          ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
            condition (during, before.2) ⟨args.info, guard, bytes⟩) := by
  unfold dataGuardB
  rw [Bool.and_eq_true, dataTypedB_iff]
  apply and_congr_right
  intro _
  rcases borrowed : borrow before.1 args with ⟨result, during⟩
  cases result with
  | error _ => simp
  | ok guard =>
    simp only
    constructor
    · intro admitted guard' during' equal view bytes found
      cases equal
      rw [found] at admitted
      exact (correct _ _).mp admitted
    · intro admitted
      cases found : Borrow.current during guard with
      | error _ => rfl
      | ok content =>
        rcases content with ⟨view, value⟩
        cases value with
        | lamports _ => rfl
        | data bytes => exact (correct _ _).mpr (admitted guard during rfl view bytes found)

def decodePayloadReadyB (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (before : W) (args :
      AccountInfo.Args) : Bool :=
  dataGuardB AccountInfo.tryBorrowData (decoderReadyB ownership storage script target checked)
    before args

theorem decodePayloadReadyB_iff (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (before : W) (args :
      AccountInfo.Args) :
    decodePayloadReadyB ownership storage script target checked before args = true ↔
      DecodePayloadReady ownership (payloadTypes storage script target checked) before args :=
  dataGuardB_iff AccountInfo.tryBorrowData _ _ (decoderReadyB_iff ownership storage script target
    checked) before args

def diagnosticExitB (observed : Solanalib.Runtime.Pubkey) (payload : ErrorPayload) (resource : Nat)
  (before : W) :
    SigOut Solanalib.Runtime.Pubkey → Bool
  | .returned diagnostic after =>
    decide (currentBox after resource = currentBox before resource) &&
      (writeBox after resource (payload.withCompared (some (.pubkeys observed diagnostic)))).isSome
  | .unwound _ after => decide (currentBox after resource = currentBox before resource)
  | .terminated _ => true

theorem diagnosticExitB_iff (observed : Solanalib.Runtime.Pubkey) (payload : ErrorPayload)
  (resource : Nat)
    (before : W) (produced : SigOut Solanalib.Runtime.Pubkey) :
    diagnosticExitB observed payload resource before produced = true ↔
      match produced with
      | .returned diagnostic after =>
        currentBox after resource = currentBox before resource ∧
          ∃ final, writeBox after resource (payload.withCompared (some (.pubkeys observed
            diagnostic))) = some final
      | .unwound _ after => currentBox after resource = currentBox before resource
      | .terminated _ => True := by
  cases produced <;> simp [diagnosticExitB, Option.isSome_iff_exists]

def diagnosticReadyB (next : W → Option (SigOut Solanalib.Runtime.Pubkey)) (failure :
  AnchorErrorOperations.Code)
    (observed : W → Solanalib.Runtime.Pubkey) (before : W) : Bool :=
  onReturnedB (some (copyString before failure.name)) fun name afterName =>
    onReturnedB (some (copyString afterName failure.message)) fun message afterMessage =>
      let payload : ErrorPayload := .anchor ⟨name, failure.number, message, none, none⟩
      onReturnedB (some (newBox afterMessage payload)) fun resource afterBox =>
        decide (currentBox afterBox resource = some payload) &&
          allExitsB (next afterBox) (diagnosticExitB (observed afterBox) payload resource afterBox)

theorem diagnosticReadyB_iff (next : W → Option (SigOut Solanalib.Runtime.Pubkey)) (failure :
  AnchorErrorOperations.Code)
    (observed : W → Solanalib.Runtime.Pubkey) (before : W) :
    diagnosticReadyB next failure observed before = true ↔
      ∀ name afterName, errors.copyLiteral before failure.name (.returned name afterName) →
      ∀ message afterMessage, errors.formatLiteral afterName failure.message (.returned message
        afterMessage) →
      ∀ resource afterBox, errors.newBox afterMessage
        (.anchor ⟨name, failure.number, message, none, none⟩) (.returned resource afterBox) →
        currentBox afterBox resource = some (.anchor ⟨name, failure.number, message, none, none⟩) ∧
          ∀ produced, next afterBox = some produced →
            match produced with
            | .returned diagnostic after =>
              currentBox after resource = currentBox afterBox resource ∧
                ∃ final, writeBox after resource
                  ((.anchor ⟨name, failure.number, message, none, none⟩ : ErrorPayload).withCompared
                    (some (.pubkeys (observed afterBox) diagnostic))) = some final
            | .unwound _ after => currentBox after resource = currentBox afterBox resource
            | .terminated _ => True := by
  unfold diagnosticReadyB
  apply onReturned_iff (PGraph.ofFunction copyString before failure.name)
  intro name afterName
  apply onReturned_iff (PGraph.ofFunction copyString afterName failure.message)
  intro message afterMessage
  apply onReturned_iff (PGraph.ofFunction newBox afterMessage _)
  intro resource afterBox
  rw [Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro _
  exact allExits_iff (PGraph.ofOption _) _ _ (diagnosticExitB_iff (observed afterBox) _ resource
    afterBox)

def ownerReadyB (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (before : W) (args : AccountInfo.Args) : Bool :=
  if storage = .boxed then
    onReturnedB (keyFn script.owner target .owner "script owner" before) fun expected after =>
      if ownerAt after.2 args.info.ownerRef ≠ expected then
        diagnosticReadyB (keyFn script.owner target .owner "script owner")
          ⟨AnchorAccount.Code.ownedByWrongProgram.payload.name,
            AnchorAccount.Code.ownedByWrongProgram.payload.code,
            AnchorAccount.Code.ownedByWrongProgram.payload.message⟩
          (fun state => ownerAt state.2 args.info.ownerRef) after
      else true
  else true

theorem ownerReadyB_iff (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (checked : Bool) (before : W) (args : AccountInfo.Args) :
    ownerReadyB storage script target before args = true ↔
      OwnerReady (payloadTypes storage script target checked) before args := by
  unfold ownerReadyB OwnerReady
  change (if storage = .boxed then _ else true) = true ↔ storage = .boxed → _
  by_cases boxed : storage = .boxed
  · simp only [boxed, ↓reduceIte, true_implies]
    apply onReturned_iff (PGraph.ofOption _)
    intro expected after
    apply whenB_iff
    rw [diagnosticReadyB_iff]
    apply forall_congr'; intro name
    apply forall_congr'; intro afterName
    apply imp_congr_right; intro _
    apply forall_congr'; intro message
    apply forall_congr'; intro afterMessage
    apply imp_congr_right; intro _
    apply forall_congr'; intro resource
    apply forall_congr'; intro afterBox
    apply imp_congr_right; intro _
    apply and_congr_right; intro _
    apply forall_congr'; intro produced
    apply imp_congr_right; intro _
    cases produced <;> rfl
  · simp [boxed]

def idReadyB (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (before : W) (args : AccountInfo.Args) : Bool :=
  if storage = .boxed then
    onReturnedB (keyFn script.id target .id "script id" before) fun expected after =>
      if args.info.key ≠ expected then
        diagnosticReadyB (keyFn script.id target .id "script id")
          ⟨Code.invalidProgramId.payload.name, Code.invalidProgramId.payload.code,
            Code.invalidProgramId.payload.message⟩
          (fun _ => args.info.key) after
      else true
  else true

theorem idReadyB_iff (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (legacy : Bool) (before : W) (args : AccountInfo.Args) :
    idReadyB storage script target before args = true ↔
      IdReady (validationTypes storage script target legacy) before args := by
  unfold idReadyB IdReady
  change (if storage = .boxed then _ else true) = true ↔ storage = .boxed → _
  by_cases boxed : storage = .boxed
  · simp only [boxed, ↓reduceIte, true_implies]
    apply onReturned_iff (PGraph.ofOption _)
    intro expected after
    apply whenB_iff
    rw [diagnosticReadyB_iff]
    apply forall_congr'; intro name
    apply forall_congr'; intro afterName
    apply imp_congr_right; intro _
    apply forall_congr'; intro message
    apply forall_congr'; intro afterMessage
    apply imp_congr_right; intro _
    apply forall_congr'; intro resource
    apply forall_congr'; intro afterBox
    apply imp_congr_right; intro _
    apply and_congr_right; intro _
    apply forall_congr'; intro produced
    apply imp_congr_right; intro _
    cases produced <;> rfl
  · simp [boxed]

def payloadReadyB (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (before : W) (args :
      AccountInfo.Args) : Bool :=
  decide (AnchorAccount.InitReady ownerAt before args) &&
    onOkB (initializedFn storage before args) fun after =>
      match kind with
      | .account => ownerReadyB storage script target after args &&
          onOkB (ownerCheckFn storage script target after args) fun validated =>
            decodePayloadReadyB ownership storage script target checked validated args
      | .interfaceAccount =>
          onOkB ((checkFn storage script.checkOwner target (.checkOwner args.info.ownerRef.id)
            "script check_owner" after).map AnchorAccount.widen) fun validated =>
              decodePayloadReadyB ownership storage script target checked validated args

theorem payloadReadyB_iff (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (checked : Bool) (before : W) (args :
      AccountInfo.Args) :
    payloadReadyB kind ownership storage script target checked before args = true ↔
      ConstructReady kind ownership (payloadTypes storage script target checked) before args := by
  unfold payloadReadyB ConstructReady
  rw [Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro _
  apply onOk_iff (initialized_graph storage script target checked before args)
  intro after
  cases kind with
  | account =>
    rw [Bool.and_eq_true]
    exact and_congr (ownerReadyB_iff storage script target checked after args)
      (onOk_iff (ownerCheck_graph storage script target checked after args) _ _ fun validated =>
        decodePayloadReadyB_iff ownership storage script target checked validated args)
  | interfaceAccount =>
    exact onOk_iff (widened_graph (PGraph.ofOption _)) _ _ fun validated =>
      decodePayloadReadyB_iff ownership storage script target checked validated args

def validationReadyB (kind : ValidationKind) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W) (args : ReferenceArgs) : Bool :=
  match kind with
  | .program => idReadyB storage script target before args.toAccountInfoArgs
  | _ => true

theorem validationReadyB_iff (kind : ValidationKind) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (legacy : Bool) (before : W) (args :
      ReferenceArgs) :
    validationReadyB kind storage script target before args = true ↔
      ValidationReady kind (validationTypes storage script target legacy) before args := by
  cases kind <;> simp only [validationReadyB, ValidationReady]
  exact idReadyB_iff storage script target legacy before args.toAccountInfoArgs

def replaceReadyB (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (guard : Borrow.Guard) (before : W)
    (decoded : AnchorConstructOwned.Decoded (Error storage) Nat) : Bool :=
  match decoded.result with
  | .error _ => true
  | .ok replacement => allExitsB (replacePayloadFn script target before replacement) (frameB before
    guard)

theorem replaceReadyB_iff (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (guard : Borrow.Guard) (before : W)
    (decoded : AnchorConstructOwned.Decoded (Error storage) Nat) :
    replaceReadyB storage script target guard before decoded = true ↔
      ∀ replacement, decoded.result = .ok replacement →
        AccountInfo.GuardCallback.Admissible guard (replacePayload (reloadTypes storage script
          target))
          before replacement := by
  unfold replaceReadyB
  cases selected : decoded.result with
  | error _ => simp
  | ok replacement =>
    simp only [Except.ok.injEq]
    constructor
    · intro admitted next equal
      cases equal
      exact (admissible_iff (replacePayload_graph storage script target before replacement)).mp
        admitted
    · intro admitted
      exact (admissible_iff (replacePayload_graph storage script target before replacement)).mpr
        (admitted replacement rfl)

def decodeReplaceHeldB (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (before : W) (args : AnchorAccount.DecodeArgs) : Bool :=
  allExitsB ((decodeFn storage script target true before args).map AnchorAccount.widen) (frameB
    before args.guard) &&
    onReturnedB ((decodeFn storage script target true before args).map AnchorAccount.widen) fun
      decoded after =>
      replaceReadyB storage script target args.guard after decoded

theorem decodeReplaceHeldB_iff (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (before : W) (args : AnchorAccount.DecodeArgs) :
    decodeReplaceHeldB storage script target before args = true ↔
      AccountInfo.GuardCallback.Admissible args.guard
        (AnchorAccount.widenCallback (reloadTypes storage script target).deserialize) before args ∧
      ∀ decoded after, AnchorAccount.widenCallback (reloadTypes storage script target).deserialize
        before args (.returned decoded after) →
        ∀ replacement, decoded.result = .ok replacement →
          AccountInfo.GuardCallback.Admissible args.guard (replacePayload (reloadTypes storage
            script target))
            after replacement := by
  unfold decodeReplaceHeldB
  rw [Bool.and_eq_true]
  exact and_congr (admissible_iff (widened_graph (PGraph.ofOption _)))
    (onReturned_iff (widened_graph (PGraph.ofOption _)) _ _ fun decoded after =>
      replaceReadyB_iff storage script target args.guard after decoded)

def decodeReplaceReadyB (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (before : W) (args : AccountInfo.Args) : Bool :=
  dataGuardB AccountInfo.tryBorrowData (decodeReplaceHeldB storage script target) before args

theorem decodeReplaceReadyB_iff (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (before : W) (args : AccountInfo.Args) :
    decodeReplaceReadyB storage script target before args = true ↔
      DecodeReplaceReady (reloadTypes storage script target) before args :=
  dataGuardB_iff AccountInfo.tryBorrowData _ _ (decodeReplaceHeldB_iff storage script target)
    before args

def reloadReadyB (mode : ReloadMode) (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (before : W) (args : AccountInfo.Args) : Bool :=
  match mode with
  | .legacy => decodeReplaceReadyB storage script target before args
  | .account => ownerReadyB storage script target before args &&
      onOkB (ownerCheckFn storage script target before args) fun after =>
        decodeReplaceReadyB storage script target after args
  | .interfaceAccount =>
      onOkB ((checkFn storage script.checkOwner target (.checkOwner args.info.ownerRef.id)
        "script check_owner" before).map AnchorAccount.widen) fun after =>
          decodePayloadReadyB .borrowed storage script target true after args

theorem reloadReadyB_iff (mode : ReloadMode) (storage : AnchorErrorOperations.Storage) (script :
  Script)
    (target : AccountInfo.Value) (before : W) (args : AccountInfo.Args) :
    reloadReadyB mode storage script target before args = true ↔
      ReloadReady mode (reloadTypes storage script target) before args := by
  cases mode with
  | legacy => exact decodeReplaceReadyB_iff storage script target before args
  | account =>
    unfold reloadReadyB ReloadReady
    rw [Bool.and_eq_true]
    exact and_congr (ownerReadyB_iff storage script target true before args)
      (onOk_iff (ownerCheck_graph storage script target true before args) _ _ fun after =>
        decodeReplaceReadyB_iff storage script target after args)
  | interfaceAccount =>
    exact onOk_iff (widened_graph (PGraph.ofOption _)) _ _ fun after =>
      decodePayloadReadyB_iff .borrowed storage script target true after args

def mutableFootprintB (mode : Borrow.Mode) (old next : AccountInfo.Content) : Bool :=
  match mode, old, next with
  | .exclusive, .data before, .data after => decide (after.length = before.length)
  | _, _, _ => decide (next = old)

theorem mutableFootprintB_iff (mode : Borrow.Mode) (view : AccountInfo.View) (old next :
  AccountInfo.Content) :
    mutableFootprintB mode old next = true ↔ mutableDataFootprint mode view old next := by
  cases mode <;> cases old <;> cases next <;> simp [mutableFootprintB, mutableDataFootprint]

def heldMutationB (before after : AccountInfo.State) (guard : Borrow.Guard) : Bool :=
  match before.resolve guard with
  | none => true
  | some slot => match before.lookupCell slot.cell, after.lookupCell slot.cell with
    | some old, some next => mutableFootprintB slot.mode old.value next.value
    | _, _ => true

def mutableStateFrameB (before after : AccountInfo.State) (guard : Borrow.Guard) : Bool :=
  validB after && historyB before after && (List.range before.cells.length).all (cellKeptB before
    after) &&
    decide (after.resolve guard = before.resolve guard) && heldMutationB before after guard

theorem mutableStateFrameB_iff (before after : AccountInfo.State) (guard : Borrow.Guard) :
    mutableStateFrameB before after guard = true ↔ Borrow.CallbackFrame mutableDataFootprint before
      after guard := by
  unfold mutableStateFrameB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, validB_iff,
    historyB_iff]
  constructor
  · rintro ⟨⟨⟨⟨valid, history⟩, cells⟩, held⟩, changes⟩
    refine ⟨valid, history, ?_, held, ?_⟩
    · intro handle old present
      have kept := cells handle.cell (lookupCell_lt present)
      simp only [cellKeptB, present] at kept
      cases found : after.lookupCell ⟨handle.cell⟩ with
      | none => rw [found] at kept; cases kept
      | some next => rw [found] at kept; exact ⟨next, rfl, of_decide_eq_true kept⟩
    · intro slot old next live oldFound nextFound
      simp only [heldMutationB, live, oldFound, nextFound] at changes
      exact (mutableFootprintB_iff slot.mode slot.view old.value next.value).mp changes
  · rintro ⟨valid, history, cells, held, changes⟩
    refine ⟨⟨⟨⟨valid, history⟩, ?_⟩, held⟩, ?_⟩
    · intro handle _
      unfold cellKeptB
      cases oldFound : before.lookupCell ⟨handle⟩ with
      | none => rfl
      | some old =>
        obtain ⟨next, found, policy⟩ := cells ⟨handle⟩ old oldFound
        simp [found, policy]
    · unfold heldMutationB
      cases live : before.resolve guard with
      | none => rfl
      | some slot =>
        cases oldFound : before.lookupCell slot.cell with
        | none => simp only [oldFound]
        | some old =>
          cases nextFound : after.lookupCell slot.cell with
          | none => simp only [oldFound, nextFound]
          | some next =>
            simp only [oldFound, nextFound]
            exact (mutableFootprintB_iff slot.mode slot.view old.value next.value).mpr
              (changes slot old next live oldFound nextFound)

def mutableFrameB {Value Unwind Terminal : Type} (before : W) (guard : Borrow.Guard) :
    Outcome W Value Unwind Terminal → Bool
  | .returned _ after | .unwound _ after => mutableStateFrameB before.1 after.1 guard
  | .terminated _ => true

theorem mutableFrameB_iff {Value Unwind Terminal : Type} (before : W) (guard : Borrow.Guard)
    (produced : Outcome W Value Unwind Terminal) :
    mutableFrameB before guard produced = true ↔ MutableFrame before guard produced := by
  cases produced <;> simp [mutableFrameB, MutableFrame, mutableStateFrameB_iff]

def serializeReadyB (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (before : W) (account : AnchorAccount.Account Nat) (profile : AccountInfo.Profile) : Bool :=
  dataGuardB AccountInfo.tryBorrowMutData (fun during args =>
    allExitsB ((serializeFn storage script target during
      ⟨account.value, account.info, args.guard, args.bytes, 0⟩).map AnchorAccount.widen)
      (mutableFrameB during args.guard)) before ⟨profile, account.info⟩

theorem serializeReadyB_iff (storage : AnchorErrorOperations.Storage) (script : Script) (target :
  AccountInfo.Value)
    (before : W) (account : AnchorAccount.Account Nat) (profile : AccountInfo.Profile) :
    serializeReadyB storage script target before account profile = true ↔
      SerializeReady (exitTypes storage script target) before account profile := by
  exact dataGuardB_iff AccountInfo.tryBorrowMutData
    (fun during args => MutableAdmissible args.guard
      (AnchorAccount.widenCallback (exitTypes storage script target).serialize) during
        ⟨account.value, account.info, args.guard, args.bytes, 0⟩) _
    (fun during args => allExits_iff (widened_graph (PGraph.ofOption _)) _ _ (mutableFrameB_iff
      during args.guard))
    before ⟨profile, account.info⟩

def serializeScopedReadyB (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W)
    (account : AnchorAccount.Account Nat) (profile : AccountInfo.Profile) : Bool :=
  if cloneLocal then onReturnedB (cloneFn before account.info) fun info after =>
    serializeReadyB storage script target after ⟨account.value, info⟩ profile
  else serializeReadyB storage script target before account profile

theorem serializeScopedReadyB_iff (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W)
    (account : AnchorAccount.Account Nat) (profile : AccountInfo.Profile) :
    serializeScopedReadyB cloneLocal storage script target before account profile = true ↔
      SerializeScopedReady cloneLocal (exitTypes storage script target) before account profile := by
  cases cloneLocal with
  | false => exact serializeReadyB_iff storage script target before account profile
  | true =>
    exact onReturned_iff (clone_graph storage before account.info) _ _ fun info after =>
      serializeReadyB_iff storage script target after ⟨account.value, info⟩ profile

def isClosedReadyB (before : W) (args : AccountInfo.Args) : Bool :=
  if ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
    decide ((AccountInfo.observe .dataLen before.1 args.info).1 ≠ .malformed)
  else true

theorem isClosedReadyB_iff (before : W) (args : AccountInfo.Args) :
    isClosedReadyB before args = true ↔ IsClosedReady ownerAt before args := by
  unfold isClosedReadyB IsClosedReady ObserveReady
  by_cases system : ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId <;> simp
    [system]

def onFalseB {S U T : Type} (step : Option (Outcome S Bool U T)) (check : S → Bool) : Bool :=
  match step with
  | some (.returned false after) => check after
  | _ => true

theorem onFalse_iff {S U T : Type} {run : Outcome S Bool U T → Prop}
    {step : Option (Outcome S Bool U T)} (graph : PGraph run step)
    (condition : S → Prop) (check : S → Bool) (correct : ∀ after, check after = true ↔ condition
      after) :
    onFalseB step check = true ↔ ∀ after, run (.returned false after) → condition after := by
  constructor
  · intro admitted after called
    rw [(graph _).mp called] at admitted
    exact (correct after).mp admitted
  · intro admitted
    cases selected : step with
    | none => rfl
    | some produced =>
      cases produced with
      | returned value after =>
        cases value with
        | false => exact (correct after).mpr (admitted after ((graph _).mpr selected))
        | true => rfl
      | unwound _ _ => rfl
      | terminated _ => rfl

def exitExpectedReadyB (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W)
    (account : AnchorAccount.Account Nat) (profile : AccountInfo.Profile) (programId expected :
      Solanalib.Runtime.Pubkey) : Bool :=
  if expected = programId then
    isClosedReadyB before ⟨profile, account.info⟩ &&
      onFalseB (isClosedFn before ⟨profile, account.info⟩) fun checked =>
        serializeScopedReadyB cloneLocal storage script target checked account profile
  else true

theorem exitExpectedReadyB_iff (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W)
    (account : AnchorAccount.Account Nat) (profile : AccountInfo.Profile) (programId expected :
      Solanalib.Runtime.Pubkey) :
    exitExpectedReadyB cloneLocal storage script target before account profile programId expected =
      true ↔
      ExitExpectedReady cloneLocal (exitTypes storage script target) before account profile
        programId expected := by
  apply whenB_iff
  rw [Bool.and_eq_true]
  exact and_congr (isClosedReadyB_iff before ⟨profile, account.info⟩)
    (onFalse_iff (isClosed_graph before ⟨profile, account.info⟩) _ _ fun checked =>
      serializeScopedReadyB_iff cloneLocal storage script target checked account profile)

def exitReadyB (kind : PayloadKind) (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W) (args : ExitArgs kind Nat) : Bool :=
  match kind, args with
  | .account, args =>
    onReturnedB ((keyFn script.owner target .owner "script owner" before).map AnchorAccount.widen)
      fun expected after =>
      exitExpectedReadyB cloneLocal storage script target after args.wrapper args.profile
        args.programId expected
  | .interfaceAccount, args =>
    exitExpectedReadyB cloneLocal storage script target before args.wrapper.account args.profile
      args.programId args.wrapper.owner

theorem exitReadyB_iff (kind : PayloadKind) (cloneLocal : Bool) (storage :
  AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W) (args : ExitArgs kind Nat) :
    exitReadyB kind cloneLocal storage script target before args = true ↔
      ExitReady kind cloneLocal (exitTypes storage script target) before args := by
  cases kind with
  | account =>
    exact onReturned_iff (widened_graph (PGraph.ofOption _)) _ _ fun expected after =>
      exitExpectedReadyB_iff cloneLocal storage script target after args.wrapper args.profile
        args.programId expected
  | interfaceAccount =>
    exact exitExpectedReadyB_iff cloneLocal storage script target before args.wrapper.account
      args.profile
      args.programId args.wrapper.owner

/-- Zero-length close reuses the reached resize readiness of the SDK. A failed
borrow or unchanged empty data does not require a loader allocation header. -/
def resizeZeroB (state : AccountInfoSdk.State) (info : AccountInfo.Value) : Bool :=
  validB state.borrow && match state.borrow.lookupCell info.data with
  | some ⟨.data bytes, _⟩ =>
    if state.borrow.exclusiveCount info.data = 0 ∧ state.borrow.sharedCount info.data = 0 ∧
      bytes.length ≠ 0 then
      (state.buffer info.data).isSome else true
  | _ => false

theorem resizeZeroB_iff (state : AccountInfoSdk.State) (info : AccountInfo.Value) :
    resizeZeroB state info = true ↔ AccountInfoSdk.ResizeReady state ⟨info, 0, false⟩ := by
  unfold resizeZeroB AccountInfoSdk.ResizeReady
  rw [Bool.and_eq_true, validB_iff]
  apply and_congr_right; intro _
  cases found : state.borrow.lookupCell info.data with
  | none => simp
  | some cell =>
    rcases cell with ⟨content, policy⟩
    cases content with
    | lamports _ => simp
    | data bytes =>
      simp only [Option.some.injEq, Borrow.Cell.mk.injEq, AccountInfo.Content.data.injEq]
      by_cases reached : state.borrow.exclusiveCount info.data = 0 ∧
          state.borrow.sharedCount info.data = 0 ∧ bytes.length ≠ 0
      · rcases reached with ⟨exclusive, shared, size⟩
        simp [exclusive, shared, size, Ne.symm size, Option.isSome_iff_exists]
      · simp only [reached, ↓reduceIte, true_iff]
        refine ⟨bytes, policy, ⟨rfl, rfl⟩, ?_⟩
        intro exclusive shared size
        exact False.elim (reached ⟨exclusive, shared, Ne.symm size⟩)

def lamportsB (state : AccountInfoSdk.State) (info : AccountInfo.Value) : Bool :=
  match state.borrow.lookupCell info.lamports with
  | some ⟨.lamports _, _⟩ => true
  | _ => false

theorem lamportsB_iff (state : AccountInfoSdk.State) (info : AccountInfo.Value) :
    lamportsB state info = true ↔ AccountInfo.ObservationReady .lamports state.borrow info := by
  unfold lamportsB AccountInfo.ObservationReady
  cases found : state.borrow.lookupCell info.lamports with
  | none => simp [AccountInfo.Observation.handle, found]
  | some cell =>
    rcases cell with ⟨content, policy⟩
    cases content <;> simp [AccountInfo.Observation.handle, AccountInfo.Observation.project, found]

def closeBalancesReadyB (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs)
    (sourceBalance destinationBalance : Nat) : Bool :=
  if sourceBalance + destinationBalance < 2^64 then
    onOkB (closeWrite (mode == .checked) args.profile state args.destination (sourceBalance +
      destinationBalance))
      fun credited => onOkB (closeWrite false args.profile credited args.info 0) fun zeroed =>
        decide (args.info.ownerRef.id < zeroed.owners.length) &&
          resizeZeroB (AccountInfoSdk.assign zeroed (args.info, AnchorAccount.systemProgramId)).2
            args.info
  else true

theorem closeBalancesReadyB_iff (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs)
    (sourceBalance destinationBalance : Nat) :
    closeBalancesReadyB mode state args sourceBalance destinationBalance = true ↔
      CloseBalancesReady mode state args sourceBalance destinationBalance := by
  apply whenB_iff
  apply onOk_iff (PGraph.ofOption _)
  intro credited
  apply onOk_iff (PGraph.ofOption _)
  intro zeroed
  rw [Bool.and_eq_true, decide_eq_true_eq, resizeZeroB_iff]

def closeCoreReadyB (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs) : Bool :=
  match mode with
  | .legacy => lamportsB state args.destination &&
      onReturnedB (closeRead args.profile state args.destination) fun destinationBalance
        afterDestination =>
        lamportsB afterDestination args.info &&
          onReturnedB (closeRead args.profile afterDestination args.info) fun sourceBalance
            afterSource =>
            closeBalancesReadyB mode afterSource args sourceBalance destinationBalance
  | .checked => lamportsB state args.info &&
      onReturnedB (closeRead args.profile state args.info) fun sourceBalance afterSource =>
        lamportsB afterSource args.destination &&
          onReturnedB (closeRead args.profile afterSource args.destination) fun destinationBalance
            afterDestination =>
            closeBalancesReadyB mode afterDestination args sourceBalance destinationBalance

theorem closeCoreReadyB_iff (mode : CloseMode) (state : AccountInfoSdk.State) (args : CloseArgs) :
    closeCoreReadyB mode state args = true ↔ CloseCoreReady mode state args := by
  cases mode with
  | legacy =>
    unfold closeCoreReadyB CloseCoreReady
    rw [Bool.and_eq_true, lamportsB_iff]
    apply and_congr_right; intro _
    apply onReturned_iff (PGraph.ofOption _)
    intro destinationBalance afterDestination
    rw [Bool.and_eq_true, lamportsB_iff]
    apply and_congr_right; intro _
    exact onReturned_iff (PGraph.ofOption _) _ _ fun sourceBalance afterSource =>
      closeBalancesReadyB_iff .legacy afterSource args sourceBalance destinationBalance
  | checked =>
    unfold closeCoreReadyB CloseCoreReady
    rw [Bool.and_eq_true, lamportsB_iff]
    apply and_congr_right; intro _
    apply onReturned_iff (PGraph.ofOption _)
    intro sourceBalance afterSource
    rw [Bool.and_eq_true, lamportsB_iff]
    apply and_congr_right; intro _
    exact onReturned_iff (PGraph.ofOption _) _ _ fun destinationBalance afterDestination =>
      closeBalancesReadyB_iff .checked afterDestination args sourceBalance destinationBalance

def closeReadyB (cloneSource : Bool) (mode : CloseMode) (before : W) (args : CloseArgs) : Bool :=
  if cloneSource then onReturnedB (cloneFn before args.info) fun info after =>
    closeCoreReadyB mode (sdk.get after) { args with info := info }
  else closeCoreReadyB mode (sdk.get before) args

theorem closeReadyB_iff (cloneSource : Bool) (mode : CloseMode) (storage :
  AnchorErrorOperations.Storage)
    (before : W) (args : CloseArgs) :
    closeReadyB cloneSource mode before args = true ↔
      ((closeFamily cloneSource mode).contract (closeTypes storage)).requires before args := by
  cases cloneSource with
  | false => exact closeCoreReadyB_iff mode (sdk.get before) args
  | true =>
    exact onReturned_iff (clone_graph storage before args.info) _ _ fun info after =>
      closeCoreReadyB_iff mode (sdk.get after) { args with info := info }

namespace Controls

def initial : AccountInfo.State :=
  ⟨[⟨.lamports 10, ⟨32⟩⟩, ⟨.data [1, 2], ⟨32⟩⟩], []⟩

def guard : Borrow.Guard := ⟨0, 0⟩

def held : AccountInfo.State := (AccountInfo.tryBorrowMutData initial AccountInfo.sampleArgs).2

def written : AccountInfo.State := (Borrow.write held guard (.data [7, 8])).2

/-- A serializer may replace the bytes in its borrowed writer, while a
deserializer admitted under an unchanged-data frame may not. -/
theorem mutable_write_admitted : mutableStateFrameB held written guard = true := by decide

theorem decoder_write_rejected : stateFrameB held written guard = false := by decide

theorem resized_writer_rejected :
    mutableStateFrameB held (Borrow.write held guard (.data [7, 8, 9])).2 guard = false := by decide

theorem released_guard_rejected :
    mutableStateFrameB held (Borrow.release written guard).2 guard = false := by decide

def shortRc : Aux where
  owners := [.zero]
  counts := [1]
  log := []
  strings := []
  boxes := []
  payload := 7
  extraLive := 0
  programString := none
  buffers := []

def conflicted : AccountInfo.State :=
  { held with slots := held.slots ++ [some ⟨AccountInfo.sampleInfo.data, .shared, 0, .whole⟩] }

/-- The first Rc primitive still needs a valid frame when the next primitive
has no finite interpretation because its resource identity is absent. -/
theorem missing_later_rc_does_not_hide_bad_prefix :
    rcReadyB true (conflicted, shortRc) AccountInfo.sampleInfo guard = false := by decide

theorem resize_conflict_needs_no_header :
    resizeZeroB ⟨held, [], []⟩ AccountInfo.sampleInfo = true := by decide

theorem reached_resize_needs_header :
    resizeZeroB ⟨initial, [], []⟩ AccountInfo.sampleInfo = false := by decide

theorem empty_resize_needs_no_header :
    resizeZeroB ⟨(Borrow.replaceCell initial AccountInfo.sampleInfo.data (.data [])).2, [], []⟩
      AccountInfo.sampleInfo = true := by decide

end Controls

private def BoxesKept {Value : Type} (before : W) : SigOut Value → Prop
  | .returned _ after => after.2.boxes = before.2.boxes
  | .unwound _ after => after.2.boxes = before.2.boxes
  | .terminated _ => True

private theorem effectsFn_boxes (target : AccountInfo.Value) (step : Step)
    (before : W) (produced : SigOut Unit) (called : effectsFn target step before = some produced) :
    BoxesKept before produced := by
  unfold effectsFn at called
  cases assigned : step.assign <;> simp only [assigned] at called <;>
    cases balance : step.lamports <;> simp only [balance] at called
  all_goals
    repeat' first | (cases called <;> rfl) | split at called

private theorem keyFn_boxes (steps : List Step) (target : AccountInfo.Value)
    (event : Event) (label : String) (before : W) (produced : SigOut Solanalib.Runtime.Pubkey)
    (called : keyFn steps target event label before = some produced) : BoxesKept before produced :=
      by
  unfold keyFn at called
  obtain ⟨⟨step, logged⟩, began, next⟩ := Option.bind_eq_some_iff.mp called
  have loggedKept : logged.2.boxes = before.2.boxes := by
    unfold begin at began
    obtain ⟨selected, found, equal⟩ := Option.map_eq_some_iff.mp began
    cases equal
    rfl
  obtain ⟨effect, effected, next⟩ := Option.bind_eq_some_iff.mp next
  have kept := effectsFn_boxes target step logged effect effected
  cases effect with
  | returned value after =>
    simp only [PGraph.bindK] at next
    split at next <;> cases next <;> exact kept.trans loggedKept
  | unwound reason after =>
    cases next
    exact kept.trans loggedKept
  | terminated reason =>
    cases next
    trivial

private theorem newBox_current (before : W) (payload : ErrorPayload) (resource : Nat) (after : W)
    (called : errors.newBox before payload (.returned resource after)) :
    currentBox after resource = some payload := by
  change newBox before payload = .returned resource after at called
  cases called
  simp [currentBox]

private theorem diagnosticReadyB_keyFn (steps : List Step) (target : AccountInfo.Value)
    (event : Event) (label : String) (failure : AnchorErrorOperations.Code)
    (observed : W → Solanalib.Runtime.Pubkey) (before : W) :
    diagnosticReadyB (keyFn steps target event label) failure observed before = true := by
  rw [diagnosticReadyB_iff]
  intro name afterName _ message afterMessage _ resource afterBox allocated
  have fresh := newBox_current afterMessage _ resource afterBox allocated
  refine ⟨fresh, ?_⟩
  intro produced called
  have kept := keyFn_boxes steps target event label afterBox produced called
  cases produced with
  | returned diagnostic after =>
    have boxes : currentBox after resource = currentBox afterBox resource :=
      congrArg (fun boxes => boxes[resource]?.join) kept
    refine ⟨boxes, ?_⟩
    simp [writeBox, boxes, fresh]
  | unwound reason after =>
    exact congrArg (fun boxes => boxes[resource]?.join) kept
  | terminated reason => trivial

/-- The tested key callback changes owner metadata, lamports and its log,
but retains every diagnostic Box. This is a fact about the concrete provider,
not an admission axiom for arbitrary generic Id implementations. -/
theorem idReadyB_true (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (before : W) (args : AccountInfo.Args) :
    idReadyB storage script target before args = true := by
  cases storage with
  | inline => rfl
  | boxed =>
    simp only [idReadyB, ↓reduceIte]
    cases called : keyFn script.id target .id "script id" before with
    | none => rfl
    | some produced =>
      cases produced with
      | returned expected after =>
        simp only [onReturnedB]
        split
        · exact diagnosticReadyB_keyFn script.id target .id "script id" _ _ after
        · rfl
      | unwound _ _ => rfl
      | terminated _ => rfl

theorem validationReadyB_always (kind : ValidationKind) (storage : AnchorErrorOperations.Storage)
    (script : Script) (target : AccountInfo.Value) (before : W) (args : ReferenceArgs) :
    validationReadyB kind storage script target before args = true := by
  cases kind <;> try rfl
  exact idReadyB_true storage script target before args.toAccountInfoArgs


end SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Ready
