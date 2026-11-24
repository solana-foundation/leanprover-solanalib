/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.ConstructCheck
import SolanalibTest.Conformance.Library.Families.Anchor.Loading
import SolanalibTest.Conformance.Library.Families.Anchor.Decide

/-!
# Preconditions of the constructor and loader models

Executable deciders, with proved equivalences, for the `requires` of
`Account`/`InterfaceAccount`/`AccountLoader::try_from` (primary and observation
models) and `AccountLoader::load`/`load_mut` at the scripted
indices of the checkers: initialization readiness, owner-check resource readiness, decoder
admission (every decoder exit frames the held data guard), Loader readiness
(validity and admission of the guarded error factory) and the token liveness of the loading
factory. Every callback and primitive has a graph, so each
quantifier over its exits is a computation on the one exit it has.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace SolanalibTest.Conformance.Library.Families.Anchor.RequiresAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Families.Anchor.Decide
open SolanalibTest.Conformance.Library.Families.Anchor.Construct

/-! ## Shared pieces -/

def dataTypedB (s : AccountInfo.State) (h : Borrow.Handle) : Bool :=
  match s.lookupCell h with
  | some ⟨.data _, _⟩ => true
  | _ => false

theorem dataTypedB_iff (s : AccountInfo.State) (h : Borrow.Handle) :
    dataTypedB s h = true ↔ ∃ bytes policy, s.lookupCell h = some ⟨.data bytes, policy⟩ := by
  unfold dataTypedB
  cases hc : s.lookupCell h with
  | none => simp
  | some cell =>
    rcases cell with ⟨content, policy⟩
    cases content with
    | lamports v => simp
    | data bytes => simp

instance initReadyDecidable {Aux : Type} (ownerAt : AccountInfo.OwnerAt Aux) (before : World Aux)
    (args : AccountInfo.Args) : Decidable (InitReady ownerAt before args) := by
  unfold InitReady; infer_instance

/-- Decoder admission at a callback given by a function. -/
def decodeReadyB {Aux D U T : Type} (deserialize : World Aux → DecodeArgs → Outcome (World Aux) D U
  T)
    (before : World Aux) (args : AccountInfo.Args) : Bool :=
  dataTypedB before.1 args.info.data &&
  match AccountInfo.tryBorrowData before.1 args with
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .ok (_, .data bytes) => frameB (during, before.2) guard (deserialize (during, before.2)
      ⟨args.info, guard, bytes⟩)
    | _ => true
  | _ => true

/-- `decodeReadyB` decides the common decoder-admission shape. -/
theorem decodeReadyB_iff {Aux D U T : Type} (deserialize : World Aux → DecodeArgs → Outcome (World
  Aux) D U T)
    (before : World Aux) (args : AccountInfo.Args) :
    decodeReadyB deserialize before args = true ↔
      ((∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
        ∀ guard during, AccountInfo.tryBorrowData before.1 args = (.ok guard, during) →
          ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
            AccountInfo.GuardCallback.Admissible guard (Callback.ofFunction deserialize) (during,
              before.2)
              ⟨args.info, guard, bytes⟩) := by
  unfold decodeReadyB
  rw [Bool.and_eq_true, dataTypedB_iff]
  apply and_congr_right
  intro _
  have adm := fun guard during bytes =>
    admissible_iff (guard := guard) (PGraph.ofFunction deserialize (during, before.2) ⟨args.info,
      guard, bytes⟩)
  rcases hb : AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · simp
  · simp only
    constructor
    · intro h guard' during' e view bytes hc
      cases e
      rw [hc] at h
      exact (adm guard during bytes).mp h
    · intro h
      rcases hc : Borrow.current during guard with e | ⟨view, content⟩
      · rfl
      · rcases content with v | bytes
        · rfl
        · exact (adm guard during bytes).mpr (h guard during rfl view bytes hc)

/-! ## Observation constructors (`AnchorAccount.ConstructorReady`) -/

def obsDecode (sc : Script) := decodeFn obsShape sc (fun r => (⟨r, []⟩ : Decoded UInt64))

def obsInit (before : OW) (args : AccountInfo.Args) :=
  initialized (Unwind := String) (Terminal := Empty) CAux.ownerAt before args

def obsReadyB (kind : Constructor) (sc : Script) (before : OW) (args : AccountInfo.Args) : Bool :=
  match kind with
  | .account => decide (InitReady CAux.ownerAt before args) &&
      onOkB (obsInit before args) fun after =>
        onOkB (obsOwnerCheckFn sc after args) fun checked => decodeReadyB (obsDecode sc) checked
          args
  | .interfaceAccount => decide (InitReady CAux.ownerAt before args) &&
      onOkB (obsInit before args) fun after =>
        onOkB (some (widen (checkFn obsShape sc after args.info.ownerRef))) fun checked =>
          decodeReadyB (obsDecode sc) checked args
  | .loader => onOkB (obsOwnerCheckFn sc before args) fun checked => dataTypedB checked.1
    args.info.data

theorem obsReadyB_iff (kind : Constructor) (sc : Script) (before : OW) (args : AccountInfo.Args) :
    obsReadyB kind sc before args = true ↔ ConstructorReady kind (obsIndex sc) before args := by
  cases kind with
  | account =>
    simp only [obsReadyB, ConstructorReady, Bool.and_eq_true, decide_eq_true_eq]
    apply and_congr_right; intro _
    exact onOk_iff (PGraph.ofOption _) _ _ fun after =>
      onOk_iff (obsOwnerCheck_graph sc after args) _ _ fun checked => decodeReadyB_iff _ checked
        args
  | interfaceAccount =>
    simp only [obsReadyB, ConstructorReady, Bool.and_eq_true, decide_eq_true_eq]
    apply and_congr_right; intro _
    exact onOk_iff (PGraph.ofOption _) _ _ fun after =>
      onOk_iff (widen_graph (PGraph.ofFunction _ after _)) _ _ fun checked => decodeReadyB_iff _
        checked args
  | loader =>
    exact onOk_iff (obsOwnerCheck_graph sc before args) _ _ fun checked => dataTypedB_iff _ _

/-! ## Owner-check readiness of the primary constructors -/

/-- The payload of the wrong-owner error before the diagnostic store. -/
def payload3 (name message : StringId) : AnchorErrorOwned.Payload StringId :=
  .anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩

def ownerExitReadyB (args : AccountInfo.Args) (name message : StringId) (resource : BoxId) (before
  : W) :
    Outcome W Solanalib.Runtime.Pubkey String Failure → Bool
  | .returned diagnostic after =>
    decide (ownedOps.currentBox after resource = ownedOps.currentBox before resource) &&
      (ownedOps.writeBox after resource ((payload3 name message).withPubkeys
        (before.2.2.ownerAt args.info.ownerRef) diagnostic)).isSome
  | .unwound _ after => decide (ownedOps.currentBox after resource = ownedOps.currentBox before
    resource)
  | .terminated _ => true

theorem ownerExitReadyB_iff (sc : Script) (args : AccountInfo.Args) (name message : StringId)
  (resource : BoxId)
    (before : W) (o : Outcome W Solanalib.Runtime.Pubkey String Failure) :
    ownerExitReadyB args name message resource before o = true ↔
      AnchorConstructOwned.OwnerExitReady (ownedTypes sc) args name message resource before o := by
  cases o with
  | returned diagnostic after =>
    simp only [ownerExitReadyB, AnchorConstructOwned.OwnerExitReady, Bool.and_eq_true,
      decide_eq_true_eq,
      Option.isSome_iff_exists]
    rfl
  | unwound r after => simp only [ownerExitReadyB, AnchorConstructOwned.OwnerExitReady,
    decide_eq_true_eq]; rfl
  | terminated r => simp [ownerExitReadyB, AnchorConstructOwned.OwnerExitReady]

def code3 : Code := AnchorAccount.Code.ownedByWrongProgram

def ownerCheckReadyB (sc : Script) (before : W) (args : AccountInfo.Args) : Bool :=
  onReturnedB (some (ownerFn ownedShape sc before ())) fun expected after =>
    decide (after.2.2.ownerAt args.info.ownerRef = expected) ||
    onReturnedB (ownedFn.copy after code3.payload.name) fun name afterName =>
      onReturnedB (ownedFn.format afterName code3.payload.message) fun message afterMessage =>
        onReturnedB (ownedFn.newBox afterMessage (payload3 name message))
          fun resource afterBox =>
            decide (ownedOps.currentBox afterBox resource = some (payload3 name message)) &&
              allExitsB (some (ownerFn ownedShape sc afterBox ()))
                (ownerExitReadyB args name message resource afterBox)

theorem ownerCheckReadyB_iff (sc : Script) (before : W) (args : AccountInfo.Args) :
    ownerCheckReadyB sc before args = true ↔ AnchorConstructOwned.OwnerCheckReady (ownedTypes sc)
      before args := by
  unfold ownerCheckReadyB AnchorConstructOwned.OwnerCheckReady
  apply onReturned_iff (PGraph.ofFunction _ before ())
  intro expected after
  rw [Bool.or_eq_true, decide_eq_true_eq]
  by_cases same : after.2.2.ownerAt args.info.ownerRef = expected
  · simp only [same, true_or, true_iff]
    intro mismatch; exact absurd same mismatch
  · simp only [same, false_or]
    have tail := onReturned_iff (ownedGraph.copy after code3.payload.name) _ _ fun name afterName =>
      onReturned_iff (ownedGraph.format afterName code3.payload.message) _ _ fun message
        afterMessage =>
        onReturned_iff (ownedGraph.newBox afterMessage (payload3 name message)) _ _ fun resource
          afterBox =>
          (iff_of_eq (Bool.and_eq_true _ _)).trans (and_congr
            (decide_eq_true_iff (p := ownedOps.currentBox afterBox resource = some (payload3 name
              message)))
            (allExits_iff (PGraph.ofFunction (ownerFn ownedShape sc) afterBox ()) _ _
              (ownerExitReadyB_iff sc args name message resource afterBox)))
    exact tail.trans ⟨fun h _ => h, fun h => h same⟩

/-! ## Loader readiness and the guarded error factory -/

def buildCodeAdmissibleB {Aux Str Box T : Type} (fn : OpsFn (World Aux) Str Box T)
    (before : World Aux) (guard : Borrow.Guard) (code : AnchorErrorOwned.Code) : Bool :=
  allExitsB (fn.copy before code.name) (frameB before guard) &&
  onReturnedB (fn.copy before code.name) (fun name afterName =>
    allExitsB (fn.format afterName code.message) (frameB afterName guard)) &&
  onReturnedB (fn.copy before code.name) (fun name afterName =>
    onReturnedB (fn.format afterName code.message) fun message afterMessage =>
      allExitsB (fn.newBox afterMessage (.anchor ⟨name, code.number, message, none, none⟩)) (frameB
        afterMessage guard))

theorem buildCodeAdmissibleB_iff {Aux Str Box T : Type} {ops : AnchorErrorOwned.Ops (World Aux) Str
  Box T}
    {fn : OpsFn (World Aux) Str Box T} (h : OpsGraph ops fn) (before : World Aux) (guard :
      Borrow.Guard)
    (code : AnchorErrorOwned.Code) :
    buildCodeAdmissibleB fn before guard code = true ↔ AnchorGuardEffects.BuildCodeAdmissible ops
      before guard code := by
  unfold buildCodeAdmissibleB
  rw [Bool.and_eq_true, Bool.and_eq_true, admissible_iff (h.copy before code.name),
    onReturned_iff (h.copy before code.name) _ _ fun name afterName => admissible_iff (h.format
      afterName code.message),
    onReturned_iff (h.copy before code.name) _ _ fun name afterName =>
      onReturned_iff (h.format afterName code.message) _ _ fun message afterMessage =>
        admissible_iff (h.newBox afterMessage _)]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

def loaderReadyB (sc : Script) (before : W) (args : AccountInfo.Args) : Bool :=
  validB before.1 &&
  match AccountInfo.tryBorrowData before.1 args with
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .ok (_, .data bytes) =>
      match AnchorConstructOwned.discriminatorFailure (ownedTypes sc).discriminator bytes with
      | some failure => buildCodeAdmissibleB ownedFn (during, before.2) guard
          ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩
      | none => true
    | _ => true
  | _ => true

theorem loaderReadyB_iff (sc : Script) (before : W) (args : AccountInfo.Args) :
    loaderReadyB sc before args = true ↔ AnchorConstructOwned.LoaderReady (ownedTypes sc) before
      args := by
  unfold loaderReadyB AnchorConstructOwned.LoaderReady
  rw [Bool.and_eq_true, validB_iff]
  apply and_congr_right; intro _
  rcases hb : AccountInfo.tryBorrowData before.1 args with ⟨borrowed, during⟩
  rcases borrowed with failure | guard
  · simp
  · simp only
    constructor
    · intro h guard' during' e view bytes hc failure hf
      cases e
      rw [hc] at h
      simp only [hf] at h
      exact (buildCodeAdmissibleB_iff ownedGraph _ _ _).mp h
    · intro h
      rcases hc : Borrow.current during guard with e | ⟨view, content⟩
      · rfl
      · rcases content with v | bytes
        · rfl
        · dsimp only
          cases hf : AnchorConstructOwned.discriminatorFailure (ownedTypes sc).discriminator bytes
            with
          | none => rfl
          | some failure =>
            exact (buildCodeAdmissibleB_iff ownedGraph _ _ _).mpr (h guard during rfl view bytes hc
              failure hf)

/-! ## Primary constructors (`AnchorConstructOwned.Ready`) -/

def ownedDecode (sc : Script) :=
  decodeFn ownedShape sc (fun r => (⟨r, []⟩ : AnchorConstructOwned.Decoded OErr UInt64))

def ownedReadyB (kind : Constructor) (sc : Script) (before : W) (args : AccountInfo.Args) : Bool :=
  match kind with
  | .account => decide (InitReady (Aux := OAux) (fun aux ref => aux.2.ownerAt ref) before args) &&
      onOkB (initFn before args) fun after =>
        ownerCheckReadyB sc after args &&
          onOkB (ownedOwnerCheckFn sc after args) fun checked => decodeReadyB (ownedDecode sc)
            checked args
  | .interfaceAccount => decide (InitReady (Aux := OAux) (fun aux ref => aux.2.ownerAt ref) before
    args) &&
      onOkB (initFn before args) fun after =>
        onOkB (some (widen (checkFn ownedShape sc after args.info.ownerRef))) fun checked =>
          decodeReadyB (ownedDecode sc) checked args
  | .loader => ownerCheckReadyB sc before args &&
      onOkB (ownedOwnerCheckFn sc before args) fun checked =>
        dataTypedB checked.1 args.info.data && loaderReadyB sc checked args

theorem ownedReadyB_iff (kind : Constructor) (sc : Script) (before : W) (args : AccountInfo.Args) :
    ownedReadyB kind sc before args = true ↔ AnchorConstructOwned.Ready kind (ownedTypes sc) before
      args := by
  cases kind with
  | account =>
    simp only [ownedReadyB, AnchorConstructOwned.Ready, Bool.and_eq_true, decide_eq_true_eq]
    apply and_congr_right; intro _
    refine onOk_iff (init_graph sc before args) _ _ fun after => ?_
    rw [Bool.and_eq_true]
    exact and_congr (ownerCheckReadyB_iff sc after args)
      (onOk_iff (ownedOwnerCheck_graph sc after args) _ _ fun checked => decodeReadyB_iff _ checked
        args)
  | interfaceAccount =>
    simp only [ownedReadyB, AnchorConstructOwned.Ready, Bool.and_eq_true, decide_eq_true_eq]
    apply and_congr_right; intro _
    exact onOk_iff (init_graph sc before args) _ _ fun after =>
      onOk_iff (widen_graph (PGraph.ofFunction _ after _)) _ _ fun checked => decodeReadyB_iff _
        checked args
  | loader =>
    simp only [ownedReadyB, AnchorConstructOwned.Ready, Bool.and_eq_true]
    exact and_congr (ownerCheckReadyB_iff sc before args) <|
      onOk_iff (ownedOwnerCheck_graph sc before args) _ _ fun checked => by
        rw [Bool.and_eq_true, dataTypedB_iff]
        exact and_congr_right fun _ => loaderReadyB_iff sc checked args

/-! ## Loading (`AnchorLoadingOwned.Admission`) -/

def dataReadyB (mode : Borrow.Mode) (s : AccountInfo.State) (h : Borrow.Handle) : Bool :=
  match AccountInfo.tryBorrow mode h s with
  | (.error _, _) => true
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .ok (_, .data _) => true
    | _ => false

theorem dataReadyB_iff (mode : Borrow.Mode) (s : AccountInfo.State) (h : Borrow.Handle) :
    dataReadyB mode s h = true ↔ AccountInfo.DataBorrow.Ready mode s h := by
  unfold dataReadyB AccountInfo.DataBorrow.Ready
  rcases AccountInfo.tryBorrow mode h s with ⟨r, during⟩
  rcases r with e | guard
  · simp
  · simp only
    rcases Borrow.current during guard with e | ⟨v, c⟩
    · simp
    · cases c <;> simp

def factoryReadyB (before : Loading.W) (guard : Borrow.Guard) (failure : Code) : Bool :=
  allExitsB (Loading.ownedFn.copy before failure.payload.name) (exitLiveB guard) &&
  onReturnedB (Loading.ownedFn.copy before failure.payload.name) (fun name afterName =>
    allExitsB (Loading.ownedFn.format afterName failure.payload.message) (exitLiveB guard)) &&
  onReturnedB (Loading.ownedFn.copy before failure.payload.name) (fun name afterName =>
    onReturnedB (Loading.ownedFn.format afterName failure.payload.message) fun message afterMessage
      =>
      allExitsB (Loading.ownedFn.newBox afterMessage (.anchor ⟨name, failure.payload.code, message,
        none, none⟩))
        (exitLiveB guard))

theorem factoryReadyB_iff (l : LoadIndex) (before : Loading.W) (guard : Borrow.Guard) (failure :
  Code) :
    factoryReadyB before guard failure = true ↔ AnchorLoadingOwned.FactoryReady (Loading.types l)
      before guard failure := by
  unfold factoryReadyB
  rw [Bool.and_eq_true, Bool.and_eq_true, liveAt_iff (Loading.ownedGraph.copy before _),
    onReturned_iff (Loading.ownedGraph.copy before _) _ _ fun name afterName =>
      liveAt_iff (Loading.ownedGraph.format afterName _),
    onReturned_iff (Loading.ownedGraph.copy before _) _ _ fun name afterName =>
      onReturned_iff (Loading.ownedGraph.format afterName _) _ _ fun message afterMessage =>
        liveAt_iff (Loading.ownedGraph.newBox afterMessage _)]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

def admissionB (mode : Borrow.Mode) (l : LoadIndex) (before : Loading.W) (args : LoadArgs l) : Bool
  :=
  (decide (mode = .exclusive ∧ args.loader.info.isWritable = false) ||
    dataReadyB mode before.1 args.loader.info.data) &&
  (decide (mode = .exclusive ∧ args.loader.info.isWritable = false) ||
    match AccountInfo.tryBorrow mode args.loader.info.data before.1 with
    | (.error _, _) => true
    | (.ok guard, during) =>
      match Borrow.current during guard with
      | .ok (_, .data bytes) =>
        match AnchorConstructOwned.discriminatorFailure l.discriminator bytes with
        | none => true
        | some failure => factoryReadyB (during, before.2) guard failure
      | _ => true)

theorem admissionB_iff (mode : Borrow.Mode) (l : LoadIndex) (before : Loading.W) (args : LoadArgs
  l) :
    admissionB mode l before args = true ↔ AnchorLoadingOwned.Admission mode (Loading.types l)
      before args := by
  unfold admissionB AnchorLoadingOwned.Admission LoadReady
  rw [Bool.and_eq_true]
  by_cases blocked : mode = .exclusive ∧ args.loader.info.isWritable = false
  · simp [blocked]
  · simp only [blocked, decide_false, Bool.false_or, ↓reduceIte, dataReadyB_iff]
    apply and_congr_right; intro _
    rcases AccountInfo.tryBorrow mode args.loader.info.data before.1 with ⟨r, during⟩
    rcases r with e | guard
    · simp
    · simp only
      rcases Borrow.current during guard with e | ⟨v, c⟩
      · simp
      · rcases c with x | bytes
        · simp
        · dsimp only [Loading.types]
          cases AnchorConstructOwned.discriminatorFailure l.discriminator bytes with
          | none => simp
          | some failure => exact factoryReadyB_iff l _ guard failure

end SolanalibTest.Conformance.Library.Families.Anchor.RequiresAccounts
