/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Spl

/-!
# `anchor_spl::token::transfer`, primary owned model (`AnchorSplTransfer.run`)

Decided at the resources of the registered sample (`AnchorSplTransfer.Sample.resources`:
the two-vector instruction ledger, the remaining-account vector ledger, `Rc`
event trace, the reference error heap with `Nat` terminals) with the
invocation instance `Spl.Invocation` (the `RefCell` pre-check of solana-invoke over
the borrow state of the record, then the scripted CPI reply), appending the request
to the `calls` log of the sample. The instruction builder (`Token.InstructionAllocated.run`
at the transfer plan), invocation, `map_err` boxing and the edition-2021 scope
cleanup (instruction vectors, the `Rc` drops of the three moved AccountInfos, the
remaining-account vector) get their graphs from their definitions.

Observation: the result (an error by its current value in the heap), the CPI
requests, and the `Rc` strong count of every cell: the trace of the model of `Rc`
drop events applied to the counts before the call, against
`Rc::strong_count` after it. The slot histories of the ledgers are ghost state.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor.TransferOwned

open Solanalib.Contracts.Model Solanalib.Specs.Core SolanalibTest.Conformance.Library.Runtime
open Solanalib.Specs.Core.AnchorSplTransfer
open SolanalibTest.Conformance.Library.Families.Anchor.Errors (both outcomeJson renderOpt emptyJson)
open SolanalibTest.Conformance.Library.Families.Anchor.Construct (pgraph_ite)
open SolanalibTest.Conformance.Library.Families.Anchor.Spl (ReqObs reqObs asCpiLog reqJson
  asTransferArgs)

abbrev S := Sample.State

/-! ## Vector ledgers -/

structure VecFn (State Element Resource U T : Type) where
  withCapacity : State → Nat → Option (Outcome State Resource U T)
  fromList : State → List Element → Option (Outcome State Resource U T)
  push : State → Resource × Element → Option (Outcome State Unit U T)
  extend : State → Resource × List Element → Option (Outcome State Unit U T)
  drop : State → Resource → Option (Outcome State Unit U T)

structure VecGraph {State Element Resource U T : Type} (ops : Owned.VectorOps State Element
  Resource U T)
    (fn : VecFn State Element Resource U T) : Prop where
  withCapacity : ∀ s a, PGraph (ops.withCapacity s a) (fn.withCapacity s a)
  fromList : ∀ s a, PGraph (ops.fromList s a) (fn.fromList s a)
  push : ∀ s a, PGraph (ops.push s a) (fn.push s a)
  extend : ∀ s a, PGraph (ops.extend s a) (fn.extend s a)
  drop : ∀ s a, PGraph (ops.drop s a) (fn.drop s a)

def refVec {E U T : Type} : VecFn (Owned.VectorState E) E Nat U T where
  withCapacity := fun s _ => some (.returned (s.allocate []).1 (s.allocate []).2)
  fromList := fun s v => some (.returned (s.allocate v).1 (s.allocate v).2)
  push := fun s (r, v) => (s.current r).map fun values => .returned () (s.set r (some (values ++
    [v])))
  extend := fun s (r, v) => (s.current r).map fun values => .returned () (s.set r (some (values ++
    v)))
  drop := fun s r => (s.current r).map fun _ => .returned () (s.set r none)

theorem returnsOf_graph {St A V U T : Type} (f : St → A → V × St) (b : St) (a : A) :
    PGraph (returnsOf (Unwind := U) (Terminal := T) f b a) (some (.returned (f b a).1 (f b a).2))
      := by
  intro o
  exact (returnsOf_iff f b a o).trans ⟨fun h => by rw [h], fun h => Option.some.inj h⟩

theorem refVec_graph {E U T : Type} : VecGraph (Owned.vectorReference (Element := E) (Unwind := U)
  (Terminal := T)) refVec where
  withCapacity := fun s a => returnsOf_graph (fun (state : Owned.VectorState E) (_ : Nat) =>
    state.allocate []) s a
  fromList := fun s a => returnsOf_graph Owned.VectorState.allocate s a
  push := fun s a => PGraph.exists_eq' _ (PGraph.ofOption _)
  extend := fun s a => PGraph.exists_eq' _ (PGraph.ofOption _)
  drop := fun s a => PGraph.exists_eq' _ (PGraph.ofOption _)

def VecFn.focus {Outer Inner E R U T : Type} (fn : VecFn Inner E R U T) (part : Owned.Focus Outer
  Inner) :
    VecFn Outer E R U T where
  withCapacity := fun s a => (fn.withCapacity (part.get s) a).map (part.liftOutcome s)
  fromList := fun s a => (fn.fromList (part.get s) a).map (part.liftOutcome s)
  push := fun s a => (fn.push (part.get s) a).map (part.liftOutcome s)
  extend := fun s a => (fn.extend (part.get s) a).map (part.liftOutcome s)
  drop := fun s a => (fn.drop (part.get s) a).map (part.liftOutcome s)

theorem VecGraph.focus {Outer Inner E R U T : Type} {ops : Owned.VectorOps Inner E R U T}
    {fn : VecFn Inner E R U T} (h : VecGraph ops fn) (part : Owned.Focus Outer Inner) :
    VecGraph (ops.focus part) (fn.focus part) where
  withCapacity := fun s a => PGraph.focusLift part (h.withCapacity _ a)
  fromList := fun s a => PGraph.focusLift part (h.fromList _ a)
  push := fun s a => PGraph.focusLift part (h.push _ a)
  extend := fun s a => PGraph.focusLift part (h.extend _ a)
  drop := fun s a => PGraph.focusLift part (h.drop _ a)

abbrev B := Sample.resources.builder

def bytesFn : VecFn S UInt8 Nat Nat Nat := (refVec.focus Owned.Focus.fst).focus Owned.Focus.fst
def metasFn : VecFn S Solanalib.Runtime.CpiMeta Nat Nat Nat := (refVec.focus Owned.Focus.snd).focus
  Owned.Focus.fst

theorem bytes_graph : VecGraph B.bytes bytesFn := (refVec_graph.focus Owned.Focus.fst).focus
  Owned.Focus.fst
theorem metas_graph : VecGraph B.metas metasFn := (refVec_graph.focus Owned.Focus.snd).focus
  Owned.Focus.fst

def doubleFn : S → Nat → Nat → Option Nat := fun _ a b => some (a + b)

theorem double_graph : ∀ s r r', PGraph (B.doubleUnwind s r r') (doubleFn s r r') :=
  fun _ _ _ => PGraph.eq_left _

/-! ## Instruction builder -/

open Token.InstructionAllocated

def writeDataFn (resource : Nat) : List Token.InstructionAllocated.DataStep → S → Option (Outcome S
  Unit Nat Nat)
  | [], s => some (.returned () s)
  | step :: rest, s =>
    (match step with
      | .push byte => bytesFn.push s (resource, byte)
      | .extend bytes => bytesFn.extend s (resource, bytes)).bind
      (PGraph.bindK fun _ state => writeDataFn resource rest state)

theorem writeData_graph (resource : Nat) :
    ∀ (steps : List Token.InstructionAllocated.DataStep) (s : S),
      PGraph (writeData B resource steps s ()) (writeDataFn resource steps s)
  | [], s => PGraph.eq_left _
  | step :: rest, s => by
    apply PGraph.bind
    · cases step with
      | push byte => exact bytes_graph.push s _
      | extend bytes => exact bytes_graph.extend s _
    · intro _ state; exact writeData_graph resource rest state

def pushMetasFn (resource : Nat) : List Solanalib.Runtime.CpiMeta → S → Option (Outcome S Unit Nat
  Nat)
  | [], s => some (.returned () s)
  | item :: rest, s => (metasFn.push s (resource, item)).bind (PGraph.bindK fun _ state =>
    pushMetasFn resource rest state)

theorem pushMetas_graph (resource : Nat) :
    ∀ (items : List Solanalib.Runtime.CpiMeta) (s : S), PGraph (pushMetas B resource items s ())
      (pushMetasFn resource items s)
  | [], s => PGraph.eq_left _
  | item :: rest, s => PGraph.bind (metas_graph.push s _) fun _ state => pushMetas_graph resource
    rest state

def buildMetasFn (plan : Token.InstructionAllocated.MetaPlan) (s : S) : Option (Outcome S Nat Nat
  Nat) :=
  match plan with
  | .fromList items => metasFn.fromList s items
  | .withCapacity capacity items =>
    (metasFn.withCapacity s capacity).bind (PGraph.bindK fun resource state =>
      ((pushMetasFn resource items state).map (Outcome.map fun _ => resource)).bind
        (PGraph.onUnwindFn doubleFn [fun current => metasFn.drop current resource]))
  | .fromListThenPush initial rest =>
    (metasFn.fromList s initial).bind (PGraph.bindK fun resource state =>
      ((pushMetasFn resource rest state).map (Outcome.map fun _ => resource)).bind
        (PGraph.onUnwindFn doubleFn [fun current => metasFn.drop current resource]))

theorem buildMetas_graph (plan : Token.InstructionAllocated.MetaPlan) (s : S) :
    PGraph (buildMetas B plan s ()) (buildMetasFn plan s) := by
  cases plan with
  | fromList items => exact metas_graph.fromList s items
  | withCapacity capacity items =>
    exact PGraph.bind (metas_graph.withCapacity s capacity) fun resource state =>
      PGraph.protect double_graph
        (PGraph.DropsGraph.cons (fun current => metas_graph.drop current resource)
          PGraph.DropsGraph.nil)
        (PGraph.map _ (pushMetas_graph resource items state))
  | fromListThenPush initial rest =>
    exact PGraph.bind (metas_graph.fromList s initial) fun resource state =>
      PGraph.protect double_graph
        (PGraph.DropsGraph.cons (fun current => metas_graph.drop current resource)
          PGraph.DropsGraph.nil)
        (PGraph.map _ (pushMetas_graph resource rest state))

def buildDataFn (steps : List Token.InstructionAllocated.DataStep) (s : S) : Option (Outcome S Nat
  Nat Nat) :=
  (bytesFn.withCapacity s B.enumSize).bind (PGraph.bindK fun resource state =>
    ((writeDataFn resource steps state).map (Outcome.map fun _ => resource)).bind
      (PGraph.onUnwindFn doubleFn [fun current => bytesFn.drop current resource]))

theorem buildData_graph (steps : List Token.InstructionAllocated.DataStep) (s : S) :
    PGraph (buildData B steps s ()) (buildDataFn steps s) :=
  PGraph.bind (bytes_graph.withCapacity s _) fun resource state =>
    PGraph.protect double_graph
      (PGraph.DropsGraph.cons (fun current => bytes_graph.drop current resource)
        PGraph.DropsGraph.nil)
      (PGraph.map _ (writeData_graph resource steps state))

abbrev IV := Token.InstructionAllocated.Value B

def buildFn (s : S) (plan : Token.InstructionAllocated.Plan) :
    Option (Outcome S (Except Token.Error IV) Nat Nat) :=
  match Token.Instruction.checkProgram plan.programs plan.programId with
  | .error error => some (.returned (.error error) s)
  | .ok () =>
    match plan.order with
    | .dataThenMetas =>
      (bytesFn.withCapacity s B.enumSize).bind (PGraph.bindK fun data after =>
        ((writeDataFn data plan.dataSteps after).bind (PGraph.bindK fun _ current =>
            (buildMetasFn plan.metas current).map (Outcome.map fun metas => Except.ok
              ({ programId := plan.programId, metas, data } : IV)))).bind
          (PGraph.onUnwindFn doubleFn [fun current => bytesFn.drop current data]))
    | .metasThenData =>
      (buildMetasFn plan.metas s).bind (PGraph.bindK fun metas after =>
        ((buildDataFn plan.dataSteps after).map (Outcome.map fun data => Except.ok
            ({ programId := plan.programId, metas, data } : IV))).bind
          (PGraph.onUnwindFn doubleFn [fun current => metasFn.drop current metas]))

theorem build_graph (s : S) (plan : Token.InstructionAllocated.Plan) :
    PGraph (Token.InstructionAllocated.run B s plan) (buildFn s plan) := by
  unfold Token.InstructionAllocated.run buildFn
  rcases Token.Instruction.checkProgram plan.programs plan.programId with error | u
  · exact PGraph.eq_left _
  · dsimp only
    rcases plan.order with _ | _
    · exact PGraph.bind (bytes_graph.withCapacity s _) fun data after =>
        PGraph.protect double_graph
          (PGraph.DropsGraph.cons (fun current => bytes_graph.drop current data)
            PGraph.DropsGraph.nil)
          (PGraph.bind (writeData_graph data _ after) fun _ current =>
            PGraph.map _ (buildMetas_graph _ current))
    · exact PGraph.bind (buildMetas_graph _ s) fun metas after =>
        PGraph.protect double_graph
          (PGraph.DropsGraph.cons (fun current => metas_graph.drop current metas)
            PGraph.DropsGraph.nil)
          (PGraph.map _ (buildData_graph _ after))

/-! ## Index, invocation and cleanup -/

/-- The invocation instance of `Spl.Invocation` on the sample state: the
`RefCell` pre-check, then the scripted reply with the request appended to the `calls` log of the
sample. -/
def invokeOut (inv : Spl.Invocation) (state : S) (request : CpiRequest.Request AccountInfo.Value) :
    Outcome S (Except ProgramError.Value Unit) Nat Nat :=
  if Spl.precheck inv.world request then
    .returned (Spl.replyOf inv.ret) (state.1, { state.2 with calls := state.2.calls ++ [request] })
  else .returned (.error .accountBorrowFailed) state

/-- The resources and error heap of the sample; the invocation is `invokeOut`. -/
def types (inv : Spl.Invocation) : AnchorSplTransfer.Types where
  resources := Sample.resources
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorErrorOwned.Reference.natOps.focus Sample.errorsFocus
  invoke := Callback.ofFunction (invokeOut inv)

def natFn : OpsFn AnchorErrorOwned.Reference.State AnchorErrorOwned.Reference.StringId
    AnchorErrorOwned.Reference.BoxId Nat where
  copy := fun s a => (RefFn.fn.copy s a).map (AnchorErrorOwned.mapTerminalOutcome
    AnchorErrorOwned.Reference.Failure.code)
  format := fun s a => (RefFn.fn.format s a).map (AnchorErrorOwned.mapTerminalOutcome
    AnchorErrorOwned.Reference.Failure.code)
  newBox := fun s a => (RefFn.fn.newBox s a).map (AnchorErrorOwned.mapTerminalOutcome
    AnchorErrorOwned.Reference.Failure.code)
  dropString := fun s a => (RefFn.fn.dropString s a).map (AnchorErrorOwned.mapTerminalOutcome
    AnchorErrorOwned.Reference.Failure.code)
  freeBox := fun s a => (RefFn.fn.freeBox s a).map (AnchorErrorOwned.mapTerminalOutcome
    AnchorErrorOwned.Reference.Failure.code)

theorem natGraph : OpsGraph AnchorErrorOwned.Reference.natOps natFn where
  copy := fun s a => PGraph.exists_eq _ (RefFn.graph.copy s a)
  format := fun s a => PGraph.exists_eq _ (RefFn.graph.format s a)
  newBox := fun s a => PGraph.exists_eq _ (RefFn.graph.newBox s a)
  dropString := fun s a => PGraph.exists_eq _ (RefFn.graph.dropString s a)
  freeBox := fun s a => PGraph.exists_eq _ (RefFn.graph.freeBox s a)

def errFn : OpsFn S AnchorErrorOwned.Reference.StringId AnchorErrorOwned.Reference.BoxId Nat :=
  natFn.focus Sample.errorsFocus

theorem errGraph (inv : Spl.Invocation) : OpsGraph (types inv).errors errFn := natGraph.focus
  Sample.errorsFocus

abbrev OErr := AnchorErrorOwned.Error AnchorErrorOwned.Reference.BoxId
abbrev Out := Outcome S (Except OErr Unit) Nat Nat

def invokeFn (inv : Spl.Invocation) (args : Args Sample.resources) (instruction : IV) (before : S)
  : Option Out :=
  match request (types inv) before args instruction with
  | none => none
  | some call =>
    (some (invokeOut inv before call)).bind (PGraph.bindK fun result after =>
      match result with
      | .ok () => some (.returned (.ok ()) after)
      | .error failure =>
        ((OwnedFn.fromProgramFn errFn after failure).map AccountInfoRc.liftOutcome).map
          (Outcome.map Except.error))

theorem invoke_graph (inv : Spl.Invocation) (args : Args Sample.resources) (instruction : IV)
  (before : S) :
    PGraph (invokeAndConvert (types inv) args instruction before ()) (invokeFn inv args instruction
      before) := by
  unfold invokeAndConvert invokeFn
  rcases request (types inv) before args instruction with _ | call
  · exact PGraph.false
  · dsimp only
    apply PGraph.bind (PGraph.ofFunction (invokeOut inv) before call)
    intro result after
    rcases result with failure | u
    · exact PGraph.map _ (PGraph.exists_eq _ (OwnedFn.fromProgram_graph (errGraph inv) after
      failure))
    · exact PGraph.eq_left _

/-! ### Cleanup -/

def rcFn (s : S) (x : AccountInfoRc.Field × Borrow.Handle) : Outcome S Unit Empty Nat :=
  .returned () (s.1, { s.2 with rcEvents := s.2.rcEvents ++ [.drop x.1 x.2] })

def dropCallFn (info : AccountInfo.Value) (s : S) : Option (Outcome S Unit Empty Nat) :=
  (some (rcFn s (.lamports, info.lamports))).bind (PGraph.bindK fun _ after => some (rcFn after
    (.data, info.data)))

theorem rc_graph (s : S) (x : AccountInfoRc.Field × Borrow.Handle) :
    PGraph (Sample.rc.dropRc s x) (some (rcFn s x)) := by
  obtain ⟨field, cell⟩ := x
  exact PGraph.eq_right _

theorem dropCall_graph (info : AccountInfo.Value) (s : S) :
    PGraph (AccountInfoRc.dropCall Sample.rc s info) (dropCallFn info s) :=
  PGraph.bind (run := fun state (_ : Unit) => Sample.rc.dropRc state (.lamports, info.lamports))
    (rc_graph s _) fun _ after => rc_graph after _

def dropInfosFn : List AccountInfo.Value → S → Option (Outcome S Unit Empty Nat)
  | [], s => some (.returned () s)
  | info :: rest, s => (dropCallFn info s).bind (PGraph.bindK fun _ after => dropInfosFn rest after)

theorem dropInfos_graph : ∀ (infos : List AccountInfo.Value) (s : S),
    PGraph (Sample.dropInfos infos s ()) (dropInfosFn infos s)
  | [], s => PGraph.ofFunction _ s ()
  | info :: rest, s => PGraph.bind (dropCall_graph info s) fun _ after => dropInfos_graph rest after

def remainingDropFn (s : S) (resource : Nat) : Option (Outcome S Unit Empty Nat) :=
  (s.2.remaining[resource]?.join).bind fun infos =>
    (dropInfosFn infos s).bind (PGraph.bindK fun _ after =>
      ((refVec (U := Empty) (T := Nat)).drop (Sample.remainingFocus.get after) resource).map
        (Sample.remainingFocus.liftOutcome after))

theorem remainingDrop_graph (s : S) (resource : Nat) :
    PGraph (Sample.remainingDrop s resource) (remainingDropFn s resource) :=
  PGraph.exists_step (PGraph.ofOption _) fun infos =>
    PGraph.bind (dropInfos_graph infos s) fun _ after =>
      PGraph.focusLift Sample.remainingFocus (refVec_graph.drop _ resource)

def liftU {V : Type} : Outcome S V Empty Nat → Outcome S V Nat Nat := AccountInfoRc.liftOutcome

def dropsFn (args : Args Sample.resources) (instruction : IV) : List (S → Option (Outcome S Unit
  Nat Nat)) :=
  [fun s => metasFn.drop s instruction.metas, fun s => bytesFn.drop s instruction.data] ++
    (movedAccounts args).map (fun info s => (dropCallFn info s).map liftU) ++
    [fun s => (remainingDropFn s args.context.remaining).map liftU]

theorem drops_graph (args : Args Sample.resources) (instruction : IV) :
    PGraph.DropsGraph (invocationDrops args instruction) (dropsFn args instruction) := by
  refine PGraph.DropsGraph.cons (fun s => metas_graph.drop s _) ?_
  refine PGraph.DropsGraph.cons (fun s => bytes_graph.drop s _) ?_
  refine PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (dropCall_graph _ s)) ?_
  refine PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (dropCall_graph _ s)) ?_
  refine PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (dropCall_graph _ s)) ?_
  exact PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (remainingDrop_graph s _))
    PGraph.DropsGraph.nil

def contextDropsFn (args : Args Sample.resources) : List (S → Option (Outcome S Unit Nat Nat)) :=
  (movedAccounts args).map (fun info s => (dropCallFn info s).map liftU) ++
    [fun s => (remainingDropFn s args.context.remaining).map liftU]

theorem contextDrops_graph (args : Args Sample.resources) :
    PGraph.DropsGraph (contextDrops args) (contextDropsFn args) := by
  refine PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (dropCall_graph _ s)) ?_
  refine PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (dropCall_graph _ s)) ?_
  refine PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (dropCall_graph _ s)) ?_
  exact PGraph.DropsGraph.cons (fun s => PGraph.exists_eq _ (remainingDrop_graph s _))
    PGraph.DropsGraph.nil

def runFn (inv : Spl.Invocation) (before : S) (args : Args Sample.resources) : Option Out :=
  (buildFn before (plan args)).bind fun built =>
    match built with
    | .returned (.error _) _ => none
    | .returned (.ok instruction) after =>
      (invokeFn inv args instruction after).bind (PGraph.cleanupFn doubleFn (dropsFn args
        instruction))
    | .unwound reason after => PGraph.cleanupFn doubleFn (contextDropsFn args) (.unwound reason
      after)
    | .terminated reason => some (.terminated reason)

theorem run_graph (inv : Spl.Invocation) (before : S) (args : Args Sample.resources) :
    PGraph (AnchorSplTransfer.run (types inv) before args) (runFn inv before args) := by
  apply PGraph.exists_step (build_graph before (plan args))
  intro built
  rcases built with ⟨v, after⟩ | ⟨reason, after⟩ | reason
  · rcases v with e | instruction
    · exact PGraph.false
    · exact PGraph.scope double_graph (drops_graph args instruction) (invoke_graph inv args
      instruction after)
  · exact PGraph.cleanup double_graph _ _ (contextDrops_graph args) _
  · exact PGraph.eq_left _

/-! ## Checker -/

/-- `Rc` strong counts after the drop events of a trace. -/
def applyDrops (counts : List Nat) (events : List AccountInfoRc.Event) : List Nat :=
  events.foldl (fun cs e => match e with
    | .drop _ cell => cs.modify cell.cell (· - 1)
    | .clone _ cell => cs.modify cell.cell (· + 1)) counts

structure TState where
  calls : List ReqObs
  replies : List Reply
  counts : List Nat
  deriving DecidableEq

abbrev TObs := Outcome TState (Except (Option ErrorValue) Unit) Nat Nat

/-- Each CPI consumes the next scripted reply; the rest are left exactly. -/
def project (inv : Spl.Invocation) (replies : List Reply) (counts : List Nat) : Out → TObs
  | .returned v s => .returned (match v with
      | .ok () => .ok ()
      | .error e => .error (AnchorErrorOwned.current (types inv).errors s e))
      ⟨s.2.calls.map reqObs, replies.drop s.2.calls.length, applyDrops counts s.2.rcEvents⟩
  | .unwound r s => .unwound r ⟨s.2.calls.map reqObs, replies.drop s.2.calls.length, applyDrops
    counts s.2.rcEvents⟩
  | .terminated r => .terminated r

def asTState (j : Json) : Result TState := do
  pure ⟨← asCpiLog j, (← syscallsOf j).replies, ← asList (fun x => x.getNat?) (← field j
    "counts")⟩

def tstateJson (s : TState) : Json :=
  Json.mkObj [("calls", listJson reqJson s.calls), ("replies_left", listJson Spl.replyJson
    s.replies),
    ("counts", listJson toJson s.counts)]

def heap0 : AnchorErrorOwned.Reference.State := ⟨[], [], Owned.budget, []⟩

def checker₀ : Checker := ofModels ("anchor_spl::token::transfer") ([])
  ("Solanalib.Specs.AnchorSpl.token.transfer_run (sample resources; invocation: RefCell \
    pre-check, scripted reply) " ++
    "+ Solanalib.Specs.AnchorSpl.token.transfer_observation_run (same invocation)")
  ["Solanalib.Specs.AnchorSpl.token.transfer_run",
    "Solanalib.Specs.AnchorSpl.token.transfer_observation_run"]
  fun c => do
    let obsVerdict ← Spl.transferChecker.check c
    let a ← asTransferArgs c
    let script ← syscallsOf c.state
    let ret ← match script.replies with
      | [r] => pure r.ret
      | _ => throw "one scripted invocation reply expected"
    let (_, world) ← asWorld c.state
    let inv : Spl.Invocation := ⟨ret, world⟩
    let counts ← asList (fun x => x.getNat?) (← field c.state "counts")
    -- The remaining-account vector of the context is slot 0 of the remaining ledger.
    let args : Args Sample.resources :=
      ⟨⟨a.context.accounts, (show Sample.resources.RemainingResource from (0 : Nat)),
        a.context.programId,
        a.context.signerSeeds⟩, a.amount⟩
    let before : S := (([], []), ⟨heap0, [], [some []], []⟩)
    let recorded ← parseOutcome (asExcept (fun e => do pure (some (← asErrorValue e))) asUnit)
      asTState
      (fun _ => none) (fun _ => none) c.outcome
    let owned := decideProjected (O := Out) (Solanalib.Specs.AnchorSpl.token.transfer_run (types
      inv) before args) _
      (run_graph inv before args) (project inv script.replies counts) recorded
      (renderOpt (outcomeJson tstateJson (exceptJson (optionJson errorValueJson) (fun _ => .null))
        toJson toJson))
    return [owned, obsVerdict]

/-- The accounts are a frame of both transfer models (the invocation instance
writes none): the whole region and the held borrows are unchanged. -/
def checker : Checker := withFrame [("accounts unchanged", accountsUnchanged)] checker₀

end SolanalibTest.Conformance.Library.Families.Anchor.TransferOwned
