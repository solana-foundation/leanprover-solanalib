/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorSystem.Checker

/-! Model-side observation controls. These deliberately corrupt the error resources of the finite
model, provider-entry state or request; they are not Rust
executions and do not change the registered contract or native fixture. -/

open SolanalibTest.Conformance.Library Lean

namespace SolanalibTest.Conformance.Library.Controls.AnchorSystemObservation

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem
open SolanalibTest.Conformance.Library.Families.AnchorSystem

def fixtureBefore : State .boxedLegacy :=
  { Sample.before .boxedLegacy with
    strings := [some "owned provider error"]
    effects := [101, 1, 9, 8, 102, 2, 9, 8, 103, 3, 9, 8, 109, 9, 9, 8] }

def fixtureArgs : Args (Sample.index .boxedLegacy).resources .programAccount .transfer :=
  modelArgs .boxedLegacy .transfer false 37

def entryCounts : List (List Nat) := expectedCounts .boxedLegacy .transfer false

def seen (mode : String) (borsh : Bool) : Option (ProviderObservation .boxedLegacy) :=
  observedInvocation .boxedLegacy entryCounts mode borsh fixtureBefore fixtureArgs

def computed (mode : String) (borsh : Bool) : Option (Out .boxedLegacy) :=
  runFn .boxedLegacy (observedInvoke .boxedLegacy entryCounts mode borsh) fixtureBefore fixtureArgs

def render (mode : String) (borsh : Bool) (outcome : Out .boxedLegacy) : Json :=
  project .boxedLegacy entryCounts (seen mode borsh) outcome

example : ["ok", "error", "unwind", "terminal"].all (fun mode =>
    (computed mode (mode == "error")).isSome && (seen mode (mode == "error")).isSome) = true := by
  decide +kernel

abbrev Payload := AnchorErrorOperations.Payload (ProgramErrorOwned.Value Nat) Nat

def mapPayload (change : Payload → Payload) : Out .boxedLegacy → Out .boxedLegacy
  | .returned value state =>
    .returned value { state with boxes := state.boxes.map (Option.map change) }
  | other => other

def copyErrorString : Out .boxedLegacy → Out .boxedLegacy
  | .returned value state => .returned value {
      state with
      strings := state.strings ++ [some "owned provider error"]
      boxes := state.boxes.map (Option.map fun payload => match payload with
        | .program value => .program { value with error := .borshIoError 1 }
        | other => other) }
  | other => other

def errorText : Out .boxedLegacy → Json
  | .returned (.error error) state => errorJson .boxedLegacy state error
  | _ => .str "not a returned error"

def observedSameString (value : Json) : Except String Bool := do
  (← (← value.getObjVal? "state").getObjVal? "same_string").getBool?

/-- Equal text does not make the new String resource the original owner. -/
example : (computed "error" true).map errorText =
    (computed "error" true).map (fun outcome => errorText (copyErrorString outcome)) ∧
    (computed "error" true).map (render "error" true) ≠
      (computed "error" true).map (fun outcome => render "error" true (copyErrorString outcome)) :=
        by
  constructor
  · rfl
  · intro same
    have different : (some (.ok true) : Option (Except String Bool)) = some (.ok false) :=
      congrArg (Option.map observedSameString) same
    contradiction

def diagnosticIsNull (name : String) (value : Json) : Except String Bool := do
  let result ← value.getObjVal? "result"
  let error ← result.getObjVal? "err"
  pure (← error.getObjVal? name).isNull

def withOrigin : Payload → Payload :=
  AnchorErrorOperations.Payload.withOrigin (some (.source ⟨"mutated.rs", 7⟩))

def withCompared : Payload → Payload :=
  AnchorErrorOperations.Payload.withCompared (some (.pubkeys (fixtureKey 1) (fixtureKey 2)))

/-- Each optional diagnostic must be observed independently of the program error. -/
example :
    (computed "error" true).map (render "error" true) ≠
      (computed "error" true).map (fun outcome => render "error" true (mapPayload withOrigin
        outcome)) ∧
    (computed "error" true).map (render "error" true) ≠
      (computed "error" true).map (fun outcome => render "error" true (mapPayload withCompared
        outcome)) := by
  constructor
  · intro same
    have different : (some (.ok true) : Option (Except String Bool)) = some (.ok false) :=
      congrArg (Option.map (diagnosticIsNull "origin")) same
    contradiction
  · intro same
    have different : (some (.ok true) : Option (Except String Bool)) = some (.ok false) :=
      congrArg (Option.map (diagnosticIsNull "compared")) same
    contradiction

def compensatedProvider (event : AccountInfoRc.Event) (before : State .boxedLegacy)
    (current : CpiRequest.Request AccountInfo.Value) : InvokeOut .boxedLegacy :=
  match observedInvoke .boxedLegacy entryCounts "ok" false before current with
  | .returned value state => .returned value { state with rcEvents := state.rcEvents ++ [event] }
  | other => other

def rcMutant (prior later : AccountInfoRc.Event) : Option (Out .boxedLegacy) :=
  runFn .boxedLegacy (compensatedProvider later) { fixtureBefore with rcEvents := [prior] }
    fixtureArgs

def rcRender (prior : AccountInfoRc.Event) (outcome : Out .boxedLegacy) : Json :=
  project .boxedLegacy entryCounts
    (observedInvocation .boxedLegacy entryCounts "ok" false
      { fixtureBefore with rcEvents := [prior] } fixtureArgs) outcome

def finalCounts : Out .boxedLegacy → Option (List (List Nat))
  | .returned _ state | .unwound _ state => some (countDrops entryCounts state.rcEvents)
  | .terminated _ => none

def firstCallCount (value : Json) : Except String Nat := do
  let state ← value.getObjVal? "state"
  let call ← (← state.getObjVal? "calls").getArrVal? 0
  let pair ← (← call.getObjVal? "counts").getArrVal? 0
  (← pair.getArrVal? 0).getNat?

def RcControl (prior later : AccountInfoRc.Event) : Prop :=
  (rcMutant prior later).isSome = true ∧
  (rcMutant prior later).bind finalCounts = (computed "ok" false).bind finalCounts ∧
  (rcMutant prior later).map (rcRender prior) ≠ (computed "ok" false).map (render "ok" false)

/-- A pre-call clone/drop is balanced inside the provider. Final counts stay
equal, so only the actual call-time observation distinguishes these runs. -/
example : RcControl (.clone .lamports ⟨2⟩) (.drop .lamports ⟨2⟩) ∧
    RcControl (.drop .lamports ⟨2⟩) (.clone .lamports ⟨2⟩) := by
  constructor
  · refine ⟨by decide +kernel, by decide +kernel, ?_⟩
    intro same
    have different :
        (rcMutant (.clone .lamports ⟨2⟩) (.drop .lamports ⟨2⟩)).map
          (fun outcome => firstCallCount (rcRender (.clone .lamports ⟨2⟩) outcome)) ≠
        (computed "ok" false).map (fun outcome => firstCallCount (render "ok" false outcome)) := by
      decide +kernel
    exact different (congrArg (Option.map firstCallCount) same)
  · refine ⟨by decide +kernel, by decide +kernel, ?_⟩
    intro same
    have different :
        (rcMutant (.drop .lamports ⟨2⟩) (.clone .lamports ⟨2⟩)).map
          (fun outcome => firstCallCount (rcRender (.drop .lamports ⟨2⟩) outcome)) ≠
        (computed "ok" false).map (fun outcome => firstCallCount (render "ok" false outcome)) := by
      decide +kernel
    exact different (congrArg (Option.map firstCallCount) same)

def builtState : State .boxedLegacy := Sample.afterBuild fixtureBefore fixtureArgs

def terminalAt (state : State .boxedLegacy) : Option (ProviderObservation .boxedLegacy) :=
  observeInvocation .boxedLegacy entryCounts "terminal" false fixtureArgs
    (Sample.builtValue fixtureBefore) state

def terminalRender (observed : ProviderObservation .boxedLegacy) : Json :=
  project .boxedLegacy entryCounts (some observed) (.terminated 92)

def changedInstruction : State .boxedLegacy :=
  { builtState with
    construction := { builtState.construction with
      bytes := builtState.construction.bytes.modify 0
        (Option.map fun bytes => bytes.modify 0 (· + 1)) } }

def changedTerminalAccounts : Option (ProviderObservation .boxedLegacy) :=
  (request builtState fixtureArgs (Sample.builtValue fixtureBefore)).map fun received =>
    observeProvider .boxedLegacy entryCounts "terminal" false builtState { received with accounts
      := [] }

def terminalBytes (value : Json) : Except String String := do
  let request ← value.getObjVal? "request"
  let instruction ← request.getObjVal? "instruction"
  (← instruction.getObjVal? "data").getStr?

def terminalCount (value : Json) : Except String Nat := do
  let request ← value.getObjVal? "request"
  let pair ← (← request.getObjVal? "counts").getArrVal? 0
  (← pair.getArrVal? 0).getNat?

def terminalAccountCount (value : Json) : Except String Nat := do
  let request ← value.getObjVal? "request"
  let accounts ← (← request.getObjVal? "accounts").getArr?
  pure accounts.size

def TerminalControl (mutant : Option (ProviderObservation .boxedLegacy)) : Prop :=
  mutant.isSome = true ∧ mutant.map terminalRender ≠ (terminalAt builtState).map terminalRender

/-- Entry args stay fixed. Mutate the current built bytes, pre-call owners, or
the request received by the terminal provider; no expected request is rebuilt. -/
example : TerminalControl (terminalAt changedInstruction) ∧
    TerminalControl (terminalAt { builtState with rcEvents := [.clone .lamports ⟨2⟩] }) ∧
    TerminalControl changedTerminalAccounts := by
  refine ⟨⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩, ⟨by decide +kernel, ?_⟩⟩
  · intro same
    have different :
        (terminalAt changedInstruction).map (fun point => terminalBytes (terminalRender point)) ≠
        (terminalAt builtState).map (fun point => terminalBytes (terminalRender point)) := by
      decide +kernel
    exact different (congrArg (Option.map terminalBytes) same)
  · intro same
    have different :
        (terminalAt { builtState with rcEvents := [.clone .lamports ⟨2⟩] }).map
          (fun point => terminalCount (terminalRender point)) ≠
        (terminalAt builtState).map (fun point => terminalCount (terminalRender point)) := by
      decide +kernel
    exact different (congrArg (Option.map terminalCount) same)
  · intro same
    have different : (some (.ok 0) : Option (Except String Nat)) = some (.ok 2) :=
      congrArg (Option.map terminalAccountCount) same
    contradiction

example : ((project .boxedLegacy entryCounts (seen "unwind" false) (.unwound 191
  fixtureBefore)).getObjVal?
    "reason").bind Json.getNat? = .ok 191 := by
  decide +kernel

/-- An unknown terminal reason keeps its code and acquires no known request. -/
example : ((project .boxedLegacy entryCounts (seen "terminal" false) (.terminated 193)).getObjVal?
      "reason").bind Json.getNat? = .ok 193 ∧
    (project .boxedLegacy entryCounts (seen "terminal" false) (.terminated 193)).getObjVal?
      "request" = .ok Json.null := by
  constructor
  · decide +kernel
  · rfl

example : terminalDetail (seen "ok" false) 92 = Json.null := by
  rfl

end SolanalibTest.Conformance.Library.Controls.AnchorSystemObservation
