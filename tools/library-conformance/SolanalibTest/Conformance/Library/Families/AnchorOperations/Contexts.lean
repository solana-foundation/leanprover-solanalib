/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorOperations.Common
import Solanalib.Specs.AnchorLang.context_operations
import Solanalib.Specs.Core.OwnedVector
import Solanalib.Specs.Core.OwnedFocus

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorContextOperations
open SolanalibTest.Conformance.Library.Families.Anchor

theorem returnsGraph {S A V U T : Type} (run : S → A → V × S) (before : S) (args : A) :
    PGraph (returnsOf (Unwind := U) (Terminal := T) run before args)
      (some (.returned (run before args).1 (run before args).2)) := by
  intro outcome
  simpa only [Option.some.injEq] using returnsOf_iff run before args outcome

abbrev contextTypes : ContextTypes := ⟨Unit, Nat, Nat, Nat, List (String × UInt8)⟩
def contextArgs : contextTypes.Value := ⟨11, 12, 13, [("first", 3), ("second", 255)]⟩

def contextResult (value : contextTypes.Value) : Json := Json.mkObj [
  ("program_identity", toJson (value.programId == contextArgs.programId)),
  ("accounts_identity", toJson (value.accounts == contextArgs.accounts)),
  ("remaining_identity", toJson (value.remainingAccounts == contextArgs.remainingAccounts)),
  ("remaining_length", toJson (if value.remainingAccounts = 13 then 1 else 0 : Nat)),
  ("accounts_value", toJson (if value.accounts = 12 then 23 else 0 : Nat)),
  ("bumps", listJson (fun (name, value) => Json.arr #[toJson name, toJson value.toNat])
    value.bumps)]

def contextChecker (function : String) : Checker := ofModel function []
    "Solanalib.Specs.AnchorLang.context.Context.new_run" fun case => do
  unless case.state.compress = "null" && case.args.compress = "null" do
    throw "Context fixture has its fixed source references and bump payload"
  let relation := context.Context.new_run contextTypes () contextArgs
  let observed ← parseOutcome pure pure (noReason (α := Empty)) (noReason (α := Empty)) case.outcome
  let render := fun (outcome : Outcome Unit contextTypes.Value Empty Empty) => match outcome with
    | .returned value () => (returnedJson (contextResult value)
        (Json.mkObj [("fresh_live", toJson (0 : Nat)), ("syscalls", emptySyscalls)])).compress
    | .unwound impossible _ | .terminated impossible => nomatch impossible
  return decideProjected relation _ (returnsGraph (fun state args => (args, state)) () contextArgs)
    render (observed.map fun
      | .returned value state => (returnedJson value state).compress
      | .unwound impossible _ | .terminated impossible => nomatch impossible) (optionJson Json.str)

/-- The old program retains the key reference and complete AccountInfo value,
including both Rc identities. New programs are copied Pubkeys. -/
structure OldProgram where
  keyReference : Nat
  account : AccountInfo.Value
  deriving DecidableEq

abbrev Program := Sum OldProgram Solanalib.Runtime.Pubkey
def info : AccountInfo.Value := ⟨pubkey 3, ⟨0⟩, ⟨1⟩, pubkey 4, 0, true, true, false, ⟨2⟩⟩
def program (version : Version) : Program :=
  match version.program with
  | some _ => .inl ⟨7, info⟩
  | none => .inr info.key

structure State where
  vectors : Owned.VectorState AccountInfo.Value
  dataCount : Nat
  lamportsCount : Nat
  freed : List Nat := []

def vecFocus : Owned.Focus State (Owned.VectorState AccountInfo.Value) where
  get := State.vectors
  set := fun state vectors => { state with vectors }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def dropFn (before : State) (owner : Nat) : Option (Outcome State Unit Empty Empty) := do
  let values ← Owned.VectorState.current before.vectors owner
  return .returned () {
    before with
    vectors := before.vectors.set owner none
    dataCount := before.dataCount - values.length
    lamportsCount := before.lamportsCount - values.length
    freed := if values.isEmpty then before.freed else before.freed ++ [owner] }

def vectors : Owned.VectorOps State AccountInfo.Value Nat Empty Empty :=
  { Owned.vectorReference.focus vecFocus with
    drop := fun state owner out => dropFn state owner = some out }

abbrev cpiTypes : CpiTypes := ⟨State, Nat, Program, Nat, Nat⟩
abbrev newTypes : NewTypes := ⟨cpiTypes, AccountInfo.Value, vectors, 0⟩
abbrev remainingTypes : RemainingTypes := ⟨cpiTypes, AccountInfo.Value, Empty, vectors⟩

def original (version : Version) : cpiTypes.Value := ⟨29, program version, 0, 1⟩

def cpiRelation (operation : Nat) (version : Version) : State →
    Outcome State cpiTypes.Value Empty Empty → Prop :=
  match operation with
  | 0 => fun before => context.CpiContext.AccountInfoProgram.new_run
    newTypes before (program version, 29)
  | 1 => fun before =>
    context.CpiContext.AccountInfoProgram.new_with_signer_run newTypes
    before ⟨program version, 29, 1⟩
  | 2 => fun before =>
    context.CpiContext.AccountInfoProgram.with_signer_run cpiTypes
    before (original version, 2)
  | _ => fun before => context.CpiContext.with_remaining_accounts_run
    remainingTypes before (original version, 1)

def cpiFn (operation : Nat) (version : Version) (before : State) : Option (Outcome State
  cpiTypes.Value Empty Empty) :=
  match operation with
  | 0 => let result := newContext newTypes before (program version, 29)
      some (.returned result.1 result.2)
  | 1 => let result := newWithSigner newTypes before ⟨program version, 29, 1⟩
      some (.returned result.1 result.2)
  | 2 => some (.returned { original version with signerSeeds := 2 } before)
  | _ => (dropFn before 0).map (Outcome.map (fun _ => { original version with remainingAccounts :=
    1 }))

theorem cpiGraph (operation : Nat) (version : Version) (before : State) :
    PGraph (cpiRelation operation version before) (cpiFn operation version before) := by
  match operation with
  | 0 => exact returnsGraph (newContext newTypes) before (program version, 29)
  | 1 => exact returnsGraph (newWithSigner newTypes) before ⟨program version, 29, 1⟩
  | 2 =>
    exact returnsGraph (fun state args => ({ args.1 with signerSeeds := args.2 }, state))
      before (original version, 2)
  | .succ (.succ (.succ _)) =>
    exact PGraph.map (run := vectors.drop) _ (PGraph.ofOption (dropFn
    before 0))

def cpiProjection (operation : Nat) (version : Version) : Outcome State cpiTypes.Value Empty Empty
  → String
  | .returned value state =>
    let remaining := (Owned.VectorState.current state.vectors value.remainingAccounts).getD []
    let expectedSeed := if operation = 0 then 0 else if operation = 2 then 2 else 1
    let result := Json.mkObj [("accounts_value", toJson value.accounts),
      ("program_identity", toJson (decide (value.program = program version))),
      ("seed_identity", toJson (value.signerSeeds == expectedSeed)),
      ("seed_count", toJson (if value.signerSeeds = 0 then 0 else 1 : Nat)),
      ("remaining_length", toJson remaining.length), ("remaining_capacity", toJson
        remaining.length),
      ("remaining_identity", toJson (operation != 3 || value.remainingAccounts == 1))]
    (returnedJson result (Json.mkObj [("data_count", toJson state.dataCount),
      ("lamports_count", toJson state.lamportsCount), ("fresh_live", toJson (0 : Nat)),
      ("old_remaining_freed", toJson (state.freed.contains 0)), ("syscalls",
        emptySyscalls)])).compress
  | .unwound impossible _ | .terminated impossible => nomatch impossible

def cpiModel : Nat → String
  | 0 => "Solanalib.Specs.AnchorLang.context.CpiContext.AccountInfoProgram.new_run"
  | 1 => "Solanalib.Specs.AnchorLang.context.CpiContext.AccountInfoProgram.new_with_signer_\
    run"
  | 2 => "Solanalib.Specs.AnchorLang.context.CpiContext.AccountInfoProgram.with_signer_run"
  | _ => "Solanalib.Specs.AnchorLang.context.CpiContext.with_remaining_accounts_run"

def cpiBefore (operation : Nat) (case : Case) : Result State := do
  unless (← natField case.args "operation") = operation && operation < 4 do
    throw "wrong CPI context fixture operation"
  let initialVectors := if operation = 3 then [some [info, info], some [info]]
    else if operation = 2 then [some []] else []
  let before : State := ⟨initialVectors, ← natField case.state "data_count", ← natField case.state
    "lamports_count", []⟩
  let expectedCount := if operation = 3 then 5 else 2
  unless before.dataCount = expectedCount && before.lamportsCount = expectedCount do
    throw "fixture alias counts do not match current program/remaining owners"
  return before

def emptyReadyDec (selected : NewTypes) [DecidableEq selected.AccountInfo]
    (before : selected.State) : Decidable (EmptyReady selected before) :=
  decidable_of_iff
    (selected.remaining.current (selected.remaining.empty before).2
        (selected.remaining.empty before).1 = some [] ∧
      selected.remaining.current before (selected.remaining.empty before).1 = none)
    ⟨fun facts => ⟨facts.1, facts.2⟩, fun ready => ⟨ready.current, ready.fresh⟩⟩

/-- A non-source primitive that reuses a live Vec owner is rejected by exactly
the generic readiness decider used on the actual constructor calls. -/
abbrev reusedEmpty : NewTypes :=
  { newTypes with remaining := { vectors with empty := fun state => (0, state) } }

theorem empty_ready_rejects_reused :
    @decide (EmptyReady reusedEmpty ⟨[some []], 2, 2, []⟩)
      (emptyReadyDec reusedEmpty ⟨[some []], 2, 2, []⟩) = false := rfl

abbrev nonemptyNew : NewTypes :=
  { newTypes with remaining := { vectors with
      empty := fun state => (state.vectors.length,
        { state with vectors := state.vectors ++ [some [info]] }) } }

/-- Freshness alone does not admit nonempty contents as Vec::new. -/
theorem empty_ready_rejects_nonempty :
    @decide (EmptyReady nonemptyNew ⟨[], 2, 2, []⟩)
      (emptyReadyDec nonemptyNew ⟨[], 2, 2, []⟩) = false := rfl

def newRequires (version : Version) (case : Case) : Result Bool := do
  let before ← cpiBefore 0 case
  return @decide
    ((context.CpiContext.AccountInfoProgram.new_contract.contract
    newTypes).requires
    before (program version, 29)) (emptyReadyDec newTypes before)

def signerRequires (version : Version) (case : Case) : Result Bool := do
  let before ← cpiBefore 1 case
  return @decide
    ((context.CpiContext.AccountInfoProgram.new_with_signer_contract.contract newTypes).requires
    before ⟨program version, 29, 1⟩) (emptyReadyDec newTypes before)

def cpiChecker (version : Version) (operation : Nat) (function : String) : Checker :=
  let preconditions := match operation with
    | 0 => [(cpiModel operation, newRequires version)]
    | 1 => [(cpiModel operation, signerRequires version)]
    | _ => []
  withRequires preconditions <| ofModel function [] (cpiModel operation) fun case => do
    let before ← cpiBefore operation case
    let observed ← parseOutcome pure pure (noReason (α := Empty)) (noReason (α := Empty))
      case.outcome
    return decideProjected (cpiRelation operation version before) _ (cpiGraph operation version
      before)
      (cpiProjection operation version) (observed.map fun
        | .returned value state => (returnedJson value state).compress
        | .unwound impossible _ | .terminated impossible => nomatch impossible) (optionJson
          Json.str)

end SolanalibTest.Conformance.Library.Families.AnchorOperations.Contexts
