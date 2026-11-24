/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.ReferenceReady
import all Init.Data.Array.Basic
import all Init.Data.String.Defs

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Sample

open Execution

/-- Distinct cells and owner locations expose source order, while repeated
copies of a value retain their aliases in both the request and Rc cleanup. -/
def info (number : Nat) : AccountInfo.Value :=
  { AccountInfo.sampleInfo with
    key := .ofNat number
    lamports := ⟨2 * number⟩
    data := ⟨2 * number + 1⟩
    isWritable := true
    ownerRef := ⟨number⟩ }

/-- Program ownership follows the actual CpiContext release. -/
def program : (profile : Profile) → profile.Program
  | .legacyInline | .legacyBoxed => info 50
  | .modern => .ofNat 50

def accounts : (operation : Operation) → operation.Accounts
  | .associated _ _ => ⟨info 1, info 2, info 3, info 4, info 5, info 6⟩
  | .memo => ()
  | .metadata => ⟨info 1, info 2, info 3, info 4, info 5, info 6, info 7⟩
  | .deactivate => ⟨info 1, info 2, info 3⟩
  | .withdraw => ⟨info 1, info 2, info 3, info 4, info 5⟩

/-- Every optional metadata field is populated, and UTF-8 is not ASCII-only. -/
def metadata : MetadataArgs Reference.resources where
  data := ⟨0, 1, 2, 375, some 0, some ⟨true, .ofNat 66⟩,
    some ⟨.multiple, 8, 13⟩⟩
  isMutable := true
  updateAuthoritySigner := false
  details := some (.v2 ⟨[1, 2, 3, 4, 5, 6, 7, 8], rfl⟩)

def extra : (operation : Operation) → operation.Extra Reference.resources
  | .associated _ _ | .deactivate => ()
  | .memo => [0, 255, 65, 0]
  | .metadata => metadata
  | .withdraw => ⟨42, some (info 6)⟩

def args (operation : Operation) : Args Reference.resources operation where
  context := {
    accounts := accounts operation
    program := program operation.profile
    remainingAccounts := 0
    signerSeeds := [[], [[1, 2], []], [[255]]] }
  extra := extra operation

/-- Owned inputs include duplicates, nonempty metadata strings and a separate
legacy dependency-error String that must survive returned-error cleanup. -/
def initial (reply : Reference.Reply := .ok) : Reference.State where
  infos := [some [info 40, info 40, info 41]]
  strings := [some "Méta", some "SPL", some "https://example.invalid/metadata", some "owne\
    d Borsh error"]
  creators := [some [⟨.ofNat 70, true, 60⟩, ⟨.ofNat 71, false, 40⟩]]
  reply := reply

/-- The exact finite executable graph computes all allocation, call and
cleanup states; it does not execute any SDK invocation implementation. -/
def computed (operation : Operation) (reply : Reference.Reply := .ok) :=
  runFn Reference.functions operation (initial reply) (args operation)

def invocationCount (state : Reference.State) : Nat :=
  state.events.countP fun event => match event with | .invoke _ => true | _ => false

def successful (operation : Operation) : Bool :=
  match computed operation with
  | some (.returned (.ok ()) after) => invocationCount after == 1 && after.effect == 1
  | _ => false

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
theorem metadata_success : successful .metadata = true := by rfl

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
theorem metadata_ready : Reference.checked .metadata (initial .ok) (args .metadata) = true := by rfl

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
theorem succeeds (operation : Operation) : successful operation = true := by
  cases operation with
  | associated profile kind => cases profile <;> cases kind <;> rfl
  | memo | deactivate | withdraw => rfl
  | metadata => exact metadata_success

set_option smartUnfolding false in
set_option maxRecDepth 8192 in
theorem inputs_ready (operation : Operation) :
    Reference.checked operation (initial .ok) (args operation) = true := by
  cases operation with
  | associated profile kind => cases profile <;> cases kind <;> rfl
  | memo | deactivate | withdraw => rfl
  | metadata => exact metadata_ready

/-- This witness satisfies the same local admission gates as every caller. -/
theorem ready (operation : Operation) : Ready Reference.types operation (initial .ok) (args
  operation) :=
  Reference.ready_of_checked operation (initial .ok) (args operation) (inputs_ready operation)

theorem has_result (operation : Operation) : (computed operation).isSome = true := by
  have success := succeeds operation
  unfold successful at success
  cases value : computed operation with
  | none => simp only [value, Bool.false_eq_true] at success
  | some final => rfl

def outcome (operation : Operation) := (computed operation).get (has_result operation)

theorem computed_eq (operation : Operation) : computed operation = some (outcome operation) :=
  (Option.some_get (has_result operation)).symm

/-- Every family has an actual successful invocation and completed cleanup,
with its own nonempty argument/resource profile. -/
theorem execution (operation : Operation) :
    FamilyHasExecution (family operation) (reference operation) Reference.types := by
  refine ⟨initial .ok, args operation, outcome operation, ready operation, ?_⟩
  exact (run_graph Reference.functions Reference.graphs operation (initial .ok) (args operation)
    (outcome operation)).mpr (computed_eq operation)

theorem satisfiable (operation : Operation) : FamilySatisfiable (family operation) Reference.types
  :=
  (execution operation).satisfiable

end Solanalib.Specs.Core.AnchorSplSupport.Sample
