/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.ReferenceReady

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Sample

open Execution

def info (number : Nat) : AccountInfo.Value :=
  { AccountInfo.sampleInfo with
    key := .ofNat number
    lamports := ⟨2 * number⟩
    data := ⟨2 * number + 1⟩
    ownerRef := ⟨number⟩ }

def program (release : Release) : release.Program :=
  match release with
  | .v027 | .v029 | .v0321 => { info 50 with key := Token.token2022ProgramId }
  | .v102 | .v112 => Token.token2022ProgramId

def parameters : (operation : Operation) → Parameters operation
  | .transfer | .burn | .mintTo => (42 : UInt64)
  | .transferChecked | .burnChecked | .mintToChecked => ⟨42, 9⟩
  | .setAuthority => ⟨3, some (.ofNat 80)⟩
  | .initializeMint2 => ⟨9, .ofNat 81, some (.ofNat 82)⟩
  | .getAccountDataSize => [7, 12]
  | .mintCloseAuthority => some (.ofNat 83)
  | .permanentDelegate => .ofNat 84
  | .metadataPointer | .groupPointer | .groupMemberPointer | .transferHook =>
      ⟨some (.ofNat 85), some (.ofNat 86)⟩
  | .closeAccount | .initializeAccount3 | .initializeImmutableOwner | .nonTransferableMint => ()

def args (binding : Binding) : Args binding Nat Nat where
  context := {
    accounts := fun index =>
      if binding.operation.extension && index.val == 0 then { info (index.val + 1) with key :=
        Token.token2022ProgramId }
      else info (index.val + 1)
    program := program binding.release
    remainingAccounts := 0
    signerSeeds := 0 }
  parameters := parameters binding.operation

def script (binding : Binding) : Reference.Script binding.release where
  returned := .present Token.token2022ProgramId (Solanalib.Runtime.u64le 165)

def types (binding : Binding) : Types binding := Reference.types binding (script binding)

/-- Every source owner contributes one count for each Rc field. Duplicate
identities would add multiplicity, rather than being deduplicated as owners. -/
def addOwner (counts : List ((AccountInfoRc.Field × Borrow.Handle) × Nat))
    (field : AccountInfoRc.Field × Borrow.Handle) : List ((AccountInfoRc.Field × Borrow.Handle) ×
      Nat) :=
  match counts.lookup field with
  | none => counts ++ [(field, 1)]
  | some count => counts.map fun (key, value) => (key, if key = field then count + 1 else value)

def initialFor (binding : Binding) (input : Args binding Nat Nat)
    (remaining : List AccountInfo.Value) : Reference.State binding.release where
  remaining := [some remaining]
  seeds := [some [[], [[1, 2], []]]]
  strings := [some "owned dependency error"]
  counts := ((allAccounts input ++ remaining ++ binding.release.programOwners
    input.context.program).flatMap
    fun account => [(.lamports, account.lamports), (.data, account.data)]).foldl addOwner []

def initial (binding : Binding) : Reference.State binding.release := initialFor binding (args
  binding) [info 40]

def computed (binding : Binding) : Option (Exit (types binding)) :=
  runFn (Reference.functions binding (script binding)) (initial binding) (args binding)

def expectedReturn (binding : Binding) : Return :=
  if binding.operation = .getAccountDataSize then .size 165 else .unit

/-- The concrete sample succeeds and has exactly one invocation. This also
checks every distinct typed argument/account profile, rather than choosing an
unreachable precondition or an early constructor error for the witnesses. -/
def successful (binding : Binding) : Bool :=
  match computed binding with
  | some (.returned (.ok value) after) => value == expectedReturn binding && after.calls.length == 1
  | _ => false

set_option maxRecDepth 8192 in
theorem succeeds (binding : Binding) : successful binding = true := by
  cases binding <;> decide

set_option maxRecDepth 8192 in
theorem requests_ready (binding : Binding) :
    Reference.requestsReadable binding (script binding) (initial binding) (args binding) = true :=
      by
  cases binding <;> decide

theorem ready (binding : Binding) : Ready (types binding) (initial binding) (args binding) :=
  Reference.ready_of_requests binding (script binding) (initial binding) (args binding)
    (requests_ready binding)

theorem has_result (binding : Binding) : (computed binding).isSome = true := by
  have success := succeeds binding
  unfold successful at success
  cases value : computed binding with
  | none => simp only [value, Bool.false_eq_true] at success
  | some final => rfl

def outcome (binding : Binding) : Exit (types binding) := (computed binding).get (has_result
  binding)

theorem computed_eq (binding : Binding) : computed binding = some (outcome binding) :=
  (Option.some_get (has_result binding)).symm

theorem execution (binding : Binding) :
    FamilyHasExecution (family binding) (reference binding) (types binding) := by
  refine ⟨initial binding, args binding, outcome binding, ready binding, ?_⟩
  exact (Reference.run_iff binding (script binding) (initial binding) (args binding) (outcome
    binding)).mpr
    (computed_eq binding)

theorem satisfiable (binding : Binding) : FamilySatisfiable (family binding) (types binding) :=
  (execution binding).satisfiable

end Solanalib.Specs.Core.AnchorSplTokenOperations.Sample
