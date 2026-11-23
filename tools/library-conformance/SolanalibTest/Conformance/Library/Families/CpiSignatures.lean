/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Cpi
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.OpaqueCpiOwnedReference
import Solanalib.Specs.SolanaInvoke.Cpi

/-!
Whole-signature mock conformance, using actual SDK value types. The native
drivers never call an invocation implementation. Records check argument order,
public keys, repeated account aliases, nested seeds, return codecs, type/layout
controls and scripted terminal exits. They are not SDK preflight execution or
runtime memory-transport evidence.

The declared callee is identity. Runtime accounts in these fixtures are the
executable program and caller, so no account data copyback is needed. Live
borrow identities are represented explicitly. Released temporary lease IDs
are ghost-only: the post-observation projects their unique preflight result,
whose physical counters are unchanged by OpaqueCpiBorrowFacts.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.CpiSignatures

open Solanalib.Runtime Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

deriving instance DecidableEq for TxState
deriving instance DecidableEq for InvState
deriving instance DecidableEq for Sdk.State

def runtime : OpaqueCpi.Index :=
  Reference.index mainnet Witness.primitives Witness.context (fun state _ => .ok state)

abbrev Out := Outcome Sdk.State (Except ProgramError.Value Unit) Empty InstrError
abbrev Relation := Sdk.State → Sdk.Args → Out → Prop

def normalized (signed : Bool) (args : Sdk.Args) : Sdk.Args :=
  if signed then args else args.toUnsignedArgs.signed

def key (json : Json) : Result Pubkey := do
  let bytes ← asBytes json
  unless bytes.length = 32 do throw "public key has the wrong width"
  return .ofBytes bytes

def list {α : Type} (parse : Json → Result α) (json : Json) : Result (List α) := do
  (← json.getArr?).toList.mapM parse

def argsOf (json : Json) : Result Sdk.Args := do
  let instruction ← field json "instruction"
  let metas ← list (fun item => do
    return (⟨← key (← field item "pubkey"),
      if ← (← field item "is_signer").getBool? then 1 else 0,
      if ← (← field item "is_writable").getBool? then 1 else 0⟩ : CpiMeta))
      (← field instruction "accounts")
  let infos ← list (fun info => do
    let address ← key (← field info "key")
    let lamports ← (← field info "lamports_cell").getNat?
    let data ← (← field info "data_cell").getNat?
    unless lamports < 2 ∧ data < 2 do throw "unexpected fixture alias"
    unless (← (← field info "executable").getBool?) &&
        !(← (← field info "is_signer").getBool?) &&
        !(← (← field info "is_writable").getBool?) do
      throw "unexpected executable fixture metadata"
    return (⟨⟨address, 0, 0, 0, 0, 0, true, 0, .zero, []⟩,
      ⟨2 * lamports⟩, ⟨2 * data + 1⟩⟩ : Sdk.Account)) (← field json "accounts")
  return ⟨⟨⟨← key (← field instruction "program_id"), metas,
    ← asBytes (← field instruction "data")⟩, infos, true⟩,
    ← list (list asBytes) (← field json "signers")⟩

def beforeOf (json : Json) : Result Sdk.State := do
  unless (← (← field json "scope").getStr?) = "whole-signature-mock" do
    throw "CPI record does not declare the mock boundary"
  let borrowed ← (← field json "borrow").getNat?
  let free := [true, true, true, true]
  let first := match borrowed with
    | 1 => [false, true, true, true]
    | 2 => [false, false, true, true]
    | 3 => [true, true, false, false]
    | _ => free
  unless (← field json "borrow_observations") == toJson [first, free, first] do
    throw "observed RefCell permissions differ from the lease fixture"
  let slots ← match borrowed with
    | 0 => pure []
    | 1 => pure [some ⟨⟨0⟩, Borrow.Mode.shared, 0, ()⟩]
    | 2 => pure [some ⟨⟨0⟩, Borrow.Mode.exclusive, 0, ()⟩]
    | 3 => pure [some ⟨⟨1⟩, Borrow.Mode.exclusive, 0, ()⟩]
    | _ => throw "unknown fixture borrow"
  return ⟨Witness.before, ⟨List.replicate 4 ⟨(), Borrow.Policy.refCell 64⟩, slots⟩⟩

def valueOf (json : Json) : Result (Except ProgramError.Value Unit) :=
  asExcept (fun json => do
    unless (← json.getStr?) = "AccountBorrowFailed" do throw "unexpected mock ProgramError"
    return .accountBorrowFailed) asUnit json

def terminalOf (json : Json) : Result InstrError := do
  match ← json.getStr? with
  | "MaxSeedLengthExceeded" => return .MaxSeedLengthExceeded
  | "ComputationalBudgetExceeded" => return .ComputationalBudgetExceeded
  | "MissingAccount" => return .MissingAccount
  | "PrivilegeEscalation" => return .PrivilegeEscalation
  | _ => throw "unknown mock runtime termination"

def expectedLayouts (legacy modern owned : Bool) : Json := Json.mkObj [
  ("constructor_control", if owned then Json.mkObj [
    ("kind", "owned-stable-constructor"), ("same_value", toJson true),
    ("fresh_accounts", toJson true), ("fresh_data", toJson true),
    ("input_retained_after_drop", toJson true)] else Json.null),
  ("vec_words", toJson (["capacity", "pointer", "length"] : List String)),
  ("instruction", toJson ([80, 8, 0, 24, 48] : List Nat)),
  ("account_info", toJson (if legacy then ([48, 8, 8, 16, 24, 32, 0, 40, 41, 42] : List Nat)
    else [48, 8, 0, 8, 16, 24, 32, 40, 41, 42])),
  ("program_error", toJson (if modern then ([8, 4, 8, 4] : List Nat) else [24, 8, 24, 8]))]

def check (signed legacy modern : Bool) (profile : String) (relation : Relation)
    (equivalent : ∀ before args outcome, relation before args outcome ↔
      Sdk.run runtime before (normalized signed args) outcome) (record : Case) : Result Verdict :=
        do
  if (← (← field record.outcome "exit").getStr?) = "unwound" then
    return ⟨false, Json.mkObj [("scope", "whole-signature-mock"),
      ("reason", "the registered family has Empty unwind reasons")]⟩
  let before ← beforeOf record.state
  let args ← argsOf record.args
  let actual := normalized signed args
  unless signed || args.signers.isEmpty do throw "unsigned mock forwarded signer seeds"
  let profileMatches := (← (← field record.state "profile").getStr?) == profile
  let owned := profile = "solana-program-1.18.26" || profile = "solana-program-2.2.1" ||
    profile = "solana-program-2.3.0"
  let layout := record.layout == some (expectedLayouts legacy modern owned)
  let physicalAfter : Sdk.State := ⟨before.invocation,
    (Sdk.preflight actual.accounts before.borrows actual.instruction.metas).2⟩
  let (outcome, observed) : Out × Bool ← match ← (← field record.outcome "exit").getStr? with
    | "returned" => do
      let state ← field record.outcome "state"
      let log ← field state "requests"
      let same := (← field state "source") == record.state && log == toJson [record.args]
      pure (.returned (← valueOf (← field record.outcome "result")) physicalAfter, same)
    | "terminated" => do
      let log ← field record.outcome "requests"
      pure (.terminated (← terminalOf (← field record.outcome "reason")), log == toJson
        [record.args])
    | _ => throw "an on-chain CPI signature does not unwind"
  let computed := Reference.sdkEvaluate mainnet Witness.primitives Witness.context
    (fun state _ => .ok state) before actual
  let allowed := match outcome with
    | .returned value after =>
      let witness := (equivalent before args (.returned value after)).trans
        (Reference.sdk_returned_iff _ _ _ _ _ _ _ _)
      have : Decidable (relation before args (.returned value after)) :=
        decidable_of_iff _ witness.symm
      decide (relation before args (.returned value after))
    | .unwound reason _ => nomatch reason
    | .terminated error =>
      let witness := (equivalent before args (.terminated error)).trans
        (Reference.sdk_terminated_iff _ _ _ _ _ _ _)
      have : Decidable (relation before args (.terminated error)) :=
        decidable_of_iff _ witness.symm
      decide (relation before args (.terminated error))
  return ⟨profileMatches && layout && observed && allowed, Json.mkObj [
    ("scope", "whole-signature-mock"), ("model_admits", toJson allowed),
    ("layout_matches", toJson layout), ("source_observations_match", toJson observed),
    ("reference_exit", match computed with
      | .returned .. => "returned" | .terminated .. => "terminated"
      | .unwound reason _ => nomatch reason)]⟩

def borrowed (function reference profile : String) (signed legacy modern : Bool)
    (relation : Relation) (same : ∀ before args outcome, relation before args outcome ↔
      Sdk.run runtime before (normalized signed args) outcome) : Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  check := check signed legacy modern profile relation same

def invoke (profile : String) (modern signed : Bool) : Checker :=
  if signed then borrowed "solana_invoke::invoke_signed"
    "Solanalib.Specs.SolanaInvoke.invoke_signed_run" profile true false modern
    (Solanalib.Specs.SolanaInvoke.invoke_signed_run runtime) (fun _ _ _ => Iff.rfl)
  else borrowed "solana_invoke::invoke"
    "Solanalib.Specs.SolanaInvoke.invoke_run" profile false false modern
    (fun before args => Solanalib.Specs.SolanaInvoke.invoke_run runtime before args.toUnsignedArgs)
    (fun _ _ _ => Iff.rfl)

def ownedOutcome (outcome : Out) :
    Outcome (Sdk.Owned.State (Reference.ownedIndex runtime))
      (Except ProgramError.Value Unit) Empty (Sdk.Owned.Terminal (Reference.ownedIndex runtime)) :=
  match outcome with
  | .returned value after => .returned value ⟨after, none⟩
  | .unwound reason _ => nomatch reason
  | .terminated error => .terminated (.runtime error)

def owned (profile : String) (signed : Bool) : Checker :=
  let relation : Relation := fun before args outcome =>
    if signed then Solanalib.Specs.SolanaProgram.program.invoke_signed_run (Reference.ownedIndex
      runtime)
      ⟨before, none⟩ args (ownedOutcome outcome)
    else Solanalib.Specs.SolanaProgram.program.invoke_run (Reference.ownedIndex runtime)
      ⟨before, none⟩ args.toUnsignedArgs (ownedOutcome outcome)
  borrowed (if signed then "solana_program::program::invoke_signed" else
    "solana_program::program::invoke")
    (if signed then "Solanalib.Specs.SolanaProgram.program.invoke_signed_run" else
      "Solanalib.Specs.SolanaProgram.program.invoke_run") profile signed false false relation (by
      intro before args outcome
      cases signed <;> cases outcome with
      | returned value after => exact Reference.owned_returned_iff _ _ _ _ _
      | unwound reason _ => exact nomatch reason
      | terminated error => exact Reference.owned_runtime_terminal_iff _ _ _ _)

end SolanalibTest.Conformance.Library.Families.CpiSignatures

namespace SolanalibTest.Conformance.Library.Families.CpiSignatures

open Solanalib.Runtime Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

deriving instance DecidableEq for TxState
deriving instance DecidableEq for InvState
deriving instance DecidableEq for Sdk.State

def old (signed : Bool) : Checker :=
  if signed then borrowed "solana_program::program::invoke_signed"
    "Solanalib.Specs.SolanaProgram.program.invoke_signed_forwarded_inputs_run"
      "solana-program-1.15.2" true true false
    (Solanalib.Specs.SolanaProgram.program.invoke_signed_forwarded_inputs_run runtime) (fun _ _ _
      => Iff.rfl)
  else borrowed "solana_program::program::invoke"
    "Solanalib.Specs.SolanaProgram.program.invoke_forwarded_inputs_run" "solana-program-1.1\
      5.2"
      false true false
    (fun before args => Solanalib.Specs.SolanaProgram.program.invoke_forwarded_inputs_run runtime
      before args.toUnsignedArgs)
    (fun _ _ _ => Iff.rfl)

end SolanalibTest.Conformance.Library.Families.CpiSignatures

namespace SolanalibTest.Conformance.Library.Families.CpiSignatures

def corpora : List (String × List Checker) := [
  ("cpi_program_2_2_1", [owned "solana-program-2.2.1" true, owned "solana-program-2.2.1" false]),
  ("cpi_program_2_3_0", [owned "solana-program-2.3.0" true]),
  ("cpi_invoke_0_4_0_i2_2_1", [invoke "solana-invoke-0.4.0-i2-2-1" false true,
    invoke "solana-invoke-0.4.0-i2-2-1" false false]),
  ("cpi_invoke_0_4_0_i2_3_3", [invoke "solana-invoke-0.4.0-i2-3-3" false true,
    invoke "solana-invoke-0.4.0-i2-3-3" false false]),
  ("cpi_invoke_0_5_0_s3_0_0", [invoke "solana-invoke-0.5.0-s3.0.0" true true,
    invoke "solana-invoke-0.5.0-s3.0.0" true false]),
  ("cpi_invoke_0_5_0_s3_0_1", [invoke "solana-invoke-0.5.0-s3.0.1" true true,
    invoke "solana-invoke-0.5.0-s3.0.1" true false]),
  ("cpi_program_1_18_26", [owned "solana-program-1.18.26" true, owned "solana-program-1.18.\
    26"
    false]),
  ("cpi_program_1_15_2", [old true, old false])]

end SolanalibTest.Conformance.Library.Families.CpiSignatures
