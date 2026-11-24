/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Cpi
import SolanalibTest.Conformance.Library.Families.CpiSignatures
import Solanalib.Specs.Pinocchio.Cpi
import Solanalib.Specs.SolanaDefineSyscall.Cpi

/-! Exact typed mock boundaries for unchecked and raw CPI signatures. The
native fixture uses real Pinocchio deserialization and value constructors,
then replaces the complete invocation signature. Runtime stages below are
the existing mathematical reference with a declared identity callee. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.CpiRawSignatures

open Solanalib.Runtime Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.OpaqueCpi

def pinLayouts : Json := Json.mkObj [
  ("instruction", toJson ([40, 8, 24, 8, 0] : List Nat)),
  ("account", toJson ([56, 8] : List Nat)),
  ("account_meta", toJson ([16, 8, 0, 8, 9] : List Nat)),
  ("seed", toJson ([16, 8] : List Nat)), ("signer", toJson ([16, 8] : List Nat))]

abbrev Out := Outcome InvState Unit Empty InstrError
abbrev Relation := InvState → CpiReq → Out → Prop

def check (raw : Bool) (profile : String) (layouts : Json) (relation : Relation)
    (equivalent : ∀ before request outcome, relation before request outcome ↔
      OpaqueCpi.run CpiSignatures.runtime before request outcome) (record : Case) : Result Verdict
        := do
  let args ← CpiSignatures.argsOf record.args
  let request := args.runtimeRequest
  let before := Witness.before
  let scope := (← (← field record.state "scope").getStr?) == "whole-signature-mock"
  let profile := (← (← field record.state "profile").getStr?) == profile
  let layout := record.layout == some layouts
  let exit ← (← field record.outcome "exit").getStr?
  let (allowed, observed) ← match exit with
    | "returned" => do
      let result ← field record.outcome "result"
      let state ← field record.outcome "state"
      let same := (← field state "source") == record.state &&
        (← field state "requests") == toJson [record.args]
      let concrete ← if raw then pure (result == toJson (0 : Nat)) else
        pure (result == Json.null)
      let sameModel := (equivalent before request (.returned () before)).trans
        (Reference.returned_iff mainnet Witness.primitives Witness.context
          (fun state _ => .ok state) before before request)
      have : Decidable (relation before request (.returned () before)) :=
        decidable_of_iff _ sameModel.symm
      let model := decide (relation before request (.returned () before))
      pure (model, same && concrete)
    | "terminated" => do
      let error ← CpiSignatures.terminalOf (← field record.outcome "reason")
      let sameModel := (equivalent before request (.terminated error)).trans
        (Reference.terminated_iff mainnet Witness.primitives Witness.context
          (fun state _ => .ok state) before request error)
      have : Decidable (relation before request (.terminated error)) :=
        decidable_of_iff _ sameModel.symm
      pure (decide (relation before request (.terminated error)),
        (← field record.outcome "requests") == toJson [record.args])
    | _ => pure (false, false)
  return ⟨scope && profile && layout && allowed && observed, Json.mkObj [
    ("scope", "whole-signature-mock"), ("model_admits", toJson allowed),
    ("source_observations_match", toJson observed), ("layout_matches", toJson layout)]⟩

def unchecked : Checker where
  function := "pinocchio::cpi::invoke_signed_unchecked"
  generics := []
  reference := "Solanalib.Specs.Pinocchio.cpi.invoke_signed_unchecked_run"
  decides := ["Solanalib.Specs.Pinocchio.cpi.invoke_signed_unchecked_run"]
  check := check false "pinocchio-0.9.2" pinLayouts
    (Solanalib.Specs.Pinocchio.cpi.invoke_signed_unchecked_run CpiSignatures.runtime)
    (fun _ _ _ => Iff.rfl)

def rawOutcome : Out → Outcome InvState UInt64 Empty InstrError
  | .returned () after => .returned 0 after
  | .unwound reason _ => nomatch reason
  | .terminated error => .terminated error

def raw : Checker where
  function := "pinocchio::syscalls::sol_invoke_signed_c"
  generics := []
  reference := "Solanalib.Specs.Pinocchio.syscalls.sol_invoke_signed_c_run"
  decides := ["Solanalib.Specs.Pinocchio.syscalls.sol_invoke_signed_c_run"]
  check := check true "pinocchio-0.9.2" pinLayouts (fun before request outcome =>
    Solanalib.Specs.Pinocchio.syscalls.sol_invoke_signed_c_run
      CpiSignatures.runtime before request (rawOutcome outcome)) (by
        intro before request outcome
        cases outcome with
        | returned value after => simp [rawOutcome,
            Solanalib.Specs.Pinocchio.syscalls.sol_invoke_signed_c_run,
            rawFamilyRun, rawRun]
        | unwound reason _ => exact nomatch reason
        | terminated error => exact Iff.rfl)

def rustLayouts : Json := Json.mkObj [
  ("descriptor_origin", "explicit-vm-fixture"),
  ("instruction", toJson ([80, 8, 0, 24, 48] : List Nat)),
  ("account_info", toJson ([48, 8, 0, 8, 16, 24, 32, 40, 41, 42] : List Nat)),
  ("meta", toJson ([34, 1, 32, 33] : List Nat)),
  ("stable_vec", toJson ([24, 0, 8, 16] : List Nat)),
  ("seed", toJson ([16, 8] : List Nat))]

def rust (profile function : String) : Checker where
  function := function
  generics := []
  reference := "Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_run"
  decides := ["Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_run"]
  check := check true profile rustLayouts (fun before request outcome =>
    Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_run
      CpiSignatures.runtime before request (rawOutcome outcome)) (by
        intro before request outcome
        cases outcome with
        | returned value after => simp [rawOutcome,
            Solanalib.Specs.SolanaDefineSyscall.definitions.sol_invoke_signed_rust_run,
            rawFamilyRun, rawRun]
        | unwound reason _ => exact nomatch reason
        | terminated error => exact Iff.rfl)

def programRust (profile function : String) : Checker where
  function := function
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_invoke_signed_rust_r\
    un"
  decides := ["Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_invoke_signed_rust_ru\
    n"]
  check := check true profile rustLayouts (fun before request outcome =>
    Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_invoke_signed_rust_run
      CpiSignatures.runtime before request (rawOutcome outcome)) (by
        intro before request outcome
        cases outcome with
        | returned value after => simp [rawOutcome,
            Solanalib.Specs.SolanaProgram.syscalls.definitions.sol_invoke_signed_rust_run,
            rawFamilyRun, rawRun]
        | unwound reason _ => exact nomatch reason
        | terminated error => exact Iff.rfl)

def corpora : List (String × List Checker) := [
  ("cpi_pinocchio_0_9_2", [unchecked, raw]),
  ("cpi_raw_define_2_3_0", [rust "solana-define-syscall-2.3.0"
    "solana_define_syscall::definitions::sol_invoke_signed_rust"]),
  ("cpi_raw_define_3_0_0", [rust "solana-define-syscall-3.0.0"
    "solana_define_syscall::definitions::sol_invoke_signed_rust"]),
  ("cpi_raw_program_1_18_26", [programRust "solana-program-1.18.26"
    "solana_program::syscalls::definitions::sol_invoke_signed_rust"]),
  ("cpi_raw_program_1_15_2", [programRust "solana-program-1.15.2"
    "solana_program::syscalls::definitions::sol_invoke_signed_rust"])]

end SolanalibTest.Conformance.Library.Families.CpiRawSignatures
