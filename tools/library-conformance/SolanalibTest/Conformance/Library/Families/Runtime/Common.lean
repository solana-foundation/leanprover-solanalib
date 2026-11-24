/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.ProgramError
import Solanalib.Specs.Core.SysvarRentArithmetic

/-!
# Shared encodings of the runtime family

`ProgramError` values are recorded by their Rust `Debug` text (`InvalidArgument`,
`Custom(7)`); integers are exact JSON numbers; addresses and other byte arrays
are hex strings. Panic payloads of checked arithmetic map to the `Sysvar.Panic` reasons of the
models; any other payload is not a reason the models admit.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Runtime

open Solanalib.Contracts.Model Solanalib.Specs.Core

def u64 (j : Json) : Result UInt64 := do pure (UInt64.ofNat (← asUInt 64 j))
def u16 (j : Json) : Result UInt16 := do pure (UInt16.ofNat (← asUInt 16 j))
def u8 (j : Json) : Result UInt8 := do pure (UInt8.ofNat (← asUInt 8 j))
def nat (j : Json) : Result Nat := j.getNat?

def u64Json (n : UInt64) : Json := toJson n.toNat
def natJson (n : Nat) : Json := toJson n

def bool (j : Json) : Result Bool := j.getBool?

def bytesN (n : Nat) (j : Json) : Result { b : Solanalib.Runtime.Bytes // b.length = n } := do
  let b ← asBytes j
  if h : b.length = n then pure ⟨b, h⟩ else throw s!"expected {n} bytes, got {b.length}"

def pubkey (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let b ← bytesN 32 j
  pure ⟨b.val, b.property⟩

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

/-! ## ProgramError (solana-program-error 3.0.1) -/

def programErrorNames : List (String × ProgramError.Value) := [
  ("InvalidArgument", .invalidArgument),
  ("InvalidInstructionData", .invalidInstructionData),
  ("InvalidAccountData", .invalidAccountData),
  ("AccountDataTooSmall", .accountDataTooSmall),
  ("InsufficientFunds", .insufficientFunds),
  ("IncorrectProgramId", .incorrectProgramId),
  ("MissingRequiredSignature", .missingRequiredSignature),
  ("AccountAlreadyInitialized", .accountAlreadyInitialized),
  ("UninitializedAccount", .uninitializedAccount),
  ("NotEnoughAccountKeys", .notEnoughAccountKeys),
  ("AccountBorrowFailed", .accountBorrowFailed),
  ("MaxSeedLengthExceeded", .maxSeedLengthExceeded),
  ("InvalidSeeds", .invalidSeeds),
  ("BorshIoError", .borshIoError),
  ("AccountNotRentExempt", .accountNotRentExempt),
  ("UnsupportedSysvar", .unsupportedSysvar),
  ("IllegalOwner", .illegalOwner),
  ("MaxAccountsDataAllocationsExceeded", .maxAccountsDataAllocationsExceeded),
  ("InvalidRealloc", .invalidRealloc),
  ("MaxInstructionTraceLengthExceeded", .maxInstructionTraceLengthExceeded),
  ("BuiltinProgramsMustConsumeComputeUnits", .builtinProgramsMustConsumeComputeUnits),
  ("InvalidAccountOwner", .invalidAccountOwner),
  ("ArithmeticOverflow", .arithmeticOverflow),
  ("Immutable", .immutable),
  ("IncorrectAuthority", .incorrectAuthority)]

def programError (j : Json) : Result ProgramError.Value := do
  let s ← j.getStr?
  match programErrorNames.lookup s with
  | some e => pure e
  | none =>
    if s.startsWith "Custom(" && s.endsWith ")" then
      match ((s.drop 7).dropEnd 1).toString.toNat? with
      | some n => if n < 2 ^ 32 then pure (.custom (UInt32.ofNat n)) else throw s!
        "custom code {n}"
      | none => throw s!"unknown ProgramError {s}"
    else throw s!"unknown ProgramError {s}"

def programErrorJson (e : ProgramError.Value) : Json :=
  match e with
  | .custom code => Json.str s!"Custom({code.toNat})"
  | other => Json.str (((programErrorNames.find? (·.2 == other)).map (·.1)).getD "?")

/-! ## Outcomes -/

def outcomeJson {S V U T : Type} (state : S → Json) (value : V → Json) (unwind : U → Json)
    (terminal : T → Json) : Outcome S V U T → Json
  | .returned v s => returnedJson (value v) (state s)
  | .unwound r s => Json.mkObj [("exit", "unwound"), ("reason", unwind r), ("state", state s)]
  | .terminated r => Json.mkObj [("exit", "terminated"), ("reason", terminal r)]

def emptyJson (e : Empty) : Json := nomatch e

/-! ## Callback graphs -/

/-- `Callback.bind` over the graph of a function continues with the outcome of that function. -/
theorem bind_ofFunction_iff {S A V N U T : Type} (f : S → A → Outcome S V U T)
    (next : V → S → Outcome S N U T → Prop) (before : S) (args : A) (o : Outcome S N U T) :
    Callback.bind (Callback.ofFunction f) next before args o ↔
      (match f before args with
       | .returned v s => next v s o
       | .unwound r s => o = .unwound r s
       | .terminated r => o = .terminated r) := by
  constructor
  · rintro ⟨i, h, k⟩
    change f before args = i at h
    subst h
    exact k
  · intro k
    exact ⟨_, rfl, k⟩

/-- Decide `relation recorded` through `relation o ↔ computed = some o`, for relations that
admit at most one outcome and possibly none (`computed = none`): a provider reply the
wrapper cannot continue from admits no outcome. -/
def decideOptGraph {S V U T : Type} [DecidableEq (Outcome S V U T)]
    (relation : Outcome S V U T → Prop) (computed : Option (Outcome S V U T))
    (graph : ∀ o, relation o ↔ computed = some o)
    (recorded : Option (Outcome S V U T)) (render : Outcome S V U T → Json) : Verdict :=
  let expected := match computed with
    | some o => render o
    | none => Json.mkObj [("exit", "none"), ("note", "the reference admits no outcome")]
  match recorded with
  | some o =>
    have : Decidable (relation o) := decidable_of_iff _ (graph o).symm
    ⟨decide (relation o), expected⟩
  | none => ⟨false, expected⟩

/-! ## Preconditions -/

/-- A record must satisfy the `requires` of the decided contract: outside it the contract leaves the
behavior open, so such a record is rejected whatever the reference admits. -/
def withRequires (name : String) (ready : Bool) (verdict : Verdict) : Verdict :=
  if ready then verdict
  else ⟨false, Json.mkObj [("precondition", Json.str s!"{name} does not hold"), ("model",
    verdict.expected)]⟩

/-! ## Checked arithmetic (solana-rent 3.0.0, pinocchio 0.10.2) -/

/-- Panic payloads of the overflow checks of rustc, mapped to the reasons of the models.
The floating BPF panic of pinocchio 0.10.2 is unreachable on the host build. -/
def panicReason : String → Option Sysvar.Panic
  | "attempt to add with overflow" => some .additionOverflow
  | "attempt to multiply with overflow" => some .multiplicationOverflow
  | "Floating-point operations are not supported on BPF targets" => some .bpfFloatingPoint
  | _ => none

def panicJson : Sysvar.Panic → Json
  | .additionOverflow => "attempt to add with overflow"
  | .multiplicationOverflow => "attempt to multiply with overflow"
  | .bpfFloatingPoint => "Floating-point operations are not supported on BPF targets"

def arithmeticProfile (j : Json) : Result Sysvar.ArithmeticProfile := do
  let checks ← bool (← field j "overflow_checks")
  let strategy ← match ← (← field j "panic").getStr? with
    | "unwind" => pure Sysvar.PanicStrategy.unwind
    | "abort" => pure .abort
    | s => throw s!"unknown panic strategy {s}"
  pure ⟨checks, strategy⟩

def arithmeticProfileFields (p : Sysvar.ArithmeticProfile) : List (String × Json) :=
  [("overflow_checks", Json.bool p.overflowChecks),
   ("panic", match p.panicStrategy with | .unwind => "unwind" | .abort => "abort")]

def arithmeticProfileJson (p : Sysvar.ArithmeticProfile) : Json :=
  Json.mkObj (arithmeticProfileFields p)

end SolanalibTest.Conformance.Library.Families.Runtime
