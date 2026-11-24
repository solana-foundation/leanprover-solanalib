/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.TokenInstruction

/-!
# Shared readers of the token-interface records

Keys are 32-byte hex strings; `ProgramError` is `{"variant", "fields"}` with
the solana-program-error 3.0.1 variant name (and the code for `Custom`). The error type of the
models is `Solanalib.Runtime.InstrError`, whose constructors carry the same
names; this reader is that representation mapping. An instruction is
`{program_id, accounts: [{pubkey, is_signer, is_writable}], data}`, read as
`Solanalib.Runtime.CpiInstruction` with the canonical 0/1 flag bytes of
`Solanalib.Specs.Core.Instruction.accountMeta`.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.TokenInterface

def pubkey (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"key must have 32 bytes, got \
    {b.length}"

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

def keyField (j : Json) (k : String) : Result Solanalib.Runtime.Pubkey := do pubkey (← field j k)

def natField (j : Json) (k : String) : Result Nat := do (← field j k).getNat?

def uintField (bits : Nat) (j : Json) (k : String) : Result Nat := do asUInt bits (← field j k)

def boolField (j : Json) (k : String) : Result Bool := do (← field j k).getBool?

def listField {α : Type} (j : Json) (k : String) (parse : Json → Result α) : Result (List α) := do
  (← (← field j k).getArr?).toList.mapM parse

/-- `ProgramError` variants other than `Custom`, by name. -/
def programErrorNames : List (String × Solanalib.Runtime.InstrError) := [
  ("InvalidArgument", .InvalidArgument), ("InvalidInstructionData", .InvalidInstructionData),
  ("InvalidAccountData", .InvalidAccountData), ("AccountDataTooSmall", .AccountDataTooSmall),
  ("InsufficientFunds", .InsufficientFunds), ("IncorrectProgramId", .IncorrectProgramId),
  ("MissingRequiredSignature", .MissingRequiredSignature),
  ("AccountAlreadyInitialized", .AccountAlreadyInitialized),
  ("UninitializedAccount", .UninitializedAccount), ("NotEnoughAccountKeys", .NotEnoughAccountKeys),
  ("AccountBorrowFailed", .AccountBorrowFailed), ("MaxSeedLengthExceeded", .MaxSeedLengthExceeded),
  ("InvalidSeeds", .InvalidSeeds), ("BorshIoError", .BorshIoError),
  ("AccountNotRentExempt", .AccountNotRentExempt), ("UnsupportedSysvar", .UnsupportedSysvar),
  ("IllegalOwner", .IllegalOwner),
  ("MaxAccountsDataAllocationsExceeded", .MaxAccountsDataAllocationsExceeded),
  ("InvalidRealloc", .InvalidRealloc),
  ("MaxInstructionTraceLengthExceeded", .MaxInstructionTraceLengthExceeded),
  ("BuiltinProgramsMustConsumeComputeUnits", .BuiltinProgramsMustConsumeComputeUnits),
  ("InvalidAccountOwner", .InvalidAccountOwner), ("ArithmeticOverflow", .ArithmeticOverflow),
  ("Immutable", .Immutable), ("IncorrectAuthority", .IncorrectAuthority)]

def programError (j : Json) : Result Solanalib.Runtime.InstrError := do
  let name ← (← field j "variant").getStr?
  let fields ← (← field j "fields").getArr?
  match name, fields.toList with
  | "Custom", [code] => return .Custom (← asUInt 32 code)
  | _, [] =>
    match programErrorNames.find? (·.1 == name) with
    | some (_, e) => return e
    | none => throw s!"unknown ProgramError {name}"
  | _, _ => throw s!"malformed ProgramError {j.compress}"

/-- For the report only. -/
def programErrorJson : Solanalib.Runtime.InstrError → Json
  | .Custom code => Json.mkObj [("variant", "Custom"), ("fields", Json.arr #[Json.num code])]
  | e => match programErrorNames.find? (·.2 == e) with
    | some (name, _) => Json.mkObj [("variant", Json.str name), ("fields", Json.arr #[])]
    | none => Json.str (toString (repr e))

def flag (b : Bool) : Nat := if b then 1 else 0

def cpiMeta (j : Json) : Result Solanalib.Runtime.CpiMeta := do
  pure ⟨← keyField j "pubkey", flag (← boolField j "is_signer"), flag (← boolField j
    "is_writable")⟩

def cpiMetaJson (m : Solanalib.Runtime.CpiMeta) : Json := Json.mkObj [
  ("pubkey", pubkeyJson m.key), ("is_signer", Json.bool (m.signerByte == 1)),
  ("is_writable", Json.bool (m.writableByte == 1)),
  ("signer_byte", Json.num m.signerByte), ("writable_byte", Json.num m.writableByte)]

def instruction (j : Json) : Result Solanalib.Runtime.CpiInstruction := do
  pure ⟨← keyField j "program_id", ← listField j "accounts" cpiMeta, ← asBytes (← field j
    "data")⟩

def instructionJson (i : Solanalib.Runtime.CpiInstruction) : Json := Json.mkObj [
  ("program_id", pubkeyJson i.programId), ("accounts", Json.arr (i.metas.map cpiMetaJson).toArray),
  ("data", bytesJson i.data)]

def resultOf {α : Type} (value : Json → Result α) (j : Json) : Result (Except
  Solanalib.Runtime.InstrError α) :=
  asExcept programError value j

def resultJson {α : Type} (value : α → Json) : Except Solanalib.Runtime.InstrError α → Json :=
  exceptJson programErrorJson value

def optionJson {α : Type} (value : α → Json) : Option α → Json
  | none => Json.null
  | some v => Json.mkObj [("some", value v)]

def asOption {α : Type} (value : Json → Result α) (j : Json) : Result (Option α) :=
  match j with
  | .null => pure none
  | _ => do some <$> value (← field j "some")

/-- Checker v2 for a Rust function observed by two registered models: `run`
gives the verdict of each model on the record and the report. A record is admitted
when both admit it. `requiresDecided` names the models whose precondition
`run` decides as part of their verdict. -/
def pairChecker (function : String) (generics : List (String × String)) (first second : String)
    (run : Case → Result (Bool × Bool × Json)) (requiresDecided : List String := []) : Checker where
  function := function
  generics := generics
  reference := first ++ "+" ++ second
  check := fun c => do
    let (a, b, expected) ← run c
    return ⟨a && b, expected⟩
  decides := [first, second]
  decidesRequires := requiresDecided
  checkModels := some fun c => do
    let (a, b, expected) ← run c
    return ([⟨first, a⟩, ⟨second, b⟩], expected)

/-- A record whose state before and after is `null` (the `Unit` of the models). -/
def unitState (j : Json) : Result Unit := asUnit j

end SolanalibTest.Conformance.Library.Families.TokenInterface
