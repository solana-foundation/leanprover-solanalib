/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Graph
import Solanalib.Specs.Core.AnchorError
import Solanalib.Specs.Core.AnchorErrorOwnedReference
import Solanalib.Specs.Core.AccountInfo
import Solanalib.Specs.Core.ProgramError

/-!
# JSON vocabulary of the Anchor corpora

Encodings written by `rust/anchor` (see its `src/enc.rs`): addresses are hex,
`ProgramError` is `{"variant", "fields"}` with the solana-program-error 3.0.1
variant name, `anchor_lang::error::Error` is `{"AnchorError": {...}}` or
`{"ProgramError": {...}}` with all diagnostic fields.

Owned errors (the primary error models) live in the registered finite heap
`AnchorErrorOwned.Reference`: the record lists the input Strings (ids are list
positions) and input Boxes. Native String and Box identities are buffer and
Box addresses; the driver maps an address to an input id, or to `null` for a
resource allocated during the call (its tracking allocator logs allocations
and frees during the call), so resource identity and liveness are observable.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! ## Scalars -/

def natField (j : Json) (k : String) : Result Nat := do (← field j k).getNat?
def boolField (j : Json) (k : String) : Result Bool := do (← field j k).getBool?
def strField (j : Json) (k : String) : Result String := do (← field j k).getStr?

def asPubkey (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

def keyField (j : Json) (k : String) : Result Solanalib.Runtime.Pubkey := do asPubkey (← field j k)

def asU64 (j : Json) : Result UInt64 := do pure (UInt64.ofNat (← asUInt 64 j))
def asU32 (j : Json) : Result UInt32 := do pure (UInt32.ofNat (← asUInt 32 j))

def asArray (j : Json) : Result (List Json) := do pure (← j.getArr?).toList

def asList {α : Type} (parse : Json → Result α) (j : Json) : Result (List α) := do
  (← asArray j).mapM parse

def listJson {α : Type} (render : α → Json) (xs : List α) : Json := Json.arr (xs.map render).toArray

def asOption {α : Type} (parse : Json → Result α) : Json → Result (Option α)
  | .null => pure none
  | j => do pure (some (← parse j))

def optionJson {α : Type} (render : α → Json) : Option α → Json
  | none => .null
  | some a => render a

/-- `{"variant": name, "fields": [...]}`. -/
def asVariant (j : Json) : Result (String × List Json) := do
  pure (← strField j "variant", ← asArray (← field j "fields"))

def variantJson (name : String) (fields : List Json) : Json :=
  Json.mkObj [("variant", name), ("fields", Json.arr fields.toArray)]

/-- A one-key object `{"Key": v}`. -/
def asTagged (j : Json) : Result (String × Json) := do
  match j with
  | .obj kvs =>
    match kvs.toList with
    | [(k, v)] => pure (k, v)
    | _ => throw s!"expected a one-key object, got {j.compress}"
  | _ => throw s!"expected a one-key object, got {j.compress}"

def tagged (k : String) (v : Json) : Json := Json.mkObj [(k, v)]

/-! ## ProgramError 3.0.1 -/

def programErrorNames : List (String × ProgramError.Value) := [
  ("InvalidArgument", .invalidArgument), ("InvalidInstructionData", .invalidInstructionData),
  ("InvalidAccountData", .invalidAccountData), ("AccountDataTooSmall", .accountDataTooSmall),
  ("InsufficientFunds", .insufficientFunds), ("IncorrectProgramId", .incorrectProgramId),
  ("MissingRequiredSignature", .missingRequiredSignature),
  ("AccountAlreadyInitialized", .accountAlreadyInitialized),
  ("UninitializedAccount", .uninitializedAccount), ("NotEnoughAccountKeys", .notEnoughAccountKeys),
  ("AccountBorrowFailed", .accountBorrowFailed), ("MaxSeedLengthExceeded", .maxSeedLengthExceeded),
  ("InvalidSeeds", .invalidSeeds), ("BorshIoError", .borshIoError),
  ("AccountNotRentExempt", .accountNotRentExempt), ("UnsupportedSysvar", .unsupportedSysvar),
  ("IllegalOwner", .illegalOwner),
  ("MaxAccountsDataAllocationsExceeded", .maxAccountsDataAllocationsExceeded),
  ("InvalidRealloc", .invalidRealloc),
  ("MaxInstructionTraceLengthExceeded", .maxInstructionTraceLengthExceeded),
  ("BuiltinProgramsMustConsumeComputeUnits", .builtinProgramsMustConsumeComputeUnits),
  ("InvalidAccountOwner", .invalidAccountOwner), ("ArithmeticOverflow", .arithmeticOverflow),
  ("Immutable", .immutable), ("IncorrectAuthority", .incorrectAuthority)]

def asProgramError (j : Json) : Result ProgramError.Value := do
  let (name, fields) ← asVariant j
  match name, fields with
  | "Custom", [code] => pure (.custom (← asU32 code))
  | n, [] => match programErrorNames.find? (·.1 == n) with
    | some (_, v) => pure v
    | none => throw s!"unknown ProgramError {n}"
  | n, _ => throw s!"bad ProgramError {n}"

def programErrorJson : ProgramError.Value → Json
  | .custom code => variantJson "Custom" [toJson code.toNat]
  | v => variantJson ((programErrorNames.find? (·.2 == v)).map (·.1) |>.getD "?") []

/-! ## anchor_lang::error::Error values -/

def asOrigin {S : Type} (string : Json → Result S) : Json → Result (Option (Sum AnchorError.Source
  S))
  | .null => pure none
  | j => do
    let (k, v) ← asTagged j
    match k with
    | "Source" => pure (some (.inl ⟨← strField v "filename", ← asU32 (← field v "line")⟩))
    | "AccountName" => pure (some (.inr (← string v)))
    | other => throw s!"unknown ErrorOrigin {other}"

def asCompared {S : Type} (string : Json → Result S) :
    Json → Result (Option (Sum (S × S) (Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey)))
  | .null => pure none
  | j => do
    let (k, v) ← asTagged j
    match k, ← asArray v with
    | "Values", [l, r] => pure (some (.inl (← string l, ← string r)))
    | "Pubkeys", [l, r] => pure (some (.inr (← asPubkey l, ← asPubkey r)))
    | other, _ => throw s!"bad ComparedValues {other}"

def toOrigin : Option (Sum AnchorError.Source String) → Option AnchorError.Origin
  | none => none
  | some (.inl s) => some (.source s)
  | some (.inr n) => some (.accountName n)

def toCompared : Option (Sum (String × String) (Solanalib.Runtime.Pubkey ×
  Solanalib.Runtime.Pubkey)) →
    Option AnchorError.ComparedValues
  | none => none
  | some (.inl (l, r)) => some (.values l r)
  | some (.inr (l, r)) => some (.pubkeys l r)

def originJson : Option AnchorError.Origin → Json
  | none => .null
  | some (.source s) => tagged "Source" (Json.mkObj [("filename", s.filename), ("line", toJson
    s.line.toNat)])
  | some (.accountName n) => tagged "AccountName" n

def comparedJson : Option AnchorError.ComparedValues → Json
  | none => .null
  | some (.values l r) => tagged "Values" (Json.arr #[l, r])
  | some (.pubkeys l r) => tagged "Pubkeys" (Json.arr #[pubkeyJson l, pubkeyJson r])

abbrev ErrorValue := AnchorError.Value ProgramError.Value

def asErrorValue (j : Json) : Result ErrorValue := do
  let (k, v) ← asTagged j
  let str := fun (x : Json) => x.getStr?
  match k with
  | "AnchorError" => pure (.anchor ⟨← strField v "name", ← asU32 (← field v "code"),
      ← strField v "message", toOrigin (← asOrigin str (← field v "origin")),
      toCompared (← asCompared str (← field v "compared"))⟩)
  | "ProgramError" => pure (.program ⟨← asProgramError (← field v "error"),
      toOrigin (← asOrigin str (← field v "origin")),
      toCompared (← asCompared str (← field v "compared"))⟩)
  | other => throw s!"unknown Error variant {other}"

def errorValueJson : ErrorValue → Json
  | .anchor e => tagged "AnchorError" (Json.mkObj [("name", e.name), ("code", toJson e.code.toNat),
      ("message", e.message), ("origin", originJson e.origin), ("compared", comparedJson
        e.compared)])
  | .program e => tagged "ProgramError" (Json.mkObj [("error", programErrorJson e.error),
      ("origin", originJson e.origin), ("compared", comparedJson e.compared)])

/-! ## Owned errors in the registered reference heap -/

namespace Owned

open AnchorErrorOwned AnchorErrorOwned.Reference

abbrev Heap := Reference.State

/-- Allocation budget of the reference heap; the native allocator never fails here. -/
def budget : Nat := 1000

def asStringId (j : Json) : Result StringId := do pure ⟨← j.getNat?⟩

def toOriginR : Option (Sum AnchorError.Source StringId) → Option (Origin StringId)
  | none => none
  | some (.inl s) => some (.source s)
  | some (.inr n) => some (.accountName n)

def toComparedR : Option (Sum (StringId × StringId) (Solanalib.Runtime.Pubkey ×
  Solanalib.Runtime.Pubkey)) →
    Option (Compared StringId)
  | none => none
  | some (.inl (l, r)) => some (.values l r)
  | some (.inr (l, r)) => some (.pubkeys l r)

/-- A boxed payload whose Strings are input ids. -/
def asPayload (j : Json) : Result (Payload StringId) := do
  let (k, v) ← asTagged j
  match k with
  | "AnchorError" => pure (.anchor ⟨← asStringId (← field v "name"), ← asU32 (← field v
    "code"),
      ← asStringId (← field v "message"), toOriginR (← asOrigin asStringId (← field v
        "origin")),
      toComparedR (← asCompared asStringId (← field v "compared"))⟩)
  | "ProgramError" => pure (.program ⟨← asProgramError (← field v "error"),
      toOriginR (← asOrigin asStringId (← field v "origin")),
      toComparedR (← asCompared asStringId (← field v "compared"))⟩)
  | other => throw s!"unknown Error variant {other}"

/-- The input heap: live Strings and Boxes at ids `0..`, no events, the budget. -/
def asHeap (j : Json) : Result Heap := do
  let strings ← asList (fun x => x.getStr?) (← field j "strings")
  let boxes ← asList asPayload (← field j "boxes")
  pure ⟨strings.map some, boxes.map some, budget, []⟩

/-- Observable identity of a resource: its input id, or `none` if it was
allocated during the call. -/
def project (inputs : Nat) (id : Nat) : Option Nat := if id < inputs then some id else none

def projectedJson : Option Nat → Json
  | none => .null
  | some n => toJson n

def asProjected (j : Json) : Result (Option Nat) := asOption (fun x => x.getNat?) j

/-- The observation of an owned error handle in a heap: its Box identity, the
current error value, and the identities of the boxed Strings in declaration
order. -/
structure ErrorObs where
  box : Option Nat
  value : Option ErrorValue
  strings : Option (List (Option Nat))
  deriving DecidableEq

def observeError (inputStrings inputBoxes : Nat) (heap : Heap) (error : Error BoxId) : ErrorObs :=
  ⟨project inputBoxes error.resource.index, current Reference.ops heap error,
    (currentBox heap error.resource).map fun p => p.strings.map fun s => project inputStrings
      s.index⟩

def errorObsJson (o : ErrorObs) : Json := Json.mkObj [("box", projectedJson o.box),
  ("value", optionJson errorValueJson o.value), ("strings", optionJson (listJson projectedJson)
    o.strings)]

def asErrorObs (j : Json) : Result ErrorObs := do
  pure ⟨← asProjected (← field j "box"), ← asOption asErrorValue (← field j "value"),
    ← asOption (asList asProjected) (← field j "strings")⟩

/-- Liveness of the input resources after the call, and the number of
resources allocated during the call that are still live (natively: the allocations of the
tracking allocator not freed by the end of the call; the logging of the
driver and the panic hook are untracked). An empty String owns no
allocation (`to_string` of an empty text), so fresh empty Strings do not count. -/
structure HeapObs where
  strings : List Bool
  boxes : List Bool
  freshLive : Nat
  deriving DecidableEq

def observeHeap (inputStrings inputBoxes : Nat) (heap : Heap) : HeapObs :=
  ⟨(List.range inputStrings).map fun i => (currentString heap ⟨i⟩).isSome,
    (List.range inputBoxes).map fun i => (currentBox heap ⟨i⟩).isSome,
    ((heap.strings.drop inputStrings).filter fun s => match s with
      | some text => !text.isEmpty
      | none => false).length +
      ((heap.boxes.drop inputBoxes).filter Option.isSome).length⟩

def heapObsJson (o : HeapObs) : Json := Json.mkObj [("strings_live", listJson toJson o.strings),
  ("boxes_live", listJson toJson o.boxes), ("fresh_live", toJson o.freshLive)]

def asHeapObs (j : Json) : Result HeapObs := do
  pure ⟨← asList (fun x => x.getBool?) (← field j "strings_live"),
    ← asList (fun x => x.getBool?) (← field j "boxes_live"), ← natField j "fresh_live"⟩

/-- Resolve the String ids of a payload in a heap (the input of the observation model). -/
def resolve (heap : Heap) (payload : Payload StringId) : Result ErrorValue :=
  match payload.observe (currentString heap) with
  | some v => pure v
  | none => throw "payload names a String outside the input heap"

end Owned

/-! ## AccountInfo values -/

/-- Decode the `key`, `lamports`, `data`, `owner`, `rent_epoch`, `is_signer`,
`is_writable`, `executable` and `owner_ref` fields of an account-info record.
Cells and owner references are identities assigned by the driver from `Rc`
and owner-storage addresses. -/
def asInfo (j : Json) : Result AccountInfo.Value := do
  pure ⟨← keyField j "key", ⟨← natField j "lamports"⟩, ⟨← natField j "data"⟩, ← keyField j
    "owner",
    ← asU64 (← field j "rent_epoch"), ← boolField j "is_signer", ← boolField j "is_writable",
    ← boolField j "executable", ⟨← natField j "owner_ref"⟩⟩

def infoJson (i : AccountInfo.Value) : Json := Json.mkObj [("key", pubkeyJson i.key),
  ("lamports", toJson i.lamports.cell), ("data", toJson i.data.cell), ("owner", pubkeyJson i.owner),
  ("rent_epoch", toJson i.unused.toNat), ("is_signer", toJson i.isSigner),
  ("is_writable", toJson i.isWritable), ("executable", toJson i.executable),
  ("owner_ref", toJson i.ownerRef.id)]

end SolanalibTest.Conformance.Library.Families.Anchor
