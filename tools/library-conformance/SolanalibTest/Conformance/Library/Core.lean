/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Lean.Data.Json
import Solanalib.Specs.Core.Outcome
import Solanalib.Runtime.Basic

/-!
# Shared vocabulary of the conformance checker

A record of the corpus (written by the Rust recorder, see the README section on
"Corpus format") holds the state before a call, its arguments and the observed
outcome. A `Checker` parses them into the types of one registered model at one
family index and decides whether the registered relation admits the recorded
outcome. The module of each checker proves by `rfl` that the relation it decides is
the registered reference, so the evaluated function is that reference and not
a copy.

Fixed exit mapping. A recorded `returned` exit (including `Result::Err`) is
`Outcome.returned`; a recorded `unwound` exit (a Rust panic caught by
`catch_unwind`, with the state observed afterwards) is `Outcome.unwound`; a
`terminated` exit is `Outcome.terminated`. A family whose `Unwind` or
`Terminal` type is empty admits no such exit, so such a record is a mismatch.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library

open Solanalib.Contracts.Model Solanalib.Specs.Core

abbrev Result := Except String

/-! ## Values -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Zero runs at least this long are written `[N]` by the recorder. -/
def zeroRun : Nat := 64

/-- Hex digits, with `[N]` standing for `N` zero bytes; tail-recursive over a
fuel bound (the number of characters). -/
def parseHexAux : Nat → List Char → Array UInt8 → Result Solanalib.Runtime.Bytes
  | 0, [], acc => pure acc.toList
  | 0, _ :: _, _ => throw "hex string too long"
  | _ + 1, [], acc => pure acc.toList
  | fuel + 1, '[' :: rest, acc =>
    let (digits, tail) := rest.span (· != ']')
    match tail, (String.ofList digits).toNat? with
    | ']' :: after, some n => parseHexAux fuel after (acc ++ Array.replicate n 0)
    | _, _ => throw "malformed zero run in hex string"
  | _ + 1, [_], _ => throw "odd-length hex string"
  | fuel + 1, a :: b :: rest, acc =>
    match hexDigit? a, hexDigit? b with
    | some x, some y => parseHexAux fuel rest (acc.push (UInt8.ofNat (16 * x + y)))
    | _, _ => throw s!"invalid hex digits {a}{b}"

/-- Lower-case hex as the recorder writes it: two digits per byte, and `[N]`
for each run of `N ≥ 64` zero bytes. -/
def parseHex (s : String) : Result Solanalib.Runtime.Bytes := parseHexAux s.length s.toList #[]

def hexOfAux (digit : Nat → Char) : Nat → Solanalib.Runtime.Bytes → String → String
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | fuel + 1, b :: bs, acc =>
    let zeros := ((b :: bs).takeWhile (· == 0)).length
    if zeroRun ≤ zeros then hexOfAux digit fuel ((b :: bs).drop zeros) (acc ++ s!"[{zeros}]")
    else hexOfAux digit fuel bs ((acc.push (digit (b.toNat / 16))).push (digit (b.toNat % 16)))

/-- The canonical hex form of the recorder (zero runs of at least 64 bytes as `[N]`). -/
def hexOf (bytes : Solanalib.Runtime.Bytes) : String :=
  hexOfAux (fun n => "0123456789abcdef".toList.getD n '0') bytes.length bytes ""

def field (j : Json) (key : String) : Result Json := j.getObjVal? key

def asBytes (j : Json) : Result Solanalib.Runtime.Bytes := do parseHex (← j.getStr?)

def bytesJson (bytes : Solanalib.Runtime.Bytes) : Json := Json.str (hexOf bytes)

def asUnit (j : Json) : Result Unit :=
  match j with
  | .null => pure ()
  | _ => throw s!"expected null for (), got {j.compress}"

/-- An unsigned integer of `bits` bits. -/
def asUInt (bits : Nat) (j : Json) : Result Nat := do
  let n ← j.getNat?
  if n < 2 ^ bits then pure n else throw s!"{n} exceeds u{bits}"

/-- A signed integer of `bits` bits. -/
def asSInt (bits : Nat) (j : Json) : Result Int := do
  let n ← j.getInt?
  if -(2 ^ (bits - 1) : Int) ≤ n ∧ n < 2 ^ (bits - 1) then pure n
  else throw s!"{n} exceeds i{bits}"

/-- An `f64` recorded as the hex string of its 64 bits. -/
def asF64Bits (j : Json) : Result UInt64 := do
  let s ← j.getStr?
  let bytes ← parseHex s
  unless bytes.length = 8 do throw s!"f64 bit pattern must have 16 hex digits: {s}"
  pure (UInt64.ofNat (bytes.foldl (fun acc b => 256 * acc + b.toNat) 0))

def f64BitsJson (bits : UInt64) : Json :=
  Json.str (hexOf ((Solanalib.Runtime.leBytes 8 bits.toNat).reverse))

/-! ## Outcomes -/

/-- `Except` has no `DecidableEq` instance in core; the checker needs one to
decide equalities of `Result`-valued references. -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-- The graph of a total reference is decidable when its values and states
have decidable equality: it admits exactly the returned outcome it computes. -/
instance instDecidableReturnsOf {State Args Value Unwind Terminal : Type}
    [DecidableEq State] [DecidableEq Value]
    (run : State → Args → Value × State) (before : State) (args : Args)
    (outcome : Outcome State Value Unwind Terminal) :
    Decidable (returnsOf run before args outcome) :=
  match outcome with
  | .returned value after => inferInstanceAs (Decidable (run before args = (value, after)))
  | .unwound _ _ => isFalse id
  | .terminated _ => isFalse id

/-- Structural decidable equality of outcomes. -/
instance instDecidableEqOutcome {S V U T : Type} [DecidableEq S] [DecidableEq V] [DecidableEq U]
    [DecidableEq T] : DecidableEq (Outcome S V U T)
  | .returned v s, .returned v' s' =>
    if h : v = v' ∧ s = s' then isTrue (by rw [h.1, h.2])
    else isFalse (fun e => h (by cases e; exact ⟨rfl, rfl⟩))
  | .unwound r s, .unwound r' s' =>
    if h : r = r' ∧ s = s' then isTrue (by rw [h.1, h.2])
    else isFalse (fun e => h (by cases e; exact ⟨rfl, rfl⟩))
  | .terminated r, .terminated r' =>
    if h : r = r' then isTrue (by rw [h]) else isFalse (fun e => h (by cases e; rfl))
  | .returned .., .unwound .. | .returned .., .terminated .. | .unwound .., .returned ..
  | .unwound .., .terminated .. | .terminated .., .returned .. | .terminated .., .unwound .. =>
    isFalse (fun e => by cases e)

/-- The graph of a total reference, as an outcome function. -/
theorem returnsOf_iff {S A V U T : Type} (run : S → A → V × S) (before : S) (args : A)
    (outcome : Outcome S V U T) :
    returnsOf run before args outcome ↔
      (Outcome.returned (run before args).1 (run before args).2 : Outcome S V U T) = outcome := by
  cases outcome with
  | returned v s =>
    show run before args = (v, s) ↔ _
    constructor
    · intro h; rw [h]
    · intro h; injection h with h1 h2; rw [← h1, ← h2]
  | unwound r s => exact ⟨False.elim, fun h => by cases h⟩
  | terminated r => exact ⟨False.elim, fun h => by cases h⟩

/-- A recorded outcome, or `none` if the family has no reason of that kind. -/
def parseOutcome {State Value Unwind Terminal : Type}
    (value : Json → Result Value) (state : Json → Result State)
    (unwind : String → Option Unwind) (terminal : String → Option Terminal)
    (j : Json) : Result (Option (Outcome State Value Unwind Terminal)) := do
  match ← (← field j "exit").getStr? with
  | "returned" => return some (.returned (← value (← field j "result")) (← state (← field j
    "state")))
  | "unwound" => do
    let reason ← (← field j "reason").getStr?
    match unwind reason with
    | some r => return some (.unwound r (← state (← field j "state")))
    | none => return none
  | "terminated" => do
    let reason ← (← field j "reason").getStr?
    return (terminal reason).map .terminated
  | other => throw s!"unknown exit {other}"

def noReason {α : Type} (_ : String) : Option α := none

def returnedJson (result state : Json) : Json :=
  Json.mkObj [("exit", "returned"), ("result", result), ("state", state)]

def okJson (value : Json) : Json := Json.mkObj [("ok", value)]
def errJson (error : Json) : Json := Json.mkObj [("err", error)]

def asExcept {ε α : Type} (error : Json → Result ε) (value : Json → Result α) (j : Json) :
    Result (Except ε α) :=
  match j.getObjVal? "ok", j.getObjVal? "err" with
  | .ok v, .error _ => return .ok (← value v)
  | .error _, .ok e => return .error (← error e)
  | _, _ => throw s!"expected {"{"}\"ok\": …} or {"{"}\"err\": …}, got {j.compress}"

def exceptJson {ε α : Type} (error : ε → Json) (value : α → Json) : Except ε α → Json
  | .ok v => okJson (value v)
  | .error e => errJson (error e)

/-! ## Records and checkers -/

structure Case where
  corpus : String
  id : String
  function : String
  generics : List (String × String)
  layout : Option Json
  state : Json
  args : Json
  outcome : Json

/-- Whether the registered relation admits the recorded outcome, and the
outcome the reference computes (for the report). -/
structure Verdict where
  admitted : Bool
  expected : Json

/-- Checker v2: the verdict of one registered model on a record. `model` is the name of the
registered constant, as in the source map (`contract`, `reference` or
`family`). -/
structure ModelVerdict where
  model : String
  admitted : Bool
  deriving Repr

structure Checker where
  /-- Rust item path, the `function` of the record. -/
  function : String
  /-- Concrete generic arguments, the `generics` of the record. -/
  generics : List (String × String)
  /-- The Lean reference relation that is decided (free text, for the report). -/
  reference : String
  check : Case → Result Verdict
  /-- Checker v2: the registered constants this checker decides (source-map
  names). The audit requires each to be registered and used by the code of the family, and the
  runner matches them against `checkModels` and divergences. -/
  decides : List String := []
  /-- Checker v2: one verdict per declared model, and the computed outcome for
  the report. When present the runner uses it instead of `check`; a record is
  admitted when every model admits it. -/
  checkModels : Option (Case → Result (List ModelVerdict × Json)) := none
  /-- The declared models (names from `decides`) whose precondition (`requires`) this checker
  decides, so that a record outside it fails. The audit requires the decision code of the
  checker to use `Solanalib.Contracts.Model.requires` and the registered contract of the model.
  A decided model with a non-trivial `requires` must be listed here by each of its checkers, or
  in `requires-open.toml`. -/
  decidesRequires : List String := []

def genericsText (generics : List (String × String)) : String :=
  ", ".intercalate (generics.map fun (k, v) => s!"{k} = {v}")

def Checker.key (c : Checker) : String := c.function ++ " [" ++ genericsText c.generics ++
  "]"

def Case.key (c : Case) : String := c.function ++ " [" ++ genericsText c.generics ++ "]"

/-- Checker v2 for a checker that decides several models: run the check of each model and report its
verdict. `checks` pairs each declared model with its check;
the report shows the computed outcome of the first check. -/
def perModel (checks : List (String × (Case → Result Verdict))) :
    Case → Result (List ModelVerdict × Json) := fun c => do
  let results ← checks.mapM fun (m, check) => do pure (m, ← check c)
  let expected := match results.head? with
    | some (_, v) => v.expected
    | none => Json.null
  pure (results.map fun (m, v) => ⟨m, v.admitted⟩, expected)

/-- Decide a total reference registered as the graph of `model`: parse the
recorded outcome and decide `relation before args outcome`. The decision
procedure is obtained through `evaluated`, the `rfl` proof of the checker that the
registered relation is the graph of the evaluated function. `model` is also
evaluated directly for the report. -/
def decideReturns {State Args Value : Type} [DecidableEq State] [DecidableEq Value]
    (relation : State → Args → Outcome State Value Empty Empty → Prop)
    (model : State → Args → Value × State)
    (evaluated : relation = returnsOf model)
    (before : State) (args : Args)
    (value : Json → Result Value) (state : Json → Result State)
    (renderValue : Value → Json) (renderState : State → Json) (recorded : Json) : Result Verdict :=
      do
  let computed := model before args
  let expected := returnedJson (renderValue computed.1) (renderState computed.2)
  match ← parseOutcome value state noReason noReason recorded with
  | some outcome =>
    have : Decidable (relation before args outcome) := by
      rw [evaluated]; exact instDecidableReturnsOf model before args outcome
    return ⟨decide (relation before args outcome), expected⟩
  | none => return ⟨false, expected⟩

/-- Decide `relation recorded` through a graph lemma `relation o ↔ computed = o`
supplied by the model. -/
def decideGraph {S V U T : Type} [DecidableEq (Outcome S V U T)]
    (relation : Outcome S V U T → Prop) (computed : Outcome S V U T)
    (graph : ∀ o, relation o ↔ computed = o)
    (recorded : Option (Outcome S V U T)) (render : Outcome S V U T → Json) : Verdict :=
  match recorded with
  | some o =>
    have : Decidable (relation o) := decidable_of_iff _ (graph o).symm
    ⟨decide (relation o), render computed⟩
  | none => ⟨false, render computed⟩

end SolanalibTest.Conformance.Library
