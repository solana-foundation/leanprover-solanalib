/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.StakeAddress
import Solanalib.Specs.Core.Instruction

/-!
# Family `Instructions`: shared record mappings

Addresses are 32-byte hex strings. An `AccountMeta`-like record
`{"pubkey", "is_signer", "is_writable"}` maps to the canonical `CpiMeta`, whose
flags are the bytes of the Rust `bool`s (0 or 1). An `Instruction` record
`{"program_id", "accounts", "data"}` maps to `CpiInstruction`.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh

abbrev Meta := Solanalib.Specs.Core.Instruction.Meta

def pubkey (j : Json) : Result Solanalib.Runtime.Pubkey := StakeAddress.pubkey j
def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := StakeAddress.pubkeyJson k

def keyField (j : Json) (k : String) : Result Solanalib.Runtime.Pubkey := do pubkey (← field j k)
def boolField (j : Json) (k : String) : Result Bool := do (← field j k).getBool?
def natField (j : Json) (k : String) (bits : Nat) : Result Nat := do asUInt bits (← field j k)

/-- The byte of a Rust `bool`. -/
def flagByte (b : Bool) : Nat := if b then 1 else 0

def metaOf (j : Json) : Result Meta := do
  pure ⟨← keyField j "pubkey", flagByte (← boolField j "is_signer"), flagByte (← boolField j
    "is_writable")⟩

def metaJson (m : Meta) : Json := Json.mkObj [
  ("pubkey", pubkeyJson m.key), ("is_signer", toJson (m.signerByte != 0)),
  ("is_writable", toJson (m.writableByte != 0))]

/-- A list of metas, or `{"repeat": n, "meta": m}` for `n` equal metas (long instructions). -/
def metasOf (j : Json) : Result (List Meta) :=
  match j.getObjVal? "repeat" with
  | .ok n => do pure (List.replicate (← n.getNat?) (← metaOf (← field j "meta")))
  | .error _ => asList metaOf j

def instructionOf (j : Json) : Result Solanalib.Runtime.CpiInstruction := do
  pure ⟨← keyField j "program_id", ← metasOf (← field j "accounts"), ← asBytes (← field j
    "data")⟩

def instructionJson (i : Solanalib.Runtime.CpiInstruction) : Json := Json.mkObj [
  ("program_id", pubkeyJson i.programId), ("accounts", listJson metaJson i.metas),
  ("data", bytesJson i.data)]

/-- Decide a record of a total value model `model : Unit → Args → Value × Unit` registered as
`returnsOf model` (`evaluated`, proved by `rfl` at the call site). The state is `()`, recorded
as `null`. -/
def decidePure {Args Value : Type} [DecidableEq Value]
    (model : Unit → Args → Value × Unit)
    (relation : Unit → Args → Outcome Unit Value Empty Empty → Prop)
    (evaluated : relation = returnsOf model)
    (args : Json → Result Args) (value : Json → Result Value) (render : Value → Json)
    (c : Case) : Result Verdict := do
  asUnit c.state
  decideReturns relation model evaluated () (← args c.args) value asUnit render (fun _ =>
    Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.Instructions
