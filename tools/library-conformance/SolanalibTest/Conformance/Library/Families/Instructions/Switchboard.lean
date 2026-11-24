/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import Solanalib.Specs.SwitchboardOnDemand.Capabilities

/-!
# Family `Instructions`: switchboard-on-demand 0.12.1 `PullFeedAccountData::parse`

The state of the record is a `RefCell<&mut [u8]>` over the account data with one live shared
`Ref`, the address of the slice and the borrow state of the cell. It maps to the AccountInfo
world of the model with that data cell and one shared whole-data guard, acquired through the
common protocol (`Oracle.Switchboard.sampleState`, the constructor of the model of exactly this
world), and to `Args ⟨guard, layout, address⟩`. The checker decides the `requires` of the
contract (`Ready`) on that world through `requires_iff`; a record whose cell is not borrowed is
outside it and fails. The layout is read from the recorded `size_of`/`align_of` (3200 bytes;
16-byte alignment on the host is `i128Align16`).

The after-state of the model carries ghost guard identities and generations, which Rust does not
expose. The checker therefore decides that the registered relation `parse_run` admits an outcome
whose observable projection equals the record: the error variant, or the range of the returned
reference within the slice; the borrow state of the cell with its share count, the state once
the returned reference is released (Rust: dropped), and the bytes of the cell. `parse_run` is
the graph of `parse` (`parse_evaluated`), so this is decidable. -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.SwitchboardOnDemand

namespace SolanalibTest.Conformance.Library.Families.Instructions.Switchboard

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Oracle.Switchboard
open SolanalibTest.Conformance.Library.Borsh

abbrev run :=
  on_demand.accounts.pull_feed.PullFeedAccountData.parse_run

abbrev Out := Outcome State (Except ParseError FeedRef) Empty Empty

/-- The registered relation is the graph of the `parse` of the model. -/
theorem parse_evaluated (before : State) (args : Args) (o : Out) :
    run before args o ↔ match o with
      | .returned result after => parse before args = some (result, after)
      | .unwound e _ => nomatch e
      | .terminated e => nomatch e := by
  cases o with
  | returned result after => exact Iff.rfl
  | unwound e _ => exact nomatch e
  | terminated e => exact nomatch e

/-- What Rust shows of an outcome. -/
structure Observation where
  /-- The error variant, or the (offset, length) of the returned reference within the slice. -/
  result : Except ParseError (Nat × Nat)
  /-- The borrow state of the cell after the call: `free`, `shared` (one share), `shared N` or
  `exclusive`. Natively one share is the returned `Ref` (see `afterDrop`). -/
  borrow : String
  /-- The borrow state once the returned reference is dropped (for an error, unchanged). -/
  afterDrop : String
  /-- The bytes of the cell after the call. -/
  data : Solanalib.Runtime.Bytes
  deriving DecidableEq

def leaseName : Solanalib.Runtime.Lease → String
  | .free => "free"
  | .shared 1 => "shared"
  | .shared n => s!"shared {n}"
  | .exclusive => "exclusive"

/-- The data cell of the checked world. -/
def dataCell : Borrow.Handle := ⟨0⟩

/-- The current bytes of the data cell; `none` for a malformed world. -/
def cellData (state : State) : Option Solanalib.Runtime.Bytes :=
  match state.lookupCell dataCell with
  | some ⟨.data bytes, _⟩ => some bytes
  | _ => none

def observe : Out → Option Observation
  | .returned (.error e) after => do
    let data ← cellData after
    let lease := leaseName (after.lease dataCell)
    pure ⟨.error e, lease, lease, data⟩
  | .returned (.ok feed) after => do
    let data ← cellData after
    match Borrow.current after feed.guard with
    | .ok (.bytesRange offset length, _) =>
      let dropped := (Borrow.release after feed.guard).2
      pure ⟨.ok (offset, length), leaseName (after.lease dataCell), leaseName (dropped.lease
        dataCell), data⟩
    | _ => none
  | .unwound e _ => nomatch e
  | .terminated e => nomatch e

/-- The registered relation admits an outcome with exactly this observation. -/
def Admits (before : State) (args : Args) (observed : Observation) : Prop :=
  ∃ o, run before args o ∧ observe o = some observed

/-- The executable decision: compute `parse` and compare the projection. -/
def admitsFn (before : State) (args : Args) (observed : Observation) : Bool :=
  match parse before args with
  | some (result, after) => decide (observe (.returned result after) = some observed)
  | none => false

theorem admits_iff (before : State) (args : Args) (observed : Observation) :
    Admits before args observed ↔ admitsFn before args observed = true := by
  unfold admitsFn
  constructor
  · rintro ⟨o, ho, hobs⟩
    cases o with
    | returned result after =>
      rw [(parse_evaluated before args _).mp ho]
      exact decide_eq_true hobs
    | unwound e _ => exact nomatch e
    | terminated e => exact nomatch e
  · cases hp : parse before args with
    | none => intro h; exact absurd h Bool.false_ne_true
    | some p =>
      obtain ⟨result, after⟩ := p
      intro h
      exact ⟨.returned result after, (parse_evaluated before args _).mpr hp, of_decide_eq_true h⟩

instance (before : State) (args : Args) (observed : Observation) : Decidable (Admits before args
  observed) :=
  decidable_of_iff _ (admits_iff before args observed).symm

/-! ## The precondition -/

abbrev contract :=
  on_demand.accounts.pull_feed.PullFeedAccountData.parse_contract

/-- The checked world of a record: the data cell with the live shared guard of the argument when the
recorded borrow is `shared` (`sampleState`, through the common acquisition), and with no guard
at all when it is `free`. Both are valid borrow states. -/
def worldOf (shared : Bool) (bytes : Solanalib.Runtime.Bytes) : State :=
  if shared then sampleState bytes else freeState bytes

theorem worldOf_valid (shared : Bool) (bytes : Solanalib.Runtime.Bytes) : (worldOf shared
  bytes).Valid := by
  unfold worldOf
  split
  · exact sampleState_valid bytes
  · exact Borrow.State.valid_empty_slots _

/-- On the checked worlds, the `requires` of the registered contract (`Ready`) is the computable
condition that the guard of the argument is live and its data readable. -/
theorem requires_iff (shared : Bool) (bytes : Solanalib.Runtime.Bytes) (args : Args) :
    contract.requires (worldOf shared bytes) args ↔
      ((worldOf shared bytes).resolve args.guard).isSome ∧ (read (worldOf shared bytes)
        args.guard).isSome := by
  show Ready (worldOf shared bytes) args ↔ _
  constructor
  · rintro ⟨_, slot, data, hslot, hdata⟩
    exact ⟨by simp [hslot], by simp [hdata]⟩
  · rintro ⟨hslot, hdata⟩
    obtain ⟨slot, hs⟩ := Option.isSome_iff_exists.mp hslot
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp hdata
    exact ⟨worldOf_valid shared bytes, slot, data, hs, hd⟩

instance requiresDecidable (shared : Bool) (bytes : Solanalib.Runtime.Bytes) (args : Args) :
    Decidable (contract.requires (worldOf shared bytes) args) :=
  decidable_of_iff _ (requires_iff shared bytes args).symm

/-- The decision rejects: without a live guard (a `free` cell) the precondition fails. -/
theorem requires_rejects_free (bytes : Solanalib.Runtime.Bytes) (args : Args) :
    ¬ contract.requires (worldOf false bytes) args := by
  rw [requires_iff]
  simp [worldOf, freeState, Borrow.State.resolve, Borrow.State.lookupSlot]

def errorName : ParseError → String
  | .invalidDiscriminator => "InvalidDiscriminator"
  | .invalidData => "InvalidData"
  | .accountDeserializeError => "AccountDeserializeError"

def error (j : Json) : Result ParseError := do
  match ← j.getStr? with
  | "InvalidDiscriminator" => pure .invalidDiscriminator
  | "InvalidData" => pure .invalidData
  | "AccountDeserializeError" => pure .accountDeserializeError
  | other => throw s!"error {other} is not a ParseError"

def range (j : Json) : Result (Nat × Nat) := do
  pure (← (← field j "offset").getNat?, ← (← field j "len").getNat?)

def observationOf (j : Json) : Result (Option Observation) := do
  match ← (← field j "exit").getStr? with
  | "returned" =>
    let st ← field j "state"
    pure (some ⟨← asExcept error range (← field j "result"), ← (← field st "borrow").getStr?,
      ← (← field st "after_drop").getStr?, ← asBytes (← field st "data")⟩)
  | _ => pure none

def observationJson (o : Observation) : Json :=
  returnedJson (exceptJson (fun e => Json.str (errorName e))
      (fun (offset, length) => Json.mkObj [("offset", toJson offset), ("len", toJson length)])
        o.result)
    (Json.mkObj [("borrow", Json.str o.borrow), ("after_drop", Json.str o.afterDrop), (
      "data",
      bytesJson o.data)])

def layoutOf (c : Case) : Result Layout := do
  let l ← match c.layout with
    | some l => pure l
    | none => throw "missing layout"
  let size ← (← field l "size").getNat?
  let align ← (← field l "align").getNat?
  unless size = payloadSize do
    throw s!"layout mismatch: size {size}, the model payload is {payloadSize}"
  match align with
  | 16 => pure .i128Align16
  | 8 => pure .i128Align8
  | other => throw s!"layout mismatch: alignment {other}"

def checker : Checker where
  function := "switchboard_on_demand::on_demand::accounts::pull_feed::PullFeedAccountData::\
    parse"
  generics := []
  reference :=
    "Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed.PullFeedAccountData.p\
      arse_run"
  decides :=
    ["Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed.PullFeedAccountData.\
      parse_run"]
  decidesRequires :=
    ["Solanalib.Specs.SwitchboardOnDemand.on_demand.accounts.pull_feed.PullFeedAccountData.\
      parse_run"]
  check := fun c => do
    let bytes ← asBytes (← field c.state "data")
    let address ← (← field c.state "address").getNat?
    let shared ← match ← (← field c.state "borrow").getStr? with
      | "shared" => pure true
      | "free" => pure false
      | other => throw s!"unknown borrow state {other}"
    asUnit c.args
    let before := worldOf shared bytes
    let args : Args := ⟨⟨0, 0⟩, ← layoutOf c, address⟩
    unless decide (contract.requires (worldOf shared bytes) args) do
      throw "outside the precondition: the argument is not a live, readable guard"
    let expected := match parse before args with
      | some (result, after) => (observe (.returned result after)).map observationJson |>.getD
        Json.null
      | none => Json.null
    match ← observationOf c.outcome with
    | some observed => pure ⟨decide (Admits before args observed), expected⟩
    | none => pure ⟨false, expected⟩

end SolanalibTest.Conformance.Library.Families.Instructions.Switchboard
