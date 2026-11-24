/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Common
import Solanalib.Specs.SplToken2022Interface.state.Mint

/-! Replay calls to the published concrete Mint::clone. Pack82 is only the
recording format of its five logical fields. The distinct source repr(C)
layout is checked separately and is never used as the account-data codec. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Clone

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.SplToken2022Interface.state

/-- Uninitialized values are valid Clone receivers; no Pack initialization
precondition is introduced by reading the canonical field recording. -/
def mint (value : Json) : Result Solanalib.Specs.Core.Token.Mint := do
  let raw ← asBytes value
  match unpackMintUnchecked raw with
  | .ok parsed => pure parsed
  | .error _ => throw "invalid packed Mint field recording"

def sourceLayout : Json := Json.mkObj [
  ("size", Lean.toJson (88 : Nat)), ("alignment", Lean.toJson (8 : Nat)),
  ("offsets", Lean.toJson ([0, 40, 48, 49, 52] : List Nat))]

def checker : Checker where
  function := "<spl_token_2022_interface::state::Mint as core::clone::Clone>::clone"
  generics := []
  reference := "Solanalib.Specs.SplToken2022Interface.state.Mint.cloneReference"
  decides := ["Solanalib.Specs.SplToken2022Interface.state.Mint.cloneReference"]
  check := fun c => do
    let before ← mint c.state
    unless c.args == Json.mkObj [] do
      throw "Mint::clone has no explicit arguments"
    let decided ← decideReturns (returnsOf Mint.cloneReference) Mint.cloneReference rfl
      before () mint mint (fun _ => c.state) (fun _ => c.state) c.outcome
    let expected := returnedJson c.state c.state
    pure ⟨decided.admitted && c.outcome == expected && c.layout == some sourceLayout, expected⟩

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Clone
