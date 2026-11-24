/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SplToken2022Interface.Extensions
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Checks
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Unpack

set_option autoImplicit false

open Solanalib.Specs.SplToken2022Interface

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.UnpackChecks

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph)

/-- The complete registered reference name is supplied alongside its run.
Exact source releases remain selected by the corpus and checker keys. -/
abbrev Run := (model : Legacy.Unpacker) → (before : model.base.State) →
  (bytes : model.base.Reference) →
  Outcome model.base.State (Except Token.Error (ExtensionUnpacked model.base.Base
    model.base.Reference))
    model.base.Unwind model.base.Terminal → Prop

def baseIsMint (args : Json) : Result Bool := do
  match ← (← field args "base_kind").getStr? with
  | "mint" => pure true
  | "account" => pure false
  | _ => throw "base kind must be Mint or Account"

/-- Pack bytes record the logical returned base. The independent returned
tail comparison keeps its origin, offset, and exact bytes. -/
def normalizedOutcome (base : Extensions.BaseType) (outcome : Json) : Result Json := do
  unless (← (← field outcome "exit").getStr?) == "returned" do
    return outcome
  let value ← resultOf (fun result => do
    let baseBytes ← asBytes (← field result "base")
    let value ← match base.decode baseBytes with
      | .ok value => pure value
      | .error _ => throw "invalid returned packed base"
    let tail ← asBytes (← field result "tlv")
    let origin ← (← field result "origin").getStr?
    let offset ← uintField 64 result "offset"
    pure (Json.mkObj [("base", base.render value), ("tlv", bytesJson tail),
      ("origin", Json.str origin), ("offset", Lean.toJson offset)])) (← field outcome
        "result")
  let retained ← asBytes (← field outcome "state")
  pure (returnedJson (resultJson id value) (bytesJson retained))

def resultJson (base : Extensions.BaseType) (input : Bytes) :
    Except Token.Error (ExtensionUnpacked base.Base Bytes) → Json :=
  TokenInterface.resultJson fun value => Json.mkObj [
    ("base", base.render value.base), ("tlv", bytesJson (Extensions.tailBytes input value.tlv)),
    ("origin", match value.tlv with | .empty => "static" | .borrowed _ => "input"),
    ("offset", Lean.toJson (match value.tlv with
      | .empty => 0
      | .borrowed region => region.offset))]

def checker (rust referenceName : String) (needsByte : Bool) (reference : Run)
    (same : ∀ model before bytes final,
      reference model before bytes final ↔ Legacy.unpack needsByte model before bytes final) :
        Checker where
  function := rust ++ "::extension::StateWithExtensions::<'data, S>::unpack"
  generics := []
  reference := referenceName
  decides := [referenceName]
  check := fun c => do
    let base := if ← baseIsMint c.args then Extensions.mintBase else Extensions.accountBase
    let bytes ← asBytes c.state
    let value := Unpack.unpackF needsByte base.baseLength base.accountType base.decode [] bytes
    let computed : Outcome Unpack.Ledger (Unpack.ResultValue base.Base) Empty Empty :=
      .returned value.1 value.2
    let run := reference (Legacy.referenceUnpacker base.baseLength base.accountType base.decode) []
      bytes
    have graph : PGraph run (some computed) := by
      intro final
      exact (same _ _ _ final).trans
        ((Unpack.unpack_iff needsByte base.baseLength base.accountType base.decode [] bytes
          final).trans
          ⟨fun eq => congrArg some eq.symm, fun eq => (Option.some.inj eq).symm⟩)
    let normalized ← normalizedOutcome base c.outcome
    pure (Checks.projected run _ graph (Checks.returned (resultJson base bytes) (bytesJson bytes))
      { c with outcome := normalized })

/-- Token 8.0.1 rejects an empty tail after the marker. -/
def token8 : Checker := checker "spl_token_2022"
  "Solanalib.Specs.SplToken2022.extension.StateWithExtensions.unpack_run" true
  Solanalib.Specs.SplToken2022.extension.StateWithExtensions.unpack_run (fun _ _ _ _ => Iff.rfl)

def tlv : Checker where
  function :=
    "<spl_token_2022::extension::StateWithExtensions<'_, S> as \
      spl_token_2022::extension::BaseStateWithExtensions<S>>::get_tlv_data"
  generics := []
  reference := "Solanalib.Specs.SplToken2022.extension.StateWithExtensions.get_tlv_data_run"
  decides := ["Solanalib.Specs.SplToken2022.extension.StateWithExtensions.get_tlv_data_run"]
  check := fun c => do
    let bytes ← asBytes c.state
    let base := if ← baseIsMint c.args then Extensions.mintBase else Extensions.accountBase
    let parsed := (Unpack.unpackF true base.baseLength base.accountType base.decode [] bytes).1
    let before ← match parsed with
      | .ok value => pure value
      | .error _ => throw "stored TLV fixture must have a valid StateWithExtensions \
        receiver"
    let run := Solanalib.Specs.SplToken2022.extension.StateWithExtensions.get_tlv_data_run
      ⟨base.Base, Bytes⟩ before ()
    let computed : Outcome (ExtensionUnpacked base.Base Bytes) (ExtensionTailReference Bytes)
        Empty Empty := .returned before.tlv before
    have graph : PGraph run (some computed) := by
      intro final
      exact Functional.returnsOf_fn
        (fun (state : ExtensionUnpacked base.Base Bytes) (_ : Unit) => (state.tlv, state)) before
          () final
    pure (Checks.projected run _ graph (Checks.returned (fun tail => Json.mkObj [
      ("bytes", bytesJson (Extensions.tailBytes bytes tail)),
      ("offset", Lean.toJson (match tail with | .empty => 0 | .borrowed region => region.offset))])
        c.state) c)

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.UnpackChecks

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.UnpackChecks

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph)

/-- Interface 2.1.0 retains old allocation but admits that empty tail. -/
def interface2 : Checker := checker "spl_token_2022_interface"
  "Solanalib.Specs.SplToken2022Interface.extension.StateWithExtensions.unpack_owned_base_ru\
    n" false
  extension.StateWithExtensions.unpack_owned_base_run (fun _
    _ _ _ => Iff.rfl)

/-- Interface 3.0.1 shares the complete owned-base reference. -/
def interface3 : Checker := checker "spl_token_2022_interface"
  "Solanalib.Specs.SplToken2022Interface.extension.StateWithExtensions.unpack_owned_base_ru\
    n" false
  extension.StateWithExtensions.unpack_owned_base_run (fun _
    _ _ _ => Iff.rfl)

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.UnpackChecks
