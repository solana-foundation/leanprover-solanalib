/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Sizing
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.NewLength
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.KeyCleanup

set_option autoImplicit false

open Solanalib.Specs
open Solanalib.Specs.SplToken2022
open Solanalib.Specs.SplToken2022Interface

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Checks

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected)

/-- Reuse the existential projection check of the harness. The recorded state
keeps the source receiver; physical allocator counters are tested natively. -/
def projected {O : Type} (run : O → Prop) (computed : Option O) (graph : PGraph run computed)
    (observe : O → Json) (c : Case) : Verdict :=
  decideProjected run computed graph (fun outcome => observe outcome == c.outcome)
    (some true) (fun _ => (computed.map observe).getD Json.null)

def returned {S V : Type} (encode : V → Json) (state : Json) : Outcome S V Empty Empty → Json
  | .returned value _ => returnedJson (encode value) state
  | .unwound reason _ => reason.elim
  | .terminated reason => reason.elim

def kinds (j : Json) : Result (List Legacy.Kind) :=
  listField j "types" fun value => do
    let tag ← value.getNat?
    match Legacy.decodeType tag with
    | none => throw s!"unsupported old extension tag {tag}"
    | some kind =>
      if old : kind.tag < 28 then pure ⟨kind, old⟩
      else throw "decoded extension is outside the selected version"

def types : Checker where
  function := "spl_token_2022" ++ "::extension::BaseStateWithExtensions::get_extension_type\
    s"
  generics := []
  reference := "Solanalib.Specs.SplToken2022" ++
    ".extension.BaseStateWithExtensions.get_extension_types_run"
  decides := ["Solanalib.Specs.SplToken2022" ++
    ".extension.BaseStateWithExtensions.get_extension_types_run"]
  check := fun c => do
    let bytes ← asBytes c.state
    let _ ← Values.noArgs c.args
    let run :=
      extension.BaseStateWithExtensions.get_extension_types_run
        (Operational.Reader bytes) [] ()
    have graph : PGraph run (Operational.typesF bytes []) := by
      exact Operational.types_fn bytes []
    pure (projected run _ graph (fun outcome =>
      match Extensions.typesObs outcome with
      | some value => returnedJson (resultJson Extensions.typesJson value) c.state
      | none => Json.null) c)

def accountLength : Checker where
  function := "spl_token_2022" ++ "::extension::ExtensionType::try_calculate_account_len"
  generics := []
  reference := "Solanalib.Specs.SplToken2022" ++
    ".extension.ExtensionType.try_calculate_account_len_run"
  decides := ["Solanalib.Specs.SplToken2022" ++
    ".extension.ExtensionType.try_calculate_account_len_run"]
  check := fun c => do
    let _ ← asUnit c.state
    let input ← kinds c.args
    let baseLength ← uintField 64 c.args "base_length"
    let run := SplToken2022.extension.ExtensionType.try_calculate_account_len_run
        ⟨Legacy.typeArrayReference, baseLength⟩ [] input
    have graph : PGraph run (Sizing.sizeF baseLength input []) := by
      exact Sizing.size_fn baseLength input []
    pure (projected run _ graph (returned (resultJson Lean.toJson) c.state) c)

def newLength : Checker where
  function :=
    "spl_token_2022::extension::BaseStateWithExtensions::try_get_new_account_len_for_variab\
      le_len_extension"
  generics := []
  reference :=
    "Solanalib.Specs.SplToken2022.extension.BaseStateWithExtensions.try_get_new_account_len\
      _for_variable_len_extension_run"
  decides :=
    ["Solanalib.Specs.SplToken2022.extension.BaseStateWithExtensions.try_get_new_account_le\
      n_for_variable_len_extension_run"]
  check := fun c => do
    let bytes ← asBytes c.state
    let args := (← uintField 64 c.args "length", ← boolField c.args "measure_error")
    let run :=
      extension.BaseStateWithExtensions.try_get_new_account_len_for_variable_len_extension_run
      (NewLength.index bytes) [] args
    pure (projected run (NewLength.runF bytes [] args) (NewLength.run_fn bytes [] args)
      (returned (resultJson Lean.toJson) c.state) c)

def extension : Checker where
  function := "spl_token_2022::extension::BaseStateWithExtensions::get_extension"
  generics := []
  reference := "Solanalib.Specs.SplToken2022.extension.BaseStateWithExtensions.get_extensio\
    n_run"
  decides := ["Solanalib.Specs.SplToken2022.extension.BaseStateWithExtensions.get_extension\
    _run"]
  check := fun c => do
    let receiver : ExtensionReceiver := ⟨.mint, 0, ← asBytes c.state⟩
    unless (← natField c.args "tag") == 1 do throw "fixture V must be TransferFeeConfig"
    let run := extension.BaseStateWithExtensions.get_extension_run
      extension.BaseStateWithExtensions.get_extension_sample receiver
        ()
    let result := Legacy.getDefaultExtension transferFeeConfigRepresentation receiver
    let outcome : Outcome ExtensionReceiver _ Empty Empty := .returned result receiver
    have graph : PGraph run (some outcome) := by
      intro final
      exact (Legacy.getDefaultExtension_iff transferFeeConfigRepresentation receiver final).trans
        ⟨fun eq => by rw [eq], fun eq => (Option.some.inj eq).symm⟩
    pure (projected run _ graph (returned (resultJson fun reference => Json.mkObj [
      ("bytes", bytesJson reference.reference.view.bytes),
      ("offset", Lean.toJson reference.reference.view.offset)]) c.state) c)

theorem key_graph (hook : Bool) (receiver : ExtensionReceiver) :
    PGraph (Legacy.keyRun (Legacy.keySample hook) receiver ())
      (some (.returned (Legacy.keyDefaultResult hook receiver) receiver)) := by
  intro final
  exact (Legacy.keySample_iff hook receiver final).trans
    ⟨fun equality => congrArg some equality.symm,
      fun equality => (Option.some.inj equality).symm⟩

def key (hook : Bool) : Checker where
  function := "spl_token_2022::extension::" ++
    if hook then "transfer_hook::get_program_id" else "permanent_delegate::get_permanent_de\
      legate"
  generics := []
  reference := "Solanalib.Specs.SplToken2022.extension." ++
    if hook then "transfer_hook.get_program_id_run" else
      "permanent_delegate.get_permanent_delegate_run"
  decides := ["Solanalib.Specs.SplToken2022.extension." ++
    if hook then "transfer_hook.get_program_id_run" else
      "permanent_delegate.get_permanent_delegate_run"]
  check := fun c => do
    if c.args == KeyCleanup.args then return ← KeyCleanup.check hook c
    let _ ← Values.noArgs c.args
    let receiver : ExtensionReceiver := ⟨.mint, 0, ← asBytes c.state⟩
    let run := if hook then
      extension.transfer_hook.get_program_id_run (Legacy.keySample
        true) receiver () else
      extension.permanent_delegate.get_permanent_delegate_run
        (Legacy.keySample false) receiver ()
    let outcome : Outcome ExtensionReceiver _ Empty Empty :=
      .returned (Legacy.keyDefaultResult hook receiver) receiver
    have graph : PGraph run (some outcome) := by cases hook <;> exact key_graph _ receiver
    pure (projected run _ graph (returned (optionJson pubkeyJson) c.state) c)

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Checks

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Checks

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected)

def crate (olderInterface : Bool) : String :=
  if olderInterface then "spl_token_2022_interface" else "spl_token_2022"

def root (olderInterface : Bool) : String :=
  if olderInterface then "Solanalib.Specs.SplToken2022Interface"
  else "Solanalib.Specs.SplToken2022"

def typesForVersion (olderInterface : Bool) : Checker where
  function := crate olderInterface ++ "::extension::BaseStateWithExtensions::get_extension_\
    types"
  generics := []
  reference := if olderInterface then
    "Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_\
      types_push_before_payload_run"
    else "Solanalib.Specs.SplToken2022.extension.BaseStateWithExtensions.get_extension_type\
      s_run"
  decides := [if olderInterface then
    "Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_\
      types_push_before_payload_run"
    else "Solanalib.Specs.SplToken2022.extension.BaseStateWithExtensions.get_extension_type\
      s_run"]
  check := fun c => do
    let bytes ← asBytes c.state
    let _ ← Values.noArgs c.args
    let run := if olderInterface then
      extension.BaseStateWithExtensions.get_extension_types_push_before_payload_run
        (Operational.Reader bytes) [] () else
      extension.BaseStateWithExtensions.get_extension_types_run
        (Operational.Reader bytes) [] ()
    have graph : PGraph run (Operational.typesF bytes []) := by
      cases olderInterface <;> exact Operational.types_fn bytes []
    pure (projected run _ graph (fun outcome =>
      match Extensions.typesObs outcome with
      | some value => returnedJson (resultJson Extensions.typesJson value) c.state
      | none => Json.null) c)

def accountLengthForVersion (olderInterface : Bool) : Checker where
  function := crate olderInterface ++ "::extension::ExtensionType::try_calculate_account_le\
    n"
  generics := []
  reference := root olderInterface ++ ".extension.ExtensionType.try_calculate_account_len_r\
    un"
  decides := [root olderInterface ++ ".extension.ExtensionType.try_calculate_account_len_ru\
    n"]
  check := fun c => do
    let _ ← asUnit c.state
    let input ← kinds c.args
    let baseLength ← uintField 64 c.args "base_length"
    let run := if olderInterface then
      SplToken2022Interface.extension.ExtensionType.try_calculate_account_len_run
        ⟨Legacy.typeArrayReference, baseLength⟩ [] input else
      SplToken2022.extension.ExtensionType.try_calculate_account_len_run
        ⟨Legacy.typeArrayReference, baseLength⟩ [] input
    have graph : PGraph run (Sizing.sizeF baseLength input []) := by
      cases olderInterface <;> exact Sizing.size_fn baseLength input []
    pure (projected run _ graph (returned (resultJson Lean.toJson) c.state) c)

def required : Checker where
  function :=
    "spl_token_2022_interface::extension::ExtensionType::get_required_init_account_extensio\
      ns"
  generics := []
  reference :=
    "Solanalib.Specs.SplToken2022Interface.extension.ExtensionType.get_required_init_accoun\
      t_extensions_run"
  decides :=
    ["Solanalib.Specs.SplToken2022Interface.extension.ExtensionType.get_required_init_accou\
      nt_extensions_run"]
  check := fun c => do
    let _ ← asUnit c.state
    let input ← kinds c.args
    let run :=
      extension.ExtensionType.get_required_init_account_extensions_run
      Legacy.typeArrayReference [] input
    pure (projected run (Sizing.requiredF input []) (Sizing.required_fn input [])
      (fun outcome => match outcome with
      | .returned resource state => match state.current resource with
        | some values => returnedJson (Extensions.typesJson values) c.state
        | none => Json.null
      | .unwound reason _ => reason.elim
      | .terminated reason => reason.elim) c)

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Checks
