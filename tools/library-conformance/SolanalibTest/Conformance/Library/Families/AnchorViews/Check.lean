/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Bindings
import SolanalibTest.Conformance.Library.Families.Anchor.World

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected ofModel withRequires
  withFrame
  boolField natField asPubkey pubkeyJson keyField)

def display (hasPayload : Bool) : Nat → Option Nat := if hasPayload then some else fun _ => none

def inputs (hasPayload savedOwner : Bool) (mode : Option Borrow.Mode) (c : Case) :
    Result (World Nat Effects) := do
  let s ← asSnapshot c.state
  unless s.payload.isSome = hasPayload do throw "wrong payload shape for this wrapper"
  pure (makeWorld (s.payload.getD 0) s mode savedOwner)

/-- Terminal calls expose no post-state. Their native detail and syscall log
are nevertheless checked: these fixtures only use process::abort with no log. -/
def terminalFrame (c : Case) : Result Bool := do
  if (← (← field c.outcome "exit").getStr?) = "terminated" then
    pure ((← field c.outcome "detail") == .null && (← asMessages c.outcome).isEmpty)
  else pure true

def profileFrame (debug : Bool) (c : Case) : Result Bool := do
  match c.args.getObjVal? "debug" with
  | .ok value => pure ((← value.getBool?) == debug)
  | .error _ => pure true

def parseNative {V : Type} (value : Json → Result V) (j : Json) :
    Result (Option (Outcome Snapshot V String String)) :=
  parseOutcome value asSnapshot some some j

def checked (function : String) (generics : List (String × String)) (model : String)
    (ready : Case → Result Bool) (run : Case → Result Verdict) : Checker :=
  withFrame [("terminal observation", terminalFrame)]
    (withRequires [(model, ready)] (ofModel function generics model run))

def keyChecker (function : String) (generics : List (String × String))
    (hasPayload savedOwner : Bool) : Checker :=
  let input := inputs hasPayload savedOwner (some .shared)
  checked function generics "Solanalib.Specs.AnchorLang.accounts.wrapper_key_run"
    (fun c => return keyReady (← input c) guard) fun c => do
      let s ← input c
      let recorded ← parseNative asPubkey c.outcome
      pure (decideProjected (Solanalib.Specs.AnchorLang.accounts.wrapper_key_run projectionTypes s
        guard) _
        (returnsGraph keyReference s guard)
        (project (display hasPayload) (fun _ (v : Solanalib.Runtime.Pubkey) => v) impossible
          impossible) recorded (render pubkeyJson))

def infoChecker (storage : InfoStorage) (binding : Binding (World Nat Effects) Borrow.Guard InfoRef
  Empty Empty) (function : String) (generics : List (String × String))
    (hasPayload savedOwner : Bool) : Checker :=
  let input := inputs hasPayload savedOwner (some .shared)
  checked function generics binding.model
    (fun c => return binding.ready (← input c) guard) fun c => do
      let s ← input c
      let recorded ← parseNative asInfoObs c.outcome
      pure (decideProjected (binding.run s guard) _ (binding.graph s guard)
        (project (display hasPayload) (observeInfo storage) impossible impossible) recorded (render
          infoObsJson))
def mutableChecker (debug : Bool) (function : String) (generics : List (String × String))
    (savedOwner : Bool) : Checker :=
  let input := inputs true savedOwner (some .exclusive)
  checked function generics "Solanalib.Specs.AnchorLang.accounts.account.Account.deref_mut_\
    run"
    (fun c => return mutableReady debug (← input c) guard) fun c => do
      let s ← input c
      let recorded ← parseNative asPayloadObs c.outcome
      pure (decideProjected (Solanalib.Specs.AnchorLang.accounts.account.Account.deref_mut_run
        (mutableTypes debug) s guard) _
        (mutable_graph debug s guard) (project some observePayload id id) recorded (render
          payloadObsJson))

def cloneChecker (storage : InfoStorage) (binding : Nat → Binding (World Nat Effects) Borrow.Guard
  Borrow.Handle String String) (function : String) (generics : List (String × String))
    (savedOwner : Bool) : Checker :=
  let input := inputs true savedOwner (some .shared)
  checked function generics (binding 0).model
    (fun c => return (binding (← natField c.args "mode")).ready (← input c) guard) fun c => do
      let s ← input c
      let mode ← natField c.args "mode"
      let recorded ← parseNative (asCloneObs true) c.outcome
      pure (decideProjected (binding mode |>.run s guard) _ (binding mode |>.graph s guard)
        (project some (observeClone storage some) id id) recorded (render (cloneObsJson true)))
def pubkeyChecker (function : String) : Checker :=
  ofModel function [] "Solanalib.Specs.AnchorLang.Pubkey.key_run" fun c => do
    let key ← keyField c.args "key"
    let _ ← asUnit c.state
    decideReturns (State := Unit) (Args := Solanalib.Runtime.Pubkey) (Value :=
      Solanalib.Runtime.Pubkey)
      (Solanalib.Specs.AnchorLang.Pubkey.key_run Unit) (fun s k => (k, s)) rfl
      () key asPubkey asUnit pubkeyJson (fun _ => .null) c.outcome

def infoInputs (c : Case) : Result (World Unit Effects) := do
  let s ← asSnapshot c.state
  unless s.payload.isNone do throw "an info-only wrapper has no decoded payload"
  pure (makeWorld () s (some .shared) false)

def infoCloneChecker (storage : InfoStorage) (binding : Binding (World Unit Effects) Borrow.Guard
  Borrow.Handle Empty String) (function : String) (generics : List (String × String)) : Checker :=
  checked function generics binding.model
    (fun c => return binding.ready (← infoInputs c) guard) fun c => do
      let s ← infoInputs c
      let recorded ← parseNative (asCloneObs false) c.outcome
      pure (decideProjected (binding.run s guard) _ (binding.graph s guard)
        (project (fun _ => none) (observeClone storage (fun _ => none)) impossible id)
        recorded (render (cloneObsJson false)))

def lamportsInputs (c : Case) : Result (Lamports.S × Lamports.Args) := do
  let s ← asSnapshot c.state
  unless s.payload.isNone do throw "Lamports holder has no decoded payload"
  pure (Lamports.initial s (← boolField c.args "conflict"),
    ⟨toInfo s.effects.account, ← boolField c.args "change", ← boolField c.args "panics"⟩)

def lamportsChecker (function : String) (generics : List (String × String)) : Checker :=
  checked function generics "Solanalib.Specs.AnchorLang.Lamports.get_lamports_run"
    (fun c => do let (s, args) ← lamportsInputs c; pure (lamportsReady s args)) fun c => do
      let (s, args) ← lamportsInputs c
      let recorded ← parseNative (asUInt 64) c.outcome
      pure (decideProjected (Solanalib.Specs.AnchorLang.Lamports.get_lamports_run Lamports.types s
        args) _
        (Lamports.run_graph s args) Lamports.project recorded (render toJson))


end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected ofModel withRequires
  withFrame
  boolField natField asPubkey pubkeyJson keyField)

def moveChecker (binding : Binding (World Nat Effects) Borrow.Handle Nat Empty String) (function :
  String) (generics : List (String × String))
    (savedOwner : Bool) : Checker :=
  let input := inputs true savedOwner none
  checked function generics binding.model
    (fun c => return binding.ready (← input c) handle) fun c => do
      let s ← input c
      let recorded ← parseNative (asUInt 64) c.outcome
      pure (decideProjected (binding.run s handle) _ (binding.graph s handle)
        (project some (fun _ v => v) impossible id) recorded (render toJson))
end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected ofModel withRequires
  withFrame
  boolField natField asPubkey pubkeyJson keyField)

def payloadChecker (function : String) (generics : List (String × String)) (savedOwner : Bool) :
  Checker :=
  let input := inputs true savedOwner (some .shared)
  checked function generics "Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar.deref_run"
    (fun c => return payloadReady (← input c) guard) fun c => do
      let s ← input c
      let recorded ← parseNative asPayloadObs c.outcome
      pure (decideProjected (Solanalib.Specs.AnchorLang.accounts.sysvar.Sysvar.deref_run
        projectionTypes s guard) _
        (returnsGraph (payloadReference false) s guard)
        (project some observePayload impossible impossible) recorded (render payloadObsJson))

def setChecker (function : String) (generics : List (String × String)) (savedOwner : Bool) :
  Checker :=
  let input := inputs true savedOwner (some .exclusive)
  checked function generics "Solanalib.Specs.AnchorLang.accounts.account.Account.set_inner_\
    run"
    (fun c => do
      let replacement ← asUInt 64 (← field c.args "replacement")
      return setReady (← natField c.args "mode") (← input c) (guard, replacement)) fun c => do
      let s ← input c
      let mode ← natField c.args "mode"
      let args := (guard, ← asUInt 64 (← field c.args "replacement"))
      let recorded ← parseNative asUnit c.outcome
      pure (decideProjected (Solanalib.Specs.AnchorLang.accounts.account.Account.set_inner_run
        (setTypes mode) s args) _
        (setInner_graph mode s args) (project some (fun _ (v : Unit) => v) id id) recorded (render
          (fun _ => .null)))

end SolanalibTest.Conformance.Library.Families.AnchorViews
