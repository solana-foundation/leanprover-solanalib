/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Graph

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews.Lamports

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

abbrev S := AccountInfo.State × Effects

structure Args where
  info : AccountInfo.Value
  change : Bool
  panics : Bool

def initial (snapshot : Snapshot) (conflict : Bool) : S :=
  (⟨[⟨.lamports (UInt64.ofNat snapshot.effects.account.lamports), policy⟩,
      ⟨.data snapshot.effects.account.data, policy⟩],
    if conflict then [some ⟨handle, .exclusive, 0, .whole⟩] else []⟩,
    snapshot.effects)

/-- The AsRef of the fixture may write through the lamports RefCell before
returning its original AccountInfo. A conflicting write unwinds at that borrow. -/
def asRefFn (before : S) (args : Args) : Outcome S AccountInfo.Value String String :=
  let logged := (before.1, { before.2 with trace := before.2.trace ++ ["as_ref"] })
  let changed : Outcome S Unit String String :=
    if args.change then
      match Borrow.acquire logged.1 args.info.lamports .exclusive .whole with
      | (.error _, during) => .unwound "RefCell already borrowed" (during, logged.2)
      | (.ok loan, during) =>
        let written := (Borrow.write during loan (.lamports 99)).2
        let finished := (Borrow.release written loan).2
        .returned () (finished, logged.2)
    else .returned () logged
  match changed with
  | .returned () after =>
    if args.panics then .unwound "script as_ref" after else .returned args.info after
  | .unwound r after => .unwound r after
  | .terminated r => .terminated r

def panicFn (s : S) (_ : AccountInfo.Panic) : Outcome S Empty String String :=
  .unwound "RefCell already mutably borrowed" s

def types : AnchorViewsLamports.Types :=
  ⟨Effects, Args, String, String, Callback.ofFunction asRefFn, Callback.ofFunction panicFn⟩

def readFn (s : S) (info : AccountInfo.Value) : Option (Outcome S Nat String String) :=
  match AccountInfo.observe .lamports s.1 info with
  | (.value value, after) => some (.returned value (after, s.2))
  | (.borrowFailed, after) =>
    (some (panicFn (after, s.2) .borrowFailed)).map (Outcome.map fun e : Empty => nomatch e)
  | (.malformed, _) => none

theorem read_graph (s : S) (info : AccountInfo.Value) :
    PGraph (AnchorViewsLamports.read types s info) (readFn s info) := by
  unfold AnchorViewsLamports.read readFn
  cases h : AccountInfo.observe .lamports s.1 info with
  | mk result after =>
    cases result with
    | value value => exact PGraph.eq_left _
    | borrowFailed => exact PGraph.map _ (PGraph.ofFunction panicFn _ _)
    | malformed => exact PGraph.false

def runFn (s : S) (args : Args) : Option (Outcome S Nat String String) :=
  (some (asRefFn s args)).bind (PGraph.bindK fun info after => readFn after info)

theorem run_graph (s : S) (args : Args) :
    PGraph (AnchorViewsLamports.run types s args) (runFn s args) :=
  PGraph.bind (PGraph.ofFunction asRefFn s args) fun info after => read_graph after info

def typedB (state : AccountInfo.State) (info : AccountInfo.Value) : Bool :=
  match state.lookupCell info.lamports with
  | some ⟨.lamports _, _⟩ => true
  | _ => false

theorem typedB_iff (state : AccountInfo.State) (info : AccountInfo.Value) :
    typedB state info = true ↔ AccountInfo.ObservationReady .lamports state info := by
  unfold typedB AccountInfo.ObservationReady
  cases h : state.lookupCell info.lamports with
  | none => simp [AccountInfo.Observation.handle, h]
  | some cell =>
    rcases cell with ⟨content, p⟩
    cases content <;> simp [AccountInfo.Observation.handle, AccountInfo.Observation.project, h]

def readyB (s : S) (args : Args) : Bool :=
  match asRefFn s args with
  | .returned info after => typedB after.1 info
  | _ => true

theorem readyB_iff (s : S) (args : Args) :
    readyB s args = true ↔ AnchorViewsLamports.Ready types s args := by
  unfold AnchorViewsLamports.Ready types Callback.ofFunction readyB
  cases h : asRefFn s args with
  | returned info after => simpa [h] using typedB_iff after.1 info
  | unwound r after => simp [h]
  | terminated t => simp [h]

def observe (s : S) : Snapshot :=
  let balance := (s.1.lookupCell handle).bind fun cell => match cell.value with
    | .lamports n => some n.toNat
    | _ => none
  let bytes := (s.1.lookupCell ⟨1⟩).bind fun cell => match cell.value with
    | .data bs => some bs
    | _ => none
  ⟨none, { s.2 with account := { s.2.account with
    lamports := balance.getD 0, data := bytes.getD [] } }⟩

def project : Outcome S Nat String String → Outcome Snapshot Nat String String
  | .returned value s => .returned value (observe s)
  | .unwound reason s => .unwound reason (observe s)
  | .terminated reason => .terminated reason

end SolanalibTest.Conformance.Library.Families.AnchorViews.Lamports
