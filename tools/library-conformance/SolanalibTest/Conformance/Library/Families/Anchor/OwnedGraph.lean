/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Values
import Solanalib.Specs.Core.AnchorErrorOwnedCallbacks

/-!
# Graphs of the owned-error operations

`OpsGraph ops fn` states that every primitive String/Box dependency of an
`AnchorErrorOwned.Ops` is the graph of the matching partial function of
`fn`. The registered reference heap `AnchorErrorOwned.Reference.ops` has such
functions (`refFn`), and focusing preserves them. From these, each owned error
operation used by the Anchor models (`buildCode`, `fromProgram`, `fromAnchor`,
`withPubkeys`, `dropError`, `dropStrings`) gets its graph from its own
definition.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace SolanalibTest.Conformance.Library.Families.Anchor

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorErrorOwned

structure OpsFn (S Str Box T : Type) where
  copy : S → String → Option (Outcome S Str Empty T)
  format : S → String → Option (Outcome S Str Empty T)
  newBox : S → Payload Str → Option (Outcome S Box Empty T)
  dropString : S → Str → Option (Outcome S Unit Empty T)
  freeBox : S → Box → Option (Outcome S Unit Empty T)

structure OpsGraph {S Str Box T : Type} (ops : Ops S Str Box T) (fn : OpsFn S Str Box T) : Prop
  where
  copy : ∀ s a, PGraph (ops.copyLiteral s a) (fn.copy s a)
  format : ∀ s a, PGraph (ops.formatLiteral s a) (fn.format s a)
  newBox : ∀ s a, PGraph (ops.newBox s a) (fn.newBox s a)
  dropString : ∀ s a, PGraph (ops.dropString s a) (fn.dropString s a)
  freeBox : ∀ s a, PGraph (ops.freeBox s a) (fn.freeBox s a)

namespace OwnedFn

variable {S Str Box T : Type}

/-- Callback-free `Owned.cleanup` over String drops (`noDouble`: Empty unwind). -/
def noDoubleFn : S → Empty → Empty → Option T := fun _ r _ => nomatch r

theorem noDouble_graph : ∀ (s : S) (r r' : Empty), PGraph (noDouble (Terminal := T) s r r')
  (noDoubleFn s r r') :=
  fun _ r _ => nomatch r

def dropFns (fn : OpsFn S Str Box T) (resources : List Str) : List (S → Option (Outcome S Unit
  Empty T)) :=
  resources.map fun r s => fn.dropString s r

theorem drops_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn) :
    ∀ resources : List Str, PGraph.DropsGraph
      (resources.map fun r s result => ops.dropString s r result) (dropFns fn resources)
  | [] => trivial
  | r :: rs => ⟨fun s => h.dropString s r, drops_graph h rs⟩

def dropStringsFn (fn : OpsFn S Str Box T) (resources : List Str) (before : S) :
    Option (Outcome S Unit Empty T) :=
  PGraph.cleanupFn noDoubleFn (dropFns fn resources) (.returned () before)

theorem dropStrings_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn)
    (resources : List Str) (before : S) :
    PGraph (dropStrings ops resources before ()) (dropStringsFn fn resources before) :=
  PGraph.cleanup noDouble_graph _ _ (drops_graph h resources) _

def fromAnchorFn (fn : OpsFn S Str Box T) (before : S) (payload : AnchorPayload Str) :
    Option (Outcome S (Error Box) Empty T) :=
  (fn.newBox before (.anchor payload)).map (Outcome.map Error.mk)

theorem fromAnchor_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn)
    (before : S) (payload : AnchorPayload Str) :
    PGraph (fromAnchor ops before payload) (fromAnchorFn fn before payload) :=
  PGraph.map Error.mk (h.newBox before _)

def fromProgramFn (fn : OpsFn S Str Box T) (before : S) (error : ProgramError.Value) :
    Option (Outcome S (Error Box) Empty T) :=
  (fn.newBox before (.program ⟨error, none, none⟩)).map (Outcome.map Error.mk)

theorem fromProgram_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn)
    (before : S) (error : ProgramError.Value) :
    PGraph (fromProgram ops before error) (fromProgramFn fn before error) :=
  PGraph.map Error.mk (h.newBox before _)

def buildCodeFn (fn : OpsFn S Str Box T) (before : S) (code : Code) :
    Option (Outcome S (Error Box) Empty T) :=
  (fn.copy before code.name).bind (PGraph.bindK fun name afterName =>
    (fn.format afterName code.message).bind (PGraph.bindK fun message afterMessage =>
      fromAnchorFn fn afterMessage ⟨name, code.number, message, none, none⟩))

theorem buildCode_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn)
    (before : S) (code : Code) :
    PGraph (buildCode ops before code) (buildCodeFn fn before code) :=
  PGraph.bind (h.copy before _) fun name afterName =>
    PGraph.bind (h.format afterName _) fun message afterMessage =>
      fromAnchor_graph h afterMessage _

def withPubkeysFn (fn : OpsFn S Str Box T) (ops : Ops S Str Box T) (before : S)
    (args : Error Box × Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey) : Option (Outcome S
      (Error Box) Empty T) :=
  (ops.currentBox before args.1.resource).bind fun payload =>
    (dropStringsFn fn (comparedStrings payload.compared) before).bind (PGraph.bindK fun _
      afterDrops =>
      (ops.currentBox afterDrops args.1.resource).bind fun actual =>
        (ops.writeBox afterDrops args.1.resource (actual.withPubkeys args.2.1 args.2.2)).bind fun
          after =>
          some (.returned args.1 after))

theorem withPubkeys_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn)
    (before : S) (args : Error Box × Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey) :
    PGraph (withPubkeys ops before args) (withPubkeysFn fn ops before args) := by
  obtain ⟨error, left, right⟩ := args
  apply PGraph.exists_step (PGraph.ofOption _)
  intro payload
  apply PGraph.bind (dropStrings_graph h _ before)
  intro _ afterDrops
  apply PGraph.exists_step (PGraph.ofOption _)
  intro actual
  apply PGraph.exists_step (PGraph.ofOption _)
  intro after
  exact PGraph.eq_left _

def dropErrorFn (fn : OpsFn S Str Box T) (ops : Ops S Str Box T) (error : Error Box) (before : S) :
    Option (Outcome S Unit Empty T) :=
  (ops.currentBox before error.resource).bind fun payload =>
    (dropStringsFn fn payload.strings before).bind (PGraph.bindK fun _ afterFields =>
      fn.freeBox afterFields error.resource)

theorem dropError_graph {ops : Ops S Str Box T} {fn : OpsFn S Str Box T} (h : OpsGraph ops fn)
    (error : Error Box) (before : S) :
    PGraph (dropError ops error before) (dropErrorFn fn ops error before) := by
  apply PGraph.exists_step (PGraph.ofOption _)
  intro payload
  exact PGraph.bind (dropStrings_graph h _ before) fun _ afterFields => h.freeBox afterFields _

/-- `AnchorErrorOwned.liftOutcome` on outcomes. -/
def liftO {V U : Type} : Outcome S V Empty T → Outcome S V U T
  | .returned v s => .returned v s
  | .unwound r _ => nomatch r
  | .terminated t => .terminated t

theorem lift_graph {A V U : Type} {run : Callback.Run S A V Empty T} {f : Option (Outcome S V Empty
  T)}
    {b : S} {a : A} (hrun : PGraph (run b a) f) :
    PGraph (lift (Unwind := U) run b a) (f.map liftO) := by
  apply PGraph.congr (PGraph.exists_eq liftO hrun)
  intro o
  apply exists_congr; intro i
  apply and_congr_right; intro _
  cases i with
  | returned v s => rfl
  | unwound r _ => exact nomatch r
  | terminated t => rfl

end OwnedFn

/-! ## The registered reference heap -/

namespace RefFn

open AnchorErrorOwned.Reference

def retireStringFn (before : Reference.State) (resource : StringId) :
    Option (Outcome Reference.State Unit Empty Failure) :=
  (currentString before resource).map fun text => .returned ()
    ⟨before.strings.set resource.index none, before.boxes, before.remaining,
      before.events ++ [.dropString resource text]⟩

def retireBoxFn (before : Reference.State) (resource : BoxId) :
    Option (Outcome Reference.State Unit Empty Failure) :=
  (currentBox before resource).map fun _ => .returned ()
    ⟨before.strings, before.boxes.set resource.index none, before.remaining,
      before.events ++ [.freeBox resource]⟩

def fn : OpsFn Reference.State StringId BoxId Failure where
  copy := fun s a => some (allocateString false s a)
  format := fun s a => some (allocateString true s a)
  newBox := fun s a => some (allocateBox s a)
  dropString := retireStringFn
  freeBox := retireBoxFn

theorem graph : OpsGraph Reference.ops fn where
  copy := fun s a => PGraph.ofFunction _ s a
  format := fun s a => PGraph.ofFunction _ s a
  newBox := fun s a => PGraph.ofFunction _ s a
  dropString := fun s r => PGraph.exists_eq' _ (PGraph.ofOption _)
  freeBox := fun s r => PGraph.exists_eq' _ (PGraph.ofOption _)

end RefFn

/-! ## Focused providers -/

def OpsFn.focus {Outer Inner Str Box T : Type} (fn : OpsFn Inner Str Box T)
    (part : Owned.Focus Outer Inner) : OpsFn Outer Str Box T where
  copy := fun s a => (fn.copy (part.get s) a).map (part.liftOutcome s)
  format := fun s a => (fn.format (part.get s) a).map (part.liftOutcome s)
  newBox := fun s a => (fn.newBox (part.get s) a).map (part.liftOutcome s)
  dropString := fun s a => (fn.dropString (part.get s) a).map (part.liftOutcome s)
  freeBox := fun s a => (fn.freeBox (part.get s) a).map (part.liftOutcome s)

theorem OpsGraph.focus {Outer Inner Str Box T : Type} {ops : Ops Inner Str Box T}
    {fn : OpsFn Inner Str Box T} (h : OpsGraph ops fn) (part : Owned.Focus Outer Inner) :
    OpsGraph (ops.focus part) (fn.focus part) where
  copy := fun s a => PGraph.focusLift part (h.copy _ a)
  format := fun s a => PGraph.focusLift part (h.format _ a)
  newBox := fun s a => PGraph.focusLift part (h.newBox _ a)
  dropString := fun s a => PGraph.focusLift part (h.dropString _ a)
  freeBox := fun s a => PGraph.focusLift part (h.freeBox _ a)

end SolanalibTest.Conformance.Library.Families.Anchor
