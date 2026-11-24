/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.OwnedGraph
import Solanalib.Specs.Core.AnchorErrorOperationsWitnesses

/-!
Executable graphs of the registered versioned error operations. These reuse
the common callback/cleanup graph lemmas. ProgramError remains generic so the
legacy String owner is present in every actual destruction and comparison.
No Rust implementation is proved here.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorErrorOperations
open SolanalibTest.Conformance.Library.Families.Anchor

structure OpsFn (S Program Str Box T : Type) where
  copy : S → String → Option (Outcome S Str Empty T)
  format : S → String → Option (Outcome S Str Empty T)
  newBox : S → Payload Program Str → Option (Outcome S Box Empty T)
  dropString : S → Str → Option (Outcome S Unit Empty T)
  freeBox : S → Box → Option (Outcome S Unit Empty T)

structure OpsGraph {S Program Str Box T : Type}
    (ops : Ops S Program Str Box T) (fn : OpsFn S Program Str Box T) : Prop where
  copy : ∀ state argument, PGraph (ops.copyLiteral state argument) (fn.copy state argument)
  format : ∀ state argument, PGraph (ops.formatLiteral state argument) (fn.format state argument)
  newBox : ∀ state argument, PGraph (ops.newBox state argument) (fn.newBox state argument)
  dropString : ∀ state argument, PGraph (ops.dropString state argument) (fn.dropString state
    argument)
  freeBox : ∀ state argument, PGraph (ops.freeBox state argument) (fn.freeBox state argument)

namespace Fn

variable {S Program Str Box T : Type}

def drops (fn : OpsFn S Program Str Box T) (resources : List Str) :
    List (S → Option (Outcome S Unit Empty T)) := resources.map fun resource state =>
  fn.dropString state resource

theorem drops_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) : ∀ resources : List Str,
    PGraph.DropsGraph (resources.map fun resource state outcome =>
      ops.dropString state resource outcome) (drops fn resources)
  | [] => trivial
  | resource :: rest => ⟨fun state => graph.dropString state resource, drops_graph graph rest⟩

def dropStrings (fn : OpsFn S Program Str Box T) (resources : List Str) (before : S) :
    Option (Outcome S Unit Empty T) :=
  PGraph.cleanupFn OwnedFn.noDoubleFn (drops fn resources) (.returned () before)

theorem dropStrings_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (resources : List Str) (before : S) :
    PGraph (AnchorErrorOperations.dropStrings ops resources before ())
      (dropStrings fn resources before) :=
  PGraph.cleanup OwnedFn.noDouble_graph _ _ (drops_graph graph resources) _

def fromPayload (storage : Storage) (fn : OpsFn S Program Str Box T) (before : S)
    (payload : Payload Program Str) : Option (Outcome S (Error storage Program Str Box) Empty T) :=
  match storage with
  | .inline => some (.returned payload before)
  | .boxed => (fn.newBox before payload).map (Outcome.map AnchorErrorOwned.Error.mk)

theorem fromPayload_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (storage : Storage) (before : S) (payload : Payload Program Str) :
    PGraph (AnchorErrorOperations.fromPayload storage ops before payload)
      (fromPayload storage fn before payload) := by
  cases storage with
  | inline => exact PGraph.eq_left _
  | boxed => exact PGraph.map AnchorErrorOwned.Error.mk (graph.newBox before payload)

def fromProgram (storage : Storage) (fn : OpsFn S Program Str Box T) (before : S)
    (program : Program) : Option (Outcome S (Error storage Program Str Box) Empty T) :=
  fromPayload storage fn before (.program ⟨program, none, none⟩)

theorem fromProgram_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (storage : Storage) (before : S) (program : Program) :
    PGraph (AnchorErrorOperations.fromProgram storage ops before program)
      (fromProgram storage fn before program) := fromPayload_graph graph storage before _

def fromCode (storage : Storage) (fn : OpsFn S Program Str Box T) (before : S) (code : Code) :
    Option (Outcome S (Error storage Program Str Box) Empty T) :=
  (fn.copy before code.name).bind (PGraph.bindK fun name afterName =>
    (fn.format afterName code.message).bind (PGraph.bindK fun message afterMessage =>
      fromPayload storage fn afterMessage (.anchor ⟨name, code.number, message, none, none⟩)))

theorem fromCode_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (storage : Storage) (before : S) (code : Code) :
    PGraph (AnchorErrorOperations.fromCode storage ops before code)
      (fromCode storage fn before code) :=
  PGraph.bind (graph.copy before _) fun name afterName =>
    PGraph.bind (graph.format afterName _) fun message afterMessage =>
      fromPayload_graph graph storage afterMessage
        (.anchor ⟨name, code.number, message, none, none⟩)

def update (storage : Storage) (ops : Ops S Program Str Box T)
    (change : Payload Program Str → Payload Program Str) (before : S)
    (error : Error storage Program Str Box) : Option (Outcome S (Error storage Program Str Box)
      Empty T) :=
  match storage with
  | .inline => some (.returned (change error) before)
  | .boxed => (ops.currentBox before error.resource).bind fun current =>
      (ops.writeBox before error.resource (change current)).map fun after => .returned error after

theorem update_graph (storage : Storage) (ops : Ops S Program Str Box T)
    (change : Payload Program Str → Payload Program Str) (before : S)
    (error : Error storage Program Str Box) :
    PGraph (updatePayload storage ops change before error) (update storage ops change before error)
      := by
  cases storage with
  | inline => exact PGraph.eq_left _
  | boxed =>
    apply PGraph.congr (PGraph.exists_step (PGraph.ofOption (ops.currentBox before error.resource))
      (fun current => PGraph.exists_eq' (fun after =>
        (Outcome.returned error after : Outcome S (Error .boxed Program Str Box) Empty T))
        (PGraph.ofOption (ops.writeBox before error.resource (change current)))))
    intro outcome
    constructor
    · rintro ⟨current, after, read, written, result⟩
      exact ⟨current, read, after, written, result⟩
    · rintro ⟨current, read, after, written, result⟩
      exact ⟨current, after, read, written, result⟩

def withCompared (storage : Storage) (ops : Ops S Program Str Box T)
    (fn : OpsFn S Program Str Box T) (compared : Option (Compared Str)) (before : S)
    (error : Error storage Program Str Box) : Option (Outcome S (Error storage Program Str Box)
      Empty T) :=
  (currentPayload storage ops before error).bind fun current =>
    (dropStrings fn (AnchorErrorOwned.comparedStrings current.compared) before).bind
      (PGraph.bindK fun _ after => update storage ops (Payload.withCompared compared) after error)

theorem withCompared_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (storage : Storage) (compared : Option (Compared Str)) (before : S)
    (error : Error storage Program Str Box) :
    PGraph (AnchorErrorOperations.withCompared storage ops compared before error)
      (withCompared storage ops fn compared before error) := by
  apply PGraph.exists_step (PGraph.ofOption _)
  intro current
  exact PGraph.bind (dropStrings_graph graph _ before) fun _ after =>
    update_graph storage ops _ after error

def withOrigin (storage : Storage) (ops : Ops S Program Str Box T)
    (fn : OpsFn S Program Str Box T) (origin : Option (Origin Str)) (before : S)
    (error : Error storage Program Str Box) : Option (Outcome S (Error storage Program Str Box)
      Empty T) :=
  (currentPayload storage ops before error).bind fun current =>
    (dropStrings fn (AnchorErrorOwned.originStrings current.origin) before).bind
      (PGraph.bindK fun _ after => update storage ops (Payload.withOrigin origin) after error)

theorem withOrigin_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (storage : Storage) (origin : Option (Origin Str)) (before : S)
    (error : Error storage Program Str Box) :
    PGraph (AnchorErrorOperations.withOrigin storage ops origin before error)
      (withOrigin storage ops fn origin before error) := by
  apply PGraph.exists_step (PGraph.ofOption _)
  intro current
  exact PGraph.bind (dropStrings_graph graph _ before) fun _ after =>
    update_graph storage ops _ after error

def drop (storage : Storage) (ops : Ops S Program Str Box T) (fn : OpsFn S Program Str Box T)
    (before : S) (error : Error storage Program Str Box) : Option (Outcome S Unit Empty T) :=
  match storage with
  | .inline => dropStrings fn (error.strings ops.programStrings) before
  | .boxed => (ops.currentBox before error.resource).bind fun current =>
      (dropStrings fn (current.strings ops.programStrings) before).bind
        (PGraph.bindK fun _ after => fn.freeBox after error.resource)

theorem drop_graph {ops : Ops S Program Str Box T} {fn : OpsFn S Program Str Box T}
    (graph : OpsGraph ops fn) (storage : Storage) (before : S)
    (error : Error storage Program Str Box) :
    PGraph (AnchorErrorOperations.drop storage ops before error) (drop storage ops fn before error)
      := by
  cases storage with
  | inline => exact dropStrings_graph graph _ before
  | boxed =>
    apply PGraph.exists_step (PGraph.ofOption _)
    intro current
    exact PGraph.bind (dropStrings_graph graph _ before) fun _ after => graph.freeBox after _

end Fn

end SolanalibTest.Conformance.Library.Families.AnchorOperations
