/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TransferHookResolution.Compute
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainIndex

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TransferHookResolution

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.TransferHookResolution
open Solanalib.Specs.Core.TransferHookResolution.Sample
open Solanalib.Specs.Core.Token (Error Bytes)
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims (VecPrims RcPrims
  ArrayPrims NoAgain)
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc
  (liftCloneF liftClone_fn liftDropF liftDrop_fn)
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv (eq_iff_some)

instance (clone : Bool) (state : Sample.State) (cell : Borrow.Handle) :
    Decidable (Sample.rcReady clone state cell) := by
  unfold Sample.rcReady
  infer_instance

def rcF (clone : Bool) (state : Sample.State) (field : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome Sample.State Unit Empty Nat) :=
  if Sample.rcReady clone state field.2 then
    some (.returned () (Sample.rcAfter clone state field.1 field.2)) else none

def rcPrims : RcPrims Sample.rcOps where
  cloneRcF := rcF true
  cloneRc_fn := by
    intro state field outcome
    by_cases ready : Sample.rcReady true state field.2 <;>
      simp only [Sample.rcOps, rcF, ready, ↓reduceIte, true_and, false_and]
    · exact eq_iff_some _ _
    · exact ⟨False.elim, fun h => by cases h⟩
  dropRcF := rcF false
  dropRc_fn := by
    intro state field outcome
    by_cases ready : Sample.rcReady false state field.2 <;>
      simp only [Sample.rcOps, rcF, ready, ↓reduceIte, true_and, false_and]
    · exact eq_iff_some _ _
    · exact ⟨False.elim, fun h => by cases h⟩

theorem sampleClone_fn (values : List AccountInfo.Value) :
    Fn (Sample.cloneInfos values) (forEachF (liftCloneF (U := Nat) rcPrims) values) := by
  induction values with
  | nil => intro s a o; exact eq_iff_some _ _
  | cons info rest ih =>
    intro s a o
    exact bind_fn (fun s _ o => liftClone_fn rcPrims s info o)
      (fun _ after o => ih after () o) s a o

theorem sampleDrop_fn (values : List AccountInfo.Value) :
    Fn (Sample.dropInfos values) (forEachF (liftDropF (U := Nat) rcPrims) values) := by
  induction values with
  | nil => intro s a o; exact eq_iff_some _ _
  | cons info rest ih =>
    intro s a o
    exact bind_fn (fun s _ o => liftDrop_fn rcPrims s info o)
      (fun _ after o => ih after () o) s a o

def infosPrims : VecPrims Sample.infosOps :=
  let base : VecPrims Sample.infoValuesOps := VecPrims.reference.focus Sample.infosFocus
  { base with
    extendF := fun before input =>
      (forEachF (liftCloneF (U := Nat) rcPrims) input.2 before ()).bind
        (thenOpt · fun _ after => base.extendF after input)
    extend_fn := fun before input outcome =>
      bind_fn (sampleClone_fn input.2) (fun _ after o => base.extend_fn after input o)
        before () outcome
    dropF := fun before resource => (Sample.infoValuesOps.current before resource).bind fun values
      =>
      (forEachF (liftDropF (U := Nat) rcPrims) values before ()).bind
        (thenOpt · fun _ after => base.dropF after resource)
    drop_fn := by
      intro before resource outcome
      apply SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims.exists_bind_iff
        (fun _ => Iff.rfl)
      intro values _
      exact bind_fn (sampleDrop_fn values) (fun _ after o => base.drop_fn after resource o)
        before () outcome }

/-- Every recorded request chooses its next explicit provider exit. -/
inductive PdaExit where
  | reply (value : Address.Operations.ZeroFindReply)
  | unwind (reason : Nat)
  | terminal (reason : Nat)

def pdaF (script : List PdaExit) (before : Sample.State) (request : Address.Syscall.PdaRequest) :
    Option (Outcome Sample.State Address.Operations.ZeroFindReply Nat Nat) := do
  let next ← script[before.2.pdaCalls.length]?
  let after := Sample.pdaAfter before request
  return match next with
    | .reply value => .returned value after
    | .unwind reason => .unwound reason after
    | .terminal reason => .terminated reason

/-- This concrete checker can execute all fixed/key-data extras and empty
PDA seed lists. Nonempty borrowed-seed storage is deliberately unsupported
by this index; the shared generic seed computation theorem is unrestricted. -/
def index (script : List PdaExit) : Types :=
  { Sample.types ⟨0, .zero, 255⟩ with
    pdaSyscall := fun before request outcome => pdaF script before request = some outcome }

def arrayPrims (script : List PdaExit) : ArrayPrims (index script).literalProvider where
  workF := fun before (count, values) =>
    if values.length < count then some (.returned .evaluate before)
    else if values.length = count then some (.returned .finish before) else none
  work_fn := by
    intro before input outcome
    rcases input with ⟨count, values⟩
    by_cases shorter : values.length < count
    · simp only [Types.literalProvider, index, Sample.types, Sample.literalOps, shorter,
        ↓reduceIte]
      exact eq_iff_some _ _
    · by_cases complete : values.length = count
      · simp only [Types.literalProvider, index, Sample.types, Sample.literalOps,
          complete, Nat.lt_irrefl, ↓reduceIte, true_and]
        exact eq_iff_some _ _
      · simp only [Types.literalProvider, index, Sample.types, Sample.literalOps, shorter,
          complete, ↓reduceIte, false_and]
        exact ⟨False.elim, fun h => by cases h⟩
  finishF := infosPrims.fromListF
  finish_fn := infosPrims.fromList_fn
  dropF := liftDropF rcPrims
  drop_fn := liftDrop_fn rcPrims
  retireF := fun before _ => some (.returned () before)
  retire_fn := fun _ _ _ => eq_iff_some _ _
  dbl := fun _ (first second : Nat) => first + second
  double_fn := fun _ _ _ _ => Iff.rfl

theorem noAgain (script : List PdaExit) : NoAgain (index script).literalProvider := by
  intro before input after
  change ¬ (if input.2.length < input.1 then _ else _)
  split <;> intro impossible
  · cases impossible
  · cases impossible.2

def collectRetireF (resource : Option Nat) (_ : List GuardElement) : DropF (index []) :=
  match resource with
  | none => fun before => some (.returned () before)
  | some token => (VecPrims.reference.focus Sample.guardsFocus).dropActionF token

theorem collectRetire_fn (resource : Option Nat) (acquired : List GuardElement) :
    DFn (Sample.collectionOps.retire resource acquired) (collectRetireF resource acquired) := by
  cases resource with
  | none => intro before outcome; exact eq_iff_some _ _
  | some token => exact (VecPrims.reference.focus Sample.guardsFocus).dropAction_fn token

def prims (script : List PdaExit) : Prims (index script) where
  bytes := VecPrims.reference.focus Sample.bytesFocus
  metas := VecPrims.reference.focus Sample.metasFocus
  infos := infosPrims
  discriminators := VecPrims.reference.focus Sample.discriminatorsFocus
  seedBytes := VecPrims.reference.focus Sample.bytesFocus
  seeds := VecPrims.reference.focus Sample.seedsFocus
  seedRefs := SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainIndex.emptyOnlyPrims
    Sample.seedRefsFocus
  rc := rcPrims
  array := arrayPrims script
  noAgain := noAgain script
  pdaF := pdaF script
  pda_fn := fun _ _ _ => Iff.rfl
  raiseF := fun before reason => some (.unwound (Sample.panicCode reason) before)
  raise_fn := by
    intro before reason outcome
    exact ⟨congrArg some, Option.some.inj⟩
  dbl := fun _ (first second : Nat) => first + second
  double_fn := fun _ _ _ _ => Iff.rfl
  collectFinishF := (VecPrims.reference.focus Sample.guardsFocus).fromListF
  collectFinish_fn := (VecPrims.reference.focus Sample.guardsFocus).fromList_fn
  collectRetireF := collectRetireF
  collectRetire_fn := collectRetire_fn
  collect_no_internal := fun _ _ _ _ => id
  collect_order := fun _ _ => rfl

end SolanalibTest.Conformance.Library.Families.TransferHookResolution
