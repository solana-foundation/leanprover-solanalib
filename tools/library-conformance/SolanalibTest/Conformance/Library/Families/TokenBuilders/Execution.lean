/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Allocated
import Solanalib.Specs.Core.CallbackGraph
import Solanalib.Specs.Core.TokenMetadataPointer
import Solanalib.Specs.Core.TokenMetadataInitializeSample

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenBuilders.Execution

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open Allocated (ST St Out samplePrims)

def doubleF (_ : St) (first second : Nat) : Option Nat := some (first + second)

theorem double_graph (state : St) (first second : Nat) :
    PGraph (ST.doubleUnwind state first second) (doubleF state first second) :=
  PGraph.eq_left _

def byteDrop (owner : Nat) : St → Option (Out Unit) := fun state => samplePrims.bytes.dropF state
  owner
def metaDrop (owner : Nat) : St → Option (Out Unit) := fun state => samplePrims.metas.dropF state
  owner

theorem byteDrop_graph (owner : Nat) (state : St) :
    PGraph (ST.bytes.drop state owner) (byteDrop owner state) := samplePrims.bytes.drop_fn state
      owner

theorem metaDrop_graph (owner : Nat) (state : St) :
    PGraph (ST.metas.drop state owner) (metaDrop owner state) := samplePrims.metas.drop_fn state
      owner

theorem byteDrops_graph (owner : Nat) :
    PGraph.DropsGraph [ST.bytes.dropAction owner] [byteDrop owner] :=
  ⟨byteDrop_graph owner, trivial⟩

theorem metaDrops_graph (owner : Nat) :
    PGraph.DropsGraph [ST.metas.dropAction owner] [metaDrop owner] :=
  ⟨metaDrop_graph owner, trivial⟩

def pointerAfterF (args : MetadataPointer.Args) (owner : Nat) (state : St) :
    Option (Out Allocated.Result) :=
  match MetadataPointer.fields args with
  | .error error => PGraph.cleanupFn doubleF [metaDrop owner] (.returned (.error error) state)
  | .ok bytes =>
    ((OnchainConstructor.buildDataF samplePrims (MetadataPointer.steps 39 bytes) state).map
      (Outcome.map fun data => Except.ok
        ({ programId := args.programId, metas := owner, data } : InstructionAllocated.Value
          ST))).bind
      (PGraph.onUnwindFn doubleF [metaDrop owner])

theorem pointerAfter_graph (args : MetadataPointer.Args) (owner : Nat) (state : St) :
    PGraph (MetadataPointer.afterMetas 39 ST args owner state) (pointerAfterF args owner state) :=
      by
  unfold MetadataPointer.afterMetas pointerAfterF
  cases MetadataPointer.fields args with
  | error error => exact PGraph.cleanup double_graph _ _ (metaDrops_graph owner) _
  | ok bytes =>
    exact PGraph.protect double_graph (metaDrops_graph owner)
      (PGraph.map _ (OnchainConstructor.buildData_fn samplePrims _ state ()))

def pointerF (state : St) (args : MetadataPointer.Args) : Option (Out Allocated.Result) :=
  match Instruction.checkProgram .token2022 args.programId with
  | .error error => some (.returned (.error error) state)
  | .ok () => (samplePrims.metas.fromListF state (MetadataPointer.metas args)).bind
      (PGraph.bindK (pointerAfterF args))

theorem pointer_graph (state : St) (args : MetadataPointer.Args) :
    PGraph (MetadataPointer.run 39 ST state args) (pointerF state args) := by
  unfold MetadataPointer.run pointerF
  cases Instruction.checkProgram .token2022 args.programId with
  | error error => exact PGraph.eq_left _
  | ok value =>
    cases value
    exact PGraph.bind (samplePrims.metas.fromList_fn state _) (pointerAfter_graph args)

namespace Metadata

open MetadataInitialize

abbrev index := Sample.index
abbrev Value := InstructionAllocated.Value ST

def appendF (state : St) (owners : Nat × Nat) : Option (Out Unit) := do
  let target ← state.1.current owners.1
  let source ← state.1.current owners.2
  return .returned ()
    ((state.1.set owners.1 (some (target ++ source))).set owners.2 (some []), state.2)

theorem append_graph (state : St) (owners : Nat × Nat) :
    PGraph (index.append state owners) (appendF state owners) := by
  intro outcome
  change Sample.append state owners outcome ↔ appendF state owners = some outcome
  unfold Sample.append appendF
  constructor
  · rintro ⟨target, source, ht, hs, rfl⟩
    rw [ht, hs]
    rfl
  · intro h
    cases ht : state.1.current owners.1 with
    | none => simp [ht] at h
    | some target =>
      cases hs : state.1.current owners.2 with
      | none => simp [ht, hs] at h
      | some source =>
        rw [ht, hs] at h
        exact ⟨target, source, rfl, rfl, (Option.some.inj h).symm⟩

def toVecAfterF (buffer : Nat) (result : Except Unit Nat) (state : St) : Option (Out Nat) :=
  match result with
  | .error () => some (.terminated 99)
  | .ok temporary => ((appendF state (buffer, temporary)).map (Outcome.map fun _ => buffer)).bind
      (PGraph.cleanupFn doubleF [byteDrop temporary])

def packF (state : St) (owners : Owners Nat) : Option (Out Nat) :=
  let (buffer, empty) := ST.bytes.empty state
  ((samplePrims.bytes.extendF empty (buffer, discriminator)).bind
    (PGraph.bindK fun _ current => (some (Sample.toVec current owners)).bind
      (PGraph.bindK (toVecAfterF buffer)))).bind
    (PGraph.onUnwindFn doubleF [byteDrop buffer])

theorem pack_graph (state : St) (owners : Owners Nat) :
    PGraph (pack index state owners) (packF state owners) := by
  unfold pack packF
  apply PGraph.protect double_graph (byteDrops_graph _)
  apply PGraph.bind (samplePrims.bytes.extend_fn _ _)
  intro _ current
  apply PGraph.bind (PGraph.ofFunction Sample.toVec current owners)
  intro result after
  cases result with
  | error value =>
    cases value
    have hu : PGraph (index.unwrap after ()) (some (Outcome.terminated 99 : Out Empty)) :=
      PGraph.eq_left _
    exact PGraph.map Empty.elim hu
  | ok temporary =>
    exact PGraph.scope double_graph (byteDrops_graph temporary)
      (PGraph.map _ (append_graph after _))

def constructF (state : St) (args : Args Nat) : Option (Out Value) :=
  (samplePrims.metas.fromListF state (metas args)).bind (PGraph.bindK fun metadata current =>
    ((packF current args.owners).map
      (Outcome.map fun data => ({ programId := args.programId, metas := metadata, data } :
        Value))).bind
      (PGraph.onUnwindFn doubleF [metaDrop metadata]))

theorem construct_graph (state : St) (args : Args Nat) :
    PGraph (construct index state args) (constructF state args) := by
  unfold construct constructF
  apply PGraph.bind (samplePrims.metas.fromList_fn _ _)
  intro metadata current
  exact PGraph.protect double_graph (metaDrops_graph metadata) (PGraph.map _ (pack_graph current _))

def stringDrops (owners : Owners Nat) : List (St → Option (Out Unit)) :=
  [byteDrop owners.name, byteDrop owners.symbol, byteDrop owners.uri]

theorem stringDrops_graph (owners : Owners Nat) :
    PGraph.DropsGraph (textDrops index owners) (stringDrops owners) :=
  ⟨byteDrop_graph _, byteDrop_graph _, byteDrop_graph _, trivial⟩

def afterConstructF (owners : Owners Nat) : Out Value → Option (Out Value)
  | .returned instruction state =>
    (PGraph.cleanupFn doubleF (stringDrops owners) (.returned instruction state)).bind
      (PGraph.onUnwindFn doubleF [metaDrop instruction.metas, byteDrop instruction.data])
  | .unwound reason state =>
    PGraph.cleanupFn doubleF (stringDrops owners) (.unwound reason state)
  | .terminated reason => some (.terminated reason)

def runF (state : St) (args : Args Nat) : Option (Out Value) :=
  (constructF state args).bind (afterConstructF args.owners)

theorem run_graph (state : St) (args : Args Nat) :
    PGraph (run index state args) (runF state args) := by
  unfold run runF
  apply PGraph.exists_step (construct_graph state args)
  intro pending
  cases pending with
  | returned instruction after =>
    have hd : PGraph.DropsGraph (InstructionAllocated.drops ST instruction)
        [metaDrop instruction.metas, byteDrop instruction.data] :=
      ⟨metaDrop_graph _, byteDrop_graph _, trivial⟩
    apply PGraph.protect double_graph hd
    exact PGraph.scope (f := some (.returned instruction after)) double_graph
      (stringDrops_graph args.owners) (PGraph.eq_left _)
  | unwound reason after => exact PGraph.cleanup double_graph _ _ (stringDrops_graph _) _
  | terminated reason => exact PGraph.eq_left _

end Metadata
end SolanalibTest.Conformance.Library.Families.TokenBuilders.Execution
