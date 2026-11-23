/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Graph
import Solanalib.Specs.Core.AnchorSystemExitWitness

/-! A functional graph of the registered wrapper relation at the finite resource interpretation of
the recorder. Constructor, conversion and cleanup graphs
are derived from those definitions; opaque invocation remains a parameter. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem
open SolanalibTest.Conformance.Library.Families.Anchor

abbrev State (profile : Profile) := Sample.State (profile.Program Nat)
abbrev Out (profile : Profile) := Outcome (State profile) (Except (Error (Sample.index profile))
  Unit) Nat Nat
abbrev InvokeOut (profile : Profile) := Outcome (State profile) (Except (profile.Program Nat) Unit)
  Nat Nat

/-- Only the explicit opaque invocation provider varies across recorded cases. -/
def recordedIndex (profile : Profile)
    (invoke : State profile → CpiRequest.Request AccountInfo.Value → InvokeOut profile) : Index
      profile :=
  { Sample.index profile with invoke := Callback.ofFunction invoke }

theorem conversion_graph (profile : Profile) (state : State profile) (error : profile.Program Nat) :
    PGraph (AnchorErrorOperations.fromProgram profile.storage (Sample.errors profile) state error)
      (some (.returned (Sample.convertedError profile state error) (Sample.afterConversion profile
        state error))) := by
  cases profile with
  | inlineLegacy => exact PGraph.eq_left _
  | boxedLegacy | boxedModern =>
    intro outcome
    constructor
    · rintro ⟨inner, computed, mapped⟩
      change Outcome.returned state.boxes.length
        { state with boxes := state.boxes ++ [some (.program ⟨error, none, none⟩)] } = inner
          at computed
      subst inner
      cases mapped
      rfl
    · intro equality
      cases equality
      exact Sample.conversion_returns _ _ _

def invokeFn (profile : Profile)
    (invoke : State profile → CpiRequest.Request AccountInfo.Value → InvokeOut profile)
    {operation : Operation} (args : Args (Sample.index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (Sample.index profile).resources.types.builder)
    (before : State profile) : Option (Out profile) :=
  (request before args value).bind fun current =>
    (some (invoke before current)).bind (PGraph.bindK fun result after => some (match result with
      | .ok () => .returned (.ok ()) after
      | .error error => .returned (.error (Sample.convertedError profile after error))
          (Sample.afterConversion profile after error)))

theorem invoke_graph (profile : Profile)
    (invoke : State profile → CpiRequest.Request AccountInfo.Value → InvokeOut profile)
    {operation : Operation} (args : Args (Sample.index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (Sample.index profile).resources.types.builder)
    (before : State profile) :
    PGraph (invokeAndConvert (recordedIndex profile invoke) args value before ())
      (invokeFn profile invoke args value before) := by
  unfold invokeAndConvert invokeFn
  dsimp only [recordedIndex]
  cases observed : request before args value with
  | none => exact PGraph.false
  | some current =>
    apply PGraph.bind (PGraph.ofFunction invoke before current)
    intro result after
    cases result with
    | ok unitValue => cases unitValue; exact PGraph.eq_left _
    | error error =>
      intro outcome
      constructor
      · rintro ⟨converted, ⟨native, executed, lifted⟩, mapped⟩
        have exactConversion := (conversion_graph profile after error native).mp executed
        cases exactConversion
        cases lifted
        cases mapped
        rfl
      · intro equality
        cases equality
        exact ⟨_, ⟨_, Sample.conversion_returns profile after error, rfl⟩, rfl⟩

theorem dropInfo_graph (Program : Type) (info : AccountInfo.Value) (before : Sample.State Program) :
    PGraph (AnchorSystem.dropInfo (Sample.resources Program) info before)
      (some (.returned () (Sample.dropInfoState before info))) := by
  intro outcome
  constructor
  · rintro ⟨inner, ⟨first, firstCall, secondCall⟩, lifted⟩
    change Outcome.returned () (Sample.dropRc before .lamports info.lamports) = first at firstCall
    subst first
    change Outcome.returned () (Sample.dropInfoState before info) = inner at secondCall
    subst inner
    cases lifted
    rfl
  · intro equality
    cases equality
    exact Sample.dropInfo_returns _ _ _

theorem metaDrop_graph (profile : Profile) (state : State profile) (resource : Nat) :
    PGraph ((Sample.index profile).resources.builder.metaVec.dropAction resource state)
      (some (.returned () (Sample.dropMeta state resource))) := by
  intro outcome
  constructor
  · rintro ⟨inner, computed, lifted⟩
    change Outcome.returned () (InstructionBuilder.Sample.retireMetas state.construction resource)
      = inner at computed
    subst inner
    cases lifted
    rfl
  · intro equality
    cases equality
    exact ⟨_, rfl, rfl⟩

theorem byteDrop_graph (profile : Profile) (state : State profile) (resource : Nat) :
    PGraph ((Sample.index profile).resources.builder.byteVec.dropAction resource state)
      (some (.returned () (Sample.dropByte state resource))) := by
  intro outcome
  constructor
  · rintro ⟨inner, computed, lifted⟩
    change Outcome.returned () (InstructionBuilder.Sample.retireBytes state.construction resource)
      = inner at computed
    subst inner
    cases lifted
    rfl
  · intro equality
    cases equality
    exact ⟨_, rfl, rfl⟩

def dropFns {profile : Profile} {operation : Operation}
    (args : Args (Sample.index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (Sample.index profile).resources.types.builder) :
    List (State profile → Option (Outcome (State profile) Unit Nat Nat)) :=
  [fun state => some (.returned () (Sample.dropMeta state value.metas)),
    fun state => some (.returned () (Sample.dropByte state value.data))] ++
    (movedAccounts args).map (fun info state => some (.returned () (Sample.dropInfoState state
      info))) ++
    [fun state => some (.returned () (Sample.dropRemaining state args.remaining))] ++
    match profile, args with
    | .inlineLegacy, args | .boxedLegacy, args =>
      [fun state => some (.returned () (Sample.dropInfoState state args.program))]
    | .boxedModern, _ => []

theorem drops_graph {profile : Profile} {operation : Operation}
    (args : Args (Sample.index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (Sample.index profile).resources.types.builder) :
    PGraph.DropsGraph (invocationDrops args value) (dropFns args value) := by
  refine PGraph.DropsGraph.cons (fun state => metaDrop_graph profile state value.metas) ?_
  refine PGraph.DropsGraph.cons (fun state => byteDrop_graph profile state value.data) ?_
  have remaining : ∀ (infos : List AccountInfo.Value),
      PGraph.DropsGraph
        (infos.map (AnchorSystem.dropInfo (Sample.index profile).resources) ++ contextTailDrops
          args)
        (infos.map (fun info state => some (.returned () (Sample.dropInfoState state info))) ++
          [fun state => some (.returned () (Sample.dropRemaining state args.remaining))] ++
          match profile, args with
          | .inlineLegacy, args | .boxedLegacy, args =>
            [fun state => some (.returned () (Sample.dropInfoState state args.program))]
          | .boxedModern, _ => []) := by
    intro infos
    induction infos with
    | nil =>
      refine PGraph.DropsGraph.cons (fun state => PGraph.ofFunction
        (fun (state : State profile) (resource : Nat) =>
          (Outcome.returned () (Sample.dropRemaining state resource) : Outcome (State profile) Unit
            Nat Nat))
        state args.remaining) ?_
      cases profile with
      | inlineLegacy | boxedLegacy =>
        exact PGraph.DropsGraph.cons (fun state => dropInfo_graph _ args.program state)
          PGraph.DropsGraph.nil
      | boxedModern => exact PGraph.DropsGraph.nil
    | cons info rest induction =>
      exact PGraph.DropsGraph.cons (dropInfo_graph _ info) induction
  exact remaining (movedAccounts args)

def doubleFn {profile : Profile} (_ : State profile) (first later : Nat) : Option Nat := some
  (first + later + 1000)

theorem double_graph (profile : Profile) (state : State profile) (first later : Nat) :
    PGraph ((Sample.index profile).resources.builder.doubleUnwind state first later)
      (doubleFn state first later) := PGraph.eq_left _

def runFn (profile : Profile)
    (invoke : State profile → CpiRequest.Request AccountInfo.Value → InvokeOut profile)
    {operation : Operation} (before : State profile)
    (args : Args (Sample.index profile).resources profile.context operation) : Option (Out profile)
      :=
  (invokeFn profile invoke args (Sample.builtValue before) (Sample.afterBuild before args)).bind
    (PGraph.cleanupFn doubleFn (dropFns args (Sample.builtValue before)))

/-- The complete selected relation admits exactly the computed finite outcome.
No expected result is substituted as a callback or asserted as a premise. -/
theorem run_graph (profile : Profile)
    (invoke : State profile → CpiRequest.Request AccountInfo.Value → InvokeOut profile)
    {operation : Operation} (before : State profile)
    (args : Args (Sample.index profile).resources profile.context operation) :
    PGraph (run (recordedIndex profile invoke) before args) (runFn profile invoke before args) := by
  apply PGraph.congr (PGraph.scope (double_graph profile)
    (drops_graph args (Sample.builtValue before))
    (invoke_graph profile invoke args (Sample.builtValue before) (Sample.afterBuild before args)))
  intro outcome
  constructor
  · rintro ⟨built, completed, next⟩
    have exactBuild := (Sample.build_exact before args built).mp completed
    subst built
    exact next
  · intro next
    exact ⟨_, Sample.build_returns before args, next⟩

end SolanalibTest.Conformance.Library.Families.AnchorSystem
