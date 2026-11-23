/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSystem
public import Solanalib.Specs.Core.AnchorErrorOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSystem

/-- Complete source differences at the owned context/error boundary. Legacy
ProgramError retains its owned Borsh string; it is not replaced by a u64 code. -/
inductive Profile where
  /-- The inline error and owned program AccountInfo in Anchor 0.27. -/
  | inlineLegacy
  /-- The boxed error with owned legacy ProgramError strings in Anchor 0.29 and 0.32. -/
  | boxedLegacy
  /-- The boxed error, string-free ProgramError and program key in Anchor 1.0 and 1.1. -/
  | boxedModern
  deriving DecidableEq, Repr

/-- The actual program field of the context at the selected source release. -/
def Profile.context : Profile → ContextKind
  | .inlineLegacy | .boxedLegacy => .programAccount
  | .boxedModern => .programId

/-- Anchor 0.27 converts errors inline; every later reviewed release boxes. -/
def Profile.storage : Profile → AnchorErrorOperations.Storage
  | .inlineLegacy => .inline
  | .boxedLegacy | .boxedModern => .boxed

/-- The complete program error carrier of the dependency, including older String
resources. The adapter separately excludes variants absent in its release. -/
def Profile.Program (profile : Profile) (StringResource : Type) : Type :=
  match profile with
  | .inlineLegacy | .boxedLegacy => ProgramErrorOwned.Value StringResource
  | .boxedModern => ProgramError.Value

/-- One fixed assignment of primitive dependencies and an explicit opaque CPI
contract over the whole wrapper state. Its returned error, unwind, terminal
and state effects are all retained. No invocation implementation is traversed. -/
structure Index (profile : Profile) where
  /-- Construction and context-cleanup providers over one actual state. -/
  resources : Resources
  /-- An identity of an owned diagnostic or legacy ProgramError string. -/
  StringResource : Type
  /-- An identity of an owned Anchor error box. -/
  BoxResource : Type
  /-- Version-selected error construction and current payload observations. -/
  errors : AnchorErrorOperations.Ops resources.types.State
    (profile.Program StringResource) StringResource BoxResource resources.types.Terminal
  /-- The whole opaque invocation signature, including all finite exits. -/
  invoke : CpiRequest.Invocation resources.types.State AccountInfo.Value
    (profile.Program StringResource) resources.types.Unwind resources.types.Terminal

/-- The exact version-selected owned Anchor error representation. -/
abbrev Error {profile : Profile} (index : Index profile) :=
  AnchorErrorOperations.Error profile.storage (profile.Program index.StringResource)
    index.StringResource index.BoxResource

/-- Invoke using the freshly observed instruction, then convert only an actual
returned ProgramError. The conversion initializes absent diagnostics and
performs the version-selected allocation before scope cleanup. -/
def invokeAndConvert {profile : Profile} (index : Index profile) {operation : Operation}
    (args : Args index.resources profile.context operation)
    (value : InstructionBuilder.Value index.resources.types.builder) :
    Callback.Run index.resources.types.State Unit (Except (Error index) Unit)
      index.resources.types.Unwind index.resources.types.Terminal :=
  fun before _ outcome =>
    match request before args value with
    | none => False
    | some current => Callback.bind index.invoke
      (fun result after => match result with
        | .ok () => fun final => final = .returned (.ok ()) after
        | .error error => Callback.map Except.error
          (AccountInfoRc.lift (AnchorErrorOperations.fromProgram profile.storage index.errors))
          after error)
      before current outcome

/-- Full wrapper execution: construct before moving accounts, invoke and
convert, then destroy the local instruction/temporary array/context remainder.
Constructor unwind cleans the still-unmoved context. Terminal paths stop at
their actual dependency; no later destructor or outcome is fabricated. -/
def run {profile : Profile} (index : Index profile) {operation : Operation}
    (before : index.resources.types.State)
    (args : Args index.resources profile.context operation)
    (outcome : Outcome index.resources.types.State (Except (Error index) Unit)
      index.resources.types.Unwind index.resources.types.Terminal) : Prop :=
  ∃ constructed, build before args constructed ∧
    match constructed with
    | .returned value after =>
      Owned.scope index.resources.builder.doubleUnwind (invocationDrops args value)
        (invokeAndConvert index args value) after () outcome
    | .unwound reason after =>
      Owned.cleanup index.resources.builder.doubleUnwind (contextDrops args)
        (.unwound reason after) outcome
    | .terminated reason => outcome = .terminated reason

/-- Generic mathematical function model above explicit primitive and opaque
invocation contracts. Readability concerns only reached constructor returns;
source ownership, ABI, initialization and dependency binding stay separate. -/
def family (profile : Profile) (operation : Operation) : Family where
  Index := Index profile
  State := fun index => index.resources.types.State
  Args := fun index => Args index.resources profile.context operation
  Value := fun index => Except (Error index) Unit
  Unwind := fun index => index.resources.types.Unwind
  Terminal := fun index => index.resources.types.Terminal
  contract := fun index => { requires := BuildReady, post := run index }

/-- The reference is the full resource/control relation, rather than only its
successful instruction-value projection. -/
def reference (profile : Profile) (operation : Operation) : FamilyRun (family profile operation) :=
  fun index => run index

/-- Every supplied index and admitted execution satisfies that same complete
contract. Closed nonvacuity and concrete paths are supplied separately. -/
theorem reference_holds (profile : Profile) (operation : Operation) :
    FamilyReference (family profile operation) (reference profile operation) := by
  intro _ _ _ _ _ execution
  exact execution

/-- An actual returned invocation success enters cleanup in its actual state.
This rule does not assert unchanged accounts, successful CPI, or normal drops. -/
theorem invokeAndConvert_ok {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (value : InstructionBuilder.Value index.resources.types.builder)
    (before after : index.resources.types.State) (current : CpiRequest.Request AccountInfo.Value)
    (observed : request before args value = some current)
    (called : index.invoke before current (.returned (.ok ()) after)) :
    invokeAndConvert index args value before () (.returned (.ok ()) after) := by
  unfold invokeAndConvert
  rw [observed]
  exact ⟨.returned (.ok ()) after, called, rfl⟩

/-- A returned program error is moved through exactly the selected conversion;
its real converted error identity and intermediate state feed cleanup. -/
theorem invokeAndConvert_error {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (value : InstructionBuilder.Value index.resources.types.builder)
    (before middle after : index.resources.types.State) (current : CpiRequest.Request
      AccountInfo.Value)
    (program : profile.Program index.StringResource) (error : Error index)
    (observed : request before args value = some current)
    (called : index.invoke before current (.returned (.error program) middle))
    (converted : AnchorErrorOperations.fromProgram profile.storage index.errors middle program
      (.returned error after)) :
    invokeAndConvert index args value before () (.returned (.error error) after) := by
  unfold invokeAndConvert
  rw [observed]
  exact ⟨.returned (.error program) middle, called,
    .returned error after, ⟨.returned error after, converted, rfl⟩, rfl⟩

/-- Provider unwind skips conversion, preserving its actual reason and state. -/
theorem invokeAndConvert_unwind {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (value : InstructionBuilder.Value index.resources.types.builder)
    (before after : index.resources.types.State) (current : CpiRequest.Request AccountInfo.Value)
    (reason : index.resources.types.Unwind)
    (observed : request before args value = some current)
    (called : index.invoke before current (.unwound reason after)) :
    invokeAndConvert index args value before () (.unwound reason after) := by
  unfold invokeAndConvert
  rw [observed]
  exact ⟨.unwound reason after, called, rfl⟩

/-- Provider terminal exit also skips conversion and every later destructor. -/
theorem invokeAndConvert_terminal {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (value : InstructionBuilder.Value index.resources.types.builder)
    (before : index.resources.types.State) (current : CpiRequest.Request AccountInfo.Value)
    (reason : index.resources.types.Terminal)
    (observed : request before args value = some current)
    (called : index.invoke before current (.terminated reason)) :
    invokeAndConvert index args value before () (.terminated reason) := by
  unfold invokeAndConvert
  rw [observed]
  exact ⟨.terminated reason, called, rfl⟩

/-- A reached builder return and full pending/cleanup executions compose without
restoring any earlier state or forgetting the actual returned error resource. -/
theorem run_after_build {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (before afterBuild : index.resources.types.State)
    (value : InstructionBuilder.Value index.resources.types.builder)
    (pending final : Outcome index.resources.types.State (Except (Error index) Unit)
      index.resources.types.Unwind index.resources.types.Terminal)
    (constructed : build before args (.returned value afterBuild))
    (invoked : invokeAndConvert index args value afterBuild () pending)
    (cleaned : Owned.cleanup index.resources.builder.doubleUnwind
      (invocationDrops args value) pending final) :
    run index before args final :=
  ⟨.returned value afterBuild, constructed, pending, invoked, cleaned⟩

/-- Construction unwind cleans the intact context, without an invocation or
error-conversion premise. Any earlier builder-owned cleanup is already part
of the supplied constructor execution. -/
theorem run_build_unwind {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (before after : index.resources.types.State) (reason : index.resources.types.Unwind)
    (final : Outcome index.resources.types.State (Except (Error index) Unit)
      index.resources.types.Unwind index.resources.types.Terminal)
    (constructed : build before args (.unwound reason after))
    (cleaned : Owned.cleanup index.resources.builder.doubleUnwind
      (contextDrops args) (.unwound reason after) final) : run index before args final :=
  ⟨.unwound reason after, constructed, cleaned⟩

/-- A construction terminal has no callback or cleanup continuation. -/
theorem run_build_terminal {profile : Profile} (index : Index profile)
    {operation : Operation} (args : Args index.resources profile.context operation)
    (before : index.resources.types.State) (reason : index.resources.types.Terminal)
    (constructed : build before args (.terminated reason)) :
    run index before args (.terminated reason) :=
  ⟨.terminated reason, constructed, rfl⟩

end Solanalib.Specs.Core.AnchorSystem
