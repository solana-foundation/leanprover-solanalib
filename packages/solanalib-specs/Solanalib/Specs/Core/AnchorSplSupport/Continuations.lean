/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Admission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- A returned serializer-owned vector contains the exact checked encoding.
The source unwrap cannot turn a serialization error into a returned vector. -/
theorem Ready.serialized_bytes {types : Types} {operation : Operation}
    {initial : types.resources.State} {args : Args types.resources operation}
    (ready : Ready types operation initial args) (before after : types.resources.State)
    (input : Serialization) (resource : types.resources.ByteResource)
    (used : SerializationUsed operation args input)
    (serialized : serializeBytes types.resources before input (.returned resource after)) :
    ∃ bytes, input.encode = .ok bytes ∧ types.resources.bytes.current after resource = some bytes
      := by
  obtain ⟨produced, called, continued⟩ := serialized
  cases produced with
  | unwound reason state => cases continued
  | terminated reason => cases continued
  | returned result state => cases result with
    | ok bytes =>
      cases continued
      have exactResult := ready.serialized before input (.ok resource) after used called
      cases encoded : input.encode with
      | error error => simp [SerializationResult, encoded] at exactResult
      | ok values =>
        exact ⟨values, rfl, by simpa [SerializationResult, encoded] using exactResult⟩
    | error error =>
      obtain ⟨impossible, _, mapped⟩ := continued
      cases impossible with
      | returned empty _ => nomatch empty
      | unwound _ _ => cases mapped
      | terminated _ => cases mapped

/-- The actual temporary key constructor return reaches memo instruction
construction with the original remaining-account key order. -/
theorem Ready.memo_continue {types : Types} {before allocated : types.resources.State}
    {args : Args types.resources .memo} (ready : Ready types .memo before args)
    (keys : types.resources.KeyResource) (remaining : List AccountInfo.Value)
    (initial : types.resources.infos.current before args.context.remainingAccounts = some remaining)
    (constructed : types.resources.keys.fromList before (remaining.map AccountInfo.Value.key)
      (.returned keys allocated))
    (pending final : Outcome types.resources.State (Built types.resources)
      types.resources.Unwind types.resources.Terminal)
    (built : buildVectors types.resources
      (memoInstruction args.extra (remaining.map AccountInfo.Value.key)) allocated () pending)
    (cleaned : Owned.cleanup types.resources.doubleUnwind [types.resources.keys.dropAction keys]
      pending final) :
    build types.resources .memo before args final := by
  obtain ⟨actual, actualCurrent, retained⟩ := ready.memo
  have equal : actual = remaining := Option.some.inj (actualCurrent.symm.trans initial)
  subst actual
  have current := retained keys allocated constructed
  change buildMemo types.resources args.context.remainingAccounts args.extra before () final
  simp only [buildMemo, initial]
  refine ⟨.returned keys allocated, constructed, pending, ?_, cleaned⟩
  change (match types.resources.keys.current allocated keys with
    | none => False
    | some values => buildVectors types.resources (memoInstruction args.extra values)
        allocated () pending)
  rw [current]
  exact built

/-- After the exact earlier metadata prefix, the same owned DataV2 fields
are available to the source serializer. Every actual serializer exit can feed
the supplied continuation; no complete constructor outcome is assumed. -/
theorem Ready.metadata_tail {types : Types} {before after : types.resources.State}
    {args : Args types.resources .metadata} (ready : Ready types .metadata before args)
    (allocated : types.resources.MetaResource × types.resources.ByteResource)
    (prefixRun : metadataPrefix types.resources args.context.accounts.keys
      args.extra.updateAuthoritySigner
      before () (.returned allocated after)) :
    ∃ data, args.extra.data.current before = some data ∧
      ∀ final, metadataTail types.resources args.context.accounts.keys args.extra
        allocated.1 allocated.2 after () final ↔
        Owned.protect types.resources.doubleUnwind
          [types.resources.bytes.dropAction allocated.2, types.resources.metas.dropAction
            allocated.1]
          (fun state (_ : Unit) => Callback.bind (serializeBytes types.resources)
            (fun argumentBytes serialized => Owned.scope types.resources.doubleUnwind
              [types.resources.bytes.dropAction argumentBytes]
              (Callback.map (fun _ => ⟨⟨Metadata.programId, allocated.1, allocated.2⟩,
                Metadata.instruction args.context.accounts.keys data args.extra.isMutable
                  args.extra.updateAuthoritySigner args.extra.details⟩)
                (fun state (_ : Unit) => types.resources.appendBytes state (allocated.2,
                  argumentBytes)))
              serialized ()) state (.metadataArguments data args.extra.isMutable
                args.extra.details))
          after () final := by
  obtain ⟨data, initial, current⟩ := ready.metadata_read allocated prefixRun
  refine ⟨data, initial, ?_⟩
  intro final
  simp only [metadataTail, Owned.protect, current]

/-- The remaining-account slice is read in the actual state returned by all
seven field constructions. Its order is retained before clone-extension. -/
theorem Ready.metadata_infos_tail {types : Types} {before builtState after : types.resources.State}
    {args : Args types.resources .metadata} (ready : Ready types .metadata before args)
    (instruction : Built types.resources) (infos : types.resources.InfoResource)
    (built : build types.resources .metadata before args (.returned instruction builtState))
    (fields : metadataFields types.resources args.context.accounts builtState () (.returned infos
      after)) :
    ∃ remaining,
      types.resources.infos.current before args.context.remainingAccounts = some remaining ∧
      ∀ final, metadataInfosTail types.resources args.context infos after () final ↔
        Owned.protect types.resources.doubleUnwind [types.resources.infos.dropAction infos]
          (fun state (_ : Unit) => Callback.bind types.resources.cloneExtendInfos
            (fun _ extended => Callback.bind
              (AccountInfoRc.lift (AccountInfoRc.cloneCall types.resources.rc))
              (fun program cloned => Callback.map (fun _ => infos) types.resources.infos.push
                cloned (infos, program)) extended args.context.program)
            state (infos, remaining)) after () final := by
  obtain ⟨remaining, initial, retained⟩ := ready.metadataRemaining
  have current := retained instruction builtState infos after built fields
  refine ⟨remaining, initial, ?_⟩
  intro final
  simp only [metadataInfosTail, Owned.protect, current]

/-- A returned invocation error has live owned payload strings; conversion
then retains those strings in the actual inline value or returned box. -/
theorem Ready.converted_error {types : Types} {operation : Operation}
    {before atCall invokedState after : types.resources.State} {args : Args types.resources
      operation}
    (ready : Ready types operation before args) (point : CallPoint types.resources)
    (reached : AtCall types.resources operation before args point atCall)
    (program : types.resources.ProgramError) (error : Error types.resources operation.profile)
    (invoked : types.invoke atCall
      ⟨point.instruction.planned, point.accounts.expected, args.context.signerSeeds⟩
      (.returned (.error program) invokedState))
    (converted : AnchorErrorOperations.fromProgram operation.profile.storage types.resources.errors
      invokedState program (.returned error after)) :
    ∃ strings, errorContents types.resources operation.profile after error =
      some (.program ⟨program, none, none⟩, strings) := by
  obtain ⟨strings, current⟩ := ready.invocationError point atCall program invokedState reached
    invoked
  exact ⟨strings, ready.errors.converted invokedState after program strings error current converted⟩

/-- The destructors that follow invocation cannot discard a pending error by
unwinding. Their terminal exits remain possible and stop cleanup immediately. -/
theorem Ready.returnDrop_noUnwind {types : Types} {operation : Operation}
    {before : types.resources.State} {args : Args types.resources operation}
    (ready : Ready types operation before args) (drop : ReturnDrop types.resources)
    (state after : types.resources.State) (reason : types.resources.Unwind) :
    ¬ drop.action state (.unwound reason after) := by
  cases drop with
  | metas resource => exact ready.metaDrop state resource reason after
  | bytes resource => exact ready.byteDrop state resource reason after
  | infos resource => exact ready.infoDrop state resource reason after
  | account value =>
    rintro ⟨produced, _, mapped⟩
    cases produced with
    | unwound impossible _ => nomatch impossible
    | returned _ _ => cases mapped
    | terminated _ => cases mapped

/-- Actual final cleanup either retains its pending value in its true final
state or terminates. There is no invented successful destructor execution. -/
theorem Ready.cleanup_exit {types : Types} {operation : Operation}
    {initial : types.resources.State} {args : Args types.resources operation}
    (ready : Ready types operation initial args) (drops : List (ReturnDrop types.resources))
    (before : types.resources.State) (value : Except (Error types.resources operation.profile) Unit)
    (final : Outcome types.resources.State (Except (Error types.resources operation.profile) Unit)
      types.resources.Unwind types.resources.Terminal)
    (cleaned : Owned.cleanup types.resources.doubleUnwind (drops.map ReturnDrop.action)
      (.returned value before) final) :
    (∃ after, final = .returned value after) ∨ (∃ reason, final = .terminated reason) := by
  induction drops generalizing before with
  | nil => exact .inl ⟨before, cleaned⟩
  | cons drop rest induction =>
    obtain ⟨produced, called, continued⟩ := cleaned
    cases produced with
    | returned valueUnit after => cases valueUnit; exact induction after continued
    | unwound reason after => exact (ready.returnDrop_noUnwind drop before after reason called).elim
    | terminated reason => exact .inr ⟨reason, continued⟩

end Solanalib.Specs.Core.AnchorSplSupport
