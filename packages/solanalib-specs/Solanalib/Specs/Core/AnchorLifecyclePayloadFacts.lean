/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecyclePayload

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

/-- The reached initialization read either has its direct source exit, or
reaches the exact zero-balance error factory. Each actual factory outcome is
retained; admission does not assume that allocation terminates. -/
theorem initialized_entry {types : PayloadTypes} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : AnchorAccount.InitReady types.ownerAt before args) :
    (∃ outcome, initialized types before args outcome) ∨
      ∃ after, types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId ∧
        observe (Unwind := types.Unwind) (Terminal := types.Terminal)
          .lamports before args (.returned 0 after) ∧
        ∀ produced, accountCode types.toBase .notInitialized after () produced →
          initialized types before args (Outcome.map Except.error produced) := by
  by_cases system : types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId
  · obtain ⟨observed, called⟩ := observe_exists (Unwind := types.Unwind) (Terminal :=
    types.Terminal)
      .lamports before args (ready system)
    cases observed with
    | returned balance after =>
      by_cases zero : balance = 0
      · subst balance
        refine Or.inr ⟨after, system, called, ?_⟩
        intro produced built
        simp only [initialized, system, ↓reduceIte]
        exact ⟨.returned 0 after, called, produced, built, rfl⟩
      · refine Or.inl ⟨.returned (.ok ()) after, ?_⟩
        simp only [initialized, system, ↓reduceIte]
        exact ⟨.returned balance after, called, by simp only [zero, ↓reduceIte]⟩
    | unwound reason after =>
      refine Or.inl ⟨.unwound reason after, ?_⟩
      simp only [initialized, system, ↓reduceIte]
      exact ⟨.unwound reason after, called, rfl⟩
    | terminated reason =>
      refine Or.inl ⟨.terminated reason, ?_⟩
      simp only [initialized, system, ↓reduceIte]
      exact ⟨.terminated reason, called, rfl⟩
  · exact Or.inl ⟨.returned (.ok ()) before, by simp only [initialized, system, ↓reduceIte]⟩

theorem ownerCheck_ok {types : PayloadTypes} {before after : World types.Aux}
    {args : AccountInfo.Args}
    (called : ownerCheck types before args (.returned (.ok ()) after)) :
    ∃ expected, AnchorAccount.widenCallback types.owner before () (.returned expected after) ∧
      types.ownerAt after.2 args.info.ownerRef = expected := by
  obtain ⟨produced, identified, next⟩ := called
  cases produced with
  | unwound _ _ => cases next
  | terminated _ => cases next
  | returned expected checked =>
    by_cases same : types.ownerAt checked.2 args.info.ownerRef = expected
    · simp only [ite_eq_left same] at next
      cases next
      exact ⟨expected, identified, same⟩
    · simp only [ite_eq_right same] at next
      obtain ⟨built, _, guarded⟩ := next
      cases built with
      | unwound _ _ => cases guarded
      | terminated _ => cases guarded
      | returned error allocated =>
        obtain ⟨pending, body, cleaned⟩ := guarded
        have equal := AnchorEffects.protected_returned _ _ cleaned
        cases equal
        obtain ⟨diagnostic, _, compared⟩ := body
        cases diagnostic with
        | unwound _ _ => cases compared
        | terminated _ => cases compared
        | returned _ _ =>
          obtain ⟨result, _, impossible⟩ := compared
          cases result <;> cases impossible

/-- A typed source cell supplies the exact live bytes passed to the selected
codec. Admission is checked at this call input, not at a completed wrapper. -/
theorem DecodePayloadReady.callback_input {storage : InfoStorage} {types : PayloadTypes}
    {before : World types.Aux} {args : AccountInfo.Args}
    (ready : DecodePayloadReady storage types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      DecoderReady storage types (during, before.2) ⟨args.info, guard, bytes⟩ := by
  obtain ⟨bytes, current⟩ := AccountInfo.GuardCallback.data_current ready.1 acquired
  exact ⟨bytes, current, ready.2 guard during acquired .whole bytes current⟩

/-- Every actual finite decoder-and-temporary-drop outcome survives the local
guard release, retaining its result, exit reason and callback state. -/
theorem DecodePayloadReady.retain {storage : InfoStorage} {types : PayloadTypes}
    {before : World types.Aux} {args : AccountInfo.Args}
    (ready : DecodePayloadReady storage types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (AnchorConstructOwned.Decoded types.toBase.Error
      types.Payload)
      types.toBase.Unw types.toBase.Term}
    (called : decoder storage types (during, before.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard
        (Outcome.map AnchorConstructOwned.Decoded.result produced) = some outcome ∧
      decodePayload storage types before args outcome := by
  have frame := ((ready.2 guard during acquired view bytes current).admissible produced called).map
    AnchorConstructOwned.Decoded.result
  have live := AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released⟩ := frame.release_exists live
  refine ⟨outcome, released, ?_⟩
  simp only [decodePayload, acquired, current]
  exact ⟨_, ⟨produced, called, rfl⟩, released⟩

/-- A successful source prefix reaches the real admitted data constructor.
The prefix does not fix or replace the result of the selected codec. -/
theorem construct_retain {kind : PayloadKind} {storage : InfoStorage} {types : PayloadTypes}
    {before after checked : World types.Aux} {args : AccountInfo.Args}
    (ready : ConstructReady kind storage types before args)
    (started : initialized types before args (.returned (.ok ()) after))
    (owned : (match kind with
      | .account => ownerCheck types
      | .interfaceAccount => fun state input =>
          AnchorAccount.widenCallback types.checkOwner state input.info.ownerRef)
      after args (.returned (.ok ()) checked)) :
    DecodePayloadReady storage types checked args := by
  cases kind with
  | account => exact (ready.2 after started).2 checked owned
  | interfaceAccount => exact ready.2 after started checked owned

/-- the successful shared borrow of Reload exposes the actual current data to the
decoder. Neither the old payload nor a saved byte snapshot supplies it. -/
theorem DecodeReplaceReady.callback_input {types : ReloadTypes}
    {before : World types.Aux} {args : AccountInfo.Args}
    (ready : DecodeReplaceReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) :=
  AccountInfo.GuardCallback.data_current ready.1 acquired

/-- Each real decoder/replacement exit is admitted at its reached input. Their
frames compose before releasing the still-live data guard of Account::reload. -/
theorem DecodeReplaceReady.retain {types : ReloadTypes}
    {before : World types.Aux} {args : AccountInfo.Args}
    (ready : DecodeReplaceReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Except types.toPayloadTypes.toBase.Error Unit)
      types.toPayloadTypes.toBase.Unw types.toPayloadTypes.toBase.Term}
    (called : AnchorEffects.resultBind
      (Callback.map AnchorConstructOwned.Decoded.result (AnchorAccount.widenCallback
        types.deserialize))
      (fun replacement after => Callback.map Except.ok (replacePayload types) after replacement)
      (during, before.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard produced = some outcome ∧
      decodeReplace types before args outcome := by
  have admitted := ready.2 guard during acquired view bytes current
  have frame : AccountInfo.GuardCallback.Frame (during, before.2) guard produced := by
    obtain ⟨mapped, ⟨decoded, decodedCall, mappedEq⟩, next⟩ := called
    have first := admitted.1 decoded decodedCall
    cases decoded with
    | unwound reason after => cases mappedEq; cases next; exact first
    | terminated reason => cases mappedEq; cases next; trivial
    | returned value after =>
      cases mappedEq
      dsimp only [Outcome.map] at next
      cases result : value.result with
      | error error =>
        simp only [result] at next
        cases next
        exact first
      | ok replacement =>
        simp only [result] at next
        obtain ⟨replaced, replacedCall, rfl⟩ := next
        exact AccountInfo.GuardCallback.Frame.prepend first
          ((admitted.2 value after decodedCall replacement result replaced replacedCall).map
            Except.ok)
  have live := AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released⟩ := frame.release_exists live
  exact ⟨outcome, released, by
    simp only [decodeReplace, acquired, current]
    exact ⟨produced, called, released⟩⟩

end Solanalib.Specs.Core.AnchorLifecycle
