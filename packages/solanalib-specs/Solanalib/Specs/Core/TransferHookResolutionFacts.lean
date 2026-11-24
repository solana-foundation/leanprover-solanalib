/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolutionRun
public import Solanalib.Specs.Core.OwnedArrayFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.TransferHookResolution

open Token (Error Bytes)
open Token.AllocatedControl

private theorem cleanup_return_origin {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    {pending : Outcome State Value Unwind Terminal} {value : Value} {after : State}
    (called : Owned.cleanup double drops pending (.returned value after)) :
    ∃ before, pending = .returned value before := by
  induction drops generalizing pending with
  | nil => cases called; exact ⟨after, rfl⟩
  | cons action rest induction =>
    cases pending with
    | terminated _ => cases called
    | unwound _ _ =>
      rcases Owned.Array.cleanup_unwound_shape double (action :: rest) called with
        ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible
    | returned item before =>
      obtain ⟨dropped, _, next⟩ := called
      cases dropped with
      | terminated _ => cases next
      | returned completed during =>
        cases completed
        obtain ⟨_, equal⟩ := induction next
        cases equal
        exact ⟨before, rfl⟩
      | unwound reason during =>
        rcases Owned.Array.cleanup_unwound_shape double rest next with
          ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible


/-- A successful question-mark sequence contains two actual successful calls
in their exact intermediate state. -/
theorem bind_ok {State Value Next Unwind Terminal : Type}
    (first : Token.AllocatedControl.Run State Value Unwind Terminal)
    (next : Value → Token.AllocatedControl.Run State Next Unwind Terminal)
    (before after : State) (value : Next) :
    bind first next before (.returned (.ok value) after) ↔
      ∃ middle item, first before (.returned (.ok item) middle) ∧
        next item middle (.returned (.ok value) after) := by
  constructor
  · rintro ⟨outcome, step, rest⟩
    cases outcome with
    | returned result middle =>
      cases result with
      | ok item => exact ⟨middle, item, step, rest⟩
      | error error => cases rest
    | unwound reason middle => cases rest
    | terminated reason => cases rest
  · rintro ⟨middle, item, step, rest⟩
    exact ⟨.returned (.ok item) middle, step, rest⟩

/-- Lifting a dependency preserves its ordinary value and actual after-state. -/
theorem perform_ok {State Value Unwind Terminal : Type}
    (call : State → Outcome State Value Unwind Terminal → Prop)
    (before after : State) (value : Value) :
    perform call before (.returned (.ok value) after) ↔ call before (.returned value after) := by
  constructor
  · rintro ⟨pending, step, same⟩
    cases pending with
    | returned item middle => cases same; exact step
    | unwound reason middle => cases same
    | terminated reason => cases same
  · intro step
    exact ⟨.returned value after, step, rfl⟩

/-- Exceptional cleanup cannot manufacture success, and successful move-out
runs no destructor on the retained value. -/
theorem moveOnOk_ok {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Token.AllocatedControl.Run State Value Unwind Terminal)
    (before after : State) (value : Value) :
    moveOnOk double drops body before (.returned (.ok value) after) ↔
      body before (.returned (.ok value) after) := by
  constructor
  · rintro ⟨pending, step, rest⟩
    cases pending with
    | returned result middle =>
      cases result with
      | ok item => cases rest; exact step
      | error error =>
        obtain ⟨_, impossible⟩ := cleanup_return_origin double drops rest
        cases impossible
    | unwound reason middle =>
      obtain ⟨_, impossible⟩ := cleanup_return_origin double drops rest
      cases impossible
    | terminated reason =>
      obtain ⟨_, impossible⟩ := cleanup_return_origin double drops rest
      cases impossible
  · intro step
    exact ⟨.returned (.ok value) after, step, rfl⟩

/-- A normal clone preserves every AccountInfo field and its cell aliases,
while its Rc dependency retains its own exact state effects. -/
theorem cloneInfo_identity (types : Types) (before after : World types.Extra)
    (info result : AccountInfo.Value)
    (cloned : cloneInfo types info before (.returned (.ok result) after)) : result = info := by
  have actual := (perform_ok _ before after result).mp cloned
  obtain ⟨pending, called, same⟩ := actual
  cases pending with
  | returned value final => cases same; exact AccountInfoRc.clone_identity types.rc called
  | unwound impossible final => exact nomatch impossible
  | terminated reason => cases same

/-- Successful helper entry proves the actual initial PDA call returned,
then selects the first matching program and validation accounts. No account
lookup can bypass a failed PDA call. -/
theorem hookEntry_ok (types : Types) (args : Args types) (programId : Solanalib.Runtime.Pubkey)
    (before after : World types.Extra) (validationKey : Solanalib.Runtime.Pubkey)
    (program : AccountInfo.Value) (validation : Option AccountInfo.Value)
    (entered : hookEntry types args programId before
      (.returned (.ok (validationKey, program, validation)) after)) :
    ∃ bump, types.findPda before (hookPdaInputs args programId)
        (.returned (validationKey, bump) after) ∧
      findAccount args.additional programId = some program ∧
      validation = findAccount args.additional validationKey := by
  obtain ⟨middle, ⟨key, bump⟩, pda, rest⟩ := (bind_ok _ _ _ _ _).mp entered
  have call := (perform_ok _ _ _ _).mp pda
  unfold hookEntry at entered
  cases found : args.additional.find? (fun info => info.key == programId) with
  | none => simp only [found, fail] at rest; cases rest
  | some selected =>
    simp only [found, Token.AllocatedControl.pure] at rest
    cases rest
    exact ⟨bump, call, found, rfl⟩

/-- Even on an ordinary error, the callback history of the collection is an ordered
prefix of the current Execute-info iterator. The exact trace retains every
acquired Ref and the prefix cleanup before that outcome. -/
theorem collectRefs_trace (types : Types) (resource : types.InfoResource)
    (before : World types.Extra)
    (outcome : Outcome (World types.Extra) (Except Error types.GuardResource)
      types.Unwind types.Terminal)
    (collected : collectRefs types resource before outcome) :
    ∃ infos calls, types.infos.current before resource = some infos ∧
      Token.AllocatedCollect.Trace types.collectProtocol (infoIterator types resource infos.length)
        (borrowElement types) 0 [] before calls outcome ∧
      calls = List.range' 0 calls.length ∧ calls.length ≤ infos.length := by
  obtain ⟨pending, observed, next⟩ := collected
  obtain ⟨infos, current, rfl⟩ := observed
  obtain ⟨calls, trace⟩ := next
  exact ⟨infos, calls, current, trace, by simpa using trace.calls_prefix,
    by simpa only [Nat.zero_add, infoIterator] using trace.calls_bound⟩

/-- Every normal resolved append uses current metadata for independent
privilege reduction, selects the first additional alias, clones that exact
AccountInfo, pushes its metadata, then moves the clone into the info vector. -/
theorem appendResolved_ok (types : Types) (args : Args types) (execute : Execute types)
    (resolved : Solanalib.Runtime.CpiMeta) (before after : World types.Extra)
    (appended : appendResolved types args execute resolved before (.returned (.ok ()) after)) :
    ∃ previous selected clonedState metaState,
      types.metas.current before execute.instruction.metas = some previous ∧
      findAccount args.additional resolved.key = some selected ∧
      cloneInfo types selected before (.returned (.ok selected) clonedState) ∧
      types.metas.push clonedState (execute.instruction.metas, deescalate previous resolved)
        (.returned () metaState) ∧
      types.infos.push metaState (execute.infos, selected) (.returned () after) := by
  obtain ⟨middle, previous, observed, rest⟩ := (bind_ok _ _ _ _ _).mp appended
  obtain ⟨actual, current, equal⟩ := observed
  cases equal
  cases found : args.additional.find? (fun info => info.key == (deescalate previous resolved).key)
    with
  | none => simp only [found, fail] at rest; cases rest
  | some selected =>
    simp only [found] at rest
    obtain ⟨clonedState, cloned, clone, rest⟩ := (bind_ok _ _ _ _ _).mp rest
    have same := cloneInfo_identity types before clonedState selected cloned clone
    subst cloned
    obtain ⟨metaState, returnedUnit, pushed, info⟩ := (bind_ok _ _ _ _ _).mp rest
    cases returnedUnit
    have pushed := (moveOnOk_ok _ _ _ _ _ _).mp pushed
    exact ⟨previous, selected, clonedState, metaState, current, found, clone,
      (perform_ok _ _ _ _).mp pushed, (perform_ok _ _ _ _).mp info⟩

/-- The registered operational contract requires no redundant mathematical
hypotheses. Valid Rust resources, borrowed lifetimes, low-call realization and
current-state frames remain explicit Rust-binding obligations. -/
def family : Family where
  Index := Types
  State := fun types => World types.Extra
  Args := Args
  Value := fun _ => Except Error Unit
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := run types }

/-- The independent mathematical reference is this finite dependency/control
relation; it supplies no Rust implementation theorem. -/
def reference : FamilyRun family := run

theorem reference_correct : FamilyReference family reference :=
  fun _ _ _ _ _ execution => execution

end Solanalib.Specs.Core.TransferHookResolution
