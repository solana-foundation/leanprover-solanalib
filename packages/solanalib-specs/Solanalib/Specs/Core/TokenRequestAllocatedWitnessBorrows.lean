/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedBorrowAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessProviders
public import Solanalib.Specs.Core.OwnedArrayFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

open AllocatedControl Admission

private def AccountsReturn {Args Value Unwind Terminal : Type}
    (call : Callback.Run State Args Value Unwind Terminal) : Prop :=
  ∀ before args value after, call before args (.returned value after) → after.1 = before.1

private theorem accounts_arguments {Args Selected Value Unwind Terminal : Type}
    {call : Callback.Run State Args Value Unwind Terminal}
    (law : AccountsReturn call) (select : Selected → Args) :
    AccountsReturn (fun before args => call before (select args)) := by
  intro before args
  exact law before (select args)

private theorem accounts_bind {Args Value Next Unwind Terminal : Type}
    {first : Callback.Run State Args Value Unwind Terminal}
    {next : Value → State → Outcome State Next Unwind Terminal → Prop}
    (firstLaw : AccountsReturn first)
    (nextLaw : ∀ value, AccountsReturn (fun state (_ : Unit) => next value state)) :
    AccountsReturn (Callback.bind first next) := by
  rintro before args value after ⟨produced, called, rest⟩
  cases produced with
  | returned item during =>
    exact (nextLaw item during () value after rest).trans
      (firstLaw before args item during called)
  | unwound _ _ | terminated _ => cases rest

private theorem accounts_map {Args Value Next Unwind Terminal : Type}
    {call : Callback.Run State Args Value Unwind Terminal}
    (law : AccountsReturn call) (f : Value → Next) : AccountsReturn (Callback.map f call) := by
  rintro before args value after ⟨produced, called, equal⟩
  cases produced with
  | returned item during => cases equal; exact law before args _ _ called
  | unwound _ _ | terminated _ => cases equal

private theorem accounts_focus {Inner Args Value Unwind Terminal : Type}
    (part : Owned.Focus State Inner) (outside : ∀ before inner, (part.set before inner).1 =
      before.1)
    (call : Callback.Run Inner Args Value Unwind Terminal) : AccountsReturn (part.lift call) := by
  rintro before args value after ⟨produced, _, equal⟩
  cases produced with
  | returned item during => cases equal; exact outside before during
  | unwound _ _ | terminated _ => cases equal

private theorem cleanup_return_origin {Value Unwind Terminal : Type}
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

private theorem accounts_protect {Args Value Unwind Terminal : Type}
    {call : Callback.Run State Args Value Unwind Terminal}
    (law : AccountsReturn call) (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal)) :
    AccountsReturn (Owned.protect double drops call) := by
  rintro before args value after ⟨produced, called, exitProof⟩
  cases produced with
  | returned item during => cases exitProof; exact law before args _ _ called
  | unwound _ _ =>
    obtain ⟨_, impossible⟩ := cleanup_return_origin double drops exitProof
    cases impossible
  | terminated _ =>
    obtain ⟨_, impossible⟩ := cleanup_return_origin double drops exitProof
    cases impossible

private theorem moveOnOk_success {Value : Type} {before after : State} {value : Value}
    {body : Run sampleTypes Value} {drops : List (Owned.DropAction State Nat Nat)}
    (called : moveOnOk sampleTypes.doubleUnwind drops body before (.returned (.ok value) after)) :
    body before (.returned (.ok value) after) := by
  obtain ⟨produced, executed, rest⟩ := called
  cases produced with
  | returned result during =>
    cases result with
    | ok item => cases rest; exact executed
    | error _ =>
      obtain ⟨_, impossible⟩ := cleanup_return_origin sampleTypes.doubleUnwind drops rest
      cases impossible
  | unwound _ _ | terminated _ =>
    obtain ⟨_, impossible⟩ := cleanup_return_origin sampleTypes.doubleUnwind drops rest
    cases impossible

private theorem write_data_accounts (resource : Nat) (steps : List InstructionAllocated.DataStep) :
    AccountsReturn (InstructionAllocated.writeData sampleTypes.constructor resource steps) := by
  induction steps with
  | nil => intro _ _ _ _ called; cases called; rfl
  | cons step rest induction =>
    cases step with
    | push byte =>
      exact accounts_bind
        (accounts_arguments (accounts_focus bytesFocus (fun _ _ => rfl) Owned.vectorReference.push)
          (fun (_ : Unit) => (resource, byte))) (fun _ => induction)
    | extend bytes =>
      exact accounts_bind
        (accounts_arguments (accounts_focus bytesFocus (fun _ _ => rfl)
          Owned.vectorReference.extend)
          (fun (_ : Unit) => (resource, bytes))) (fun _ => induction)

private theorem push_metas_accounts (resource : Nat) (items : List Solanalib.Runtime.CpiMeta) :
    AccountsReturn (InstructionAllocated.pushMetas sampleTypes.constructor resource items) := by
  induction items with
  | nil => intro _ _ _ _ called; cases called; rfl
  | cons item rest induction =>
    exact accounts_bind
      (accounts_arguments (accounts_focus metasFocus (fun _ _ => rfl) Owned.vectorReference.push)
        (fun (_ : Unit) => (resource, item))) (fun _ => induction)

private theorem build_metas_accounts (plan : InstructionAllocated.MetaPlan) :
    AccountsReturn (InstructionAllocated.buildMetas sampleTypes.constructor plan) := by
  cases plan with
  | fromList items =>
    exact accounts_arguments
      (accounts_focus metasFocus (fun _ _ => rfl) Owned.vectorReference.fromList) (fun (_ : Unit)
        => items)
  | withCapacity capacity items =>
    exact accounts_bind
      (accounts_arguments (accounts_focus metasFocus (fun _ _ => rfl)
        Owned.vectorReference.withCapacity)
        (fun (_ : Unit) => capacity))
      (fun resource => accounts_protect (accounts_map (push_metas_accounts resource items) (fun _
        => resource)) _ _)
  | fromListThenPush initial rest =>
    exact accounts_bind
      (accounts_arguments (accounts_focus metasFocus (fun _ _ => rfl)
        Owned.vectorReference.fromList)
        (fun (_ : Unit) => initial))
      (fun resource => accounts_protect (accounts_map (push_metas_accounts resource rest) (fun _ =>
        resource)) _ _)

private theorem build_data_accounts (steps : List InstructionAllocated.DataStep) :
    AccountsReturn (InstructionAllocated.buildData sampleTypes.constructor steps) :=
  accounts_bind
    (accounts_arguments (accounts_focus bytesFocus (fun _ _ => rfl)
      Owned.vectorReference.withCapacity)
      (fun (_ : Unit) => sampleTypes.tokenEnumSize))
    (fun resource => accounts_protect (accounts_map (write_data_accounts resource steps) (fun _ =>
      resource)) _ _)

private theorem constructor_accounts (plan : InstructionAllocated.Plan) :
    AccountsReturn (fun state (_ : Unit) => InstructionAllocated.run sampleTypes.constructor state
      plan) := by
  cases accepted : Instruction.checkProgram plan.programs plan.programId with
  | error error =>
    intro before args value after called
    simp only [InstructionAllocated.run, accepted] at called
    cases called
    rfl
  | ok completed =>
    cases completed
    cases order : plan.order with
    | dataThenMetas =>
      intro before input value after called
      simp only [InstructionAllocated.run, accepted, order] at called
      exact accounts_bind
        (accounts_arguments (accounts_focus bytesFocus (fun _ _ => rfl)
          Owned.vectorReference.withCapacity)
          (fun (_ : Unit) => sampleTypes.tokenEnumSize))
        (fun resource => accounts_protect
          (accounts_bind (write_data_accounts resource plan.dataSteps)
            (fun _ => accounts_map (build_metas_accounts plan.metas) _)) _ _) before () value after
              called
    | metasThenData =>
      intro before input value after called
      simp only [InstructionAllocated.run, accepted, order] at called
      exact accounts_bind (build_metas_accounts plan.metas)
        (fun _ => accounts_protect (accounts_map (build_data_accounts plan.dataSteps) _) _ _)
          before () value after called

private theorem rc_clone_accounts : AccountsReturn rcOps.cloneRc := by
  rintro before input value after ⟨_, same⟩
  cases same
  rfl

private theorem clone_call_accounts : AccountsReturn (AccountInfoRc.cloneCall rcOps) := by
  intro before info value after called
  exact accounts_bind
    (accounts_arguments rc_clone_accounts (fun (_ : Unit) => (.lamports, info.lamports)))
    (fun _ => accounts_map
      (accounts_arguments rc_clone_accounts (fun (_ : Unit) => (.data, info.data)))
      (fun _ => AccountInfo.clone info)) before () value after called

private theorem clone_lift_accounts :
    AccountsReturn (AccountInfoRc.lift (Unwind := Nat) (AccountInfoRc.cloneCall rcOps)) := by
  rintro before info value after ⟨produced, called, equal⟩
  cases produced with
  | returned item during => cases equal; exact clone_call_accounts before info _ _ called
  | unwound impossible _ => exact nomatch impossible
  | terminated _ => cases equal

private theorem initial_expression_accounts (args : Onchain.Args) :
    AccountsReturn (initialInfoAt sampleTypes args) := by
  intro before index value after called
  unfold initialInfoAt at called
  split at called
  · exact clone_lift_accounts before _ value after called
  · exact False.elim called

private theorem literal_work_accounts : AccountsReturn sampleTypes.infoLiteral.work := by
  intro before input command after called
  change (if input.2.length < input.1 then _ else _) at called
  split at called
  · cases called; rfl
  · cases called.2; rfl

private theorem initial_prefix_accounts (args : Onchain.Args)
    {prior values : List AccountInfo.Value} {before after : State}
    (called : Owned.Array.PrefixTrace sampleTypes.literalProvider 4 (initialInfoAt sampleTypes args)
      prior before values after) : after.1 = before.1 := by
  induction called with
  | stop => rfl
  | again values finalValues before middle after work rest induction =>
    exact induction.trans (literal_work_accounts before (4, values) .again middle work)
  | next values finalValues before ready middle after value bound work expression rest induction =>
    exact induction.trans ((initial_expression_accounts args ready values.length value middle
      expression).trans
      (literal_work_accounts before (4, values) .evaluate ready work))

private theorem initial_infos_accounts (args : Onchain.Args) :
    AccountsReturn (fun state (_ : Unit) => initialInfos sampleTypes args state) := by
  rintro before input value after ⟨produced, ⟨detailed, trace, erased⟩, mapped⟩
  cases produced with
  | unwound _ _ | terminated _ => cases mapped
  | returned resource during =>
    cases mapped
    cases detailed with
    | unwound _ _ | terminated _ => cases erased
    | returned actual finishState =>
      cases erased
      obtain ⟨values, ready, completing, progress, _, work, finished⟩ :=
        trace.returned_decomposition rfl
      exact (accounts_focus infosFocus (fun _ _ => rfl) Owned.vectorReference.fromList
        completing values _ _ finished).trans
        ((literal_work_accounts ready (4, values) .finish completing work).trans
          (initial_prefix_accounts args progress))

/-- Every successful sample base prefix keeps the source account cells and
guard world, although constructors and clones change the auxiliary ledgers. -/
theorem sample_base_accounts {args : Onchain.Args} {before after : State} {prepared : Prepared
  sampleTypes}
    (called : base sampleTypes args before (.returned (.ok prepared) after)) : after.1 = before.1
      := by
  obtain ⟨built, constructed, rest⟩ := called
  cases built with
  | unwound _ _ | terminated _ => cases rest
  | returned result builtState =>
    cases result with
    | error _ => cases rest
    | ok instruction =>
      have first := constructor_accounts (transferPlan args) before () (.ok instruction) builtState
        constructed
      obtain ⟨listed, infosBuilt, continuation⟩ := moveOnOk_success rest
      cases listed with
      | unwound _ _ | terminated _ => cases continuation
      | returned result infoState =>
        cases result with
        | error _ => cases continuation
        | ok infos =>
          have second := initial_infos_accounts args builtState () (.ok infos) infoState infosBuilt
          obtain ⟨recognized, selected, returned⟩ := moveOnOk_success continuation
          obtain ⟨checked, checkedCall, checkedRest⟩ := selected
          change checked = .returned (.ok false) infoState at checkedCall
          cases checkedCall
          cases checkedRest
          cases returned
          exact second.trans first

private theorem no_hook_entry (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey)
    (before : State) (outcome : Outcome State (Except Error (Solanalib.Runtime.Pubkey ×
      AccountInfo.Value ×
      Option AccountInfo.Value)) Nat Nat) : ¬ hookEntry sampleTypes args programId before outcome
        := by
  rintro ⟨_, ⟨_, ⟨_, source⟩, _⟩, _⟩
  obtain ⟨_, ⟨_, impossible, _⟩, _⟩ := source
  exact impossible

/-- The unchanged sample needs data admission only at its reached mint
borrow. Its constant non-token owner bypasses authority reads; its unavailable
PDA dependency has no validation or collection prefix. -/
theorem sample_borrows (deps : Dependencies sampleTypes)
    (protocol : AllocatedCollect.Protocol Extra Nat Nat Nat) :
    BorrowReady sampleTypes deps protocol initialState Onchain.witnessArgs := by
  have noValidation : ∀ helperArgs execute info before,
      ¬ ValidationPrefix sampleTypes initialState Onchain.witnessArgs helperArgs execute info
        before := by
    intro helperArgs execute info before reached
    cases reached with
    | reached _ _ _ entered _ _ => exact no_hook_entry _ _ _ _ entered
  intro kind before info reached
  cases reached with
  | authorityLength _ owned =>
    have nonToken : Solanalib.Runtime.Pubkey.zero ≠ token2022ProgramId ∧
      Solanalib.Runtime.Pubkey.zero ≠ legacyProgramId := by
      decide +kernel
    rcases owned with token | legacy
    · exact False.elim (nonToken.1 token)
    · exact False.elim (nonToken.2 legacy)
  | authorityUnchecked _ selected _ =>
    change (Outcome.returned (.ok true) _ : Outcome State (Except Error Bool) Nat Nat) =
      .returned (.ok false) _ at selected
    cases selected
  | mint based =>
    have same : before.1 = Onchain.witnessState := sample_base_accounts based
    refine ⟨?_, fun _ _ _ _ => ?_, fun impossible => nomatch impossible⟩
    · apply AccountInfo.DataBorrow.ready_of_data
        (bytes := Onchain.witnessMintBytes) (policy := AccountInfo.sampleProfile.policy)
      rw [same]
      rfl
    · rw [same]
      exact Onchain.witnessInfo_valid.2.1
  | validation reached => exact False.elim (noValidation _ _ _ _ reached)
  | collection reached _ _ _ _ _ _ _ _ => exact False.elim (noValidation _ _ _ _ reached)

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
