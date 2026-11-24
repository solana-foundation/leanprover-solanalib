/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionBatchRun

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Batch

/-- Determinism is an optional property of an explicit callback interpretation,
never a requirement on the generic Batch contract. -/
def Deterministic {State Args Value Unwind Terminal : Type}
    (run : Callback.Run State Args Value Unwind Terminal) : Prop :=
  ∀ before args first second, run before args first → run before args second → first = second

/-- Framing the batch buffers adds no choices to a deterministic callback. -/
theorem framedAsRef_deterministic {types : Types} (asRef : AsRef types)
    (deterministic : Deterministic asRef) : Deterministic (framedAsRef asRef) := by
  intro before signer first second left right
  obtain ⟨actualLeft, callLeft, liftLeft⟩ := left
  obtain ⟨actualRight, callRight, liftRight⟩ := right
  have same := deterministic before.context signer actualLeft actualRight callLeft callRight
  cases same
  exact liftLeft.symm.trans liftRight

/-- A fixed callback interpretation determines the outcome of each ordered pass,
including its actual state on unwind and its state-free terminal result. -/
theorem signerPass_deterministic {types : Types} (asRef : AsRef types)
    (deterministic : Deterministic asRef)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (signers : List types.Signer) (before : State types.Ambient) (offset : Nat)
    (first second : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (left : signerPass asRef write before offset signers first)
    (right : signerPass asRef write before offset signers second) : first = second := by
  induction signers generalizing before offset first second with
  | nil => exact left.trans right.symm
  | cons signer rest ih =>
    obtain ⟨actualLeft, callLeft, tailLeft⟩ := left
    obtain ⟨actualRight, callRight, tailRight⟩ := right
    have same := framedAsRef_deterministic asRef deterministic
      before signer actualLeft actualRight callLeft callRight
    cases same
    cases actualLeft with
    | returned handle current => exact ih _ _ _ _ tailLeft tailRight
    | unwound reason current => exact tailLeft.trans tailRight.symm
    | terminated reason => exact tailLeft.trans tailRight.symm

/-- The precedence checks of the account writer and ordered pass add no choices. -/
theorem writeAccounts_deterministic {types : Types} (asRef : AsRef types)
    (deterministic : Deterministic asRef) : Deterministic (writeAccounts asRef) := by
  intro before args first second left right
  by_cases capacity : before.buffers.accounts.length - before.lengths.accounts <
      4 + args.multisigSigners.length
  · simp only [writeAccounts, capacity, ↓reduceIte] at left right
    exact left.trans right.symm
  · by_cases borrowed : (AccountView.isBorrowed before.context.world args.fromAccount ||
        AccountView.isBorrowed before.context.world args.toAccount) = true
    · simp only [writeAccounts, capacity, borrowed, ↓reduceIte] at left right
      exact left.trans right.symm
    · simp only [writeAccounts, capacity, borrowed, ↓reduceIte] at left right
      obtain ⟨actualLeft, passLeft, mapLeft⟩ := left
      obtain ⟨actualRight, passRight, mapRight⟩ := right
      have same := signerPass_deterministic asRef deterministic writeAccount
        args.multisigSigners (writeBaseAccounts before args) (before.lengths.accounts + 4)
        actualLeft actualRight passLeft passRight
      cases same
      exact mapLeft.symm.trans mapRight

/-- The metadata writer uses a new callback pass, still with no added choices. -/
theorem writeMetas_deterministic {types : Types} (asRef : AsRef types)
    (deterministic : Deterministic asRef) : Deterministic (writeMetas asRef) := by
  intro before args first second left right
  by_cases capacity : before.buffers.instructionAccounts.length -
    before.lengths.instructionAccounts <
      4 + args.multisigSigners.length
  · simp only [writeMetas, capacity, ↓reduceIte] at left right
    exact left.trans right.symm
  · simp only [writeMetas, capacity, ↓reduceIte] at left right
    obtain ⟨actualLeft, passLeft, mapLeft⟩ := left
    obtain ⟨actualRight, passRight, mapRight⟩ := right
    have same := signerPass_deterministic asRef deterministic
      (fun state offset handle => writeMeta state offset handle true false)
      args.multisigSigners (writeBaseMetas before args) (before.lengths.instructionAccounts + 4)
      actualLeft actualRight passLeft passRight
    cases same
    exact mapLeft.symm.trans mapRight

/-- With a selected deterministic callback interpretation the complete local
preparation has one finite outcome. This supplies negative controls without
restricting the generic family to deterministic callbacks. -/
theorem intoBatch_deterministic {types : Types} (asRef : AsRef types)
    (deterministic : Deterministic asRef) : Deterministic (intoBatch asRef) := by
  intro before args first second left right
  by_cases header : before.buffers.data.length < before.lengths.data + 2
  · simp only [intoBatch, header, ↓reduceIte] at left right
    exact left.trans right.symm
  · obtain ⟨dataResult, afterData, data⟩ :
        ∃ result after, writeData before args = (result, after) :=
      ⟨(writeData before args).1, (writeData before args).2, rfl⟩
    cases dataResult with
    | error reason =>
      simp only [intoBatch, header, ↓reduceIte, data] at left right
      exact left.trans right.symm
    | ok dataCount =>
      simp only [intoBatch, header, ↓reduceIte, data] at left right
      obtain ⟨accountsLeft, runLeft, restLeft⟩ := left
      obtain ⟨accountsRight, runRight, restRight⟩ := right
      have same := writeAccounts_deterministic asRef deterministic
        afterData args accountsLeft accountsRight runLeft runRight
      cases same
      cases accountsLeft with
      | unwound reason current => exact restLeft.trans restRight.symm
      | terminated reason => exact restLeft.trans restRight.symm
      | returned result current =>
        cases result with
        | error reason => exact restLeft.trans restRight.symm
        | ok accountCount =>
          obtain ⟨metasLeft, runMetasLeft, finishLeft⟩ := restLeft
          obtain ⟨metasRight, runMetasRight, finishRight⟩ := restRight
          have sameMetas := writeMetas_deterministic asRef deterministic
            current args metasLeft metasRight runMetasLeft runMetasRight
          cases sameMetas
          cases metasLeft with
          | unwound reason current => exact finishLeft.trans finishRight.symm
          | terminated reason => exact finishLeft.trans finishRight.symm
          | returned result current =>
            cases result <;> exact finishLeft.trans finishRight.symm

/-- Evaluate a predicate only when the outcome actually contains a state. -/
def OnState {State Value Unwind Terminal : Type} (predicate : State → Prop) :
    Outcome State Value Unwind Terminal → Prop
  | .returned _ state | .unwound _ state => predicate state
  | .terminated _ => True

/-- Every returning or unwinding pass preserves a selected buffer observation
when callback framing and each writer preserve it. A terminal exit has no
fabricated post-state. -/
theorem signerPass_preserves {types : Types} {Observed : Type} (asRef : AsRef types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (observe : State types.Ambient → Observed)
    (contextFrame : ∀ before context, observe { before with context } = observe before)
    (writeFrame : ∀ before offset handle, observe (write before offset handle) = observe before)
    (before : State types.Ambient) (offset : Nat) (signers : List types.Signer)
    (outcome : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (execution : signerPass asRef write before offset signers outcome) :
    OnState (fun after => observe after = observe before) outcome := by
  induction signers generalizing before offset outcome with
  | nil => cases execution; rfl
  | cons signer rest ih =>
    obtain ⟨actual, ⟨callback, _, framed⟩, tail⟩ := execution
    cases framed
    cases callback with
    | returned handle context =>
      have continued := ih _ _ _ tail
      have same : observe (write { before with context } offset handle) = observe before :=
        (writeFrame _ _ _).trans (contextFrame _ _)
      cases outcome with
      | returned value state => exact continued.trans same
      | unwound reason state => exact continued.trans same
      | terminated reason => trivial
    | unwound reason context => cases tail; exact contextFrame _ _
    | terminated reason => cases tail; trivial

/-- No account callback pass changes committed lengths, even if it unwinds. -/
theorem accountPass_lengths {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (offset : Nat) (signers : List types.Signer)
    (outcome : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (execution : signerPass asRef writeAccount before offset signers outcome) :
    OnState (fun after => after.lengths = before.lengths) outcome :=
  signerPass_preserves asRef writeAccount State.lengths (fun _ _ => rfl) (fun _ _ _ => rfl)
    before offset signers outcome execution

/-- No metadata callback pass changes committed lengths, even if it unwinds. -/
theorem metaPass_lengths {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (offset : Nat) (signers : List types.Signer)
    (outcome : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (execution : signerPass asRef (fun state index handle => writeMeta state index handle true
      false)
      before offset signers outcome) :
    OnState (fun after => after.lengths = before.lengths) outcome :=
  signerPass_preserves asRef (fun state index handle => writeMeta state index handle true false)
    State.lengths (fun _ _ => rfl) (fun _ _ _ => rfl) before offset signers outcome execution

/-- Every sent byte, account and metadata entry has the same position and
committed length as its initialized source prefix. -/
theorem request_exact {Ambient : Type} {before : State Ambient} {signers : List (List Bytes)}
    {sent : Request} (decoded : request before signers = some sent) :
    (sent.data.length = before.lengths.data ∧
      sent.data.map some = before.buffers.data.take before.lengths.data) ∧
    (sent.accounts.length = before.lengths.accounts ∧
      sent.accounts.map some = before.buffers.accounts.take before.lengths.accounts) ∧
    (sent.instructionAccounts.length = before.lengths.instructionAccounts ∧
      sent.instructionAccounts.map some =
        before.buffers.instructionAccounts.take before.lengths.instructionAccounts) := by
  obtain ⟨metas, data, accounts, _⟩ := request_parts decoded
  exact ⟨initializedPrefix_exact data, initializedPrefix_exact accounts, initializedPrefix_exact
    metas⟩

/-- An unchecked unit-returning provider cannot produce an ordinary ProgramError
through this wrapper, regardless of the state effects of the provider. -/
theorem invokeSigned_no_error {types : Types} (before after : State types.Ambient)
    (args : InvokeCall types) (reason : Error) :
    ¬ invokeSigned before args (.returned (.error reason) after) := by
  rintro ⟨_, _, actual, _, equality⟩
  cases actual <;> cases equality

end Solanalib.Specs.Core.Token.Batch
