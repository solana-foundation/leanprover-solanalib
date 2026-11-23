/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedGuards

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.AllocatedGuard

/-- One real shared acquisition in the common AccountInfo sample. -/
def heldAccounts : AccountInfo.State :=
  { AccountInfo.sampleState with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] }

/-- The acquired source reference keeps its actual guard id and slice length. -/
def reference : AllocatedControl.DataRef := ⟨⟨0, 0⟩, 3⟩

/-- Observable auxiliary effects are deliberately separate from held bytes. -/
abbrev State := World Nat

/-- The callback starts with a live reference and nonzero auxiliary state. -/
def held : State := (heldAccounts, 4)

/-- Exact validity follows from the actual common acquisition operation. -/
theorem held_valid : heldAccounts.Valid :=
  Borrow.acquire_valid AccountInfo.sample_valid.2.1 ⟨1⟩ .shared .whole

/-- The initial observation follows the actual live current cell. -/
theorem held_read : reference.read held = some [10, 20, 30] := rfl

/-- This real finite primitive exit consumes a guard held by its caller. -/
def destroys {Extra : Type} : Callback.Run (World Extra) Unit Unit Nat Nat :=
  fun before _ outcome =>
    outcome = .returned () ((Borrow.release before.1 reference.guard).2, before.2)

/-- The destructive primitive has an actual ordinary return. -/
theorem destroying_exit : destroys held ()
    (.returned () ({ AccountInfo.sampleState with slots := [none] }, 4)) := rfl

/-- The unchanged raw source composition would lose that exit at its next read. -/
def killedRead : AllocatedControl.Run State Bytes Nat Nat :=
  AllocatedControl.bind (AllocatedControl.perform (fun before => destroys before ()))
    (fun _ => AllocatedControl.inspect reference.read)

/-- No later read can turn the consumed identity into live source bytes. -/
theorem killed_read_has_no_exit : ∀ outcome, ¬ killedRead held outcome := by
  rintro outcome ⟨pending, ⟨actual, destroyed, mapped⟩, continued⟩
  cases destroyed
  cases mapped
  obtain ⟨bytes, read, _⟩ := continued
  cases read

/-- A whole-body finite-exit premise would be vacuous for this bad prefix. -/
theorem complete_body_frame_is_vacuous : AccountInfo.GuardCallback.Admissible
    reference.guard (fun before (_ : Unit) => killedRead before) held () := by
  intro outcome impossible
  exact False.elim (killed_read_has_no_exit outcome impossible)

/-- The new primitive law rejects the same real exit before that lost read. -/
theorem destroying_primitive_rejected : ¬ Preserves (destroys (Extra := Nat)) := by
  intro law
  have impossible := law.read_returned held_valid held_read destroying_exit
  cases impossible

/-- Malformed guard cleanup remains partial; no successful drop is invented. -/
theorem killed_guard_cannot_drop : ∀ outcome,
    ¬ reference.drop (Unwind := Nat) (Terminal := Nat)
      (({ AccountInfo.sampleState with slots := [none] }, 4) : State) outcome := by
  intro _ impossible
  exact False.elim impossible

/-- Replace the metadata provider by the same guard-destroying operation. -/
def badTypes : OnchainAllocated.Types :=
  { OnchainAllocated.Witness.sampleTypes with
    metas := { OnchainAllocated.Witness.sampleTypes.metas with
      push := fun before _ => destroys before () } }

/-- The conditional metadata-push law rejects its actual destructive exit,
independently of whether a complete invocation has an outcome. -/
theorem bad_metadata_push_rejected : ¬ Preserves badTypes.metas.push := by
  intro law
  have readable : reference.read ((heldAccounts, {}) : OnchainAllocated.Witness.State) =
      some [10, 20, 30] := rfl
  have impossible := law.read_returned held_valid readable
    (args := ((0 : Nat), Instruction.accountMeta .zero false false)) (by rfl)
  cases impossible

/-- The unchanged collector and invocation relations give a concrete bad index. -/
def badDependencies : OnchainAllocated.Dependencies badTypes :=
  { collect := OnchainAllocated.Witness.sampleDependencies.collect
    invoke := OnchainAllocated.Witness.sampleDependencies.invoke }

/-- The contract rejects the finite guard-destroying primitive before its
later read can erase the exit. The raw callback and failed read stay exact. -/
theorem bad_family_rejects_destroyed_guard_prefix :
    ¬ (OnchainAllocated.family.contract ⟨badTypes, badDependencies⟩).requires
      ((heldAccounts, {}) : OnchainAllocated.Witness.State) Onchain.witnessArgs ∧
    badTypes.metas.push (heldAccounts, {})
      ((0 : Nat), Instruction.accountMeta .zero false false)
      (.returned () ({ AccountInfo.sampleState with slots := [none] }, {})) ∧
    reference.read (({ AccountInfo.sampleState with slots := [none] }, {}) :
      OnchainAllocated.Witness.State) = none := by
  refine ⟨?_, rfl, rfl⟩
  rintro ⟨_, ready, _⟩
  exact bad_metadata_push_rejected (ready.primitive .metasPush).1

/-- A provider may mutate its auxiliary state and return, unwind or terminate. -/
def effects : Callback.Run State Unit Unit Nat Nat := fun before _ outcome =>
  outcome = .returned () (before.1, before.2 + 7) ∨
  outcome = .unwound 23 (before.1, before.2 + 7) ∨ outcome = .terminated 91

/-- Every actual normal/unwind exit preserves the held footprint, while its
nontrivial auxiliary mutation remains visible. -/
theorem effects_admitted : Preserves effects := by
  apply Preserves.of_accounts
  intro before args outcome called
  rcases called with normal | unwind | terminal
  · cases normal; rfl
  · cases unwind; rfl
  · cases terminal; trivial

/-- The same effects satisfy independent input typing even with no guards. -/
theorem effects_inputs : InputPreserves 64 effects := by
  apply InputPreserves.of_accounts
  intro before args outcome called
  rcases called with normal | unwind | terminal
  · cases normal; rfl
  · cases unwind; rfl
  · cases terminal; trivial

/-- The actual effect, current read and checked release are composed in order. -/
def effectBody : AllocatedControl.Run State Bytes Nat Nat :=
  AllocatedControl.bind (AllocatedControl.perform (fun before => effects before ()))
    (fun _ => AllocatedControl.inspect reference.read)

/-- The double-unwind policy of the fixture is explicit; a data-guard drop cannot
itself unwind in this mathematical model. -/
def double : Owned.DoubleUnwind State Nat Nat := fun _ first later terminal => terminal = first +
  later

/-- All finite primitive exits survive the read and the cleanup of the same guard. -/
theorem every_effect_retained (pending : Outcome State Unit Nat Nat)
    (called : effects held () pending) :
    ∃ observed final, effectBody held observed ∧
      AccountInfo.GuardCallback.releaseOutcome reference.guard observed = some final ∧
      AllocatedControl.scope double [reference.drop] effectBody held final :=
  perform_read_scope_retains double effects_admitted held_valid held_read called

/-- Normal cleanup retains changed auxiliary state and current source bytes. -/
theorem normal_effect_executes : AllocatedControl.scope double [reference.drop] effectBody held
    (.returned (.ok [10, 20, 30]) ({ AccountInfo.sampleState with slots := [none] }, 11)) := by
  refine ⟨.returned (.ok [10, 20, 30]) (heldAccounts, 11), ?_, ?_⟩
  · exact ⟨.returned (.ok ()) (heldAccounts, 11),
      ⟨.returned () (heldAccounts, 11), Or.inl rfl, rfl⟩, [10, 20, 30], rfl, rfl⟩
  · exact (data_cleanup_iff double reference _ _).mpr rfl

/-- Unwind cleanup uses the actual changed state and preserves its reason. -/
theorem unwind_effect_executes : AllocatedControl.scope double [reference.drop] effectBody held
    (.unwound 23 ({ AccountInfo.sampleState with slots := [none] }, 11)) := by
  refine ⟨.unwound 23 (heldAccounts, 11), ?_, ?_⟩
  · exact ⟨.unwound 23 (heldAccounts, 11),
      ⟨.unwound 23 (heldAccounts, 11), Or.inr (Or.inl rfl), rfl⟩, rfl⟩
  · exact (data_cleanup_iff double reference _ _).mpr rfl

/-- Terminal exits bypass both the next source read and destructor execution. -/
theorem terminal_effect_executes : AllocatedControl.scope double [reference.drop] effectBody held
    (.terminated 91) := by
  refine ⟨.terminated 91, ?_, rfl⟩
  exact ⟨.terminated 91, ⟨.terminated 91, Or.inr (Or.inr rfl), rfl⟩, rfl⟩

/-- A subsequent ordinary ProgramError still runs real guard cleanup. -/
theorem error_effect_executes : AllocatedControl.scope double [reference.drop]
    (AllocatedControl.bind (AllocatedControl.perform (fun before => effects before ()))
      (fun _ => AllocatedControl.fail .InvalidAccountData)) held
    (.returned (.error .InvalidAccountData : Except Error Unit)
      ({ AccountInfo.sampleState with slots := [none] }, 11)) := by
  refine ⟨.returned (.error .InvalidAccountData) (heldAccounts, 11), ?_, ?_⟩
  · exact ⟨.returned (.ok ()) (heldAccounts, 11),
      ⟨.returned () (heldAccounts, 11), Or.inl rfl, rfl⟩, rfl⟩
  · exact (data_cleanup_iff double reference _ _).mpr rfl

/-- Dropping a second live alias is allowed and keeps the original token live. -/
theorem owned_alias_drop_preserves_outer :
    (AllocatedControl.DataRef.mk ⟨1, 0⟩ 3).drop (Unwind := Nat) (Terminal := Nat)
      (({ heldAccounts with slots := heldAccounts.slots ++ [some ⟨⟨1⟩, .shared, 0, .whole⟩] }, 4) :
        State)
      (.returned () ({ heldAccounts with slots := heldAccounts.slots ++ [none] }, 4)) ∧
    reference.read (({ heldAccounts with slots := heldAccounts.slots ++ [none] }, 4) : State) =
      some [10, 20, 30] := ⟨rfl, rfl⟩

/-- A live guard and an allocated empty metadata vector in the sample provider. -/
def metadataBefore : OnchainAllocated.Witness.State :=
  (heldAccounts, { metas := [some []] })

/-- The actual insertion changes only the current vector contents. -/
def metadataAfter : OnchainAllocated.Witness.State :=
  (heldAccounts, { metas := [some [Instruction.accountMeta .zero false false]] })

/-- The real vector operation of the sample has a nonempty finite state effect. -/
theorem sample_metadata_push : OnchainAllocated.Witness.sampleTypes.metas.push metadataBefore
    ((0 : Nat), Instruction.accountMeta .zero false false) (.returned () metadataAfter) :=
  ⟨.returned () [some [Instruction.accountMeta .zero false false]], ⟨[], rfl, rfl⟩, rfl⟩

/-- The primitive helper is consumed by a real push to retain the exact
current data read. The family supplies this law through its admission. -/
theorem sample_metadata_read_retained : reference.read metadataAfter = some [10, 20, 30] :=
  after_meta_push (Preserves.focus OnchainAllocated.Witness.metasFocus
    (fun _ _ => rfl) Owned.vectorReference.push)
    held_valid (show reference.read metadataBefore = some [10, 20, 30] from rfl)
    sample_metadata_push

/-- Actual family admission retains the finite effect of the push through the
next held-data read and the same checked guard release. -/
theorem sample_family_primitive_continues :
    ∃ observed final,
      AllocatedControl.bind
        (AllocatedControl.perform fun state => OnchainAllocated.Witness.sampleTypes.metas.push
          state ((0 : Nat), Instruction.accountMeta .zero false false))
        (fun _ => AllocatedControl.inspect reference.read) metadataBefore observed ∧
      AccountInfo.GuardCallback.releaseOutcome reference.guard observed = some final ∧
      AllocatedControl.scope OnchainAllocated.Witness.sampleTypes.doubleUnwind [reference.drop]
        (AllocatedControl.bind
          (AllocatedControl.perform fun state => OnchainAllocated.Witness.sampleTypes.metas.push
            state ((0 : Nat), Instruction.accountMeta .zero false false))
          (fun _ => AllocatedControl.inspect reference.read)) metadataBefore final :=
  OnchainAllocated.family_primitive_retain OnchainAllocated.Witness.sample_ready
    .metasPush held_valid (show reference.read metadataBefore = some [10, 20, 30] from rfl)
    sample_metadata_push

/-- The registered family supplies the input domain of the actual mint prefix.
Its successful acquisition reads and releases the source Ref without an
additional validity or typed-cell hypothesis in this control. -/
theorem sample_family_mint_scope :
    ∃ bytes : Bytes,
      AllocatedControl.withData OnchainAllocated.Witness.sampleTypes.raise
        OnchainAllocated.Witness.sampleTypes.doubleUnwind true Onchain.witnessArgs.mint
        (fun reference => AllocatedControl.inspect reference.read)
        OnchainAllocated.Witness.infosState
        (.returned (.ok bytes)
          ((Borrow.release OnchainAllocated.Witness.mintBorrowWorld
            OnchainAllocated.Witness.mintReference.guard).2,
            OnchainAllocated.Witness.infosState.2)) := by
  obtain ⟨protocol, _, _, borrows⟩ := OnchainAllocated.Witness.sample_ready
  exact borrows.acquired_read_scope (.mint OnchainAllocated.Witness.base_returns)
    (by decide) (by rfl)

/-- Its same full execution still reaches the actual cleaned final state. -/
theorem full_sample_executes :
    FamilyHasExecution OnchainAllocated.family OnchainAllocated.reference
      OnchainAllocated.Witness.sample := OnchainAllocated.Witness.has_execution

/-- This mathematical input exceeds the Rust amount width. Its rejected
program ID reaches the existing early error before any amount is packed. -/
def earlyErrorArgs : Onchain.Args :=
  { Onchain.witnessArgs with tokenProgramId := .zero, amount := Solanalib.Runtime.U64_LIMIT }

/-- The removed scalar restriction excluded this input independently of the
borrow store, even though the actual early error can execute. -/
theorem early_error_outside_scalar_domain :
    ¬ earlyErrorArgs.Valid OnchainAllocated.Witness.initialState.1 := by
  intro ready
  exact Nat.lt_irrefl Solanalib.Runtime.U64_LIMIT ready.2.1

/-- Provider admission does not reinstate the removed scalar-domain gate.
The same large abstract amount still reaches the actual early error below. -/
theorem early_error_admitted :
    (OnchainAllocated.family.contract OnchainAllocated.Witness.sample).requires
      OnchainAllocated.Witness.initialState earlyErrorArgs := by
  obtain ⟨protocol, admitted, resources, _⟩ := OnchainAllocated.Witness.sample_ready
  exact ⟨protocol, admitted, resources,
    OnchainAllocated.Admission.BorrowReady.of_instruction_error (by rfl)⟩

/-- The error path drops the four moved arguments without allocating a vector. -/
def earlyErrorState : OnchainAllocated.Witness.State :=
  OnchainAllocated.Witness.dropped OnchainAllocated.Witness.arguments
    OnchainAllocated.Witness.initialState

/-- The actual program check rejects before either instruction-vector call. -/
theorem early_error_base :
    OnchainAllocated.base OnchainAllocated.Witness.sampleTypes earlyErrorArgs
      OnchainAllocated.Witness.initialState
      (.returned (.error .IncorrectProgramId) OnchainAllocated.Witness.initialState) := by
  refine ⟨.returned (.error .IncorrectProgramId) OnchainAllocated.Witness.initialState, ?_, rfl⟩
  rfl

/-- The original error survives the real ordered Rc cleanup, rather than a
supplied cleanup post-state or an assumed whole-function result. -/
theorem early_error_cleanup :
    Owned.cleanup OnchainAllocated.Witness.sampleTypes.doubleUnwind
      (OnchainAllocated.argumentDrops OnchainAllocated.Witness.sampleTypes earlyErrorArgs)
      (.returned (.error .IncorrectProgramId) OnchainAllocated.Witness.initialState :
        Outcome OnchainAllocated.Witness.State
          (Except Error (OnchainAllocated.Prepared OnchainAllocated.Witness.sampleTypes)) Nat Nat)
      (.returned (.error .IncorrectProgramId) earlyErrorState) := by
  have ready : OnchainAllocated.Witness.dropsReady OnchainAllocated.Witness.arguments
      OnchainAllocated.Witness.initialState := by
    simp only [OnchainAllocated.Witness.arguments, OnchainAllocated.Witness.dropsReady,
      OnchainAllocated.Witness.dropReady, OnchainAllocated.Witness.rcReady]
    decide +kernel
  exact (OnchainAllocated.Witness.drop_trace OnchainAllocated.Witness.arguments
    OnchainAllocated.Witness.initialState ready).cleanup_returned
    OnchainAllocated.Witness.sampleTypes.doubleUnwind
    (Except.error .IncorrectProgramId :
      Except Error (OnchainAllocated.Prepared OnchainAllocated.Witness.sampleTypes))

/-- The same full reference, with the admitted provider above, reaches this
finite error and actual cleanup without calling its opaque CPI dependency. -/
theorem early_error_executes :
    OnchainAllocated.reference OnchainAllocated.Witness.sample
      OnchainAllocated.Witness.initialState earlyErrorArgs
      (.returned (.error .IncorrectProgramId) earlyErrorState) := by
  refine ⟨.returned (.error .IncorrectProgramId) earlyErrorState, ?_, rfl⟩
  exact ⟨.returned (.error .IncorrectProgramId) earlyErrorState,
    ⟨.returned (.error .IncorrectProgramId) OnchainAllocated.Witness.initialState,
      early_error_base, early_error_cleanup⟩, rfl⟩

/-- Exactly the four argument owners retire. No instruction or account
vector, data guard or CPI effect is invented on the early-error path. -/
theorem early_error_resources :
    earlyErrorState.1 = OnchainAllocated.Witness.initialState.1 ∧
    earlyErrorState.2.bytes = [] ∧ earlyErrorState.2.metas = [] ∧
    earlyErrorState.2.infos = [] ∧ earlyErrorState.2.lamportsOwners = 1 ∧
    earlyErrorState.2.dataOwners = 1 ∧ earlyErrorState.2.invocations = 0 ∧
    earlyErrorState.2.rcEvents = OnchainAllocated.Witness.arguments.flatMap
      (fun info => [.drop .lamports info.lamports, .drop .data info.data]) := by
  decide +kernel

end SolanalibTest.Specs.Core.TokenAllocatedGuards
