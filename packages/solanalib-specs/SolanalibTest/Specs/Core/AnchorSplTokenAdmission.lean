/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Sample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SolanalibTest.Specs.Core.AnchorSplTokenAdmission

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

namespace MissingReturnBytes

def binding := Binding.token2022GetAccountDataSize0321
def script := Sample.script binding
def initial := Sample.initial binding
def args := Sample.args binding

def afterGetter (state : Reference.State .v0321) : Reference.State .v0321 :=
  { state with bytes := state.bytes ++ [none], events := state.events ++ [.getReturnData] }

/-- The primitive really returns the selected program and a dead byte owner;
no completed-wrapper premise is used to discover this malformed reply. -/
def getter (state : Reference.State .v0321) (_ : Unit) :
    Option (Outcome (Reference.State .v0321) (Option (Solanalib.Runtime.Pubkey × Nat)) Nat Nat) :=
  some (.returned (some (Token.token2022ProgramId, 1)) (afterGetter state))

def types : Types binding :=
  { Reference.types binding script with getReturnData := Reference.relation getter }

def functions : Execution.Functions types where
  instruction := (Reference.functions binding script).instruction
  copyExtensions := (Reference.functions binding script).copyExtensions
  dropExtensions := (Reference.functions binding script).dropExtensions
  cloneRc := (Reference.functions binding script).cloneRc
  dropRc := (Reference.functions binding script).dropRc
  dropRemaining := (Reference.functions binding script).dropRemaining
  newBox := (Reference.functions binding script).newBox
  invoke := (Reference.functions binding script).invoke
  getReturnData := getter

theorem graphs : Execution.Graph functions where
  instruction := (Reference.graphs binding script).instruction
  copyExtensions := (Reference.graphs binding script).copyExtensions
  dropExtensions := (Reference.graphs binding script).dropExtensions
  cloneRc := (Reference.graphs binding script).cloneRc
  dropRc := (Reference.graphs binding script).dropRc
  dropRemaining := (Reference.graphs binding script).dropRemaining
  newBox := (Reference.graphs binding script).newBox
  invoke := (Reference.graphs binding script).invoke
  getReturnData := fun _ _ _ => Iff.rfl

def instruction : InstructionOwner types := ⟨Token.token2022ProgramId, (0 : Nat), (0 : Nat)⟩

def built : Reference.State .v0321 :=
  match Execution.buildFn functions initial (argsConstruction args) with
  | some (.returned _ after) => after
  | _ => initial

theorem actual_build : build types.builder initial (argsConstruction args) (.returned (.ok
  instruction) built) :=
  (Execution.build_graph functions graphs initial (argsConstruction args) _).mpr rfl

theorem actual_prepare : prepareAccounts types args built () (.returned (invocationAccounts args)
  built) := rfl

def statement : Reference.State .v0321 :=
  match Execution.sizeInvokeFn functions args instruction (invocationAccounts args) built with
  | some (.returned _ after) => after
  | _ => built

theorem actual_statement : sizeInvoke types args instruction (invocationAccounts args) built ()
    (.returned (.ok ()) statement) :=
  (Execution.sizeInvoke_graph functions graphs args instruction (invocationAccounts args) built
    _).mpr rfl

theorem actual_bad_getter : types.getReturnData statement ()
    (.returned (some (Token.token2022ProgramId, (1 : Nat))) (afterGetter statement)) := rfl

theorem registered_family_rejects_bad_reply :
    ¬ ((family binding).contract types).requires initial args := by
  intro ready
  have live := ready.returnedBytes rfl instruction built actual_build
    (invocationAccounts args) built actual_prepare statement actual_statement
    (1 : Nat) (afterGetter statement) actual_bad_getter
  obtain ⟨bytes, current⟩ := live
  have dead : types.builder.instruction.bytes.current (afterGetter statement) (1 : Nat) = none :=
    rfl
  rw [dead] at current
  cases current

theorem raw_decoder_has_no_fabricated_exit (final : Exit types) :
    ¬ run types initial args final := by
  have empty : Execution.runFn functions initial args = none := rfl
  intro execution
  have computed := (Execution.run_graph functions graphs initial args final).mp execution
  rw [empty] at computed
  cases computed

end MissingReturnBytes

namespace MissingRequestBytes

def binding := Binding.tokenTransfer027
def script := Sample.script binding
def initial := Sample.initial binding
def args := Sample.args binding

/-- This callback keeps a real normal Rc exit but erases the live instruction
bytes. It is not repaired by inventing a later vector observation. -/
def clone (state : Reference.State .v027) (_ : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome (Reference.State .v027) Unit Empty Nat) :=
  some (.returned () { state with bytes := [none] })

def types : Types binding :=
  { Reference.types binding script with
    rc := { (Reference.types binding script).rc with cloneRc := Reference.relation clone } }

def functions : Execution.Functions types where
  instruction := (Reference.functions binding script).instruction
  copyExtensions := (Reference.functions binding script).copyExtensions
  dropExtensions := (Reference.functions binding script).dropExtensions
  cloneRc := clone
  dropRc := (Reference.functions binding script).dropRc
  dropRemaining := (Reference.functions binding script).dropRemaining
  newBox := (Reference.functions binding script).newBox
  invoke := (Reference.functions binding script).invoke
  getReturnData := (Reference.functions binding script).getReturnData

theorem graphs : Execution.Graph functions where
  instruction := (Reference.graphs binding script).instruction
  copyExtensions := (Reference.graphs binding script).copyExtensions
  dropExtensions := (Reference.graphs binding script).dropExtensions
  cloneRc := fun _ _ _ => Iff.rfl
  dropRc := (Reference.graphs binding script).dropRc
  dropRemaining := (Reference.graphs binding script).dropRemaining
  newBox := (Reference.graphs binding script).newBox
  invoke := (Reference.graphs binding script).invoke
  getReturnData := (Reference.graphs binding script).getReturnData

def instruction : InstructionOwner types := ⟨Token.legacyProgramId, (0 : Nat), (0 : Nat)⟩

def built : Reference.State .v027 :=
  match Execution.buildFn functions initial (argsConstruction args) with
  | some (.returned _ after) => after
  | _ => initial

theorem actual_build : build types.builder initial (argsConstruction args) (.returned (.ok
  instruction) built) :=
  (Execution.build_graph functions graphs initial (argsConstruction args) _).mpr rfl

def prepared : Reference.State .v027 := { built with bytes := [none] }

theorem actual_clone_return : types.rc.cloneRc built (.lamports, (Sample.info 1).lamports)
    (.returned () prepared) := rfl

theorem actual_prepare : prepareAccounts types args built () (.returned (invocationAccounts args)
  prepared) :=
  (Execution.prepare_graph functions graphs args built _).mpr rfl

theorem registered_family_rejects_erased_request :
    ¬ ((family binding).contract types).requires initial args := by
  intro ready
  obtain ⟨_, bytes, _⟩ := ready.requestInput instruction built actual_build
    (invocationAccounts args) prepared actual_prepare
  obtain ⟨values, current⟩ := bytes
  change none = some values at current
  cases current

theorem raw_constructor_retains_bad_clone_exit (final : Exit types) :
    ¬ run types initial args final := by
  have empty : Execution.runFn functions initial args = none := rfl
  intro execution
  have computed := (Execution.run_graph functions graphs initial args final).mp execution
  rw [empty] at computed
  cases computed

theorem cloneCall_mono {State Terminal : Type} (first second : AccountInfoRc.Ops State Terminal)
    (included : ∀ state field final, first.cloneRc state field final → second.cloneRc state field
      final)
    (state : State) (info : AccountInfo.Value) (final : Outcome State AccountInfo.Value Empty
      Terminal)
    (called : AccountInfoRc.cloneCall first state info final) :
    AccountInfoRc.cloneCall second state info final := by
  obtain ⟨one, called, next⟩ := called
  refine ⟨one, included _ _ _ called, ?_⟩
  cases one with
  | unwound impossible _ => nomatch impossible
  | terminated _ => exact next
  | returned _ _ =>
    obtain ⟨two, called, next⟩ := next
    exact ⟨two, included _ _ _ called, next⟩

theorem cloneAccounts_mono {State Terminal : Type} (first second : AccountInfoRc.Ops State Terminal)
    (included : ∀ state field final, first.cloneRc state field final → second.cloneRc state field
      final) :
    ∀ accounts state final, cloneAccounts first accounts state () final →
      cloneAccounts second accounts state () final := by
  intro accounts
  induction accounts with
  | nil => exact fun _ _ called => called
  | cons info rest induction =>
    intro state final called
    obtain ⟨one, called, next⟩ := called
    refine ⟨one, cloneCall_mono first second included state info one called, ?_⟩
    cases one with
    | unwound impossible _ => nomatch impossible
    | terminated _ => exact next
    | returned _ _ =>
      obtain ⟨two, called, next⟩ := next
      exact ⟨two, induction _ _ called, next⟩

def mixedTypes : Types binding :=
  { Reference.types binding script with rc := {
      (Reference.types binding script).rc with
      cloneRc := fun state field final =>
        (Reference.types binding script).rc.cloneRc state field final ∨ types.rc.cloneRc state
          field final } }

theorem mixed_bad_prepare : prepareAccounts mixedTypes args built ()
    (.returned (invocationAccounts args) prepared) := by
  obtain ⟨produced, called, equal⟩ := actual_prepare
  exact ⟨produced, cloneAccounts_mono types.rc mixedTypes.rc (fun _ _ _ => Or.inr) _ _ _ called,
    equal⟩

theorem one_good_path_does_not_hide_bad_request :
    ¬ ((family binding).contract mixedTypes).requires initial args := by
  intro ready
  obtain ⟨_, bytes, _⟩ := ready.requestInput instruction built actual_build
    (invocationAccounts args) prepared mixed_bad_prepare
  obtain ⟨values, current⟩ := bytes
  change none = some values at current
  cases current

def goodPrepared : Reference.State .v027 :=
  match Execution.prepareFn (Reference.functions binding script) args built with
  | some (.returned _ after) => after
  | _ => built

theorem mixed_good_prepare : prepareAccounts mixedTypes args built ()
    (.returned (invocationAccounts args) goodPrepared) := by
  have base : prepareAccounts (Reference.types binding script) args built ()
      (.returned (invocationAccounts args) goodPrepared) :=
    (Execution.prepare_graph (Reference.functions binding script) (Reference.graphs binding script)
      args built _).mpr rfl
  obtain ⟨produced, called, equal⟩ := base
  exact ⟨produced, cloneAccounts_mono (Reference.types binding script).rc mixedTypes.rc
    (fun _ _ _ => Or.inl) _ _ _ called, equal⟩

theorem mixed_provider_keeps_actual_success : run mixedTypes initial args (Sample.outcome binding)
  := by
  apply run_after_prepared mixedTypes args initial built goodPrepared instruction
    (invocationAccounts args)
    (Sample.outcome binding) actual_build mixed_good_prepare
  have base := (Execution.afterPrepared_graph (Reference.functions binding script)
    (Reference.graphs binding script)
    args instruction (invocationAccounts args) goodPrepared (Sample.outcome binding)).mpr rfl
  have dropped : dropInfo mixedTypes = dropInfo (Reference.types binding script) := by
    funext info state final
    rfl
  have converted : convertResult (Value := Unit) mixedTypes =
      convertResult (Reference.types binding script) := by
    funext state value
    cases value <;> rfl
  have invoked : invokeAndConvert mixedTypes args instruction (invocationAccounts args) =
      invokeAndConvert (Reference.types binding script) args instruction (invocationAccounts args)
        := by
    unfold invokeAndConvert
    rw [converted]
    rfl
  have ordinary : binding.operation ≠ .getAccountDataSize := by decide
  simp only [afterPrepared, ordinary, ↓reduceIte, tailDrops, remainingContextDrops,
    contextDrops, infoDrops] at base ⊢
  rw [dropped, invoked]
  exact base

end MissingRequestBytes

end SolanalibTest.Specs.Core.AnchorSplTokenAdmission
