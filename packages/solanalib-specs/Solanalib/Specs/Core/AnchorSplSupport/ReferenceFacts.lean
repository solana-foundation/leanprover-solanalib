/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Reference
public import Solanalib.Specs.Core.CallbackGraph

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Reference

theorem returns_exact {S A V U T : Type} (fn : S → A → V × S) (before : S) (args : A)
    (outcome : Outcome S V U T) :
    returnsOf fn before args outcome ↔ outcome = .returned (fn before args).1 (fn before args).2 :=
      by
  cases outcome with
  | returned value after => simp [returnsOf, Prod.ext_iff, eq_comm]
  | unwound _ _ => simp [returnsOf]
  | terminated _ => simp [returnsOf]

theorem returns_graph {S A V U T : Type} (fn : S → A → V × S) (before : S) (args : A) :
    PGraph (returnsOf fn before args : Outcome S V U T → Prop)
      (some (.returned (fn before args).1 (fn before args).2)) :=
  PGraph.congr (PGraph.eq_left _) fun outcome => returns_exact fn before args outcome

def cloned (before : State) (info : AccountInfo.Value) : State :=
  { before with events := before.events ++ [.cloneRc .lamports info.lamports, .cloneRc .data
    info.data] }

def dropped (before : State) (info : AccountInfo.Value) : State :=
  { before with events := before.events ++ [.dropRc .lamports info.lamports, .dropRc .data
    info.data] }

theorem clone_exact (before : State) (info : AccountInfo.Value) (outcome : Outcome State
  AccountInfo.Value String String) :
    AccountInfoRc.lift (AccountInfoRc.cloneCall rc) before info outcome ↔
      outcome = .returned info (cloned before info) := by
  simp [AccountInfoRc.lift, AccountInfoRc.cloneCall, rc, Callback.bind, Callback.map,
    returns_exact, AccountInfoRc.liftOutcome, Outcome.map, AccountInfo.clone, cloned,
      List.append_assoc, eq_comm]

theorem drop_exact (before : State) (info : AccountInfo.Value) (outcome : Outcome State Unit String
  String) :
    AccountInfoRc.lift (AccountInfoRc.dropCall rc) before info outcome ↔
      outcome = .returned () (dropped before info) := by
  simp [AccountInfoRc.lift, AccountInfoRc.dropCall, rc, Callback.bind, returns_exact,
    AccountInfoRc.liftOutcome, dropped, List.append_assoc, eq_comm]

def infoAllocated (before : State) (values : List AccountInfo.Value) : State :=
  { before with infos := before.infos ++ [some values]
                events := before.events ++ [.allocate "infos" before.infos.length] }

theorem info_list_exact (before : State) (values : List AccountInfo.Value)
    (outcome : Outcome State Nat String String) :
    infos.fromList before values outcome ↔ outcome = .returned before.infos.length (infoAllocated
      before values) := by
  simp only [infos, plainInfos, vector, returns_exact, Owned.VectorState.allocate, infoAllocated]

theorem literal_control (count : Nat) : LiteralControl resources count := by
  constructor
  · intro before values after _ work
    change (if values.length < count then Owned.Array.Command.evaluate else .finish, before) =
      (.evaluate, after) at work
    by_cases bound : values.length < count
    · exact bound
    · simp [bound] at work
  · intro before values after bounded work
    change (if values.length < count then Owned.Array.Command.evaluate else .finish, before) =
      (.finish, after) at work
    by_cases bound : values.length < count
    · simp [bound] at work
    · omega
  · intro before values _
    exact List.Perm.refl _

theorem literal_work_evaluate (before : State) (count : Nat) (values : List AccountInfo.Value)
    (bound : values.length < count) (outcome : Outcome State Owned.Array.Command String String) :
    resources.literalProvider.work before (count, values) outcome ↔ outcome = .returned .evaluate
      before := by
  simp only [Resources.literalProvider, resources, literal, returns_exact, bound, ↓reduceIte]

theorem literal_work_finish (before : State) (count : Nat) (values : List AccountInfo.Value)
    (complete : values.length = count) (outcome : Outcome State Owned.Array.Command String String) :
    resources.literalProvider.work before (count, values) outcome ↔ outcome = .returned .finish
      before := by
  simp only [Resources.literalProvider, resources, literal, returns_exact, complete, Nat.lt_irrefl,
    ↓reduceIte]

/-- Exact one-step inversion for this named normal-work reference. It is not
a schedule restriction on the general literal dependency. -/
theorem literal_step (count : Nat) (evaluate : Run resources Nat AccountInfo.Value)
    (values : List AccountInfo.Value) (before after : State) (value : AccountInfo.Value)
    (bound : values.length < count)
    (expression : ∀ outcome, evaluate before values.length outcome ↔ outcome = .returned value
      after)
    (outcome : Outcome State Nat (Owned.Array.Failure × String) String) :
    Owned.Array.Trace resources.literalProvider count evaluate values before outcome ↔
      Owned.Array.Trace resources.literalProvider count evaluate (values ++ [value]) after outcome
        := by
  constructor
  · intro trace
    cases trace with
    | again _ _ _ _ work _ =>
      have impossible := (literal_work_evaluate _ _ _ bound _).mp work
      cases impossible
    | next _ _ ready nextState nextValue _ _ work evaluated rest =>
      have same := (literal_work_evaluate _ _ _ bound _).mp work
      cases same
      have equal := (expression _).mp evaluated
      cases equal
      exact rest
    | workUnwind _ _ _ _ _ work _ =>
      have impossible := (literal_work_evaluate _ _ _ bound _).mp work
      cases impossible
    | workTerminal _ _ _ work =>
      have impossible := (literal_work_evaluate _ _ _ bound _).mp work
      cases impossible
    | evaluateUnwind _ _ ready _ _ _ _ work evaluated _ =>
      have same := (literal_work_evaluate _ _ _ bound _).mp work
      cases same
      have impossible := (expression _).mp evaluated
      cases impossible
    | evaluateTerminal _ _ ready _ _ work evaluated =>
      have same := (literal_work_evaluate _ _ _ bound _).mp work
      cases same
      have impossible := (expression _).mp evaluated
      cases impossible
    | finishReturn _ _ _ _ _ _ work _ =>
      have impossible := (literal_work_evaluate _ _ _ bound _).mp work
      cases impossible
    | finishUnwind _ _ _ _ _ _ _ work _ _ =>
      have impossible := (literal_work_evaluate _ _ _ bound _).mp work
      cases impossible
    | finishTerminal _ _ _ _ _ work _ =>
      have impossible := (literal_work_evaluate _ _ _ bound _).mp work
      cases impossible
  · intro rest
    exact .next values before before after value outcome bound
      ((literal_work_evaluate _ _ _ bound _).mpr rfl) ((expression _).mpr rfl) rest

/-- At the exact completed count, this reference allocates the real vector
containing the entire evaluated prefix, without another clone or destructor. -/
theorem literal_done (count : Nat) (evaluate : Run resources Nat AccountInfo.Value)
    (values : List AccountInfo.Value) (before : State) (complete : values.length = count)
    (outcome : Outcome State Nat (Owned.Array.Failure × String) String) :
    Owned.Array.Trace resources.literalProvider count evaluate values before outcome ↔
      outcome = .returned before.infos.length (infoAllocated before values) := by
  constructor
  · intro trace
    cases trace with
    | again _ _ _ _ work _ =>
      have impossible := (literal_work_finish _ _ _ complete _).mp work
      cases impossible
    | next _ _ _ _ _ _ _ work _ _ =>
      have impossible := (literal_work_finish _ _ _ complete _).mp work
      cases impossible
    | workUnwind _ _ _ _ _ work _ =>
      have impossible := (literal_work_finish _ _ _ complete _).mp work
      cases impossible
    | workTerminal _ _ _ work =>
      have impossible := (literal_work_finish _ _ _ complete _).mp work
      cases impossible
    | evaluateUnwind _ _ _ _ _ _ _ work _ _ =>
      have impossible := (literal_work_finish _ _ _ complete _).mp work
      cases impossible
    | evaluateTerminal _ _ _ _ _ work _ =>
      have impossible := (literal_work_finish _ _ _ complete _).mp work
      cases impossible
    | finishReturn _ _ ready final resource _ work finished =>
      have same := (literal_work_finish _ _ _ complete _).mp work
      cases same
      have actual := (info_list_exact before values (.returned resource final)).mp finished
      cases actual
      rfl
    | finishUnwind _ _ ready _ _ _ _ work finished _ =>
      have same := (literal_work_finish _ _ _ complete _).mp work
      cases same
      exact False.elim finished
    | finishTerminal _ _ ready _ _ work finished =>
      have same := (literal_work_finish _ _ _ complete _).mp work
      cases same
      exact False.elim finished
  · intro same
    subst outcome
    exact .finishReturn values before before (infoAllocated before values) before.infos.length
      complete
      ((literal_work_finish _ _ _ complete _).mpr rfl) ((info_list_exact _ _ _).mpr rfl)

theorem singleton_exact (before : State) (info : AccountInfo.Value) (outcome : Outcome State Nat
  String String) :
    singletonInfo resources info before () outcome ↔
      outcome = .returned before.infos.length (infoAllocated (cloned before info) [info]) := by
  let evaluate : Run resources Nat AccountInfo.Value := fun state index =>
    if index = 0 then AccountInfoRc.lift (AccountInfoRc.cloneCall rc) state info else fun _ => False
  have first : ∀ produced, evaluate before 0 produced ↔ produced = .returned info (cloned before
    info) :=
    fun produced => clone_exact before info produced
  change (∃ detailed, Owned.Array.Trace resources.literalProvider 1 evaluate [] before detailed ∧
    Owned.Array.erase detailed = outcome) ↔ _
  have trace_eq : ∀ detailed,
      Owned.Array.Trace resources.literalProvider 1 evaluate [] before detailed ↔
        detailed = .returned before.infos.length (infoAllocated (cloned before info) [info]) := by
    intro detailed
    exact (literal_step 1 evaluate [] before (cloned before info) info (by decide) first
      detailed).trans
      (literal_done 1 evaluate [info] (cloned before info) rfl detailed)
  simp only [trace_eq, exists_eq_left, Owned.Array.erase]
  exact eq_comm

end Solanalib.Specs.Core.AnchorSplSupport.Reference
