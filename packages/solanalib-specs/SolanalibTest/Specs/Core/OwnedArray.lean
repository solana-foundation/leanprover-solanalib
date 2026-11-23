/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedArrayProgress
public import Solanalib.Specs.Core.OwnedArrayContracts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.OwnedArray

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Owned
  Solanalib.Specs.Core.Owned.Array

/-- Observable dependency events in the finite adversarial ledger. -/
inductive Event where
  /-- Storage acquired before any following expression. -/
  | allocate (resource : Nat)
  /-- Work at the indicated completed-prefix length. -/
  | work (completed : Nat)
  /-- The exact indexed expression was called. -/
  | evaluate (index : Nat)
  /-- Work or completion mutated partial storage before unwinding. -/
  | partialWrite (completed : Nat)
  /-- Completion returned the retained storage token. -/
  | finish (resource : Nat)
  /-- One owned occurrence was destroyed. -/
  | drop (value : Nat)
  /-- Only the storage token was retired. -/
  | retire (resource : Nat)
  deriving DecidableEq, Repr

/-- A finite ownership ledger, distinct from a Rust allocator or representation.
Live occurrences retain multiplicities; storage and pending values are separate. -/
structure State where
  /-- The reusable vector ledger, including unrelated live slots. -/
  heap : VectorState Nat := []
  /-- The stable storage identity of this construction. -/
  retained : Option Nat := none
  /-- Whether the last value is outside the stored prefix. -/
  pending : Bool := false
  /-- All currently owned element occurrences. -/
  live : List Nat := []
  /-- Expression indices actually evaluated. -/
  calls : List Nat := []
  /-- Values actually destroyed, retaining repeated equal occurrences. -/
  dropped : List Nat := []
  /-- Partial failing-expression inputs cleaned by the evaluator itself. -/
  failedInputs : Nat := 0
  /-- Dependency ordering and storage effects. -/
  events : List Event := []
  deriving DecidableEq, Repr

/-- Distinct original and destructor unwind reasons. -/
inductive Reason where
  /-- Work or allocation failure. -/
  | allocation
  /-- Failure while evaluating an expression. -/
  | expression
  /-- Failure while completing the vector. -/
  | completion
  /-- Failure after an element destructor consumed its occurrence. -/
  | destructor
  /-- Failure after storage retirement consumed its token. -/
  | retirement
  deriving DecidableEq, Repr

/-- Terminal observations, including the exact state of a second unwind. -/
inductive Terminal where
  /-- A direct terminal exit from the selected dependency. -/
  | direct (site : Reason)
  /-- The actual second-unwind state and both reasons, without later cleanup. -/
  | double (state : State) (original later : Reason)
  deriving DecidableEq, Repr

/-- Acquire fresh logical storage without evaluating any element. -/
def acquire (before : State) : State :=
  { before with
    heap := before.heap ++ [some []]
    retained := some before.heap.length
    events := before.events ++ [.allocate before.heap.length] }

/-- Store the supplied prefix under the retained identity. -/
def store (before : State) (values : List Nat) : State :=
  { before with
    heap := match before.retained with
      | none => before.heap
      | some resource => before.heap.set resource (some values)
    pending := false, events := before.events ++ [.work values.length] }

/-- A partial mutation leaves the last returned element pending outside storage. -/
def partialWrite (before : State) (values : List Nat) : State :=
  { store before values.dropLast with
    pending := !values.isEmpty
    events := before.events ++ [.partialWrite values.length] }

/-- One returned expression adds one owned occurrence and its exact call index. -/
def evaluated (before : State) (index value : Nat) : State :=
  { before with
    live := before.live ++ [value]
    calls := before.calls ++ [index]
    pending := true
    events := before.events ++ [.evaluate index] }

/-- The evaluator cleans its own partial input while preserving earlier outputs. -/
def failedExpression (before : State) (index : Nat) : State :=
  { before with
    calls := before.calls ++ [index]
    failedInputs := before.failedInputs + 1
    events := before.events ++ [.evaluate index] }

/-- One destructor removes one occurrence, including when the values are equal. -/
def destroyed (before : State) (value : Nat) : State :=
  { before with
    live := before.live.erase value
    dropped := before.dropped ++ [value]
    events := before.events ++ [.drop value] }

/-- Storage-only retirement keeps element lifecycle observations unchanged. -/
def retired (before : State) (resource : Nat) : State :=
  { before with
    heap := before.heap.set resource none
    retained := none
    pending := false
    events := before.events ++ [.retire resource] }

/-- Completion fills the current slot without allocating another identity. -/
def completed (before : State) (values : List Nat) (resource : Nat) : State :=
  { before with
    heap := before.heap.set resource (some values)
    pending := false
    events := before.events ++ [.finish resource] }

/-- A dependency with actual normal, unwind and terminal branches.
It permits finite work interleaving rather than a fixed macro expansion. -/
inductive Work : Callback.Run State (Nat × List Nat) Command Reason Terminal
  /-- Allocation may precede the first or any later expression. -/
  | allocate (before : State) (count : Nat) (values : List Nat)
      (absent : before.retained = none) :
      Work before (count, values) (.returned .again (acquire before))
  /-- A storage chunk need not evaluate another expression. -/
  | chunk (before : State) (count : Nat) (values : List Nat) :
      Work before (count, values) (.returned .again (store before values))
  /-- Work requests only the next still-unevaluated expression. -/
  | evaluate (before : State) (count : Nat) (values : List Nat)
      (bound : values.length < count) :
      Work before (count, values) (.returned .evaluate (store before values))
  /-- Work requests completion only at the requested count. -/
  | finish (before : State) (count : Nat) (values : List Nat)
      (complete : values.length = count) :
      Work before (count, values) (.returned .finish (store before values))
  /-- A failing chunk can change storage and cleanup order. -/
  | unwind (before : State) (count : Nat) (values : List Nat) :
      Work before (count, values) (.unwound .allocation (partialWrite before values))
  /-- Work can stop without providing a cleanup state. -/
  | terminal (before : State) (count : Nat) (values : List Nat) :
      Work before (count, values) (.terminated (.direct .allocation))

/-- The supplied expression relation exposes every finite outcome. -/
inductive Evaluate : Callback.Run State Nat Nat Reason Terminal
  /-- A successful callback contributes its actual returned value. -/
  | returned (before : State) (index value : Nat) :
      Evaluate before index (.returned value (evaluated before index value))
  /-- The callback owns its failing partial-input cleanup. -/
  | unwound (before : State) (index : Nat) :
      Evaluate before index (.unwound .expression (failedExpression before index))
  /-- A callback may terminate directly. -/
  | terminal (before : State) (index : Nat) :
      Evaluate before index (.terminated (.direct .expression))

/-- Completion retains all outputs on unwind and moves them on success. -/
inductive Finish : Callback.Run State (List Nat) Nat Reason Terminal
  /-- Success updates a live retained slot with the exact supplied sequence. -/
  | returned (before : State) (values : List Nat) (resource : Nat) (old : List Nat)
      (retained : before.retained = some resource)
      (current : before.heap.current resource = some old) :
      Finish before values (.returned resource (completed before values resource))
  /-- Partial completion leaves all evaluated occurrences owned. -/
  | unwound (before : State) (values : List Nat) :
      Finish before values (.unwound .completion (partialWrite before values))
  /-- A terminal completion has no following cleanup. -/
  | terminal (before : State) (values : List Nat) :
      Finish before values (.terminated (.direct .completion))

/-- Element destruction has full outcomes with actual state changes. -/
inductive Drop : Callback.Run State Nat Unit Reason Terminal
  /-- Successful destruction consumes exactly one live occurrence. -/
  | returned (before : State) (value : Nat) (live : value ∈ before.live) :
      Drop before value (.returned () (destroyed before value))
  /-- Unwinding destruction has already consumed its occurrence. -/
  | unwound (before : State) (value : Nat) (live : value ∈ before.live) :
      Drop before value (.unwound .destructor (destroyed before value))
  /-- Terminal destruction stops before every later action. -/
  | terminal (before : State) (value : Nat) :
      Drop before value (.terminated (.direct .destructor))

/-- Retirement is separate from element destruction and can itself unwind. -/
inductive Retire : Callback.Run State (List Nat) Unit Reason Terminal
  /-- With no acquired storage, retirement is exactly the identity. -/
  | absent (before : State) (values : List Nat) (absent : before.retained = none) :
      Retire before values (.returned () before)
  /-- A normal retirement consumes the current storage identity. -/
  | returned (before : State) (values : List Nat) (resource : Nat) (old : List Nat)
      (retained : before.retained = some resource)
      (current : before.heap.current resource = some old) :
      Retire before values (.returned () (retired before resource))
  /-- An unwinding retirement has also consumed that identity. -/
  | unwound (before : State) (values : List Nat) (resource : Nat) (old : List Nat)
      (retained : before.retained = some resource)
      (current : before.heap.current resource = some old) :
      Retire before values (.unwound .retirement (retired before resource))
  /-- Storage can terminate directly. -/
  | terminal (before : State) (values : List Nat) (resource : Nat)
      (retained : before.retained = some resource) :
      Retire before values (.terminated (.direct .retirement))

/-- The actual pending marker selects a permutation of occurrence positions. -/
def order (state : State) (values : List Nat) : List (Fin values.length) :=
  if state.pending then
    (List.finRange values.length).drop (values.length - 1) ++
      (List.finRange values.length).take (values.length - 1)
  else List.finRange values.length

/-- The adversarial provider used by both successful and abnormal executions. -/
abbrev provider : Provider State Nat Nat Reason Terminal where
  work := Work
  finish := Finish
  cleanupOrder := order
  drop := Drop
  retire := Retire
  double := fun state original later terminal => terminal = .double state original later

/-- An ordinary vector callback lifted through the heap field of the test ledger. -/
def liftVector {Args Value : Type}
    (run : Callback.Run (VectorState Nat) Args Value Reason Terminal) :
    Callback.Run State Args Value Reason Terminal := fun before args final =>
  ∃ outcome, run before.heap args outcome ∧
    match outcome with
    | .returned value heap => final = .returned value { before with heap }
    | .unwound reason heap => final = .unwound reason { before with heap }
    | .terminated reason => final = .terminated reason

/-- The common mathematical vector reference with other ledger fields framed. -/
def vectors : VectorOps State Nat Nat Reason Terminal where
  current := fun state resource => state.heap.current resource
  empty := fun state =>
    let (resource, heap) := state.heap.allocate []
    (resource, { state with heap })
  withCapacity := liftVector vectorReference.withCapacity
  fromList := liftVector vectorReference.fromList
  push := liftVector vectorReference.push
  extend := liftVector vectorReference.extend
  drop := liftVector vectorReference.drop

/-- Actual unwind branches satisfy the scheduling and occurrence-order obligations. -/
theorem provider_conforms : provider.Conforms := by
  constructor
  · intro before count values after _ execution
    cases execution with
    | evaluate _ _ _ bound => exact bound
  · intro before count values after _ execution
    cases execution with
    | finish _ _ _ complete => exact complete
  · intro state values
    change (order state values).Perm _
    unfold order
    split
    · simpa only [List.take_append_drop] using
        List.perm_append_comm (l₁ := (List.finRange values.length).drop (values.length - 1))
          (l₂ := (List.finRange values.length).take (values.length - 1))
    · exact List.Perm.refl _

/-- Actual completion supplies the exact current vector contents. -/
theorem provider_current_law : provider.CurrentLaw vectors := by
  constructor
  intro before values resource after execution
  cases execution with
  | returned _ _ _ old _ current =>
    exact VectorState.current_set _ _ _ (VectorState.current_bound current)

/-- Initial empty construction with one unrelated vector already live. -/
abbrev initial : State := { heap := [some [90]] }
/-- Fresh storage token acquired before the first expression. -/
abbrev allocated : State := acquire initial
/-- Work state immediately before expression zero. -/
abbrev ready0 : State := store allocated []
/-- One successfully evaluated owned output. -/
abbrev one : State := evaluated ready0 0 11
/-- The first output is stored before expression one. -/
abbrev ready1 : State := store one [11]
/-- Two evaluated outputs, with the second still pending insertion. -/
abbrev two : State := evaluated ready1 1 22
/-- Both outputs stored before the failing work chunk. -/
abbrev storedTwo : State := store two [11, 22]
/-- Actual partial work or completion unwind state. -/
abbrev failedTwo : State := partialWrite storedTwo [11, 22]
/-- Actual state after destroying the pending last output. -/
abbrev droppedLast : State := destroyed failedTwo 22
/-- Actual state after destroying both outputs. -/
abbrev droppedBoth : State := destroyed droppedLast 11
/-- Actual state after both element drops and storage retirement. -/
abbrev goneTwo : State := retired droppedBoth 1
/-- Successful state retaining the exact vector token and ordered elements. -/
abbrev successTwo : State := completed storedTwo [11, 22] 1
/-- Work unwind after exactly one returned expression. -/
abbrev failedOne : State := partialWrite one [11]
/-- The sole returned output has been destroyed. -/
abbrev droppedOne : State := destroyed failedOne 11
/-- Storage retired after one-output cleanup. -/
abbrev goneOne : State := retired droppedOne 1
/-- The second evaluator has cleaned its own partial input. -/
abbrev failedEval : State := failedExpression ready1 1
/-- The earlier output has been destroyed after evaluator failure. -/
abbrev droppedEval : State := destroyed failedEval 11
/-- Final state after evaluator failure and constructor cleanup. -/
abbrev goneEval : State := retired droppedEval 1

private theorem throughFirst (count : Nat) (bound : 0 < count)
    (final : Outcome State Nat (Failure × Reason) Terminal)
    (rest : Trace provider count Evaluate [11] one final) :
    provider.runDetailed count Evaluate initial final := by
  refine .again [] initial allocated final (.allocate _ _ _ rfl) ?_
  exact .next [] allocated ready0 one 11 final bound
    (.evaluate _ _ _ bound) (.returned _ _ _) rest

private theorem throughSecond (count : Nat) (bound : 1 < count)
    (final : Outcome State Nat (Failure × Reason) Terminal)
    (rest : Trace provider count Evaluate [11, 22] two final) :
    provider.runDetailed count Evaluate initial final := by
  apply throughFirst count (by omega) final
  exact .next [11] one ready1 two 22 final bound
    (.evaluate _ _ _ bound) (.returned _ _ _) rest

private theorem closeEmpty (before : State) (absent : before.retained = none)
    (site : FailureSite) (reason : Reason) :
    provider.close [] site before reason (.unwound (⟨0, site⟩, reason) before) := by
  apply Provider.close_of_dropReturns provider_conforms
  have emptyOrder : provider.cleanupOrder before [] = [] := by
    simp [order]
  rw [emptyOrder]
  change DropReturns [fun state outcome => Retire state [] outcome] before before
  exact .cons _ [] before before before (.absent _ _ absent) (.nil _)

private theorem cleanupTwo :
    DropReturns (provider.cleanupActions [11, 22] (provider.cleanupOrder failedTwo [11, 22]))
      failedTwo goneTwo := by
  change DropReturns
    [fun state outcome => Drop state 22 outcome, fun state outcome => Drop state 11 outcome,
      fun state outcome => Retire state [11, 22] outcome] failedTwo goneTwo
  exact .cons _ _ failedTwo droppedLast goneTwo
    (.returned _ _ (by decide +kernel))
    (.cons _ _ droppedLast droppedBoth goneTwo (.returned _ _ (by decide +kernel))
      (.cons _ [] droppedBoth goneTwo goneTwo
        (.returned _ _ 1 [11] rfl rfl) (.nil _)))

private theorem closeTwo (site : FailureSite) (reason : Reason) :
    provider.close [11, 22] site failedTwo reason
      (.unwound (⟨2, site⟩, reason) goneTwo) :=
  Provider.close_of_dropReturns provider_conforms _ _ _ _ _ cleanupTwo

private theorem cleanupOne :
    DropReturns (provider.cleanupActions [11] (provider.cleanupOrder failedOne [11]))
      failedOne goneOne := by
  change DropReturns [fun state outcome => Drop state 11 outcome,
    fun state outcome => Retire state [11] outcome] failedOne goneOne
  exact .cons _ _ failedOne droppedOne goneOne (.returned _ _ (by decide +kernel))
    (.cons _ [] droppedOne goneOne goneOne (.returned _ _ 1 [] rfl rfl) (.nil _))

private theorem cleanupEval :
    DropReturns (provider.cleanupActions [11] (provider.cleanupOrder failedEval [11]))
      failedEval goneEval := by
  change DropReturns [fun state outcome => Drop state 11 outcome,
    fun state outcome => Retire state [11] outcome] failedEval goneEval
  exact .cons _ _ failedEval droppedEval goneEval (.returned _ _ (by decide +kernel))
    (.cons _ [] droppedEval goneEval goneEval (.returned _ _ 1 [11] rfl rfl) (.nil _))

/-- Allocation failure before the first expression performs no expression or element drop. -/
theorem allocation_failure_before_first :
    provider.runDetailed 2 Evaluate initial
      (.unwound (⟨0, .work⟩, .allocation) (partialWrite initial [])) ∧
    (partialWrite initial []).calls = [] ∧ (partialWrite initial []).dropped = [] ∧
    (partialWrite initial []).retained = none := by
  refine ⟨?_, rfl, rfl, rfl⟩
  exact .workUnwind [] initial (partialWrite initial []) .allocation _
    (Work.unwind initial 2 []) (closeEmpty _ rfl _ _)

/-- Failure between expressions destroys only the completed prefix and retires its storage. -/
theorem work_failure_between_evaluations :
    provider.runDetailed 2 Evaluate initial (.unwound (⟨1, .work⟩, .allocation) goneOne) ∧
    goneOne.calls = [0] ∧ goneOne.dropped = [11] ∧ goneOne.live = [] ∧
    goneOne.retained = none ∧ vectors.current goneOne 1 = none := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  apply throughFirst 2 (by decide +kernel)
  exact .workUnwind [11] one failedOne .allocation _ (Work.unwind one 2 [11])
    (Provider.close_of_dropReturns provider_conforms _ _ _ _ _ cleanupOne)

/-- Actual partial mutation moves the last value outside storage and changes cleanup order. -/
theorem partial_mutation_changes_current_cleanup :
    vectors.current storedTwo 1 = some [11, 22] ∧
    vectors.current failedTwo 1 = some [11] ∧
    (provider.cleanupOrder storedTwo [11, 22]).map Fin.val = [0, 1] ∧
    (provider.cleanupOrder failedTwo [11, 22]).map Fin.val = [1, 0] ∧
    failedTwo.live = [11, 22] := by
  decide +kernel

/-- Pending-last cleanup threads every actual destructor state before retiring storage. -/
theorem pending_last_work_unwind :
    provider.runDetailed 3 Evaluate initial (.unwound (⟨2, .work⟩, .allocation) goneTwo) ∧
    goneTwo.calls = [0, 1] ∧ goneTwo.dropped = [22, 11] ∧ goneTwo.live = [] ∧
    goneTwo.retained = none ∧ vectors.current goneTwo 1 = none ∧
    vectors.current goneTwo 0 = some [90] := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply throughSecond 3 (by decide +kernel)
  exact .again [11, 22] two storedTwo _ (.chunk _ _ _)
    (.workUnwind [11, 22] storedTwo failedTwo .allocation _ (Work.unwind storedTwo 3 [11, 22])
      (closeTwo .work .allocation))

/-- Allocation and storage work interleave with evaluations, returning the same live handles. -/
theorem success_interleaves_and_retains_current_resource :
    provider.run 2 Evaluate initial (.returned 1 successTwo) ∧
    successTwo.calls = [0, 1] ∧ successTwo.live = [11, 22] ∧
    successTwo.dropped = [] ∧ successTwo.retained = allocated.retained ∧
    vectors.current successTwo 1 = some [11, 22] ∧
    vectors.current successTwo 0 = some [90] ∧
    successTwo.events = [.allocate 1, .work 0, .evaluate 0, .work 1, .evaluate 1,
      .work 2, .finish 1] := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨.returned 1 successTwo, ?_, rfl⟩
  apply throughSecond 2 (by decide +kernel)
  exact .finishReturn [11, 22] two storedTwo successTwo 1 rfl
    (.finish _ _ _ rfl) (.returned _ _ 1 [11, 22] rfl rfl)

/-- A failing evaluator cleans its own partial input; array cleanup destroys only earlier outputs.
-/
theorem evaluator_unwind_keeps_exact_progress :
    provider.runDetailed 2 Evaluate initial (.unwound (⟨1, .evaluate⟩, .expression) goneEval) ∧
    goneEval.calls = [0, 1] ∧ goneEval.failedInputs = 1 ∧
    goneEval.dropped = [11] ∧ goneEval.live = [] ∧ vectors.current goneEval 1 = none := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  apply throughFirst 2 (by decide +kernel)
  exact .evaluateUnwind [11] one ready1 failedEval .expression _ (by decide +kernel)
    (.evaluate _ _ _ (by decide +kernel)) (.unwound _ _)
    (Provider.close_of_dropReturns provider_conforms _ _ _ _ _ cleanupEval)

/-- A completion unwind leaves all returned outputs for exactly one constructor cleanup. -/
theorem completion_unwind_preserves_then_cleans_outputs :
    provider.runDetailed 2 Evaluate initial (.unwound (⟨2, .finish⟩, .completion) goneTwo) ∧
    failedTwo.live = [11, 22] ∧ goneTwo.dropped = [22, 11] ∧ goneTwo.live = [] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  apply throughSecond 2 (by decide +kernel)
  exact .finishUnwind [11, 22] two storedTwo failedTwo .completion _ rfl
    (.finish _ _ _ rfl) (Finish.unwound storedTwo [11, 22]) (closeTwo .finish .completion)

/-- Two distinct owned occurrences with equal element values. -/
abbrev sameValues : State :=
  { heap := [some [90], some [7]], retained := some 1, pending := true, live := [7, 7] }
/-- Exactly one of two equal occurrences remains live. -/
abbrev sameFirst : State := destroyed sameValues 7
/-- Both equal occurrences have been destroyed. -/
abbrev sameBoth : State := destroyed sameFirst 7
/-- Storage retired after two equal-occurrence destructor calls. -/
abbrev sameGone : State := retired sameBoth 1

/-- Equal values at distinct positions require two destructor calls, preserving multiplicity. -/
theorem equal_values_are_distinct_owned_occurrences :
    provider.close [7, 7] .work sameValues .allocation
      (.unwound (⟨2, .work⟩, .allocation) sameGone) ∧
    (provider.cleanupOrder sameValues [7, 7]).map Fin.val = [1, 0] ∧
    sameFirst.live = [7] ∧ sameGone.live = [] ∧ sameGone.dropped = [7, 7] := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  apply Provider.close_of_dropReturns provider_conforms
  change DropReturns [fun state outcome => Drop state 7 outcome,
    fun state outcome => Drop state 7 outcome, fun state outcome => Retire state [7, 7] outcome]
    sameValues sameGone
  exact .cons _ _ sameValues sameFirst sameGone (.returned _ _ (by decide +kernel))
    (.cons _ _ sameFirst sameBoth sameGone (.returned _ _ (by decide +kernel))
      (.cons _ [] sameBoth sameGone sameGone (.returned _ _ 1 [7] rfl rfl) (.nil _)))

/-- A pending last output and a two-element stored prefix. -/
abbrev threeValues : State :=
  { heap := [some [90], some [11, 22]], retained := some 1, pending := true,
    live := [11, 22, 33] }
/-- The pending third output has been destroyed. -/
abbrev threeLast : State := destroyed threeValues 33
/-- The first stored output has been destroyed after the pending output. -/
abbrev threeFirst : State := destroyed threeLast 11
/-- All three outputs have been destroyed in the selected order. -/
abbrev threeAll : State := destroyed threeFirst 22
/-- Storage retired after the pending value and ordered stored prefix. -/
abbrev threeGone : State := retired threeAll 1

/-- The pending value drops first, followed by the stored prefix in its own order. -/
theorem pending_last_then_stored_prefix_order :
    provider.close [11, 22, 33] .work threeValues .allocation
      (.unwound (⟨3, .work⟩, .allocation) threeGone) ∧
    (provider.cleanupOrder threeValues [11, 22, 33]).map Fin.val = [2, 0, 1] ∧
    threeGone.dropped = [33, 11, 22] ∧ threeGone.live = [] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  apply Provider.close_of_dropReturns provider_conforms
  change DropReturns [fun state outcome => Drop state 33 outcome,
    fun state outcome => Drop state 11 outcome, fun state outcome => Drop state 22 outcome,
    fun state outcome => Retire state [11, 22, 33] outcome] threeValues threeGone
  exact .cons _ _ threeValues threeLast threeGone (.returned _ _ (by decide +kernel))
    (.cons _ _ threeLast threeFirst threeGone (.returned _ _ (by decide +kernel))
      (.cons _ _ threeFirst threeAll threeGone (.returned _ _ (by decide +kernel))
        (.cons _ [] threeAll threeGone threeGone
          (.returned _ _ 1 [11, 22] rfl rfl) (.nil _))))


/-- A terminal-test provider for which no destructor or retirement can execute. -/
abbrev noCleanup : Provider State Nat Nat Reason Terminal :=
  { provider with drop := fun _ _ _ => False, retire := fun _ _ _ => False }

private theorem noCleanupConforms : noCleanup.Conforms :=
  ⟨provider_conforms.evaluate_bound, provider_conforms.finish_count,
    provider_conforms.cleanup_permutation⟩

/-- Work termination after one live output succeeds even when cleanup has no finite exit. -/
theorem terminal_work_skips_cleanup :
    noCleanup.Conforms ∧ noCleanup.runDetailed 2 Evaluate initial
      (.terminated (.direct .allocation)) := by
  refine ⟨noCleanupConforms, ?_⟩
  refine .again [] initial allocated _ (.allocate _ _ _ rfl) ?_
  refine .next [] allocated ready0 one 11 _ (by decide +kernel)
    (.evaluate _ _ _ (by decide +kernel)) (.returned _ _ _) ?_
  exact .workTerminal [11] one _ (.terminal _ _ _)

/-- Evaluator termination never destroys earlier live outputs or temporary storage. -/
theorem terminal_evaluator_skips_cleanup :
    noCleanup.runDetailed 2 Evaluate initial (.terminated (.direct .expression)) := by
  refine .again [] initial allocated _ (.allocate _ _ _ rfl) ?_
  refine .next [] allocated ready0 one 11 _ (by decide +kernel)
    (.evaluate _ _ _ (by decide +kernel)) (.returned _ _ _) ?_
  exact .evaluateTerminal [11] one ready1 _ (by decide +kernel)
    (.evaluate _ _ _ (by decide +kernel)) (.terminal _ _)

/-- Completion termination succeeds without invoking even the first unavailable destructor. -/
theorem terminal_completion_skips_cleanup :
    noCleanup.runDetailed 1 Evaluate initial (.terminated (.direct .completion)) := by
  refine .again [] initial allocated _ (.allocate _ _ _ rfl) ?_
  refine .next [] allocated ready0 one 11 _ (by decide +kernel)
    (.evaluate _ _ _ (by decide +kernel)) (.returned _ _ _) ?_
  exact .finishTerminal [11] one ready1 _ rfl (.finish _ _ _ rfl) (.terminal _ _)

private theorem closeDoubleDrop :
    provider.close [11, 22] .work failedTwo .allocation
      (.terminated (.double droppedLast .allocation .destructor)) := by
  refine ⟨provider_conforms.cleanup_permutation _ _,
    .terminated (.double droppedLast .allocation .destructor), ?_, rfl⟩
  change cleanup provider.double
    [fun state outcome => Drop state 22 outcome, fun state outcome => Drop state 11 outcome,
      fun state outcome => Retire state [11, 22] outcome]
    (.unwound Reason.allocation failedTwo)
    (.terminated (.double droppedLast .allocation .destructor))
  exact cleanup_double_unwind (Value := Nat) provider.double _ _ failedTwo droppedLast
    Reason.allocation Reason.destructor _ (Drop.unwound _ _ (by decide +kernel)) rfl

/-- A second unwind from a destructor uses its actual post-drop state and stops with earlier outputs
live. -/
theorem destructor_double_unwind_uses_actual_state :
    provider.runDetailed 3 Evaluate initial
      (.terminated (.double droppedLast .allocation .destructor)) ∧
    droppedLast.live = [11] ∧ droppedLast.dropped = [22] ∧
    droppedLast.retained = some 1 ∧ vectors.current droppedLast 1 = some [11] := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  apply throughSecond 3 (by decide +kernel)
  exact .again [11, 22] two storedTwo _ (.chunk _ _ _)
    (.workUnwind [11, 22] storedTwo failedTwo .allocation _
      (Work.unwind storedTwo 3 [11, 22]) closeDoubleDrop)

/-- A directly terminal first destructor skips the remaining elements and storage retirement. -/
theorem terminal_destructor_stops_remaining_cleanup :
    provider.close [11, 22] .work failedTwo .allocation
      (.terminated (.direct .destructor)) := by
  refine ⟨provider_conforms.cleanup_permutation _ _, .terminated (.direct .destructor), ?_, rfl⟩
  change cleanup provider.double
    [fun state outcome => Drop state 22 outcome, fun state outcome => Drop state 11 outcome,
      fun state outcome => Retire state [11, 22] outcome]
    (.unwound Reason.allocation failedTwo) (.terminated (.direct .destructor))
  exact ⟨.terminated (.direct .destructor), Drop.terminal _ _, rfl⟩

/-- Retirement unwinds only after the element drops, using the state with storage already consumed.
-/
theorem retirement_double_unwind_after_elements :
    provider.close [11, 22] .work failedTwo .allocation
      (.terminated (.double goneTwo .allocation .retirement)) ∧
    goneTwo.live = [] ∧ goneTwo.dropped = [22, 11] ∧ goneTwo.retained = none := by
  refine ⟨?_, rfl, rfl, rfl⟩
  refine ⟨provider_conforms.cleanup_permutation _ _,
    .terminated (.double goneTwo .allocation .retirement), ?_, rfl⟩
  change cleanup provider.double
    [fun state outcome => Drop state 22 outcome, fun state outcome => Drop state 11 outcome,
      fun state outcome => Retire state [11, 22] outcome]
    (.unwound Reason.allocation failedTwo)
    (.terminated (.double goneTwo .allocation .retirement))
  refine ⟨.returned () droppedLast, Drop.returned _ _ (by decide +kernel), ?_⟩
  refine ⟨.returned () droppedBoth, Drop.returned _ _ (by decide +kernel), ?_⟩
  exact cleanup_double_unwind (Value := Nat) provider.double _ [] droppedBoth goneTwo
    Reason.allocation Reason.retirement _
    (Retire.unwound _ _ 1 [11] rfl rfl) rfl

/-- An altered scheduler requests another expression even when none remains. -/
abbrev evaluatesTooFar : Provider State Nat Nat Reason Terminal :=
  { provider with work := fun before _ outcome => outcome = .returned .evaluate before }

/-- The local bound obligation rejects an extra evaluation after the requested count. -/
theorem extra_evaluation_rejected : ¬ evaluatesTooFar.Conforms := by
  intro conforms
  have impossible := conforms.evaluate_bound initial 0 [] initial (by decide +kernel) rfl
  exact Nat.lt_irrefl 0 impossible

/-- An altered scheduler requests completion before the next required expression. -/
abbrev finishesTooSoon : Provider State Nat Nat Reason Terminal :=
  { provider with work := fun before _ outcome => outcome = .returned .finish before }

/-- The exact completion-count obligation rejects a truncated expression schedule. -/
theorem premature_completion_rejected : ¬ finishesTooSoon.Conforms := by
  intro conforms
  have impossible : 0 = 1 :=
    conforms.finish_count initial 1 [] initial (by decide +kernel) rfl
  cases impossible

/-- A malformed dependency omits every evaluated position from cleanup. -/
abbrev missingCleanup : Provider State Nat Nat Reason Terminal :=
  { provider with cleanupOrder := fun _ _ => [] }

/-- Permutation checking rejects omitted destructor positions. -/
theorem missing_cleanup_rejected : ¬ missingCleanup.Conforms := by
  intro conforms
  have impossible : 0 = 1 := (conforms.cleanup_permutation one [11]).length_eq
  cases impossible

/-- A malformed dependency repeats every evaluated position. -/
abbrev repeatedCleanup : Provider State Nat Nat Reason Terminal :=
  { provider with
    cleanupOrder := fun _ values =>
      List.finRange values.length ++ List.finRange values.length }

/-- Permutation checking rejects duplicate destructor positions, even for equal values. -/
theorem duplicate_cleanup_rejected : ¬ repeatedCleanup.Conforms := by
  intro conforms
  have impossible : 2 = 1 := (conforms.cleanup_permutation one [11]).length_eq
  cases impossible

/-- A stale pre-destructor state cannot satisfy the exact double-unwind policy of this provider. -/
theorem stale_double_unwind_state_rejected :
    ¬ provider.double droppedLast .allocation .destructor
      (.double failedTwo .allocation .destructor) := by
  change Terminal.double failedTwo .allocation .destructor ≠
    Terminal.double droppedLast .allocation .destructor
  decide +kernel

/-- This scheduler admits both the next step and premature
completion of the reference. Its invalid alternatives do not erase its valid finite traces. -/
def permissiveScheduler : Provider (VectorState Nat) Nat Nat Empty Empty :=
  { natReference with
    work := fun before request outcome =>
      natReference.work before request outcome ∨ outcome = .returned .finish before }

/-- The completion operation is unchanged, so its current-content law still
holds even though the scheduling certificate does not. -/
def permissiveIndex : construction_contract.Index where
  State := VectorState Nat
  Element := Nat
  Resource := Nat
  Unwind := Empty
  Terminal := Empty
  provider := permissiveScheduler
  evaluate := natReferenceEvaluate
  vectors := vectorReference
  currentLaw := { finish_current := natReference_currentLaw.finish_current }

/-- A provider need not satisfy global scheduling conformance for the contract
to describe an actual valid one-expression execution and its exact contents. -/
theorem nonconforming_valid_execution_admitted :
    ¬ permissiveScheduler.Conforms ∧
      (construction_contract.contract permissiveIndex).requires natReferenceInitial (1 : Nat) ∧
      (construction_contract.contract permissiveIndex).post natReferenceInitial (1 : Nat)
        (.returned (1 : Nat) [some [42], some [7]]) := by
  refine ⟨?_, trivial, ?_⟩
  · intro conforms
    have impossible : 0 = 1 :=
      conforms.finish_count natReferenceInitial 1 [] natReferenceInitial
        (by decide +kernel) (Or.inr rfl)
    cases impossible
  · apply construction_reference permissiveIndex natReferenceInitial (1 : Nat)
      (.returned (1 : Nat) [some [42], some [7]]) trivial
    refine ⟨.returned (1 : Nat) [some [42], some [7]], ?_, rfl⟩
    exact Trace.next [] natReferenceInitial natReferenceInitial natReferenceInitial (7 : Nat) _
      (by decide +kernel) (Or.inl rfl) rfl
      (Trace.finishReturn [7] natReferenceInitial natReferenceInitial
        [some [42], some [7]] (1 : Nat) rfl (Or.inr rfl) rfl)

/-- Removing the redundant contract precondition does not admit the premature empty completion of
the scheduler for a requested one-expression construction. -/
theorem premature_empty_result_still_rejected :
    ¬ permissiveScheduler.run 1 natReferenceEvaluate natReferenceInitial
      (.returned 1 [some [42], some []]) := by
  intro execution
  have law : permissiveScheduler.CurrentLaw vectorReference :=
    ⟨natReference_currentLaw.finish_current⟩
  obtain ⟨values, _, _, count, current⟩ := Provider.run_returned_current law execution
  change some [] = some values at current
  have empty : values = [] := Option.some.inj current.symm
  subst values
  cases count

end SolanalibTest.Specs.Core.OwnedArray
