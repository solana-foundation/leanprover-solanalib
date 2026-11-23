/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.StakeCodecs.Values
import SolanalibTest.Conformance.Library.Families.Instructions.Builder

/-!
The native constructor records observe returned instruction contents. The
functional index below represents owned metadata and byte buffers by fresh
ledger slots; it does not claim to observe native allocation events or addresses.
The checker reconstructs those slots from the actual returned contents and
decides the registered operational relation at this successful provider index.
-/

set_option autoImplicit false
open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.StakeCodecs.Builder

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.LegacyStakeInstruction
open SolanalibTest.Conformance.Library.Borsh

abbrev State := InstructionBuilder.Sample.State
abbrev Item := Instruction.OwnedValue Nat Nat

def extended (before : State) (values : List Instruction.Meta) : State :=
  { before with metas := before.metas ++ [some values] }

theorem push_fresh (before : State) (values extra : List Instruction.Meta)
    (outcome : Outcome State Unit Nat Nat) :
    pushMetas Sample.index before.metas.length extra (extended before values) () outcome ↔
      outcome = .returned () (extended before (values ++ extra)) := by
  induction extra generalizing values with
  | nil => simp only [pushMetas, List.append_nil]; rfl
  | cons head tail ih =>
    simp only [pushMetas, Callback.bind]
    have pushed : Sample.index.providers.metaVec.push (extended before values)
        (before.metas.length, head) = (fun result : Outcome State Unit Nat Nat =>
          .returned () (extended before (values ++ [head])) = result) := by
      funext result
      simp [Sample.index, Sample.Ledger.providers, InstructionBuilder.Sample.providers,
        InstructionBuilder.Sample.metaVec, InstructionBuilder.Sample.metasAt, extended,
        Callback.ofFunction, List.set_append_right]
    rw [pushed]
    constructor
    · rintro ⟨intermediate, rfl, rest⟩
      simpa only [List.append_assoc, List.singleton_append] using (ih (values ++ [head])).mp rest
    · intro result
      refine ⟨_, rfl, ?_⟩
      apply (ih (values ++ [head])).mpr
      simpa only [List.append_assoc, List.singleton_append] using result

def prepared (before : State) (plan : Plan) : State :=
  { before with metas := before.metas ++ [some (plan.initial ++ plan.extra)], events :=
    before.events ++ [10] }

theorem prepare_graph (before : State) (plan : Plan) (outcome : Outcome State Nat Nat Nat) :
    prepareMetas Sample.index plan before () outcome ↔
      outcome = .returned before.metas.length (prepared before plan) := by
  unfold prepareMetas
  simp only [Callback.bind]
  have allocated : Sample.index.providers.metaVec.fromList before plan.initial =
      (fun result => .returned before.metas.length
        (extended { before with events := before.events ++ [10] } plan.initial) = result) := rfl
  rw [allocated]
  simp only [Callback.map, Owned.protect]
  constructor
  · rintro ⟨middle, rfl, pushed, ⟨body, bodyRuns, protectedOut⟩, mapped⟩
    have exactBody := (push_fresh { before with events := before.events ++ [10] } plan.initial
      plan.extra body).mp bodyRuns
    subst body
    change pushed = .returned () (prepared before plan) at protectedOut
    subst pushed
    exact mapped.symm
  · intro result
    subst outcome
    refine ⟨_, rfl, .returned () (prepared before plan),
      ⟨.returned () (prepared before plan), ?_, rfl⟩, rfl⟩
    exact (push_fresh { before with events := before.events ++ [10] } plan.initial plan.extra
      _).mpr rfl

def builderFns : Instructions.Builder.Fns Sample.index.builderTypes where
  fromList := fun before values => .returned before.metas.length
    (InstructionBuilder.Sample.allocateMetas before values)
  drop := fun before resource => .returned () (InstructionBuilder.Sample.retireMetas before
    resource)
  serialize := fun before (format, data) => .returned (.ok before.bytes.length)
    (InstructionBuilder.Sample.afterSerialize id format before data)
  unwrap := fun (before : State) (error : Nat) => .unwound (error + 100) { before with events :=
    before.events ++ [30] }
  double := fun (_ : State) (first later : Nat) => first + later + 1000

theorem builderFns_realizes : builderFns.Realizes Sample.index.providers :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def buildFn (before : State) (plan : Plan) : Item × State :=
  (⟨plan.programId, before.metas.length, before.bytes.length⟩,
    InstructionBuilder.Sample.afterSerialize id .bincode (prepared before plan) plan.data)

theorem build_graph (before : State) (plan : Plan) (outcome : Outcome State Item Nat Nat) :
    build Sample.index plan before () outcome ↔
      outcome = .returned (buildFn before plan).1 (buildFn before plan).2 := by
  unfold build
  simp only [Callback.bind]
  constructor
  · rintro ⟨middle, ready, built⟩
    have exactReady := (prepare_graph before plan middle).mp ready
    rw [exactReady] at built
    have exact := (Instructions.Builder.run_iff builderFns .bincode (prepared before plan) _
      builderFns_realizes outcome).mp built
    simpa [Instructions.Builder.runFn, Instructions.Builder.protectFn, Instructions.Builder.rawFn,
      builderFns, buildFn, prepared, Index.builderTypes, Sample.index, InstructionBuilder.Value]
        using exact.symm
  · intro result
    refine ⟨_, (prepare_graph before plan _).mpr rfl, ?_⟩
    apply (Instructions.Builder.run_iff builderFns .bincode (prepared before plan) _
      builderFns_realizes outcome).mpr
    simpa [Instructions.Builder.runFn, Instructions.Builder.protectFn, Instructions.Builder.rawFn,
      builderFns, buildFn, prepared, Index.builderTypes, Sample.index, InstructionBuilder.Value]
        using result.symm

def collect (evaluate : State → Nat → Item × State) : Nat → List Item → State → List Item × State
  | 0, values, before => (values, before)
  | count + 1, values, before =>
    let next := evaluate before values.length
    collect evaluate count (values ++ [next.1]) next.2

/-- The successful reference scheduler still decides the full trace relation:
its actual work and element callbacks rule out all unwind/terminal branches. -/
theorem trace_graph (count : Nat)
    (evaluate : Callback.Run State Nat Item Nat Nat)
    (evaluateFn : State → Nat → Item × State)
    (evaluated : ∀ before position outcome, position < count →
      (evaluate before position outcome ↔
        outcome = .returned (evaluateFn before position).1 (evaluateFn before position).2))
    (fuel : Nat) (values : List Item) (before : State)
    (outcome : Outcome State (List Item) (Owned.Array.Failure × Nat) Nat)
    (remaining : values.length + fuel = count) :
    Owned.Array.Trace Sample.Ledger.array count evaluate values before outcome ↔
      outcome = .returned (collect evaluateFn fuel values before).1 (collect evaluateFn fuel values
        before).2 := by
  induction fuel generalizing values before outcome with
  | zero =>
    have complete : values.length = count := by omega
    have inactive : ¬ values.length < count := by omega
    constructor
    · intro execution
      cases execution with
      | again _ _ _ _ work _ => simp [Sample.Ledger.array, Callback.ofFunction, inactive] at work
      | next _ _ _ _ _ _ bound _ _ _ => omega
      | workUnwind _ _ _ _ _ work _ => simp [Sample.Ledger.array, Callback.ofFunction, inactive]
        at work
      | workTerminal _ _ _ work => simp [Sample.Ledger.array, Callback.ofFunction, inactive] at work
      | evaluateUnwind _ _ _ _ _ _ bound _ _ _ => omega
      | evaluateTerminal _ _ _ _ bound _ _ => omega
      | finishReturn _ _ ready after resource _ work finished =>
        have readyEq : before = ready := by simpa [Sample.Ledger.array, Callback.ofFunction,
          inactive] using work
        cases readyEq
        change Outcome.returned values before = .returned resource after at finished
        cases finished
        rfl
      | finishUnwind _ _ _ _ _ _ _ _ finished _ => cases finished
      | finishTerminal _ _ _ _ _ _ finished => cases finished
    · intro exact
      cases exact
      exact .finishReturn values before before before values complete
        (by simp [Sample.Ledger.array, Callback.ofFunction, inactive]) rfl
  | succ fuel ih =>
    have active : values.length < count := by omega
    constructor
    · intro execution
      cases execution with
      | again _ _ _ _ work _ => simp [Sample.Ledger.array, Callback.ofFunction, active] at work
      | next _ _ ready after value _ bound work expression rest =>
        have readyEq : before = ready := by simpa [Sample.Ledger.array, Callback.ofFunction,
          active] using work
        cases readyEq
        have expr := (evaluated before values.length _ active).mp expression
        have valueEq := (Outcome.returned.inj expr).1
        have stateEq := (Outcome.returned.inj expr).2
        subst value after
        have more : (values ++ [(evaluateFn before values.length).1]).length + fuel = count := by
          simp only [List.length_append, List.length_singleton]
          omega
        exact (ih _ _ _ more).mp rest
      | workUnwind _ _ _ _ _ work _ => simp [Sample.Ledger.array, Callback.ofFunction, active]
        at work
      | workTerminal _ _ _ work => simp [Sample.Ledger.array, Callback.ofFunction, active] at work
      | evaluateUnwind _ _ ready after reason _ bound work expression _ =>
        have impossible := (evaluated ready values.length _ bound).mp expression
        cases impossible
      | evaluateTerminal _ _ ready reason bound work expression =>
        have impossible := (evaluated ready values.length _ bound).mp expression
        cases impossible
      | finishReturn _ _ _ _ _ complete _ _ => omega
      | finishUnwind _ _ _ _ _ _ complete _ _ _ => omega
      | finishTerminal _ _ _ _ complete _ _ => omega
    · intro exact
      rw [exact]
      apply Owned.Array.Trace.next values before before (evaluateFn before values.length).2
        (evaluateFn before values.length).1 _ active
        (by simp [Sample.Ledger.array, Callback.ofFunction, active])
      · exact (evaluated before values.length _ active).mpr rfl
      · apply (ih _ _ _ (by simp only [List.length_append, List.length_singleton]; omega)).mpr
        rfl

def emptyPlan : Plan := ⟨.zero, [], [], []⟩

def splitEvaluateFn (args : SplitArgs) (before : State) (position : Nat) : Item × State :=
  buildFn before ((splitPlans args).getD position emptyPlan)

theorem split_evaluate_graph (args : SplitArgs) (before : State) (position : Nat)
    (outcome : Outcome State Item Nat Nat) (bound : position < 3) :
    (∃ plan, (splitPlans args)[position]? = some plan ∧ build Sample.index plan before () outcome) ↔
      outcome = .returned (splitEvaluateFn args before position).1 (splitEvaluateFn args before
        position).2 := by
  have bounded : position < (splitPlans args).length := by simpa only [split_instruction_count]
    using bound
  have found : (splitPlans args)[position]? = some ((splitPlans args).getD position emptyPlan) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bounded]
  simp only [found, Option.some.injEq, splitEvaluateFn]
  constructor
  · rintro ⟨plan, rfl, ran⟩
    exact (build_graph _ _ _).mp ran
  · intro result
    exact ⟨_, rfl, (build_graph _ _ _).mpr result⟩

def splitFn (before : State) (args : SplitArgs) : List Item × State :=
  collect (splitEvaluateFn args) 3 [] before

theorem split_graph (before : State) (args : SplitArgs)
    (outcome : Outcome State (List Item) Nat Nat) :
    Solanalib.Specs.SolanaProgram.stake.instruction.split_run Sample.index before args outcome ↔
      .returned (splitFn before args).1 (splitFn before args).2 = outcome := by
  change (∃ detailed, Owned.Array.Trace Sample.Ledger.array 3
      (fun state position result => ∃ plan, (splitPlans args)[position]? = some plan ∧
        build Sample.index plan state () result) [] before detailed ∧ Owned.Array.erase detailed =
          outcome) ↔ _
  have graph := trace_graph 3 _ (splitEvaluateFn args) (split_evaluate_graph args) 3 [] before
  constructor
  · rintro ⟨detailed, trace, erased⟩
    have exact := (graph detailed rfl).mp trace
    subst detailed
    exact erased
  · intro exact
    refine ⟨.returned (splitFn before args).1 (splitFn before args).2, ?_, exact⟩
    exact (graph _ rfl).mpr rfl

def mergeElementFn (args : MergeArgs) (resource : Nat) (before : State) (_ : Nat) : Item × State :=
  (⟨(mergePlan args).programId, resource, before.bytes.length⟩,
    InstructionBuilder.Sample.afterSerialize id .bincode before (mergePlan args).data)

theorem merge_element_graph (args : MergeArgs) (resource : Nat) (before : State) (position : Nat)
    (outcome : Outcome State Item Nat Nat) :
    (InstructionBuilder.run Sample.index.builderTypes .bincode before
      ⟨(mergePlan args).programId, (mergePlan args).data, resource, Sample.index.providers⟩ outcome
        ↔
      outcome = .returned (mergeElementFn args resource before position).1 (mergeElementFn args
        resource before position).2) := by
  rw [Instructions.Builder.run_iff builderFns .bincode before _ builderFns_realizes outcome]
  simp only [Instructions.Builder.runFn, Instructions.Builder.rawFn, builderFns,
    Instructions.Builder.protectFn, mergeElementFn]
  exact eq_comm

def mergeFn (before : State) (args : MergeArgs) : List Item × State :=
  let ready := InstructionBuilder.Sample.allocateMetas before (mergePlan args).initial
  collect (mergeElementFn args before.metas.length) 1 [] ready

theorem merge_graph (before : State) (args : MergeArgs)
    (outcome : Outcome State (List Item) Nat Nat) :
    Solanalib.Specs.SolanaProgram.stake.instruction.merge_run Sample.index before args outcome ↔
      .returned (mergeFn before args).1 (mergeFn before args).2 = outcome := by
  change mergeRun Sample.index before args outcome ↔ _
  unfold mergeRun
  simp only [Callback.bind]
  have allocated : Sample.index.providers.metaVec.fromList before (mergePlan args).initial =
      (fun result => .returned before.metas.length
        (InstructionBuilder.Sample.allocateMetas before (mergePlan args).initial) = result) := rfl
  rw [allocated]
  let ready := InstructionBuilder.Sample.allocateMetas before (mergePlan args).initial
  have graph := trace_graph 1 _ (mergeElementFn args before.metas.length)
    (fun state position outcome _ => merge_element_graph args before.metas.length state position
      outcome) 1 [] ready
  constructor
  · rintro ⟨middle, rfl, detailed, trace, final⟩
    have exact := (graph detailed rfl).mp trace
    subst detailed
    exact final.symm
  · intro exact
    refine ⟨_, rfl, .returned (mergeFn before args).1 (mergeFn before args).2, ?_, exact.symm⟩
    exact (graph _ rfl).mpr rfl

/-! The recording contains instruction contents, so the lift assigns fresh
logical ledger slots to those contents. No native allocation trace is inferred. -/

instance : DecidableEq Item := fun a b =>
  if h : a.programId = b.programId ∧ a.metas = b.metas ∧ a.data = b.data then
    isTrue (by cases a; cases b; simp only at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl, rfl⟩)

def liftSingle (value : Instruction.Value) : Item × State :=
  (⟨value.programId, 0, 0⟩, ⟨[some value.metas], [some value.data], [10, 20]⟩)

def liftMany (values : List Instruction.Value) : List Item × State :=
  (values.zipIdx.map (fun (value, slot) => ⟨value.programId, slot, slot⟩),
    ⟨values.map (some ∘ (·.metas)), values.map (some ∘ (·.data)),
      (List.replicate values.length [10, 20]).flatten⟩)

def recordedBy {A V : Type} (parse : Json → Result A) (lift : A → V × State)
    (j : Json) : Result (Option (Outcome State V Nat Nat)) := do
  let result : Option (Outcome Unit A Empty Empty) ← parseOutcome parse asUnit noReason noReason j
  pure (result.map fun outcome => match outcome with
    | .returned value () => .returned (lift value).1 (lift value).2
    | .unwound impossible _ => nomatch impossible
    | .terminated impossible => nomatch impossible)

def observed (state : State) (item : Item) : Json :=
  match item.observe (InstructionBuilder.Sample.metasAt state) (InstructionBuilder.Sample.bytesAt
    state) with
  | some value => Instructions.instructionJson value
  | none => Json.str "instruction ledger resource is absent"

def outJson {V : Type} (render : State → V → Json) : Outcome State V Nat Nat → Json
  | .returned value state => returnedJson (render state value) Json.null
  | .unwound reason _ => Json.mkObj [("exit", toJson "unwound"), ("reason", toJson reason)]
  | .terminated reason => Json.mkObj [("exit", toJson "terminated"), ("reason", toJson reason)]

def initializeArgs (j : Json) : Result InitializeArgs := do
  pure ⟨← Instructions.keyField j "stake", ← StakeAddress.authorized (← field j "authorized"),
    ← StakeAddress.lockup (← field j "lockup")⟩

def authorizeArgs (j : Json) : Result AuthorizeArgs := do
  let role ← match ← (← field j "role").getStr? with
    | "staker" => pure Authorize.staker
    | "withdrawer" => pure Authorize.withdrawer
    | other => throw s!"unknown stake authority role {other}"
  pure ⟨← Instructions.keyField j "stake", ← Instructions.keyField j "authority",
    ← Instructions.keyField j "new_authority", role, ← nullable StakeAddress.pubkey (← field j
      "custodian")⟩

def delegateArgs (j : Json) : Result DelegateArgs := do
  pure ⟨← Instructions.keyField j "stake", ← Instructions.keyField j "authority", ←
    Instructions.keyField j "vote"⟩

def setLockupArgs (j : Json) : Result SetLockupArgs := do
  let lockup ← field j "lockup"
  pure ⟨← Instructions.keyField j "stake",
    ⟨← nullable i64Parse (← field lockup "unix_timestamp"), ← nullable u64Parse (← field lockup
      "epoch"),
      ← nullable StakeAddress.pubkey (← field lockup "custodian")⟩,
    ← Instructions.keyField j "custodian"⟩

def mergeArgs (j : Json) : Result MergeArgs := do
  pure ⟨← Instructions.keyField j "destination", ← Instructions.keyField j "source", ←
    Instructions.keyField j "authority"⟩

def splitArgs (j : Json) : Result SplitArgs := do
  pure ⟨← Instructions.keyField j "stake", ← Instructions.keyField j "authority", ←
    StakeAddress.u64Field j "lamports",
    ← Instructions.keyField j "destination"⟩

theorem initialize_evaluated (before : State) (args : InitializeArgs) (outcome : Outcome State Item
  Nat Nat) :
    Solanalib.Specs.SolanaProgram.stake.instruction.initialize_run Sample.index before args outcome
      ↔
      .returned (buildFn before (initializePlan args)).1 (buildFn before (initializePlan args)).2 =
        outcome :=
  (build_graph before (initializePlan args) outcome).trans eq_comm

theorem authorize_evaluated (before : State) (args : AuthorizeArgs) (outcome : Outcome State Item
  Nat Nat) :
    Solanalib.Specs.SolanaProgram.stake.instruction.authorize_run Sample.index before args outcome ↔
      .returned (buildFn before (authorizePlan args)).1 (buildFn before (authorizePlan args)).2 =
        outcome :=
  (build_graph before (authorizePlan args) outcome).trans eq_comm

theorem delegate_evaluated (before : State) (args : DelegateArgs) (outcome : Outcome State Item Nat
  Nat) :
    Solanalib.Specs.SolanaProgram.stake.instruction.delegate_stake_run Sample.index before args
      outcome ↔
      .returned (buildFn before (delegatePlan args)).1 (buildFn before (delegatePlan args)).2 =
        outcome :=
  (build_graph before (delegatePlan args) outcome).trans eq_comm

theorem set_lockup_evaluated (before : State) (args : SetLockupArgs) (outcome : Outcome State Item
  Nat Nat) :
    Solanalib.Specs.SolanaProgram.stake.instruction.set_lockup_run Sample.index before args outcome
      ↔
      .returned (buildFn before (setLockupPlan args)).1 (buildFn before (setLockupPlan args)).2 =
        outcome :=
  (build_graph before (setLockupPlan args) outcome).trans eq_comm

def initializeChecker : Checker where
  function := "solana_program::stake::instruction::initialize"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.instruction.initialize_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.instruction.initialize_run"]
  check := fun c => do
    asUnit c.state
    let args ← initializeArgs c.args
    pure (decideGraph _ _ (initialize_evaluated {} args)
      (← recordedBy Instructions.instructionOf liftSingle c.outcome) (outJson observed))

def authorizeChecker : Checker where
  function := "solana_program::stake::instruction::authorize"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.instruction.authorize_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.instruction.authorize_run"]
  check := fun c => do
    asUnit c.state
    let args ← authorizeArgs c.args
    pure (decideGraph _ _ (authorize_evaluated {} args)
      (← recordedBy Instructions.instructionOf liftSingle c.outcome) (outJson observed))

def delegateChecker : Checker where
  function := "solana_program::stake::instruction::delegate_stake"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.instruction.delegate_stake_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.instruction.delegate_stake_run"]
  check := fun c => do
    asUnit c.state
    let args ← delegateArgs c.args
    pure (decideGraph _ _ (delegate_evaluated {} args)
      (← recordedBy Instructions.instructionOf liftSingle c.outcome) (outJson observed))

def setLockupChecker : Checker where
  function := "solana_program::stake::instruction::set_lockup"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.instruction.set_lockup_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.instruction.set_lockup_run"]
  check := fun c => do
    asUnit c.state
    let args ← setLockupArgs c.args
    pure (decideGraph _ _ (set_lockup_evaluated {} args)
      (← recordedBy Instructions.instructionOf liftSingle c.outcome) (outJson observed))

def mergeChecker : Checker where
  function := "solana_program::stake::instruction::merge"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.instruction.merge_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.instruction.merge_run"]
  check := fun c => do
    asUnit c.state
    let args ← mergeArgs c.args
    pure (decideGraph _ _ (merge_graph {} args)
      (← recordedBy (asList Instructions.instructionOf) liftMany c.outcome)
      (outJson fun state values => listJson (observed state) values))

def splitChecker : Checker where
  function := "solana_program::stake::instruction::split"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.stake.instruction.split_run"
  decides := ["Solanalib.Specs.SolanaProgram.stake.instruction.split_run"]
  check := fun c => do
    asUnit c.state
    let args ← splitArgs c.args
    pure (decideGraph _ _ (split_graph {} args)
      (← recordedBy (asList Instructions.instructionOf) liftMany c.outcome)
      (outJson fun state values => listJson (observed state) values))

end SolanalibTest.Conformance.Library.Families.StakeCodecs.Builder
