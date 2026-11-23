/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTransferOwned
public import Solanalib.Specs.Core.AnchorSplTransferVectorSample
public import Solanalib.Specs.Core.AnchorErrorOwnedReference
public import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTransfer.Sample

/-- Independent concrete error resources, Rc scheduling events, remaining
account storage, and exact invocation requests. This is a mathematical client
state; no event claims a Rust allocation or reference-count implementation. -/
structure Aux where
  errors : AnchorErrorOwned.Reference.State
  rcEvents : List AccountInfoRc.Event
  remaining : Owned.VectorState AccountInfo.Value
  calls : List (CpiRequest.Request AccountInfo.Value)

abbrev State := Token.InstructionAllocated.Witness.State × Aux

def errorsFocus : Owned.Focus State AnchorErrorOwned.Reference.State where
  get := fun state => state.2.errors
  set := fun state errors => (state.1, { state.2 with errors })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def remainingFocus : Owned.Focus State (Owned.VectorState AccountInfo.Value) where
  get := fun state => state.2.remaining
  set := fun state remaining => (state.1, { state.2 with remaining })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def rc : AccountInfoRc.Ops State Nat where
  cloneRc := Callback.ofFunction fun state (field, cell) =>
    .returned () (state.1, { state.2 with rcEvents := state.2.rcEvents ++ [.clone field cell] })
  dropRc := Callback.ofFunction fun state (field, cell) =>
    .returned () (state.1, { state.2 with rcEvents := state.2.rcEvents ++ [.drop field cell] })

def infoEvents (info : AccountInfo.Value) : List AccountInfoRc.Event :=
  [.drop .lamports info.lamports, .drop .data info.data]

def afterInfo (state : State) (info : AccountInfo.Value) : State :=
  (state.1, { state.2 with rcEvents := state.2.rcEvents ++ infoEvents info })

theorem info_drop (state : State) (info : AccountInfo.Value) :
    AccountInfoRc.dropCall rc state info (.returned () (afterInfo state info)) := by
  refine ⟨.returned () (state.1,
    { state.2 with rcEvents := state.2.rcEvents ++ [.drop .lamports info.lamports] }), rfl, ?_⟩
  simp only [rc, Callback.ofFunction, afterInfo, infoEvents, List.append_assoc]
  rfl

/-- The reference remaining-vector provider explicitly uses the same Rc
element interpretation before retiring its ledger slot. The generic SDK
wrapper calls this provider once and never duplicates these element drops. -/
def dropInfos : List AccountInfo.Value → Callback.Run State Unit Unit Empty Nat
  | [] => Callback.ofFunction fun state _ => .returned () state
  | info :: rest => fun state _ => Callback.bind
    (fun before (_ : Unit) => AccountInfoRc.dropCall rc before info)
    (fun _ after => dropInfos rest after ()) state ()

def afterInfos (state : State) (infos : List AccountInfo.Value) : State :=
  (state.1, { state.2 with rcEvents := state.2.rcEvents ++ infos.flatMap infoEvents })

theorem infos_drop (state : State) (infos : List AccountInfo.Value) :
    dropInfos infos state () (.returned () (afterInfos state infos)) := by
  induction infos generalizing state with
  | nil => simp [dropInfos, Callback.ofFunction, afterInfos]
  | cons info rest induction =>
    refine ⟨.returned () (afterInfo state info), info_drop state info, ?_⟩
    simpa [afterInfo, afterInfos, List.append_assoc] using induction (afterInfo state info)

def remainingDrop : Callback.Run State Nat Unit Empty Nat :=
  fun state resource outcome => ∃ infos,
    state.2.remaining[resource]?.join = some infos ∧
    Callback.bind (dropInfos infos)
      (fun _ after => (Owned.vectorReference.focus remainingFocus).drop after resource)
      state () outcome

def remainingOps : Owned.VectorOps State AccountInfo.Value Nat Nat Nat :=
  { Owned.vectorReference.focus remainingFocus with
    drop := AccountInfoRc.lift remainingDrop }

/-- The same concrete element-drop interpretation satisfies the current-content and retirement laws
of the vector. This proves ledger behavior only; Rc
events remain dependency scheduling observations. -/
theorem remainingOps_laws : remainingOps.Laws := by
  refine { Owned.VectorOps.focus_laws Owned.vectorReference_laws remainingFocus with
    drop_current := ?_
    drop_unwind_consumed := ?_ }
  · intro before resource after _ run
    obtain ⟨produced, called, equal⟩ := run
    cases produced with
    | unwound impossible _ => nomatch impossible
    | terminated reason => cases equal
    | returned completed final =>
      cases completed
      cases equal
      obtain ⟨infos, _, stepped, _, next⟩ := called
      cases stepped with
      | unwound impossible _ => nomatch impossible
      | terminated reason => cases next
      | returned completed middle =>
        cases completed
        obtain ⟨innerAfter, retired, rfl⟩ :=
          (remainingFocus.lift_returned_iff Owned.vectorReference.drop middle resource () after).mp
            next
        exact Owned.VectorState.retire_current retired
  · intro before resource reason after _ run
    obtain ⟨produced, _, equal⟩ := run
    cases produced with
    | returned completed final => cases equal
    | unwound impossible _ => nomatch impossible
    | terminated reason => cases equal

def resources : Resources where
  builder := VectorSample.types Aux
  RemainingResource := Nat
  remaining := remainingOps
  rc := rc

def types : Types where
  resources := resources
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorErrorOwned.Reference.natOps.focus errorsFocus
  invoke := Callback.ofFunction fun state request => .returned (.error .insufficientFunds)
    (state.1, { state.2 with calls := state.2.calls ++ [request] })

def info (number : Nat) : AccountInfo.Value :=
  { AccountInfo.sampleInfo with
    key := .ofNat number
    lamports := ⟨2 * number⟩
    data := ⟨2 * number + 1⟩ }

def args : Args resources :=
  ⟨⟨⟨info 1, info 2, info 3⟩, (0 : Nat), .ofNat 99, [[], [[1, 2], []]]⟩, 42⟩

def auxiliary : Aux :=
  ⟨AnchorErrorOwned.Reference.initial 1, [], [some [info 4]], []⟩

def initial : State := (([], []), auxiliary)
def instruction := VectorSample.value Aux (plan args)

def builtState : State :=
  (([some (plan args).data], [some (plan args).metas.items]), auxiliary)

def call : CpiRequest.Request AccountInfo.Value :=
  ⟨(plan args).instruction, movedAccounts args, args.context.signerSeeds⟩

def afterInvoke : State :=
  (builtState.1, { builtState.2 with calls := [call] })

def boxed := AnchorErrorOwned.Reference.fromProgramResult afterInvoke.2.errors .insufficientFunds
def afterBox : State := errorsFocus.set afterInvoke boxed.2
def afterMetas : State := ((afterBox.1.1, [none]), afterBox.2)
def afterBytes : State := (([none], [none]), afterBox.2)
def afterAccounts : State := afterInfo (afterInfo (afterInfo afterBytes (info 1)) (info 2)) (info 3)
def finalState : State := remainingFocus.set (afterInfos afterAccounts [info 4]) [none]

/-- Every successful construction by the concrete vector interpretation leaves
both current instruction vectors readable. This covers all builder outcomes,
not just the execution chosen below. -/
theorem build_ready (aux : Aux) (args : Args resources) :
    BuildReady resources (([], []), aux) args := by
  intro instruction after built
  exact VectorSample.transfer_readable aux (Solanalib.Runtime.u64le args.amount.toNat)
    (Instruction.accountMeta args.context.accounts.source.key false true)
    (Instruction.accountMeta args.context.accounts.destination.key false true)
    (Instruction.accountMeta args.context.accounts.authority.key true false)
    instruction after built

theorem builder_returns : Token.InstructionAllocated.run resources.builder initial (plan args)
    (.returned (.ok instruction) builtState) :=
  VectorSample.run_returns (plan args) auxiliary (plan_admitted args)

theorem invocation_returns_error : invokeAndConvert types args instruction builtState ()
    (.returned (.error boxed.1) afterBox) := by
  refine ⟨.returned (.error .insufficientFunds) afterInvoke, rfl, ?_⟩
  refine ⟨.returned boxed.1 afterBox, ?_, rfl⟩
  refine ⟨.returned boxed.1 afterBox, ?_, rfl⟩
  exact AnchorErrorOwned.fromProgram_focus_returned AnchorErrorOwned.Reference.natOps errorsFocus
    afterInvoke .insufficientFunds boxed.1 boxed.2
    (AnchorErrorOwned.Reference.fromProgram_returns_nat afterInvoke.2.errors .insufficientFunds (by
      decide))

theorem sdk_info_drop (state : State) (value : AccountInfo.Value) :
    dropInfo resources value state (.returned () (afterInfo state value)) :=
  ⟨.returned () (afterInfo state value), info_drop state value, rfl⟩

theorem remaining_drop (state : State) (infos : List AccountInfo.Value)
    (current : state.2.remaining = [some infos]) :
    remainingOps.drop state 0
      (.returned () (remainingFocus.set (afterInfos state infos) [none])) := by
  refine ⟨.returned () (remainingFocus.set (afterInfos state infos) [none]), ?_, rfl⟩
  refine ⟨infos, ?_, .returned () (afterInfos state infos), infos_drop state infos, ?_⟩
  · change state.2.remaining[0]?.join = some infos
    rw [current]
    rfl
  · refine ⟨.returned () [none], ?_, rfl⟩
    refine ⟨infos, ?_, ?_⟩
    · change state.2.remaining[0]?.join = some infos
      rw [current]
      rfl
    · change Outcome.returned () [none] =
        (Outcome.returned () (state.2.remaining.set 0 none) :
          Outcome (Owned.VectorState AccountInfo.Value) Unit Empty Nat)
      rw [current]
      rfl

/-- The normal error remains owned while the instruction vectors, moved
account array and remaining-account vector are cleaned up in edition 2021 order. -/
theorem cleanup_returns :
    Owned.DropReturns (invocationDrops args instruction) afterBox finalState := by
  refine .cons _ _ afterBox afterMetas finalState ?_ ?_
  · exact ⟨.returned () (afterBox.1.1, [none]),
      Token.InstructionAllocated.Witness.metas_drop _ _, rfl⟩
  refine .cons _ _ _ afterBytes finalState ?_ ?_
  · exact ⟨.returned () ([none], [none]),
      Token.InstructionAllocated.Witness.bytes_drop _ _, rfl⟩
  refine .cons _ _ afterBytes (afterInfo afterBytes (info 1)) finalState (sdk_info_drop _ _) ?_
  refine .cons _ _ _ (afterInfo (afterInfo afterBytes (info 1)) (info 2)) finalState (sdk_info_drop
    _ _) ?_
  refine .cons _ _ _ afterAccounts finalState (sdk_info_drop _ _) ?_
  exact .cons _ _ _ finalState finalState (remaining_drop afterAccounts [info 4] rfl) (.nil _)

/-- A closed reference execution composes real vector operations, a failing
invocation, an owned ProgramError Box, and all source-ordered cleanup. -/
theorem execution : FamilyHasExecution family reference types := by
  refine ⟨initial, args, .returned (.error boxed.1) finalState, build_ready auxiliary args, ?_⟩
  exact run_after_build types args initial builtState instruction _ _ builder_returns
    invocation_returns_error (cleanup_returns.cleanup_returned _ (Except.error boxed.1))

/-- Cleanup retains the exact code and absent diagnostics of the live returned error. -/
theorem final_error_current : AnchorErrorOwned.current types.errors finalState boxed.1 =
    some (AnchorAccount.programError .insufficientFunds) := rfl

/-- Current instruction and remaining-vector resources are actually retired. -/
theorem final_vectors_retired :
    resources.builder.bytes.current finalState instruction.data = none ∧
    resources.builder.metas.current finalState instruction.metas = none ∧
    resources.remaining.current finalState args.context.remaining = none := ⟨rfl, rfl, rfl⟩

/-- The invocation includes three moved accounts only; the fourth account is
ignored by CPI but its Rc fields are subsequently destroyed through its vector. -/
theorem final_rc_order : finalState.2.rcEvents =
    infoEvents (info 1) ++ infoEvents (info 2) ++ infoEvents (info 3) ++ infoEvents (info 4) := rfl

end Solanalib.Specs.Core.AnchorSplTransfer.Sample
