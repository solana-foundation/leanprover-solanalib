/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTransferResources
public import Solanalib.Specs.Core.AnchorErrorOwned
public import Solanalib.Specs.Core.AnchorErrorOwnedTransport

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTransfer

/-- The wrapper of Anchor shares one actual state across vector construction,
invocation, owned-error conversion and cleanup. The invocation itself is the
opaque boundary; its outcome supplies no success or rollback guarantee. -/
structure Types where
  resources : Resources
  StringResource : Type
  BoxResource : Type
  errors : AnchorErrorOwned.Ops resources.builder.State StringResource BoxResource
    resources.builder.Terminal
  invoke : CpiRequest.Invocation resources.builder.State AccountInfo.Value ProgramError.Value
    resources.builder.Unwind resources.builder.Terminal

abbrev Error (types : Types) := AnchorErrorOwned.Error types.BoxResource

/-- Read the constructed instruction resources at the point the actual call
is formed. Provider effects cannot be hidden by reusing a saved wire snapshot.
The three moved accounts and nested seed groups retain their exact order. -/
def request (types : Types) (state : types.resources.builder.State)
    (args : Args types.resources)
    (instruction : Token.InstructionAllocated.Value types.resources.builder) :
    Option (CpiRequest.Request AccountInfo.Value) :=
  (Token.InstructionAllocated.observe types.resources.builder state instruction).map
    fun value => ⟨value, movedAccounts args, args.context.signerSeeds⟩

/-- Both current observations are exactly the local request-construction
domain. Neither observation can be replaced by the planned bytes of the builder. -/
theorem request_hasResult_iff (types : Types) (state : types.resources.builder.State)
    (args : Args types.resources)
    (instruction : Token.InstructionAllocated.Value types.resources.builder) :
    (∃ call, request types state args instruction = some call) ↔
      ConstructedReadable types.resources state instruction := by
  unfold request Token.InstructionAllocated.observe Instruction.OwnedValue.observe
    ConstructedReadable Owned.VectorOps.Live
  cases metas : types.resources.builder.metas.current state instruction.metas <;>
    cases bytes : types.resources.builder.bytes.current state instruction.data <;>
    simp

/-- Admission is precisely current request availability at every actual
successful construction exit; it places no condition on an unreached call. -/
theorem buildReady_iff_requests (types : Types) (before : types.resources.builder.State)
    (args : Args types.resources) :
    BuildReady types.resources before args ↔
      ∀ instruction after,
        Token.InstructionAllocated.run types.resources.builder before (plan args)
          (.returned (.ok instruction) after) →
          ∃ call, request types after args instruction = some call := by
  constructor
  · intro ready instruction after built
    exact (request_hasResult_iff types after args instruction).mpr (ready instruction after built)
  · intro available instruction after built
    exact (request_hasResult_iff types after args instruction).mp (available instruction after
      built)

/-- `map_err(Into::into)` runs before the temporary account array is dropped.
It boxes the exact ProgramError returned by the invocation in the actual state of that callback. The
fixed conversion has no unwind callback of its own. -/
def invokeAndConvert (types : Types) (args : Args types.resources)
    (instruction : Token.InstructionAllocated.Value types.resources.builder) :
    Callback.Run types.resources.builder.State Unit (Except (Error types) Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal :=
  fun before _ outcome => match request types before args instruction with
    | none => False
    | some call => Callback.bind (fun state (_ : Unit) => types.invoke state call)
      (fun result after final => match result with
        | .ok () => final = .returned (.ok ()) after
        | .error failure => Callback.map Except.error
          (AccountInfoRc.lift (AnchorErrorOwned.fromProgram types.errors)) after failure final)
      before () outcome

/-- Continue one actual invocation exit. Success, unwind and terminal exits
keep their states and reasons. A ProgramError uses each actual Box-allocation
exit, without assuming that allocation returns or terminates. -/
def InvocationContinuation (types : Types)
    (invoked : Outcome types.resources.builder.State (Except ProgramError.Value Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal)
    (pending : Outcome types.resources.builder.State (Except (Error types) Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal) : Prop :=
  match invoked with
  | .returned (.ok ()) after => pending = .returned (.ok ()) after
  | .returned (.error failure) after => Callback.map Except.error
      (AccountInfoRc.lift (AnchorErrorOwned.fromProgram types.errors)) after failure pending
  | .unwound reason after => pending = .unwound reason after
  | .terminated reason => pending = .terminated reason

/-- Once the actual request is readable, local forwarding loses no invocation
exit or supplied conversion continuation. No finite invocation is invented. -/
theorem invokeAndConvert_iff (types : Types) (args : Args types.resources)
    (instruction : Token.InstructionAllocated.Value types.resources.builder)
    (before : types.resources.builder.State) (call : CpiRequest.Request AccountInfo.Value)
    (readable : request types before args instruction = some call)
    (pending : Outcome types.resources.builder.State (Except (Error types) Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal) :
    invokeAndConvert types args instruction before () pending ↔
      ∃ invoked, types.invoke before call invoked ∧ InvocationContinuation types invoked pending :=
        by
  rw [invokeAndConvert, readable]
  simp only [Callback.bind]
  apply exists_congr
  intro invoked
  cases invoked with
  | returned value after =>
    cases value with
    | error _ => rfl
    | ok value => cases value; rfl
  | unwound _ _ => rfl
  | terminated _ => rfl

/-- The source first constructs its instruction through the shared token
builder. A construction unwind drops the still-unmoved context. After success,
the three fields move into the invocation array. Edition 2021 cleanup drops
the fields of the instruction, the array, then the remaining-account
vector of the context. The separate source no-unwind premises rule out a destructor unwind
replacing an owned pending return; the raw relation retains all provider exits.
Every terminal stops immediately and has no fabricated final state. -/
def run (types : Types) :
    Callback.Run types.resources.builder.State (Args types.resources) (Except (Error types) Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal :=
  fun before args outcome => ∃ built,
    Token.InstructionAllocated.run types.resources.builder before (plan args) built ∧
    (match built with
      | .returned (.error _) _ => False
      | .returned (.ok instruction) after =>
        Owned.scope types.resources.builder.doubleUnwind (invocationDrops args instruction)
          (invokeAndConvert types args instruction) after () outcome
      | .unwound reason after =>
        Owned.cleanup types.resources.builder.doubleUnwind (contextDrops args)
          (.unwound reason after) outcome
      | .terminated reason => outcome = .terminated reason)

def family : Family where
  Index := Types
  State := fun types => types.resources.builder.State
  Args := fun types => Args types.resources
  Value := fun types => Except (Error types) Unit
  Unwind := fun types => types.resources.builder.Unwind
  Terminal := fun types => types.resources.builder.Terminal
  contract := fun types => {
    requires := BuildReady types.resources
    post := run types }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ step
  exact step

/-- Composition after an actual successful builder execution. The retained
instruction identities, invocation effects and cleanup states are all explicit. -/
theorem run_after_build (types : Types) (args : Args types.resources)
    (before after : types.resources.builder.State)
    (instruction : Token.InstructionAllocated.Value types.resources.builder)
    (pending final : Outcome types.resources.builder.State (Except (Error types) Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal)
    (built : Token.InstructionAllocated.run types.resources.builder before (plan args)
      (.returned (.ok instruction) after))
    (called : invokeAndConvert types args instruction after () pending)
    (cleaned : Owned.cleanup types.resources.builder.doubleUnwind
      (invocationDrops args instruction) pending final) : run types before args final :=
  ⟨.returned (.ok instruction) after, built, pending, called, cleaned⟩

/-- Every admitted successful construction forms its actual current request.
Each actual invocation, conversion and source-ordered cleanup continuation then
produces the corresponding transfer exit, with all intermediate states kept. -/
theorem BuildReady.after_build (types : Types) (args : Args types.resources)
    (before after : types.resources.builder.State)
    (instruction : Token.InstructionAllocated.Value types.resources.builder)
    (ready : BuildReady types.resources before args)
    (built : Token.InstructionAllocated.run types.resources.builder before (plan args)
      (.returned (.ok instruction) after)) :
    ∃ call, request types after args instruction = some call ∧
      ∀ invoked pending final,
        types.invoke after call invoked → InvocationContinuation types invoked pending →
        Owned.cleanup types.resources.builder.doubleUnwind
          (invocationDrops args instruction) pending final → run types before args final := by
  obtain ⟨call, readable⟩ := (buildReady_iff_requests types before args).mp ready instruction after
    built
  refine ⟨call, readable, ?_⟩
  intro invoked pending final called converted cleaned
  exact run_after_build types args before after instruction pending final built
    ((invokeAndConvert_iff types args instruction after call readable pending).mpr
      ⟨invoked, called, converted⟩) cleaned

/-- An actual construction unwind needs only its actual context-cleanup
continuation. It never forms a request or invokes CPI. -/
theorem run_build_unwind (types : Types) (args : Args types.resources)
    (before after : types.resources.builder.State) (reason : types.resources.builder.Unwind)
    (final : Outcome types.resources.builder.State (Except (Error types) Unit)
      types.resources.builder.Unwind types.resources.builder.Terminal)
    (built : Token.InstructionAllocated.run types.resources.builder before (plan args)
      (.unwound reason after))
    (cleaned : Owned.cleanup types.resources.builder.doubleUnwind (contextDrops args)
      (.unwound reason after) final) : run types before args final :=
  ⟨.unwound reason after, built, cleaned⟩

/-- A terminal builder dependency prevents invocation, boxing and all caller
cleanup, regardless of whether those providers have any finite executions. -/
theorem run_build_terminal (types : Types) (args : Args types.resources)
    (before : types.resources.builder.State) (reason : types.resources.builder.Terminal)
    (built : Token.InstructionAllocated.run types.resources.builder before (plan args)
      (.terminated reason)) : run types before args (.terminated reason) :=
  ⟨.terminated reason, built, rfl⟩

/-- The continuation obligation for every actual builder exit. Successful
construction supplies an actual request and preserves every supplied later
exit; unwind follows actual cleanup, and a terminal stops immediately. The
fixed program ID makes an ordinary builder rejection impossible. -/
theorem BuildReady.builder_continuation (types : Types) (args : Args types.resources)
    (before : types.resources.builder.State)
    (built : Outcome types.resources.builder.State
      (Except Token.Error (Token.InstructionAllocated.Value types.resources.builder))
      types.resources.builder.Unwind types.resources.builder.Terminal)
    (ready : BuildReady types.resources before args)
    (execution : Token.InstructionAllocated.run types.resources.builder before (plan args) built) :
    match built with
    | .returned (.error _) _ => False
    | .returned (.ok instruction) after =>
        ∃ call, request types after args instruction = some call ∧
          ∀ invoked pending final,
            types.invoke after call invoked → InvocationContinuation types invoked pending →
            Owned.cleanup types.resources.builder.doubleUnwind
              (invocationDrops args instruction) pending final → run types before args final
    | .unwound reason after => ∀ final,
        Owned.cleanup types.resources.builder.doubleUnwind (contextDrops args)
          (.unwound reason after) final → run types before args final
    | .terminated reason => run types before args (.terminated reason) := by
  cases built with
  | returned value after =>
    cases value with
    | error error => exact builder_error_impossible args before after error execution
    | ok instruction => exact ready.after_build types args before after instruction execution
  | unwound reason after =>
    exact fun final cleaned => run_build_unwind types args before after reason final execution
      cleaned
  | terminated reason => exact run_build_terminal types args before reason execution

end Solanalib.Specs.Core.AnchorSplTransfer
