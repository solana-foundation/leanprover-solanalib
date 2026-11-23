/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSpl
public import Solanalib.Specs.Core.AnchorContextOwned
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.TokenInstructionAllocated
public import Solanalib.Specs.Core.TokenInstructionPlan

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTransfer

/-- Resources and explicit providers owned by the transfer call of Anchor SPL.
The drop provider of the remaining-account vector owns both element destruction
and storage retirement; its binding must use the same AccountInfoRc
interpretation, without a second element-drop pass in the SDK wrapper.
Source non-unwind guarantees are premises of the separate cleanup theorem,
not hidden fields restricting the raw transfer family. -/
structure Resources where
  builder : Token.InstructionAllocated.Types
  RemainingResource : Type
  remaining : Owned.VectorOps builder.State AccountInfo.Value RemainingResource
    builder.Unwind builder.Terminal
  rc : AccountInfoRc.Ops builder.State builder.Terminal

/-- The context owns three AccountInfo values and one remaining-account vector.
Its signer seeds and program ID are borrowed/copyable values, not invented
allocation resources. The source helper deliberately ignores its program ID. -/
abbrev Context (resources : Resources) :=
  AnchorContextOwned.Value AnchorSpl.TransferAccounts resources.RemainingResource

structure Args (resources : Resources) where
  context : Context resources
  amount : UInt64

/-- Builder arguments use the fixed legacy program, no multisig signers, and
the ordered source, destination and authority keys. -/
def builderArgs {resources : Resources} (args : Args resources) :
    Token.Instruction.TransferArgs where
  programId := Token.legacyProgramId
  source := args.context.accounts.source.key
  destination := args.context.accounts.destination.key
  authority := args.context.accounts.authority.key
  signers := []
  amount := args.amount.toNat

def plan {resources : Resources} (args : Args resources) : Token.InstructionAllocated.Plan :=
  Token.InstructionAllocated.transferPlan (builderArgs args)

/-- The program-ID check cannot reject this fixed-ID helper. Allocation and
other dependency exits are separate from this ordinary admission result. -/
theorem plan_admitted {resources : Resources} (args : Args resources) :
    Token.Instruction.checkProgram (plan args).programs (plan args).programId = .ok () := by
  simp [plan, Token.InstructionAllocated.transferPlan, builderArgs,
    Token.Instruction.checkProgram, Token.Instruction.ProgramSet.accepts]

/-- The two current vector observations needed when the constructed instruction
is borrowed by the invocation. This asserts neither a saved wire value nor
Rust ownership, layout or pointer permission. -/
def ConstructedReadable (resources : Resources) (state : resources.builder.State)
    (instruction : Token.InstructionAllocated.Value resources.builder) : Prop :=
  resources.builder.metas.Live state instruction.metas ∧
    resources.builder.bytes.Live state instruction.data

/-- Every actual successful builder return must leave its two constructed
vectors readable in that returned state. Earlier unwind and terminal exits
need neither observation. This condition assumes no dependency execution,
vector laws, destructor return or CPI outcome. -/
def BuildReady (resources : Resources) (before : resources.builder.State)
    (args : Args resources) : Prop :=
  ∀ instruction after,
    Token.InstructionAllocated.run resources.builder before (plan args)
      (.returned (.ok instruction) after) →
      ConstructedReadable resources after instruction

/-- The temporary invocation array contains moved fields in source order.
It contains neither cloned values nor ctx.remaining_accounts. -/
def movedAccounts {resources : Resources} (args : Args resources) : List AccountInfo.Value :=
  [args.context.accounts.source, args.context.accounts.destination, args.context.accounts.authority]

/-- One actual moved AccountInfo owner invokes its lamports and data Rc drops.
The surrounding cleanup engine supplies its current state. -/
def dropInfo (resources : Resources) (info : AccountInfo.Value) :
    Owned.DropAction resources.builder.State resources.builder.Unwind resources.builder.Terminal :=
  fun state => AccountInfoRc.lift (AccountInfoRc.dropCall resources.rc) state info

/-- Array elements drop in ascending index order. Repeated aliasing values
still represent separately moved owners; this list is never deduplicated. -/
def accountDrops {resources : Resources} (args : Args resources) :
    List (Owned.DropAction resources.builder.State resources.builder.Unwind
      resources.builder.Terminal) :=
  (movedAccounts args).map (dropInfo resources)

/-- Before the instruction returns, all context account fields remain owned
by the parameter. Its ordinary field order is accounts, then remaining vector. -/
def contextDrops {resources : Resources} (args : Args resources) :
    List (Owned.DropAction resources.builder.State resources.builder.Unwind
      resources.builder.Terminal) :=
  accountDrops args ++ [resources.remaining.dropAction args.context.remaining]

/-- Anchor SPL 1.0.2 uses edition 2021. The account array is a temporary in the tail expression of
the function body, so its scope extends past the local ix: instruction metadata then bytes drop
before the elements of the array. The remaining vector is still owned by the partially moved
context parameter. -/
def invocationDrops {resources : Resources} (args : Args resources)
    (instruction : Token.InstructionAllocated.Value resources.builder) :
    List (Owned.DropAction resources.builder.State resources.builder.Unwind
      resources.builder.Terminal) :=
  Token.InstructionAllocated.drops resources.builder instruction ++ accountDrops args ++
    [resources.remaining.dropAction args.context.remaining]

/-- Lifting the actual Rc field-drop sequence cannot add an unwind outcome. -/
theorem dropInfo_no_unwind (resources : Resources) (info : AccountInfo.Value)
    (before after : resources.builder.State) (reason : resources.builder.Unwind) :
    ¬ dropInfo resources info before (.unwound reason after) := by
  rintro ⟨produced, _, equal⟩
  cases produced with
  | returned value state => cases equal
  | unwound impossible state => nomatch impossible
  | terminated reason => cases equal

/-- The three source destructor guarantees rule out unwind for every action
in the actual post-invocation scope. No destructor return is assumed, and
terminal exits remain possible. -/
theorem invocationDrops_no_unwind {resources : Resources}
    (byteDropNoUnwind : ∀ before resource reason after,
      ¬ resources.builder.bytes.drop before resource (.unwound reason after))
    (metaDropNoUnwind : ∀ before resource reason after,
      ¬ resources.builder.metas.drop before resource (.unwound reason after))
    (remainingDropNoUnwind : ∀ before resource reason after,
      ¬ resources.remaining.drop before resource (.unwound reason after))
    (args : Args resources)
    (instruction : Token.InstructionAllocated.Value resources.builder)
    (action : Owned.DropAction resources.builder.State resources.builder.Unwind
      resources.builder.Terminal)
    (member : action ∈ invocationDrops args instruction)
    (before after : resources.builder.State) (reason : resources.builder.Unwind) :
    ¬ action before (.unwound reason after) := by
  simp only [invocationDrops, accountDrops, movedAccounts, Token.InstructionAllocated.drops,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact metaDropNoUnwind before instruction.metas reason after
  · exact byteDropNoUnwind before instruction.data reason after
  · exact dropInfo_no_unwind resources _ before after reason
  · exact dropInfo_no_unwind resources _ before after reason
  · exact dropInfo_no_unwind resources _ before after reason
  · exact remainingDropNoUnwind before args.context.remaining reason after

/-- Non-unwinding cleanup cannot discard an owned pending return by replacing
it with an unwind. Terminal exits remain explicit and are not excluded. -/
theorem cleanup_return_not_unwound {State Value Unwind Terminal : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (noUnwind : ∀ action ∈ drops, ∀ before reason after,
      ¬ action before (.unwound reason after))
    (value : Value) (before after : State) (reason : Unwind) :
    ¬ Owned.cleanup double drops (.returned value before) (.unwound reason after) := by
  induction drops generalizing before with
  | nil => intro impossible; cases impossible
  | cons action rest induction =>
    rintro ⟨produced, called, continuation⟩
    cases produced with
    | returned completed middle =>
      cases completed
      exact induction (fun current member => noUnwind current (List.mem_cons_of_mem action member))
        middle continuation
    | unwound reason middle => exact noUnwind action (by simp) before reason middle called
    | terminated terminal => cases continuation

/-- Fixed-ID admission has no ordinary builder-error branch, even for a
provider interpretation with no normal allocation execution. -/
theorem builder_error_impossible {resources : Resources} (args : Args resources)
    (before after : resources.builder.State) (error : Token.Error) :
    ¬ Token.InstructionAllocated.run resources.builder before (plan args)
      (.returned (.error error) after) := by
  intro run
  unfold Token.InstructionAllocated.run at run
  rw [plan_admitted args] at run
  obtain ⟨allocated, _, rest⟩ := run
  cases allocated with
  | unwound reason middle => cases rest
  | terminated reason => cases rest
  | returned resource middle =>
    obtain ⟨body, bodyRun, cleanup⟩ := rest
    cases body with
    | unwound reason state =>
      -- The unwind-only protector cannot turn an unwind into a returned error.
      have : False := by
        simp only [Owned.onUnwind, Owned.cleanup] at cleanup
        obtain ⟨dropped, dropRun, continuation⟩ := cleanup
        cases dropped with
        | returned value state => cases value; cases continuation
        | unwound reason state =>
          obtain ⟨terminal, _, impossible⟩ := continuation
          cases impossible
        | terminated reason => cases continuation
      exact this
    | terminated reason =>
      simp only [Owned.onUnwind, Owned.cleanup] at cleanup
      cases cleanup
    | returned value state =>
      change (Outcome.returned (.error error) after :
        Outcome resources.builder.State
          (Except Token.Error (Token.InstructionAllocated.Value resources.builder))
          resources.builder.Unwind resources.builder.Terminal) = .returned value state at cleanup
      cases cleanup
      obtain ⟨written, _, continuation⟩ := bodyRun
      cases written with
      | unwound reason state => cases continuation
      | terminated reason => cases continuation
      | returned completed state =>
        obtain ⟨metas, _, impossible⟩ := continuation
        cases metas <;> cases impossible

end Solanalib.Specs.Core.AnchorSplTransfer
