/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Builders
public import Solanalib.Specs.Core.CpiRequest

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations

/-- The only source return shapes in this set. Version bindings provide the
corresponding Unit or u64 source-result adapter. -/
inductive Return where
  | unit
  | size (value : UInt64)
  deriving DecidableEq, Repr

/-- Shared actual state and primitive providers. Invocation stays opaque at
its complete signature. The optional seed reference distinguishes invoke from
invoke_signed even when the observed seed list is empty. -/
structure Types (binding : Binding) where
  builder : Builder
  RemainingResource : Type
  SeedRef : Type
  StringResource : Type
  BoxResource : Type
  rc : AccountInfoRc.Ops builder.instruction.State builder.instruction.Terminal
  dropRemaining : Callback.Run builder.instruction.State RemainingResource Unit Empty
    builder.instruction.Terminal
  currentSeeds : builder.instruction.State → SeedRef → Option (List (List Solanalib.Runtime.Bytes))
  errors : AnchorErrorOperations.Ops builder.instruction.State
    (binding.release.ProgramError StringResource) StringResource BoxResource
      builder.instruction.Terminal
  invoke : Option SeedRef → CpiRequest.Invocation builder.instruction.State AccountInfo.Value
    (binding.release.ProgramError StringResource) builder.instruction.Unwind
      builder.instruction.Terminal
  getReturnData : Callback.Run builder.instruction.State Unit
    (Option (Solanalib.Runtime.Pubkey × builder.instruction.ByteResource))
    builder.instruction.Unwind builder.instruction.Terminal

abbrev Input {binding : Binding} (types : Types binding) :=
  Args binding types.RemainingResource types.SeedRef

abbrev Error {binding : Binding} (types : Types binding) :=
  AnchorErrorOperations.Error binding.release.storage
    (binding.release.ProgramError types.StringResource) types.StringResource types.BoxResource

abbrev InstructionOwner {binding : Binding} (types : Types binding) :=
  Token.InstructionAllocated.Value types.builder.instruction

abbrev Exit {binding : Binding} (types : Types binding) :=
  Outcome types.builder.instruction.State (Except (Error types) Return)
    types.builder.instruction.Unwind types.builder.instruction.Terminal

def dropInfo {binding : Binding} (types : Types binding) (info : AccountInfo.Value) :
    Owned.DropAction types.builder.instruction.State types.builder.instruction.Unwind
      types.builder.instruction.Terminal :=
  fun state => AccountInfoRc.lift (AccountInfoRc.dropCall types.rc) state info

def infoDrops {binding : Binding} (types : Types binding) (accounts : List AccountInfo.Value) :=
  accounts.map (dropInfo types)

/-- CpiContext field destruction is accounts, remaining_accounts, program.
Modern copied program IDs and borrowed signer slices have no owned drop. -/
def contextDrops {binding : Binding} (types : Types binding) (args : Input types)
    (accounts : List AccountInfo.Value) :
    List (Owned.DropAction types.builder.instruction.State types.builder.instruction.Unwind
      types.builder.instruction.Terminal) :=
  infoDrops types accounts ++
    [fun state => AccountInfoRc.lift types.dropRemaining state args.context.remainingAccounts] ++
    infoDrops types (binding.release.programOwners args.context.program)

def fullContextDrops {binding : Binding} (types : Types binding) (args : Input types) :=
  contextDrops types args (allAccounts args)

def remainingContextDrops {binding : Binding} (types : Types binding) (args : Input types) :=
  contextDrops types args (retainedAccounts args)

/-- Clone each array operand in evaluation order. Rc cloning can terminate,
but has no unwind; every normal clone retains the original AccountInfo value. -/
def cloneAccounts {State Terminal : Type} (rc : AccountInfoRc.Ops State Terminal) :
    List AccountInfo.Value → Callback.Run State Unit (List AccountInfo.Value) Empty Terminal
  | [] => fun before _ final => final = .returned [] before
  | info :: rest => Callback.bind (fun state (_ : Unit) => AccountInfoRc.cloneCall rc state info)
      fun copied after => Callback.map (List.cons copied) (cloneAccounts rc rest) after ()

/-- Moving fields introduces no primitive call. The clone profile retains each
actual Rc effect and returns the array produced by those calls. -/
def prepareAccounts {binding : Binding} (types : Types binding) (args : Input types) :
    Callback.Run types.builder.instruction.State Unit (List AccountInfo.Value)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  if binding.release.clones then
    AccountInfoRc.lift (cloneAccounts types.rc (invocationAccounts args))
  else fun before _ final => final = .returned (invocationAccounts args) before

/-- Neither account movement nor cloning deduplicates aliased owners. -/
theorem cloneAccounts_identity {State Terminal : Type} (rc : AccountInfoRc.Ops State Terminal)
    (accounts : List AccountInfo.Value) (before after : State) (copied : List AccountInfo.Value)
    (execution : cloneAccounts rc accounts before () (.returned copied after)) : copied = accounts
      := by
  induction accounts generalizing before copied with
  | nil => cases execution; rfl
  | cons info rest induction =>
    obtain ⟨first, cloned, next⟩ := execution
    cases first with
    | unwound impossible _ => nomatch impossible
    | terminated reason => cases next
    | returned value middle =>
      have identity := AccountInfoRc.clone_identity rc cloned
      obtain ⟨tail, remaining, returned⟩ := next
      cases tail with
      | unwound impossible _ => nomatch impossible
      | terminated reason => cases returned
      | returned values state =>
        cases returned
        rw [identity, induction middle values remaining]

/-- The seed reference identity is passed only to signed invocation. -/
def seedReference {binding : Binding} {Remaining SeedRef : Type}
    (args : Args binding Remaining SeedRef) : Option SeedRef :=
  if binding.operation.signed then some args.context.signerSeeds else none

/-- Current instruction vectors are read at the invocation point, after any
Rc clones. Unsigned helpers do not require a seed observation. -/
def request {binding : Binding} (types : Types binding)
    (before : types.builder.instruction.State) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) :
    Option (CpiRequest.Request AccountInfo.Value) := do
  let value ← Token.InstructionAllocated.observe types.builder.instruction before instruction
  let seeds ← if binding.operation.signed then types.currentSeeds before args.context.signerSeeds
    else some []
  return ⟨value, accounts, seeds⟩

/-- The exact local input domain; no AccountInfo.Valid, global heap validity,
allocation success or callback termination is bundled into it. -/
def RequestReadable {binding : Binding} (types : Types binding)
    (before : types.builder.instruction.State) (args : Input types)
    (instruction : InstructionOwner types) : Prop :=
  types.builder.instruction.metas.Live before instruction.metas ∧
  types.builder.instruction.bytes.Live before instruction.data ∧
  (binding.operation.signed = true → ∃ seeds, types.currentSeeds before args.context.signerSeeds =
    some seeds)

theorem request_hasResult_iff {binding : Binding} (types : Types binding)
    (before : types.builder.instruction.State) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) :
    (∃ call, request types before args instruction accounts = some call) ↔
      RequestReadable types before args instruction := by
  unfold request RequestReadable Token.InstructionAllocated.observe Instruction.OwnedValue.observe
    Owned.VectorOps.Live
  cases signed : binding.operation.signed <;>
    cases metas : types.builder.instruction.metas.current before instruction.metas <;>
    cases bytes : types.builder.instruction.bytes.current before instruction.data <;>
    cases seeds : types.currentSeeds before args.context.signerSeeds <;> simp

/-- Fixed ProgramError conversion preserves the complete selected dependency
value, including an old owned Borsh String. -/
def convert {binding : Binding} (types : Types binding) :
    Callback.Run types.builder.instruction.State (binding.release.ProgramError types.StringResource)
      (Error types) types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  AccountInfoRc.lift (AnchorErrorOperations.fromProgram binding.release.storage types.errors)

/-- The shared constructors can return IncorrectProgramId, and pointer field
conversion can additionally return InvalidArgument. No invocation status is
projected through this constructor-only translation. -/
def builderFailure {binding : Binding} (types : Types binding) (error : Token.Error) :
    binding.release.ProgramError types.StringResource :=
  match error with
  | .IncorrectProgramId => binding.release.incorrectProgramId types.StringResource
  | _ => binding.release.invalidArgument types.StringResource

end Solanalib.Specs.Core.AnchorSplTokenOperations
