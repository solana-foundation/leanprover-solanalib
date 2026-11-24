/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.MetadataPointer

open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Metadata-pointer initialization arguments, before either optional-key
conversion. `Some zero` is a returned InvalidArgument, not the encoding of None. -/
structure Args where
  /-- The source accepts only the Token-2022 program. -/
  programId : Solanalib.Runtime.Pubkey
  /-- Sole writable nonsigner account. -/
  mint : Solanalib.Runtime.Pubkey
  /-- Optional metadata-pointer update authority. -/
  authority : Option Solanalib.Runtime.Pubkey
  /-- Optional metadata account address. -/
  metadataAddress : Option Solanalib.Runtime.Pubkey
  deriving DecidableEq, Repr

/-- The checked OptionalNonZeroPubkey conversion, in its raw 32-byte layout. -/
def optionalNonzero : Option Solanalib.Runtime.Pubkey → Except Error Bytes
  | none => .ok Solanalib.Runtime.Pubkey.zero.bytes
  | some key => if key = .zero then .error .InvalidArgument else .ok key.bytes

/-- The fields are converted in declaration order. These checks happen only
after the metadata Vec literal has returned. -/
def fields (args : Args) : Except Error Bytes := do
  let authority ← optionalNonzero args.authority
  let metadata ← optionalNonzero args.metadataAddress
  return authority ++ metadata

/-- Literal account metadata; key aliases are not compared or rejected. -/
def metas (args : Args) : List Solanalib.Runtime.CpiMeta :=
  [Solanalib.Specs.Core.Instruction.accountMeta args.mint false true]

/-- Exact `encode_instruction` byte operations: the extension discriminator,
the sub-instruction byte, then the contiguous two-field POD payload. -/
def steps (tag : UInt8) (encoded : Bytes) : List DataStep := [.push tag, .push 0, .extend encoded]

/-- Continue from the actual metadata-allocation return. Invalid field
conversion drops that owner before returning its error. Valid conversion
protects it across byte packing, whose own cleanup runs before metadata cleanup. -/
def afterMetas (tag : UInt8) (types : Types) (args : Args) (resource : types.MetaResource)
    (before : types.State)
    (final : Outcome types.State (Except Error (Value types)) types.Unwind types.Terminal) : Prop :=
  match fields args with
  | .error error => Owned.cleanup types.doubleUnwind
      [types.metas.dropAction resource] (.returned (.error error) before) final
  | .ok encoded => Owned.protect types.doubleUnwind [types.metas.dropAction resource]
      (Callback.map (fun data => Except.ok
        ({ programId := args.programId, metas := resource, data } : Value types))
        (buildData types (steps tag encoded))) before () final

/-- Program check precedes all allocation. Field conversion follows metadata
allocation and retains the actual state of that dependency and every finite exit. -/
def run (tag : UInt8) (types : Types) : Callback.Run types.State Args
    (Except Error (Value types)) types.Unwind types.Terminal :=
  fun before args final =>
    match Instruction.checkProgram .token2022 args.programId with
    | .error error => final = .returned (.error error) before
    | .ok () => Callback.bind (fun state (_ : Unit) => types.metas.fromList state (metas args))
        (afterMetas tag types args) before () final

/-- Full local source model, with the actual vector providers as its index. -/
def family (tag : UInt8) : Family where
  Index := Types
  State := Types.State
  Args := fun _ => Args
  Value := fun types => Except Error (Value types)
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := run tag types }

/-- The reference keeps the checked-field branch and resource lifetimes. -/
def reference (tag : UInt8) : FamilyRun (family tag) := run tag

/-- The relation covers all selected finite dependency exits. -/
theorem reference_holds (tag : UInt8) : FamilyReference (family tag) (reference tag) := fun _ _ _ _
  _ h => h

/-- Source continuation for any actual first-allocation return and local
continuation; no existentially chosen good allocation replaces another exit. -/
theorem from_allocated {tag : UInt8} {types : Types} {args : Args} {before allocated : types.State}
    {resource : types.MetaResource} {final}
    (program : Instruction.checkProgram .token2022 args.programId = .ok ())
    (allocation : types.metas.fromList before (metas args) (.returned resource allocated))
    (continuation : afterMetas tag types args resource allocated final) :
    run tag types before args final := by
  simp only [run, program]
  exact ⟨.returned resource allocated, allocation, continuation⟩

/-- A field-conversion failure follows actual cleanup; a destructor unwind
does not become a normal ProgramError return. -/
theorem invalid_fields {tag : UInt8} {types : Types} {args : Args} {before : types.State}
    {resource : types.MetaResource} {error : Error} {final}
    (invalid : fields args = .error error)
    (cleaned : Owned.cleanup types.doubleUnwind [types.metas.dropAction resource]
      (.returned (.error error) before) final) :
    afterMetas tag types args resource before final := by
  simp only [afterMetas, invalid]
  exact cleaned

/-- Successful mathematical example with two distinct nonzero optional keys. -/
def sampleArgs : Args := ⟨token2022ProgramId, .ofNat 1, some (.ofNat 2), some (.ofNat 3)⟩

/-- The concrete witness uses the existing disjoint byte and metadata ledgers. -/
def sample : (family 39).Index := Witness.sampleTypes

/-- Every successful field conversion executes all three byte operations and
returns both retained owners at the concrete ledger index. -/
theorem sample_returns (tag : UInt8) (args : Args) (encoded : Bytes)
    (program : Instruction.checkProgram .token2022 args.programId = .ok ())
    (valid : fields args = .ok encoded) :
    run tag sample Witness.initialState args
      (.returned (.ok ⟨args.programId, (0 : Nat), (0 : Nat)⟩)
        ([some ((steps tag encoded).flatMap DataStep.bytes)], [some (metas args)])) := by
  apply from_allocated program (Witness.metas_from_list [] [] (metas args))
  simp only [afterMetas, valid]
  exact ⟨_, ⟨.returned (0 : Nat) _, Witness.build_data_returns _ _, rfl⟩, rfl⟩

/-- Closed successful execution, rather than only a satisfiable precondition. -/
theorem has_execution : FamilyHasExecution (family 39) (reference 39) sample := by
  refine ⟨Witness.initialState, sampleArgs, _, trivial, sample_returns 39 sampleArgs
    ((Solanalib.Runtime.Pubkey.ofNat 2).bytes ++ (Solanalib.Runtime.Pubkey.ofNat 3).bytes) rfl ?_⟩
  rfl

/-- Admission is inhabited by the actual successful constructor example. -/
theorem satisfiable : FamilySatisfiable (family 39) sample := has_execution.satisfiable

end Solanalib.Specs.Core.Token.MetadataPointer
