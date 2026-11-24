/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolution
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectProtocol
public import Solanalib.Specs.Core.TokenRequestAllocatedSeeds
public import Solanalib.Specs.Core.TokenRequestAllocatedTlv
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.AddressOperations
public import Solanalib.Specs.Core.OwnedArrayProgress

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.TransferHookResolution

open Token (Error Bytes)
open Token.AllocatedControl

/-- One shared borrow world for every source read and dependency effect. -/
abbrev World (Extra : Type) := AccountInfo.State × Extra

/-- The element of the temporary owning Ref vector of the resolver. -/
abbrev GuardElement := Solanalib.Runtime.Pubkey × DataRef

/-- The primitive work and storage operations of the ordinary array constructor.
The SDK supplies the five expressions, their AccountInfo destructor and the
surrounding double-unwind policy separately. -/
structure LiteralOps (State Resource Unwind Terminal : Type) where
  work : Callback.Run State (Nat × List AccountInfo.Value) Owned.Array.Command Unwind Terminal
  finish : Callback.Run State (List AccountInfo.Value) Resource Unwind Terminal
  cleanupOrder : (state : State) → (values : List AccountInfo.Value) → List (Fin values.length)
  retire : Callback.Run State (List AccountInfo.Value) Unit Unwind Terminal

/-- Only the external storage/work portion of Result collection is supplied.
The model itself fixes callback order, short-circuiting and shared-Ref release. -/
structure CollectionOps (Extra Resource Unwind Terminal : Type) where
  current : World Extra → Resource → Option (List GuardElement)
  internal : Nat → List GuardElement → Owned.DropAction (World Extra) Unwind Terminal
  finish : Callback.Run (World Extra) (List GuardElement) Resource Unwind Terminal
  partialOrder : World Extra → List GuardElement → List GuardElement
  retire : Option Resource → List GuardElement → Owned.DropAction (World Extra) Unwind Terminal

/-- Actual dependency choices for transfer-hook-interface 0.9.0. There is no
invocation dependency: the selected helper only prepares the vectors of its caller.
Vector identities denote ownership, not copies of mutable referents. Primitive
bindings must justify their Rust resource, allocation, clone and frame meaning;
in particular AccountInfo extend clones its slice and drop destroys its owners.
No source/body or allocator correctness is asserted by these parameters. -/
structure Types where
  Extra : Type
  ByteResource : Type
  MetaResource : Type
  InfoResource : Type
  GuardResource : Type
  DiscResource : Type
  SeedResource : Type
  SeedRefResource : Type
  Unwind : Type
  Terminal : Type
  bytes : Owned.VectorOps (World Extra) UInt8 ByteResource Unwind Terminal
  metas : Owned.VectorOps (World Extra) Solanalib.Runtime.CpiMeta MetaResource Unwind Terminal
  infos : Owned.VectorOps (World Extra) AccountInfo.Value InfoResource Unwind Terminal
  literal : LiteralOps (World Extra) InfoResource Unwind Terminal
  collection : CollectionOps Extra GuardResource Unwind Terminal
  discriminators : Owned.VectorOps (World Extra) Bytes DiscResource Unwind Terminal
  seedOps : Token.AllocatedSeeds.Ops (World Extra) ByteResource SeedResource SeedRefResource
    Unwind Terminal
  rc : AccountInfoRc.Ops (World Extra) Terminal
  /-- Pubkey 2.2.1 passes a zeroed output buffer, including on partial writes. -/
  pdaSyscall : Callback.Run (World Extra) Address.Syscall.PdaRequest
    Address.Operations.ZeroFindReply Unwind Terminal
  raise : Callback.Run (World Extra) Panic Empty Unwind Terminal
  doubleUnwind : Owned.DoubleUnwind (World Extra) Unwind Terminal

/-- The caller lends the instruction and AccountInfo vector. The helper owns
the four named standard accounts; additional accounts are a borrowed slice.
`UInt64` is the exact source amount domain, without a spare range assumption. -/
structure Args (types : Types) where
  instruction : Instruction.OwnedValue types.MetaResource types.ByteResource
  infos : types.InfoResource
  programId : Solanalib.Runtime.Pubkey
  source : AccountInfo.Value
  mint : AccountInfo.Value
  destination : AccountInfo.Value
  authority : AccountInfo.Value
  amount : UInt64
  additional : List AccountInfo.Value

/-- An owned temporary Execute instruction and its owned account vector. -/
structure Execute (types : Types) where
  instruction : Instruction.OwnedValue types.MetaResource types.ByteResource
  infos : types.InfoResource

abbrev Run (types : Types) (Value : Type) :=
  Token.AllocatedControl.Run (World types.Extra) Value types.Unwind types.Terminal

/-- The actual pubkey wrapper, shared by validation and seed-derived PDAs.
A nonzero status invokes the ordinary local panic in the after-state of the syscall. -/
def Types.findPda (types : Types) :
    Token.AllocatedSeeds.FindPda (World types.Extra) types.Unwind types.Terminal :=
  Address.Operations.zeroFindRun {
    State := World types.Extra
    Unwind := types.Unwind
    Terminal := types.Terminal
    syscall := types.pdaSyscall
    panic := fun state _ => types.raise state .noViableProgramAddress }

/-- A checked data borrow is an actual shared guard operation. A RefCell
conflict is AccountBorrowFailed; a malformed logical handle is outside the
representation domain, rather than a made-up source error. -/
def borrowData (types : Types) (info : AccountInfo.Value) : Run types DataRef :=
  fun before outcome =>
    let (step, after) := Token.Onchain.borrowData true before.1 info
    match step with
    | .success reference =>
      outcome = .returned (.ok ⟨reference.guard, reference.bytes.length⟩) (after, before.2)
    | .error error => outcome = .returned (.error error) (after, before.2)
    | .panic _ | .malformed => False

/-- The borrowed guard remains live through the body and is released on
ordinary success, ProgramError or unwind. Terminal outcomes bypass cleanup. -/
def withData (types : Types) {Value : Type} (info : AccountInfo.Value)
    (body : DataRef → Run types Value) : Run types Value :=
  bind (borrowData types info) fun reference =>
    scope types.doubleUnwind [reference.drop] (body reference)

/-- Derived AccountInfo Clone retains the same keys, fields and cell aliases. -/
def cloneInfo (types : Types) (info : AccountInfo.Value) : Run types AccountInfo.Value :=
  perform fun before => AccountInfoRc.lift (Unwind := types.Unwind)
    (AccountInfoRc.cloneCall types.rc) before info

/-- Each owned AccountInfo drops lamports Rc before data Rc. -/
def dropInfo (types : Types) (info : AccountInfo.Value) :
    Owned.DropAction (World types.Extra) types.Unwind types.Terminal :=
  fun before => AccountInfoRc.lift (Unwind := types.Unwind)
    (AccountInfoRc.dropCall types.rc) before info

/-- The function arguments that have not moved drop in reverse declaration order. -/
def argumentDrops (types : Types) (args : Args types) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  [dropInfo types args.authority, dropInfo types args.destination,
    dropInfo types args.mint, dropInfo types args.source]

/-- The owned fields of the instruction drop in declaration order. -/
def instructionDrops (types : Types)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  [types.metas.dropAction instruction.metas, types.bytes.dropAction instruction.data]

/-- Construction receives only the source expressions and ordinary destructor. -/
def Types.literalProvider (types : Types) :
    Owned.Array.Provider (World types.Extra) AccountInfo.Value types.InfoResource
      types.Unwind types.Terminal where
  work := types.literal.work
  finish := types.literal.finish
  cleanupOrder := types.literal.cleanupOrder
  drop := fun before info => dropInfo types info before
  retire := types.literal.retire
  double := types.doubleUnwind

/-- The collection protocol fixes the callback/cleanup control flow of the SDK.
Internal std work remains explicit, including failed partial insertion. -/
def Types.collectProtocol (types : Types) :
    Token.AllocatedCollect.Protocol types.Extra types.GuardResource types.Unwind types.Terminal
      where
  internal := types.collection.internal
  finish := types.collection.finish
  partialOrder := types.collection.partialOrder
  retire := types.collection.retire
  double := types.doubleUnwind

/-- Successful collection cleanup uses the same live guard identities as
resolution, then retires only their vector storage. -/
def dropReferences (types : Types) (resource : types.GuardResource) :
    Owned.DropAction (World types.Extra) types.Unwind types.Terminal :=
  fun before outcome => ∃ entries, types.collection.current before resource = some entries ∧
    Owned.cleanup types.doubleUnwind
      (types.collectProtocol.drops (some resource) entries) (.returned () before) outcome

end Solanalib.Specs.Core.TransferHookResolution
