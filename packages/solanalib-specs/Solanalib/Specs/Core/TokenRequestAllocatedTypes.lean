/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedControl
public import Solanalib.Specs.Core.TokenInstructionAllocated
public import Solanalib.Specs.Core.TokenRequestAllocatedSeedsTypes
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.AddressSyscall
public import Solanalib.Specs.Core.OwnedArray

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

/-- The actual borrowed-data world is shared with every allocation, clone,
drop and invocation dependency. Ambient state can carry vector storage,
reference counts and other effects; callbacks do not receive a saved world. -/
abbrev World (Extra : Type) := AccountInfo.State × Extra

/-- A collected element owns one data Ref and a copied account key. Its
vector destructor is responsible for releasing that Ref exactly once. -/
abbrev GuardElement := Solanalib.Runtime.Pubkey × AllocatedControl.DataRef

/-- The explicit dependencies of the ordinary preparation in Token-2022 11.0.0.
Each VectorOps field denotes its actual source call sites. In particular the
3.0.0 zero-padding repeat constructor is separate from instruction packing
and seed literal construction. AccountInfo vector `extend` includes the
selected concrete Clone operations; its destructor includes element drops.
Binding those primitive operations and their frame/lifetime behavior to Rust
is separate from this SDK control-flow model. -/
structure Types where
  /-- Ambient storage and dependency effects alongside the shared borrow world. -/
  Extra : Type
  /-- Stable logical identities for owned byte vectors. -/
  ByteResource : Type
  /-- Stable logical identities for owned metadata vectors. -/
  MetaResource : Type
  /-- Stable logical identities for owned AccountInfo vectors. -/
  InfoResource : Type
  /-- Stable logical identities for vectors owning shared data Refs. -/
  GuardResource : Type
  /-- Stable logical identities for temporary TLV discriminator vectors. -/
  DiscResource : Type
  /-- Stable logical identities for unpacked, potentially owning seed vectors. -/
  SeedResource : Type
  /-- Stable logical identities for borrowed seed-view vectors. -/
  SeedRefResource : Type
  /-- Reasons for finite unwinding exits. -/
  Unwind : Type
  /-- Reasons for finite terminal exits, which expose no post-state. -/
  Terminal : Type
  /-- The selected target usize width. -/
  wordBits : Nat
  /-- The selected interface 3.0.0 TokenInstruction enum size. -/
  tokenEnumSize : Nat
  /-- Actual instruction byte-vector dependency operations. -/
  bytes : Owned.VectorOps (World Extra) UInt8 ByteResource Unwind Terminal
  /-- Actual account-metadata vector dependency operations. -/
  metas : Owned.VectorOps (World Extra) Solanalib.Runtime.CpiMeta MetaResource Unwind Terminal
  /-- Actual AccountInfo vector operations, including moved/clone ownership. -/
  infos : Owned.VectorOps (World Extra) AccountInfo.Value InfoResource Unwind Terminal
  /-- Array-constructor work, completion and temporary storage at the two
  literal-vector sites. `literalProvider` composes the ordinary AccountInfo
  destructor and the shared unwind policy, rather than taking them as opaque. -/
  infoLiteral : Owned.Array.Provider (World Extra) AccountInfo.Value InfoResource Unwind Terminal
  /-- Current collected Ref storage and its element-owning destructor. -/
  guards : Owned.VectorOps (World Extra) GuardElement GuardResource Unwind Terminal
  /-- The temporary discriminator-vector operations of the TLV validator. -/
  discriminators : Owned.VectorOps (World Extra) Bytes DiscResource Unwind Terminal
  /-- The interface 3.0.0 repeated-zero constructor and temporary drop. -/
  paddingBytes : Owned.VectorOps (World Extra) UInt8 ByteResource Unwind Terminal
  /-- The literal, owned-seed and borrowed-seed-view vector dependencies. -/
  seedOps : AllocatedSeeds.Ops (World Extra) ByteResource SeedResource SeedRefResource
    Unwind Terminal
  /-- The concrete AccountInfo Rc clone and drop dependencies. -/
  rc : AccountInfoRc.Ops (World Extra) Terminal
  /-- Current owner values reached through AccountInfo owner-reference identities. -/
  ownerAt : AccountInfo.OwnerAt Extra
  /-- The actual selected-Solana PDA syscall, including metering, returned
  output observations and every finite exit. It is composed with the ordinary
  Address wrapper below; output initialization remains a source binding, and
  a mathematical PDA does not imply success. -/
  pdaSyscall : Callback.Run (World Extra) Address.Syscall.PdaRequest
    Address.Syscall.PdaReply Unwind Terminal
  /-- The local panic behavior of the selected target, with no ordinary return. -/
  raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal
  /-- The explicit terminal policy for a destructor unwinding during unwind. -/
  doubleUnwind : Owned.DoubleUnwind (World Extra) Unwind Terminal
  /-- Interpretation of one ordinary, allocation-free metadata field write.
  The call below separately enforces the exact current sequence update.
  Its representation proof must justify the write and its memory frame; it
  cannot be interpreted as an allocator or an arbitrary SDK function. -/
  writeMeta : World Extra → MetaResource → Nat → Solanalib.Runtime.CpiMeta → World Extra → Prop

/-- Result-aware SDK computations over the selected concrete account world. -/
abbrev Run (types : Types) (Value : Type) :=
  AllocatedControl.Run (World types.Extra) Value types.Unwind types.Terminal

/-- Both PDA call sites admit the representable slices of the selected source and
use the ordinary Address wrapper over the actual syscall. A returned nonzero
status reaches panic in the current state of the syscall; abnormal syscall exits
bypass that panic. The bound is an explicit actual-call representation domain,
not a claim that arbitrary earlier callbacks preserve valid borrowed slices. -/
def Types.findPda (types : Types) :
    AllocatedSeeds.FindPda (World types.Extra) types.Unwind types.Terminal :=
  fun before inputs outcome => inputs.Bounded ∧
    Address.Syscall.findRun types.pdaSyscall
      (fun state _ => types.raise state .noViableProgramAddress) before inputs outcome

/-- The same token pack and metadata-construction engine is used by standalone
constructors and by this caller. No whole builder result is assumed here. -/
def Types.constructor (types : Types) : InstructionAllocated.Types where
  State := World types.Extra
  ByteResource := types.ByteResource
  MetaResource := types.MetaResource
  Unwind := types.Unwind
  Terminal := types.Terminal
  wordBits := types.wordBits
  enumSize := types.tokenEnumSize
  bytes := types.bytes
  metas := types.metas
  doubleUnwind := types.doubleUnwind

/-- The two returned owned values retain the identities created by their
dependencies. Merely copying this record does not create another Rust owner. -/
structure Prepared (types : Types) where
  /-- The owned instruction retaining its metadata and byte resource identities. -/
  instruction : Instruction.OwnedValue types.MetaResource types.ByteResource
  /-- The retained identity of the owned AccountInfo vector. -/
  infos : types.InfoResource

/-- Observe the current owned instruction and account vector immediately at
the call boundary. Missing resources are representation failures. -/
def Prepared.observe (types : Types) (prepared : Prepared types)
    (state : World types.Extra) (signers : List (List Bytes)) :
    Option (CpiRequest.Request AccountInfo.Value) := do
  let instruction ← prepared.instruction.observe (types.metas.current state)
    (types.bytes.current state)
  let accounts ← types.infos.current state prepared.infos
  return ⟨instruction, accounts, signers⟩

/-- Instruction fields drop in declaration order: account metas, then bytes. -/
def instructionDrops (types : Types)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  [types.metas.dropAction instruction.metas, types.bytes.dropAction instruction.data]

/-- The later local account vector drops before the earlier instruction.
Each action receives its actual current resource token and state. -/
def Prepared.drops (types : Types) (prepared : Prepared types) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  types.infos.dropAction prepared.infos :: instructionDrops types prepared.instruction

/-- The concrete AccountInfo clone supplies no unwind path. Its Rc calls may
still terminate and may change the ambient state. -/
def cloneInfo (types : Types) (info : AccountInfo.Value) : Run types AccountInfo.Value :=
  AllocatedControl.perform fun state =>
    AccountInfoRc.lift (Unwind := types.Unwind) (AccountInfoRc.cloneCall types.rc) state info

/-- A single retained AccountInfo owner drops its two Rc fields in source
order. A repeated mathematical AccountInfo value is not a second permission. -/
def dropInfo (types : Types) (info : AccountInfo.Value) :
    Owned.DropAction (World types.Extra) types.Unwind types.Terminal :=
  fun state => AccountInfoRc.lift (Unwind := types.Unwind)
    (AccountInfoRc.dropCall types.rc) state info

/-- Unmoved function arguments drop in reverse declaration order. The caller
switches this list at the actual move into the transfer-hook helper. -/
def argumentDrops (types : Types) (args : Onchain.Args) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  [dropInfo types args.authority, dropInfo types args.destination,
    dropInfo types args.mint, dropInfo types args.source]

/-- The public checked transfer selects fee=None and starts with no multisig
signers. Multisig selection mutates the constructed instruction later. -/
def transferPlan (args : Onchain.Args) : InstructionAllocated.Plan :=
  InstructionAllocated.transferCheckedPlan .either {
    programId := args.tokenProgramId
    source := args.source.key
    mint := args.mint.key
    destination := args.destination.key
    authority := args.authority.key
    signers := []
    amount := args.amount
    decimals := args.decimals }

/-- Current-list metadata mutation at the fixed authority slot of the source. No
Vec allocation, panic callback or ProgramError is introduced by this write.
An absent resource or slot is outside its valid representation domain. -/
def clearAuthoritySigner (types : Types) (resource : types.MetaResource) :
    Run types Unit :=
  fun before outcome => ∃ items item after,
    types.metas.current before resource = some items ∧
    items[3]? = some item ∧
    types.writeMeta before resource 3 { item with signerByte := 0 } after ∧
    types.metas.current after resource = some (items.set 3 { item with signerByte := 0 }) ∧
    outcome = .returned (.ok ()) after

end Solanalib.Specs.Core.Token.OnchainAllocated
