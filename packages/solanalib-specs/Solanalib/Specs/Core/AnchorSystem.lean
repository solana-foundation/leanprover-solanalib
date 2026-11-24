/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.CpiRequest
public import Solanalib.Specs.Core.InstructionBuilder
public import Solanalib.Specs.Core.InstructionSystemCreateAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSystem

/-- The four fixed System instruction wrappers. Their account field order is
part of the operation, rather than a caller-supplied list or permutation. -/
inductive Operation where
  /-- Resize the one supplied the data allocation of the account through System CPI. -/
  | allocate
  /-- Assign the one supplied account to the requested owner. -/
  | assign
  /-- Create the second account using lamports from the first account. -/
  | createAccount
  /-- Transfer lamports from the first account to the second account. -/
  | transfer
  deriving DecidableEq, Repr

/-- Older Anchor contexts own a program AccountInfo; newer contexts carry its
public key by value. Neither field is an operand of these four invocations. -/
inductive ContextKind where
  /-- A moved AccountInfo whose two Rc fields require cleanup. -/
  | programAccount
  /-- A copied public key with no owned destructor. -/
  | programId
  deriving DecidableEq, Repr

/-- The exact owned/copyable program field of the selected context version. -/
def ContextKind.Program : ContextKind → Type
  | .programAccount => AccountInfo.Value
  | .programId => _root_.Solanalib.Runtime.Pubkey

/-- System enum values supplied to bincode. Bounded source integers avoid
inventing overflow behavior for these copy-only instruction fields. -/
inductive Data where
  /-- the copied space field of Allocate, encoded after enum tag 8. -/
  | allocate (space : UInt64)
  /-- the copied owner key of Assign, encoded after enum tag 1. -/
  | assign (owner : _root_.Solanalib.Runtime.Pubkey)
  /-- the lamports, space and owner of CreateAccount, encoded after enum tag 0. -/
  | createAccount (lamports space : UInt64) (owner : _root_.Solanalib.Runtime.Pubkey)
  /-- the copied lamports field of Transfer, encoded after enum tag 2. -/
  | transfer (lamports : UInt64)
  deriving DecidableEq, Repr

/-- The bincode 1.3.3 encoding used by every reviewed constructor: a u32 enum
tag, then fields in declaration order, with little-endian u64 integers. -/
def Data.bytes : Data → _root_.Solanalib.Runtime.Bytes
  | .allocate space => Instruction.systemAmountData 8 space.toNat
  | .assign owner => _root_.Solanalib.Runtime.u32le 1 ++ owner.bytes
  | .createAccount lamports space owner =>
    _root_.Solanalib.Runtime.u32le 0 ++ _root_.Solanalib.Runtime.u64le lamports.toNat ++
      _root_.Solanalib.Runtime.u64le space.toNat ++ owner.bytes
  | .transfer lamports => Instruction.systemAmountData 2 lamports.toNat

/-- A one-field wrapper or a from/to pair, following the Rust account structs. -/
def Operation.Accounts : Operation → Type
  | .allocate | .assign => AccountInfo.Value
  | .createAccount | .transfer => AccountInfo.Value × AccountInfo.Value

/-- The additional source arguments of a particular public wrapper. -/
def Operation.Parameters : Operation → Type
  | .allocate | .transfer => UInt64
  | .assign => _root_.Solanalib.Runtime.Pubkey
  | .createAccount => UInt64 × UInt64 × _root_.Solanalib.Runtime.Pubkey

/-- Primitive resource and exit types. No source layout or allocator success
is assumed by this mathematical carrier. -/
structure Types where
  /-- The single state shared by construction, invocation and every cleanup. -/
  State : Type
  /-- An owner of the ordered instruction-meta vector of the constructor. -/
  MetaResource : Type
  /-- An owner of the serialized instruction bytes of the constructor. -/
  ByteResource : Type
  /-- An owner of the remaining-account vector of the context. -/
  RemainingResource : Type
  /-- A serializer error consumed by the unwrap provider of the constructor. -/
  SerializeError : Type
  /-- A finite unwind reason carried together with its actual state. -/
  Unwind : Type
  /-- A terminal reason with no subsequent state or cleanup continuation. -/
  Terminal : Type

/-- The existing generic instruction constructor at the actual System enum. -/
abbrev Types.builder (types : Types) : InstructionBuilder.Types :=
  ⟨types.State, Data, types.MetaResource, types.ByteResource,
    types.SerializeError, types.Unwind, types.Terminal⟩

/-- Fixed vector/serializer/unwrap and Rc dependencies. The remaining-vector
drop owns element destruction and storage retirement; the wrapper must not
add a second element-drop pass. Each operation receives its actual state. -/
structure Resources where
  /-- Resource identities and exit types for this dependency assignment. -/
  types : Types
  /-- Ordered vector construction, serialization, unwrap and destruction. -/
  builder : InstructionBuilder.Providers types.builder
  /-- The current contents and element/storage destruction of the context vector. -/
  remaining : Owned.VectorOps types.State AccountInfo.Value types.RemainingResource
    types.Unwind types.Terminal
  /-- The two AccountInfo Rc-field primitives, applied in source order. -/
  rc : AccountInfoRc.Ops types.State types.Terminal

/-- The moved context and separately supplied instruction arguments. The
remaining vector is retained for cleanup, not forwarded to CPI. -/
structure Args (resources : Resources) (kind : ContextKind) (operation : Operation) where
  /-- The one account of the operation or ordered from/to pair, moved without Clone. -/
  accounts : operation.Accounts
  /-- The current remaining-account vector owner, retained for cleanup. -/
  remaining : resources.types.RemainingResource
  /-- The owned program account of the selected context version or copied key. -/
  program : kind.Program
  /-- The borrowed nested seed values, preserving empty slices and duplicates. -/
  signerSeeds : List (List _root_.Solanalib.Runtime.Bytes)
  /-- The copied numeric and key arguments supplied after the context. -/
  parameters : operation.Parameters

/-- Actual account values moved into the temporary array of the invocation. Repeated
aliases are retained as separate owned occurrences. No Clone callback runs. -/
def movedAccounts {resources : Resources} {kind : ContextKind}
    {operation : Operation} (args : Args resources kind operation) : List AccountInfo.Value :=
  match operation, args.accounts with
  | .allocate, account | .assign, account => [account]
  | .createAccount, (source, target) | .transfer, (source, target) => [source, target]

/-- The exact source enum constructed before the account fields are moved. -/
def data {resources : Resources} {kind : ContextKind}
    {operation : Operation} (args : Args resources kind operation) : Data :=
  match operation, args.parameters with
  | .allocate, space => .allocate space
  | .assign, owner => .assign owner
  | .createAccount, (lamports, space, owner) => .createAccount lamports space owner
  | .transfer, lamports => .transfer lamports

/-- Metas preserve constructor order and flags, independently of the input
AccountInfo flags. The destination of a transfer is not a signer; the CreateAccount destination is.
-/
def metas {resources : Resources} {kind : ContextKind}
    {operation : Operation} (args : Args resources kind operation) : List Instruction.Meta :=
  match operation, args.accounts with
  | .allocate, account | .assign, account => [Instruction.accountMeta account.key true true]
  | .createAccount, (source, target) =>
    [Instruction.accountMeta source.key true true, Instruction.accountMeta target.key true true]
  | .transfer, (source, target) =>
    [Instruction.accountMeta source.key true true, Instruction.accountMeta target.key false true]

/-- The mathematical value established when the vector and codec dependencies
return their specified contents. It does not replace current resource reads. -/
def instruction {resources : Resources} {kind : ContextKind}
    {operation : Operation} (args : Args resources kind operation) : Instruction.Value :=
  Instruction.make Instruction.systemProgramId (metas args) (data args).bytes

/-- Allocate the ordered meta vector before serializing the System enum. The
four selected source constructors all use bincode, without program-ID checks. -/
def allocation {resources : Resources} {kind : ContextKind}
    {operation : Operation} (args : Args resources kind operation) :
    InstructionBuilder.AllocateArgs resources.types.builder where
  programId := Instruction.systemProgramId
  data := data args
  accounts := metas args
  providers := resources.builder

/-- Construct through the existing explicit dependency protocol. Serialization
failure reaches the actual unwind/terminal exit and meta-vector cleanup of the unwrap. -/
def build {resources : Resources} {kind : ContextKind} {operation : Operation}
    (before : resources.types.State) (args : Args resources kind operation) :=
  InstructionBuilder.allocateRun resources.types.builder .bincode before (allocation args)

/-- Observe instruction resources at the actual constructor return, retaining
all account identities, nested seed order and repeated occurrences. -/
def request {resources : Resources} {kind : ContextKind} {operation : Operation}
    (state : resources.types.State) (args : Args resources kind operation)
    (value : InstructionBuilder.Value resources.types.builder) :
    Option (CpiRequest.Request AccountInfo.Value) :=
  (InstructionBuilder.observe resources.types.builder resources.builder state value).map
    (fun current => ⟨current, movedAccounts args, args.signerSeeds⟩)

/-- Readability is required only at actual successful constructor returns. It
asserts neither a dependency execution nor source ownership/layout validity. -/
def BuildReady {resources : Resources} {kind : ContextKind} {operation : Operation}
    (before : resources.types.State) (args : Args resources kind operation) : Prop :=
  ∀ value after, build before args (.returned value after) →
    resources.builder.metaVec.Live after value.metas ∧
      resources.builder.byteVec.Live after value.data

/-- One moved AccountInfo owner destroys lamports Rc before data Rc. -/
def dropInfo (resources : Resources) (info : AccountInfo.Value) :
    Owned.DropAction resources.types.State resources.types.Unwind resources.types.Terminal :=
  fun state => AccountInfoRc.lift (AccountInfoRc.dropCall resources.rc) state info

/-- The partially moved context drops the remaining vector, then the older
owned program account. A copied modern program ID has no destructor. -/
def contextTailDrops {resources : Resources} {kind : ContextKind} {operation : Operation}
    (args : Args resources kind operation) :
    List (Owned.DropAction resources.types.State resources.types.Unwind resources.types.Terminal) :=
  [resources.remaining.dropAction args.remaining] ++
    match kind, args.program with
    | .programAccount, program => [dropInfo resources program]
    | .programId, _ => []

/-- Before construction returns, every context account remains in its original
owner. An unwind releases fields in context declaration order. -/
def contextDrops {resources : Resources} {kind : ContextKind} {operation : Operation}
    (args : Args resources kind operation) :
    List (Owned.DropAction resources.types.State resources.types.Unwind resources.types.Terminal) :=
  (movedAccounts args).map (dropInfo resources) ++ contextTailDrops args

/-- All reviewed wrappers use edition 2021. The tail-expression array outlives
the local instruction: metadata, data, moved array elements, then the context
remainder are destroyed. The same order applies to an ordinary returned Err. -/
def invocationDrops {resources : Resources} {kind : ContextKind} {operation : Operation}
    (args : Args resources kind operation)
    (value : InstructionBuilder.Value resources.types.builder) :
    List (Owned.DropAction resources.types.State resources.types.Unwind resources.types.Terminal) :=
  [resources.builder.metaVec.dropAction value.metas,
    resources.builder.byteVec.dropAction value.data] ++
    (movedAccounts args).map (dropInfo resources) ++ contextTailDrops args

/-- Actual vector observations establish the complete provider request. Neither
the context program field nor its remaining vector contributes to it. -/
theorem request_of_current {resources : Resources} {kind : ContextKind}
    {operation : Operation} (state : resources.types.State) (args : Args resources kind operation)
    (value : InstructionBuilder.Value resources.types.builder)
    (accounts : List Instruction.Meta) (bytes : _root_.Solanalib.Runtime.Bytes)
    (hm : resources.builder.metaVec.current state value.metas = some accounts)
    (hd : resources.builder.byteVec.current state value.data = some bytes) :
    request state args value = some
      ⟨Instruction.make value.programId accounts bytes, movedAccounts args, args.signerSeeds⟩ := by
  rw [request, InstructionBuilder.observe_of_current _ _ _ _ _ _ hm hd]
  rfl

/-- The source-selected codec/vector result gives the exact fixed System
request; this is independent of opaque provider success or account effects. -/
theorem request_of_encoded {resources : Resources} {kind : ContextKind}
    {operation : Operation} (state : resources.types.State) (args : Args resources kind operation)
    (value : InstructionBuilder.Value resources.types.builder)
    (pid : value.programId = Instruction.systemProgramId)
    (hm : resources.builder.metaVec.current state value.metas = some (metas args))
    (hd : resources.builder.byteVec.current state value.data = some (data args).bytes) :
    request state args value = some ⟨instruction args, movedAccounts args, args.signerSeeds⟩ := by
  rw [request_of_current state args value _ _ hm hd, pid]
  rfl

/-- Readability at a reached constructor return is enough to form the actual
request, with no invented source error for missing abstract resources. -/
theorem BuildReady.request {resources : Resources} {kind : ContextKind}
    {operation : Operation} {before : resources.types.State} {args : Args resources kind operation}
    (ready : BuildReady before args) {value : InstructionBuilder.Value resources.types.builder}
    {after : resources.types.State} (built : build before args (.returned value after)) :
    ∃ current, request after args value = some current := by
  obtain ⟨⟨accounts, hm⟩, ⟨bytes, hd⟩⟩ := ready value after built
  exact ⟨_, request_of_current after args value accounts bytes hm hd⟩

end Solanalib.Specs.Core.AnchorSystem
