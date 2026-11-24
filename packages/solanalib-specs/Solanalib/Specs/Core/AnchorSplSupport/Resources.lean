/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Instructions
public import Solanalib.Specs.Core.AnchorContextOperations
public import Solanalib.Specs.Core.AnchorErrorOperations
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedArray
public import Solanalib.Specs.Core.AddressOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- Only the source distinctions consumed by these wrappers. Exact release,
dependency and target selection is recorded by the separate applicability map. -/
inductive Profile where
  | legacyInline
  | legacyBoxed
  | modern
  deriving DecidableEq, Repr

def Profile.storage : Profile → AnchorErrorOperations.Storage
  | .legacyInline => .inline
  | .legacyBoxed | .modern => .boxed

/-- Old contexts own a program AccountInfo. New contexts copy a public key. -/
def Profile.Program : Profile → Type
  | .legacyInline | .legacyBoxed => AccountInfo.Value
  | .modern => Solanalib.Runtime.Pubkey

def Profile.programOwners : (profile : Profile) → profile.Program → List AccountInfo.Value
  | .legacyInline, program | .legacyBoxed, program => [program]
  | .modern, _ => []

/-- The checked length failure of the serializer. Allocation and panic outcomes
are distinct exits of its supplied dependency, not ordinary Result errors. -/
inductive SerializationError where
  | lengthOverflow
  deriving DecidableEq, Repr

/-- Actual serializer inputs; the discriminator and metadata arguments are
two separate Borsh Vec constructions in the generated metadata helper. -/
inductive Serialization where
  | stakeDeactivate
  | stakeWithdraw (amount : UInt64)
  | metadataDiscriminator
  | metadataArguments (data : Metadata.DataV2) (isMutable : Bool)
      (details : Option Metadata.CollectionDetails)
  deriving DecidableEq, Repr

/-- The selected bincode/Borsh encodings retain every field. A checked
length conversion is never replaced by a truncated successful encoding. -/
def Serialization.encode : Serialization → Except SerializationError Solanalib.Runtime.Bytes
  | .stakeDeactivate => .ok (Solanalib.Runtime.u32le 5)
  | .stakeWithdraw amount => .ok (Solanalib.Runtime.u32le 4 ++ Solanalib.Runtime.u64le amount.toNat)
  | .metadataDiscriminator => .ok [33]
  | .metadataArguments data isMutable details =>
      if data.Encodable then .ok (Metadata.argumentBytes data isMutable details)
      else .error .lengthOverflow

/-- The dependency operations used at the actual allocation, clone,
serialization and destructor sites. They all share one state. Ordinary
ProgramError is generic: old profiles retain an owned Borsh String; new
profiles use the string-free SDK enum. No invocation implementation is here. -/
structure Resources where
  State : Type
  MetaResource : Type
  ByteResource : Type
  InfoResource : Type
  KeyResource : Type
  StringResource : Type
  CreatorResource : Type
  BoxResource : Type
  ProgramError : Type
  Unwind : Type
  Terminal : Type
  metas : Owned.VectorOps State Instruction.Meta MetaResource Unwind Terminal
  bytes : Owned.VectorOps State UInt8 ByteResource Unwind Terminal
  infos : Owned.VectorOps State AccountInfo.Value InfoResource Unwind Terminal
  /-- Vector-literal construction can allocate before evaluating its first
  expression. Evaluated owners are destroyed exactly once on failure. -/
  infoLiteral : Owned.Array.Provider State AccountInfo.Value InfoResource Unwind Terminal
  keys : Owned.VectorOps State Solanalib.Runtime.Pubkey KeyResource Unwind Terminal
  creatorCurrent : State → CreatorResource → Option (List Metadata.Creator)
  creatorDrop : Callback.Run State CreatorResource Unit Empty Terminal
  rc : AccountInfoRc.Ops State Terminal
  errors : AnchorErrorOperations.Ops State ProgramError StringResource BoxResource Terminal
  /-- `Vec<u8>::append`: moves the current bytes and leaves its source empty. -/
  appendBytes : Callback.Run State (ByteResource × ByteResource) Unit Unwind Terminal
  /-- `Vec<AccountInfo>::extend(Vec<AccountInfo>)`: its argument is consumed;
  this dependency owns iterator cleanup, including any unconsumed elements. -/
  extendInfos : Callback.Run State (InfoResource × InfoResource) Unit Unwind Terminal
  /-- The slice-extension dependency clones AccountInfo elements in order,
  using the same Rc interpretation, and owns partial-extension cleanup. -/
  cloneExtendInfos : Callback.Run State (InfoResource × List AccountInfo.Value) Unit Unwind Terminal
  /-- Serialization owns its internal output Vec until its actual Ok return.
  Its Err/unwind exits include the cleanup of that internal Vec. -/
  serialize : Callback.Run State Serialization (Except SerializationError ByteResource)
    Unwind Terminal
  /-- The source `.unwrap()` failure cannot return normally. -/
  unwrapSerialization : Callback.Run State SerializationError Empty Unwind Terminal
  pda : Callback.Run State Address.Syscall.PdaRequest Address.Syscall.PdaReply Unwind Terminal
  /-- Pubkey 2.x starts from an initialized zero address, so even an untouched
  or partially written success has a complete source value. -/
  zeroPda : Callback.Run State Address.Syscall.PdaRequest Address.Operations.ZeroFindReply
    Unwind Terminal
  pdaPanic : Callback.Run State Address.SearchPanic Empty Unwind Terminal
  doubleUnwind : Owned.DoubleUnwind State Unwind Terminal

/-- The older and newer public-key dependencies have distinct syscall output
initialization. This selection changes neither the seeds nor the returned bump. -/
def Resources.find (resources : Resources) (profile : Profile) :
    Callback.Run resources.State Address.Syscall.PdaInputs (Solanalib.Runtime.Pubkey × UInt8)
      resources.Unwind resources.Terminal :=
  match profile with
  | .modern => Address.Syscall.findRun resources.pda resources.pdaPanic
  | .legacyInline | .legacyBoxed => Address.Operations.zeroFindRun {
      State := resources.State, Unwind := resources.Unwind, Terminal := resources.Terminal
      syscall := resources.zeroPda, panic := resources.pdaPanic }

/-- Owned metadata inputs retain the three String identities and optional
creator-vector identity. Scalar options have no hidden allocation. -/
structure MetadataInput (resources : Resources) where
  name : resources.StringResource
  symbol : resources.StringResource
  uri : resources.StringResource
  sellerFeeBasisPoints : UInt16
  creators : Option resources.CreatorResource
  collection : Option Metadata.Collection
  uses : Option Metadata.Uses

/-- Borrow the actual metadata input fields in the current
state of the serializer. A missing resource is not silently replaced by a saved input value. -/
def MetadataInput.current {resources : Resources} (input : MetadataInput resources)
    (state : resources.State) : Option Metadata.DataV2 := do
  let name ← resources.errors.currentString state input.name
  let symbol ← resources.errors.currentString state input.symbol
  let uri ← resources.errors.currentString state input.uri
  let creators ← match input.creators with
    | none => some none
    | some resource => (resources.creatorCurrent state resource).map some
  pure ⟨name, symbol, uri, input.sellerFeeBasisPoints, creators, input.collection, input.uses⟩

/-- Strings and the creator Vec drop in source field order. The scalar
metadata fields have no destructor. These selected destructors cannot unwind. -/
def MetadataInput.drops {resources : Resources} (input : MetadataInput resources) :
    List (Owned.DropAction resources.State resources.Unwind resources.Terminal) :=
  [fun state => AccountInfoRc.lift resources.errors.dropString state input.name,
    fun state => AccountInfoRc.lift resources.errors.dropString state input.symbol,
    fun state => AccountInfoRc.lift resources.errors.dropString state input.uri] ++
    input.creators.toList.map (fun resource state =>
      AccountInfoRc.lift resources.creatorDrop state resource)

/-- The retained source identities and the mathematical wire
value of the constructor. `planned` is ghost information for dependency admission; calls always
read the actual current vectors and never substitute this saved value. -/
structure Built (resources : Resources) extends
    Instruction.OwnedValue resources.MetaResource resources.ByteResource where
  planned : Instruction.Value

def observe (resources : Resources) (state : resources.State) (instruction : Built resources) :
    Option Instruction.Value :=
  instruction.toOwnedValue.observe (resources.metas.current state) (resources.bytes.current state)

/-- Instruction field declaration order is metadata followed by data. -/
def instructionDrops (resources : Resources) (instruction : Built resources) :
    List (Owned.DropAction resources.State resources.Unwind resources.Terminal) :=
  [resources.metas.dropAction instruction.metas, resources.bytes.dropAction instruction.data]

def infoDrop (resources : Resources) (info : AccountInfo.Value) :
    Owned.DropAction resources.State resources.Unwind resources.Terminal :=
  fun state => AccountInfoRc.lift (AccountInfoRc.dropCall resources.rc) state info

/-- Repeated aliases are distinct source owners and are never deduplicated. -/
def infoDrops (resources : Resources) (infos : List AccountInfo.Value) :
    List (Owned.DropAction resources.State resources.Unwind resources.Terminal) :=
  infos.map (infoDrop resources)

/-- Return the actual serializer-owned byte resource, or take the actual
nonreturning unwrap failure. No serializer Err can become a wrapper Ok/Err. -/
def serializeBytes (resources : Resources) :
    Callback.Run resources.State Serialization resources.ByteResource
      resources.Unwind resources.Terminal :=
  fun before input => Callback.bind resources.serialize
    (fun result after final => match result with
      | .ok bytes => final = .returned bytes after
      | .error failure => Callback.map (fun impossible : Empty => nomatch impossible)
          resources.unwrapSerialization after failure final)
    before input

/-- Source-order `push` calls retain the same destination identity. -/
def pushMetas (resources : Resources) (destination : resources.MetaResource) :
    List Instruction.Meta → Callback.Run resources.State Unit Unit resources.Unwind
      resources.Terminal
  | [] => fun before _ outcome => outcome = .returned () before
  | value :: rest => fun before _ => Callback.bind resources.metas.push
      (fun _ after => pushMetas resources destination rest after ()) before (destination, value)

/-- An array/collect metadata dependency is evaluated before byte-vector
construction. A failing byte construction drops the same metadata owner. -/
def buildVectors (resources : Resources) (instruction : Instruction.Value) :
    Callback.Run resources.State Unit (Built resources) resources.Unwind resources.Terminal :=
  fun before _ => Callback.bind resources.metas.fromList
    (fun metas after => Owned.protect resources.doubleUnwind [resources.metas.dropAction metas]
      (Callback.map (fun bytes => ⟨⟨instruction.programId, metas, bytes⟩, instruction⟩)
        (fun state (_ : Unit) => resources.bytes.fromList state instruction.data)) after ())
    before instruction.metas

/-- Stake metadata is built before bincode serialization; optional custodian
metadata is a later push, not part of the initial five-element array. -/
def buildStake (resources : Resources) (metas : List Instruction.Meta)
    (custodian : Option Instruction.Meta) (data : Serialization) (planned : Instruction.Value) :
    Callback.Run resources.State Unit (Built resources) resources.Unwind resources.Terminal :=
  fun before _ => Callback.bind resources.metas.fromList
    (fun resource after => Owned.protect resources.doubleUnwind
      [resources.metas.dropAction resource]
      (fun state (_ : Unit) => Callback.bind (pushMetas resources resource custodian.toList)
        (fun _ middle => Callback.map (fun bytes => ⟨⟨Solanalib.Runtime.Ids.stakeProgram, resource,
          bytes⟩, planned⟩)
          (serializeBytes resources) middle data) state ()) after ()) before metas

/-- The selected AccountInfo destructor and double-unwind policy are shared
by ordinary locals and the partially evaluated prefix of the vector literal. -/
def Resources.literalProvider (resources : Resources) :
    Owned.Array.Provider resources.State AccountInfo.Value resources.InfoResource
      resources.Unwind resources.Terminal :=
  { resources.infoLiteral with
    drop := AccountInfoRc.lift (AccountInfoRc.dropCall resources.rc)
    double := resources.doubleUnwind }

/-- One generated AccountInfo field creates a singleton clone Vec. The
literal protocol owns allocation, expression order, and every returned clone
until completion. Its failed construction, not a second outer destructor,
cleans the evaluated prefix. -/
def singletonInfo (resources : Resources) (info : AccountInfo.Value) :
    Callback.Run resources.State Unit resources.InfoResource resources.Unwind resources.Terminal :=
  fun before _ => resources.literalProvider.run 1
    (fun state index => if index = 0 then
      AccountInfoRc.lift (AccountInfoRc.cloneCall resources.rc) state info
      else fun _ => False) before

/-- The derive macro extends an initially empty vector once per field, in
field declaration order. Each consumed singleton keeps its separate identity. -/
def accountFields (resources : Resources) (destination : resources.InfoResource) :
    List AccountInfo.Value → Callback.Run resources.State Unit Unit resources.Unwind
      resources.Terminal
  | [] => fun before _ outcome => outcome = .returned () before
  | field :: rest => fun before _ => Callback.bind (singletonInfo resources field)
      (fun singleton after => Callback.bind resources.extendInfos
        (fun _ middle => accountFields resources destination rest middle ())
        after (destination, singleton)) before ()

end Solanalib.Specs.Core.AnchorSplSupport
