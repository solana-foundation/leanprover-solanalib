/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Continuations
public import Solanalib.Specs.Core.CallbackGraph

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Execution

/-- The computations below are certified interpretations of the existing
relations. They are not additional dependencies or new source assumptions. -/
inductive Primitive (types : Types) : Type → Type → Type 1 where
  | metaCapacity : Primitive types Nat types.resources.MetaResource
  | metaList : Primitive types (List Instruction.Meta) types.resources.MetaResource
  | metaPush : Primitive types (types.resources.MetaResource × Instruction.Meta) Unit
  | metaExtend : Primitive types (types.resources.MetaResource × List Instruction.Meta) Unit
  | metaDrop : Primitive types types.resources.MetaResource Unit
  | byteList : Primitive types Solanalib.Runtime.Bytes types.resources.ByteResource
  | byteDrop : Primitive types types.resources.ByteResource Unit
  | infoPush : Primitive types (types.resources.InfoResource × AccountInfo.Value) Unit
  | infoDrop : Primitive types types.resources.InfoResource Unit
  | keyList : Primitive types (List Solanalib.Runtime.Pubkey) types.resources.KeyResource
  | keyDrop : Primitive types types.resources.KeyResource Unit
  | serialize : Primitive types Serialization types.resources.ByteResource
  | find (profile : Profile) : Primitive types Address.Syscall.PdaInputs (Solanalib.Runtime.Pubkey
    × UInt8)
  | singleton : Primitive types AccountInfo.Value types.resources.InfoResource
  | cloneInfo : Primitive types AccountInfo.Value AccountInfo.Value
  | dropInfo : Primitive types AccountInfo.Value Unit
  | appendBytes : Primitive types (types.resources.ByteResource × types.resources.ByteResource) Unit
  | extendInfos : Primitive types (types.resources.InfoResource × types.resources.InfoResource) Unit
  | cloneExtendInfos : Primitive types (types.resources.InfoResource × List AccountInfo.Value) Unit
  | stringDrop : Primitive types types.resources.StringResource Unit
  | creatorDrop : Primitive types types.resources.CreatorResource Unit
  | convert (profile : Profile) : Primitive types types.resources.ProgramError (Error
    types.resources profile)
  | invoke : Primitive types (CpiRequest.Request AccountInfo.Value) (Except
    types.resources.ProgramError Unit)

def Primitive.run {types : Types} {A V : Type} (primitive : Primitive types A V) :
    Run types.resources A V :=
  match primitive with
  | .metaCapacity => types.resources.metas.withCapacity
  | .metaList => types.resources.metas.fromList
  | .metaPush => types.resources.metas.push
  | .metaExtend => types.resources.metas.extend
  | .metaDrop => types.resources.metas.drop
  | .byteList => types.resources.bytes.fromList
  | .byteDrop => types.resources.bytes.drop
  | .infoPush => types.resources.infos.push
  | .infoDrop => types.resources.infos.drop
  | .keyList => types.resources.keys.fromList
  | .keyDrop => types.resources.keys.drop
  | .serialize => serializeBytes types.resources
  | .find profile => types.resources.find profile
  | .singleton => fun state info => singletonInfo types.resources info state ()
  | .cloneInfo => AccountInfoRc.lift (AccountInfoRc.cloneCall types.resources.rc)
  | .dropInfo => AccountInfoRc.lift (AccountInfoRc.dropCall types.resources.rc)
  | .appendBytes => types.resources.appendBytes
  | .extendInfos => types.resources.extendInfos
  | .cloneExtendInfos => types.resources.cloneExtendInfos
  | .stringDrop => AccountInfoRc.lift types.resources.errors.dropString
  | .creatorDrop => AccountInfoRc.lift types.resources.creatorDrop
  | .convert profile => AccountInfoRc.lift
      (AnchorErrorOperations.fromProgram profile.storage types.resources.errors)
  | .invoke => types.invoke

abbrev Out (types : Types) (V : Type) :=
  Outcome types.resources.State V types.resources.Unwind types.resources.Terminal

structure Functions (types : Types) where
  primitive : {A V : Type} → Primitive types A V → types.resources.State → A → Option (Out types V)
  literal : types.resources.State → WithdrawAccounts → Option
    (Outcome types.resources.State types.resources.InfoResource
      (Owned.Array.Failure × types.resources.Unwind) types.resources.Terminal)
  double : types.resources.State → types.resources.Unwind → types.resources.Unwind → Option
    types.resources.Terminal

structure Graph {types : Types} (fn : Functions types) : Prop where
  primitive : ∀ {A V} (primitive : Primitive types A V) state args,
    PGraph (primitive.run state args) (fn.primitive primitive state args)
  literal : ∀ state accounts,
    PGraph (withdrawLiteral types.resources accounts state) (fn.literal state accounts)
  double : ∀ state first second,
    PGraph (types.resources.doubleUnwind state first second) (fn.double state first second)

variable {types : Types} (fn : Functions types)

def returnDrops (drops : List (ReturnDrop types.resources)) :
    List (types.resources.State → Option (Out types Unit)) :=
  drops.map fun drop state => match drop with
    | .metas resource => fn.primitive .metaDrop state resource
    | .bytes resource => fn.primitive .byteDrop state resource
    | .infos resource => fn.primitive .infoDrop state resource
    | .account info => fn.primitive .dropInfo state info

theorem returnDrops_graph (graphs : Graph fn) (drops : List (ReturnDrop types.resources)) :
    PGraph.DropsGraph (drops.map ReturnDrop.action) (returnDrops fn drops) := by
  induction drops with
  | nil => trivial
  | cons drop rest induction =>
    apply PGraph.DropsGraph.cons _ induction
    intro state
    cases drop with
    | metas resource => exact graphs.primitive .metaDrop state resource
    | bytes resource => exact graphs.primitive .byteDrop state resource
    | infos resource => exact graphs.primitive .infoDrop state resource
    | account info => exact graphs.primitive .dropInfo state info

def instructionDrops (instruction : Built types.resources) : List (ReturnDrop types.resources) :=
  [.metas instruction.metas, .bytes instruction.data]

def tailDrops {operation : Operation} (context : Context types.resources operation) :
    List (ReturnDrop types.resources) :=
  [.infos context.remainingAccounts] ++ (operation.profile.programOwners context.program).map
    .account

def contextDrops {operation : Operation} (context : Context types.resources operation) :
    List (ReturnDrop types.resources) := (operation.owners context.accounts).map .account ++
      tailDrops context

@[simp] theorem instructionDrops_actions (instruction : Built types.resources) :
    (instructionDrops instruction).map ReturnDrop.action =
      AnchorSplSupport.instructionDrops types.resources instruction := rfl

@[simp] theorem tailDrops_actions {operation : Operation} (context : Context types.resources
  operation) :
    (tailDrops context).map ReturnDrop.action = AnchorSplSupport.tailDrops context := by
  simp [tailDrops, AnchorSplSupport.tailDrops, infoDrops, ReturnDrop.action, List.map_map]

@[simp] theorem contextDrops_actions {operation : Operation} (context : Context types.resources
  operation) :
    (contextDrops context).map ReturnDrop.action = AnchorSplSupport.contextDrops context := by
  simp [contextDrops, AnchorSplSupport.contextDrops, infoDrops, ReturnDrop.action, List.map_map]

def metadataDrops (input : MetadataInput types.resources) :
    List (types.resources.State → Option (Out types Unit)) :=
  [fun state => fn.primitive .stringDrop state input.name,
   fun state => fn.primitive .stringDrop state input.symbol,
   fun state => fn.primitive .stringDrop state input.uri] ++
    input.creators.toList.map fun resource state => fn.primitive .creatorDrop state resource

theorem metadataDrops_graph (graphs : Graph fn) (input : MetadataInput types.resources) :
    PGraph.DropsGraph input.drops (metadataDrops fn input) := by
  apply PGraph.DropsGraph.cons (fun state => graphs.primitive .stringDrop state input.name)
  apply PGraph.DropsGraph.cons (fun state => graphs.primitive .stringDrop state input.symbol)
  apply PGraph.DropsGraph.cons (fun state => graphs.primitive .stringDrop state input.uri)
  cases input.creators with
  | none => trivial
  | some resource =>
    exact PGraph.DropsGraph.cons
      (fun state => graphs.primitive .creatorDrop state resource) PGraph.DropsGraph.nil

end Solanalib.Specs.Core.AnchorSplSupport.Execution
