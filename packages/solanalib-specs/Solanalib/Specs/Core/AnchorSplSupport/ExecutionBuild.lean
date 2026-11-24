/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.ExecutionTypes

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport.Execution

variable {types : Types} (fn : Functions types)

def pushMetasFn (destination : types.resources.MetaResource) :
    List Instruction.Meta → types.resources.State → Option (Out types Unit)
  | [], before => some (.returned () before)
  | value :: rest, before => (fn.primitive .metaPush before (destination, value)).bind
      (PGraph.bindK fun _ after => pushMetasFn destination rest after)

theorem pushMetas_graph (graphs : Graph fn) (destination : types.resources.MetaResource) :
    ∀ values before, PGraph (pushMetas types.resources destination values before ())
      (pushMetasFn fn destination values before)
  | [], _ => PGraph.eq_left _
  | value :: rest, before => PGraph.bind (graphs.primitive .metaPush before (destination, value))
      fun _ after => pushMetas_graph graphs destination rest after

def buildVectorsFn (instruction : Instruction.Value) (before : types.resources.State) :
    Option (Out types (Built types.resources)) :=
  (fn.primitive .metaList before instruction.metas).bind (PGraph.bindK fun metas after =>
    ((fn.primitive .byteList after instruction.data).map (Outcome.map fun data =>
      (⟨⟨instruction.programId, metas, data⟩, instruction⟩ : Built types.resources))).bind
        (PGraph.onUnwindFn fn.double (returnDrops fn [.metas metas])))

theorem buildVectors_graph (graphs : Graph fn) (instruction : Instruction.Value) (before :
  types.resources.State) :
    PGraph (buildVectors types.resources instruction before ()) (buildVectorsFn fn instruction
      before) :=
  PGraph.bind (graphs.primitive .metaList before instruction.metas) fun metas after =>
    PGraph.protect graphs.double (returnDrops_graph fn graphs [.metas metas])
      (PGraph.map _ (graphs.primitive .byteList after instruction.data))

def buildAssociatedFn (profile : Profile) (kind : CreateKind) (keys : AssociatedKeys)
    (before : types.resources.State) : Option (Out types (Built types.resources)) :=
  (fn.primitive (.find profile) before (associatedSeeds keys)).bind
    (PGraph.bindK fun address after => buildVectorsFn fn (associatedInstruction kind keys
      address.1) after)

theorem buildAssociated_graph (graphs : Graph fn) (profile : Profile) (kind : CreateKind)
    (keys : AssociatedKeys) (before : types.resources.State) :
    PGraph (buildAssociated types.resources profile kind keys before ())
      (buildAssociatedFn fn profile kind keys before) :=
  PGraph.bind (graphs.primitive (.find profile) before (associatedSeeds keys))
    fun address after => buildVectors_graph fn graphs (associatedInstruction kind keys address.1)
      after

def buildMemoFn (remaining : types.resources.InfoResource) (memo : Solanalib.Runtime.Bytes)
    (before : types.resources.State) : Option (Out types (Built types.resources)) :=
  (types.resources.infos.current before remaining).bind fun infos =>
    (fn.primitive .keyList before (infos.map AccountInfo.Value.key)).bind (PGraph.bindK fun keys
      after =>
      ((types.resources.keys.current after keys).bind fun values =>
        buildVectorsFn fn (memoInstruction memo values) after).bind
          (PGraph.cleanupFn fn.double [fun state => fn.primitive .keyDrop state keys]))

theorem buildMemo_graph (graphs : Graph fn) (remaining : types.resources.InfoResource)
    (memo : Solanalib.Runtime.Bytes) (before : types.resources.State) :
    PGraph (buildMemo types.resources remaining memo before ()) (buildMemoFn fn remaining memo
      before) := by
  unfold buildMemo buildMemoFn
  cases current : types.resources.infos.current before remaining with
  | none => exact PGraph.false
  | some infos =>
    apply PGraph.bind (graphs.primitive .keyList before (infos.map AccountInfo.Value.key))
    intro keys after
    apply PGraph.scope graphs.double
      (PGraph.DropsGraph.cons (fun state => graphs.primitive .keyDrop state keys)
        PGraph.DropsGraph.nil)
    cases types.resources.keys.current after keys with
    | none => exact PGraph.false
    | some values => exact buildVectors_graph fn graphs (memoInstruction memo values) after

def buildStakeFn (metas : List Instruction.Meta) (custodian : Option Instruction.Meta)
    (data : Serialization) (planned : Instruction.Value) (before : types.resources.State) :
    Option (Out types (Built types.resources)) :=
  (fn.primitive .metaList before metas).bind (PGraph.bindK fun resource after =>
    ((pushMetasFn fn resource custodian.toList after).bind (PGraph.bindK fun _ middle =>
      (fn.primitive .serialize middle data).map (Outcome.map fun bytes =>
        (⟨⟨Solanalib.Runtime.Ids.stakeProgram, resource, bytes⟩, planned⟩ : Built
          types.resources)))).bind
          (PGraph.onUnwindFn fn.double (returnDrops fn [.metas resource])))

theorem buildStake_graph (graphs : Graph fn) (metas : List Instruction.Meta) (custodian : Option
  Instruction.Meta)
    (data : Serialization) (planned : Instruction.Value) (before : types.resources.State) :
    PGraph (buildStake types.resources metas custodian data planned before ())
      (buildStakeFn fn metas custodian data planned before) :=
  PGraph.bind (graphs.primitive .metaList before metas) fun resource after =>
    PGraph.protect graphs.double (returnDrops_graph fn graphs [.metas resource])
      (PGraph.bind (pushMetas_graph fn graphs resource custodian.toList after) fun _ middle =>
        PGraph.map _ (graphs.primitive .serialize middle data))

def metadataPrefixFn (keys : Metadata.Keys) (signer : Bool) (before : types.resources.State) :
    Option (Out types (types.resources.MetaResource × types.resources.ByteResource)) :=
  (fn.primitive .metaCapacity before 7).bind (PGraph.bindK fun metas after =>
    ((pushMetasFn fn metas (Metadata.metas keys signer) after).bind (PGraph.bindK fun _ pushed =>
      (fn.primitive .metaExtend pushed (metas, [])).bind (PGraph.bindK fun _ extended =>
        (fn.primitive .serialize extended .metadataDiscriminator).map (Outcome.map fun data =>
          (metas, data))))).bind
          (PGraph.onUnwindFn fn.double (returnDrops fn [.metas metas])))

theorem metadataPrefix_graph (graphs : Graph fn) (keys : Metadata.Keys) (signer : Bool)
    (before : types.resources.State) : PGraph (metadataPrefix types.resources keys signer before ())
      (metadataPrefixFn fn keys signer before) :=
  PGraph.bind (graphs.primitive .metaCapacity before 7) fun metas after =>
    PGraph.protect graphs.double (returnDrops_graph fn graphs [.metas metas])
      (PGraph.bind (pushMetas_graph fn graphs metas (Metadata.metas keys signer) after) fun _
        pushed =>
        PGraph.bind (graphs.primitive .metaExtend pushed (metas, [])) fun _ extended =>
          PGraph.map _ (graphs.primitive .serialize extended .metadataDiscriminator))

def metadataTailFn (keys : Metadata.Keys) (args : MetadataArgs types.resources)
    (metas : types.resources.MetaResource) (data : types.resources.ByteResource)
    (before : types.resources.State) : Option (Out types (Built types.resources)) :=
  ((args.data.current before).bind fun value =>
    (fn.primitive .serialize before (.metadataArguments value args.isMutable args.details)).bind
      (PGraph.bindK fun argumentBytes serialized =>
        ((fn.primitive .appendBytes serialized (data, argumentBytes)).map (Outcome.map fun _ =>
          (⟨⟨Metadata.programId, metas, data⟩,
            Metadata.instruction keys value args.isMutable args.updateAuthoritySigner args.details⟩
              : Built types.resources))).bind
          (PGraph.cleanupFn fn.double (returnDrops fn [.bytes argumentBytes])))).bind
            (PGraph.onUnwindFn fn.double (returnDrops fn [.bytes data, .metas metas]))

theorem metadataTail_graph (graphs : Graph fn) (keys : Metadata.Keys) (args : MetadataArgs
  types.resources)
    (metas : types.resources.MetaResource) (data : types.resources.ByteResource) (before :
      types.resources.State) :
    PGraph (metadataTail types.resources keys args metas data before ())
      (metadataTailFn fn keys args metas data before) := by
  apply PGraph.protect graphs.double (returnDrops_graph fn graphs [.bytes data, .metas metas])
  cases args.data.current before with
  | none => exact PGraph.false
  | some value =>
    exact PGraph.bind (graphs.primitive .serialize before (.metadataArguments value args.isMutable
      args.details))
      fun argumentBytes serialized => PGraph.scope graphs.double
        (returnDrops_graph fn graphs [.bytes argumentBytes])
        (PGraph.map _ (graphs.primitive .appendBytes serialized (data, argumentBytes)))

def buildMetadataFn (keys : Metadata.Keys) (args : MetadataArgs types.resources) (before :
  types.resources.State) :
    Option (Out types (Built types.resources)) :=
  ((metadataPrefixFn fn keys args.updateAuthoritySigner before).bind
    (PGraph.bindK fun allocated after => metadataTailFn fn keys args allocated.1 allocated.2
      after)).bind
      (PGraph.cleanupFn fn.double (metadataDrops fn args.data))

theorem buildMetadata_graph (graphs : Graph fn) (keys : Metadata.Keys) (args : MetadataArgs
  types.resources)
    (before : types.resources.State) : PGraph (buildMetadata types.resources keys args before ())
      (buildMetadataFn fn keys args before) :=
  PGraph.scope graphs.double (metadataDrops_graph fn graphs args.data)
    (PGraph.bind (metadataPrefix_graph fn graphs keys args.updateAuthoritySigner before)
      fun allocated after => metadataTail_graph fn graphs keys args allocated.1 allocated.2 after)

def accountFieldsFn (destination : types.resources.InfoResource) :
    List AccountInfo.Value → types.resources.State → Option (Out types Unit)
  | [], before => some (.returned () before)
  | value :: rest, before => (fn.primitive .singleton before value).bind (PGraph.bindK fun
    singleton after =>
      (fn.primitive .extendInfos after (destination, singleton)).bind
        (PGraph.bindK fun _ middle => accountFieldsFn destination rest middle))

theorem accountFields_graph (graphs : Graph fn) (destination : types.resources.InfoResource) :
    ∀ values before, PGraph (accountFields types.resources destination values before ())
      (accountFieldsFn fn destination values before)
  | [], _ => PGraph.eq_left _
  | value :: rest, before => PGraph.bind (graphs.primitive .singleton before value) fun singleton
    after =>
      PGraph.bind (graphs.primitive .extendInfos after (destination, singleton))
        fun _ middle => accountFields_graph graphs destination rest middle

def metadataFieldsFn (accounts : MetadataAccounts) (before : types.resources.State) :
    Option (Out types types.resources.InfoResource) :=
  let (infos, after) := types.resources.infos.empty before
  ((accountFieldsFn fn infos accounts.owners after).map (Outcome.map fun _ => infos)).bind
    (PGraph.onUnwindFn fn.double (returnDrops fn [.infos infos]))

theorem metadataFields_graph (graphs : Graph fn) (accounts : MetadataAccounts) (before :
  types.resources.State) :
    PGraph (metadataFields types.resources accounts before ()) (metadataFieldsFn fn accounts
      before) :=
  PGraph.protect graphs.double (returnDrops_graph fn graphs [.infos (types.resources.infos.empty
    before).1])
    (PGraph.map _ (accountFields_graph fn graphs _ accounts.owners (types.resources.infos.empty
      before).2))

def metadataInfosTailFn (context : Context types.resources .metadata) (infos :
  types.resources.InfoResource)
    (before : types.resources.State) : Option (Out types types.resources.InfoResource) :=
  ((types.resources.infos.current before context.remainingAccounts).bind fun remaining =>
    (fn.primitive .cloneExtendInfos before (infos, remaining)).bind (PGraph.bindK fun _ extended =>
      (fn.primitive .cloneInfo extended context.program).bind (PGraph.bindK fun program cloned =>
        (fn.primitive .infoPush cloned (infos, program)).map (Outcome.map fun _ => infos)))).bind
          (PGraph.onUnwindFn fn.double (returnDrops fn [.infos infos]))

theorem metadataInfosTail_graph (graphs : Graph fn) (context : Context types.resources .metadata)
    (infos : types.resources.InfoResource) (before : types.resources.State) :
    PGraph (metadataInfosTail types.resources context infos before ())
      (metadataInfosTailFn fn context infos before) := by
  apply PGraph.protect graphs.double (returnDrops_graph fn graphs [.infos infos])
  cases types.resources.infos.current before context.remainingAccounts with
  | none => exact PGraph.false
  | some remaining =>
    exact PGraph.bind (graphs.primitive .cloneExtendInfos before (infos, remaining)) fun _ extended
      =>
      PGraph.bind (graphs.primitive .cloneInfo extended context.program) fun program cloned =>
        PGraph.map _ (graphs.primitive .infoPush cloned (infos, program))

def metadataInfosFn (context : Context types.resources .metadata) (before : types.resources.State) :
    Option (Out types types.resources.InfoResource) :=
  (metadataFieldsFn fn context.accounts before).bind
    (PGraph.bindK fun infos after => metadataInfosTailFn fn context infos after)

theorem metadataInfos_graph (graphs : Graph fn) (context : Context types.resources .metadata)
    (before : types.resources.State) : PGraph (metadataInfos types.resources context before ())
      (metadataInfosFn fn context before) :=
  PGraph.bind (metadataFields_graph fn graphs context.accounts before)
    fun infos after => metadataInfosTail_graph fn graphs context infos after

def buildFn (operation : Operation) (before : types.resources.State) :
    Args types.resources operation → Option (Out types (Built types.resources)) :=
  match operation with
  | .associated profile kind => fun args => buildAssociatedFn fn profile kind
    args.context.accounts.keys before
  | .memo => fun args => buildMemoFn fn args.context.remainingAccounts args.extra before
  | .metadata => fun args => buildMetadataFn fn args.context.accounts.keys args.extra before
  | .deactivate => fun args =>
      let planned := deactivateInstruction args.context.accounts.stake.key
        args.context.accounts.staker.key
      buildStakeFn fn planned.metas none .stakeDeactivate planned before
  | .withdraw => fun args =>
      let accounts := args.context.accounts
      let base := withdrawInstruction accounts.stake.key accounts.withdrawer.key
        accounts.destination.key args.extra.amount none
      buildStakeFn fn base.metas
        (args.extra.custodian.map (fun info => Instruction.accountMeta info.key true false))
        (.stakeWithdraw args.extra.amount)
        (withdrawInstruction accounts.stake.key accounts.withdrawer.key accounts.destination.key
          args.extra.amount (args.extra.custodian.map AccountInfo.Value.key)) before

theorem build_graph (graphs : Graph fn) (operation : Operation) (before : types.resources.State)
    (args : Args types.resources operation) :
    PGraph (build types.resources operation before args) (buildFn fn operation before args) := by
  cases operation with
  | associated profile kind => exact buildAssociated_graph fn graphs profile kind _ before
  | memo => exact buildMemo_graph fn graphs _ _ before
  | metadata => exact buildMetadata_graph fn graphs _ _ before
  | deactivate => exact buildStake_graph fn graphs _ _ _ _ before
  | withdraw => exact buildStake_graph fn graphs _ _ _ _ before

end Solanalib.Specs.Core.AnchorSplSupport.Execution
