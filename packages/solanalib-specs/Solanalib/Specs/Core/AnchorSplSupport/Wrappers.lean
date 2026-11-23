/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplSupport.Resources
public import Solanalib.Specs.Core.CpiRequest
public import Solanalib.Specs.Core.AddressSyscall
public import Solanalib.Specs.Core.OwnedArrayProgress

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplSupport

/-- The source wrapper families. Version selection is a separate, exact
applicability record; the profile controls only the observed source difference. -/
inductive Operation where
  | associated (profile : Profile) (kind : CreateKind)
  | memo
  | metadata
  | deactivate
  | withdraw
  deriving DecidableEq, Repr

def Operation.profile : Operation → Profile
  | .associated profile _ => profile
  | .memo | .metadata => .legacyBoxed
  | .deactivate | .withdraw => .legacyInline

structure AssociatedAccounts where
  payer : AccountInfo.Value
  associatedToken : AccountInfo.Value
  authority : AccountInfo.Value
  mint : AccountInfo.Value
  systemProgram : AccountInfo.Value
  tokenProgram : AccountInfo.Value

def AssociatedAccounts.owners (accounts : AssociatedAccounts) : List AccountInfo.Value :=
  [accounts.payer, accounts.associatedToken, accounts.authority, accounts.mint,
    accounts.systemProgram, accounts.tokenProgram]

def AssociatedAccounts.keys (accounts : AssociatedAccounts) : AssociatedKeys :=
  ⟨accounts.payer.key, accounts.authority.key, accounts.mint.key, accounts.tokenProgram.key⟩

structure DeactivateAccounts where
  stake : AccountInfo.Value
  staker : AccountInfo.Value
  clock : AccountInfo.Value

def DeactivateAccounts.owners (accounts : DeactivateAccounts) : List AccountInfo.Value :=
  [accounts.stake, accounts.staker, accounts.clock]

def DeactivateAccounts.moved (accounts : DeactivateAccounts) : List AccountInfo.Value :=
  [accounts.stake, accounts.clock, accounts.staker]

structure WithdrawAccounts where
  stake : AccountInfo.Value
  withdrawer : AccountInfo.Value
  destination : AccountInfo.Value
  clock : AccountInfo.Value
  stakeHistory : AccountInfo.Value

def WithdrawAccounts.owners (accounts : WithdrawAccounts) : List AccountInfo.Value :=
  [accounts.stake, accounts.withdrawer, accounts.destination, accounts.clock, accounts.stakeHistory]

def WithdrawAccounts.moved (accounts : WithdrawAccounts) : List AccountInfo.Value :=
  [accounts.stake, accounts.destination, accounts.clock, accounts.stakeHistory, accounts.withdrawer]

/-- After partial move evaluation, remaining fields still drop in their
declaration order. Position tags distinguish equal or aliased AccountInfos. -/
def WithdrawAccounts.unmoved (accounts : WithdrawAccounts) (completed : Nat) :
    List AccountInfo.Value :=
  ([(0, accounts.stake), (4, accounts.withdrawer), (1, accounts.destination),
    (2, accounts.clock), (3, accounts.stakeHistory)].filter
      (fun entry => completed ≤ entry.1)).map Prod.snd

structure MetadataAccounts where
  metadata : AccountInfo.Value
  mint : AccountInfo.Value
  mintAuthority : AccountInfo.Value
  payer : AccountInfo.Value
  updateAuthority : AccountInfo.Value
  systemProgram : AccountInfo.Value
  rent : AccountInfo.Value

def MetadataAccounts.owners (accounts : MetadataAccounts) : List AccountInfo.Value :=
  [accounts.metadata, accounts.mint, accounts.mintAuthority, accounts.payer,
    accounts.updateAuthority, accounts.systemProgram, accounts.rent]

def MetadataAccounts.keys (accounts : MetadataAccounts) : Metadata.Keys :=
  ⟨accounts.metadata.key, accounts.mint.key, accounts.mintAuthority.key,
    accounts.payer.key, accounts.updateAuthority.key⟩

def Operation.Accounts : Operation → Type
  | .associated _ _ => AssociatedAccounts
  | .memo => Unit
  | .metadata => MetadataAccounts
  | .deactivate => DeactivateAccounts
  | .withdraw => WithdrawAccounts

def Operation.owners : (operation : Operation) → operation.Accounts → List AccountInfo.Value
  | .associated _ _, accounts => accounts.owners
  | .memo, _ => []
  | .metadata, accounts => accounts.owners
  | .deactivate, accounts => accounts.owners
  | .withdraw, accounts => accounts.owners

structure MetadataArgs (resources : Resources) where
  data : MetadataInput resources
  isMutable : Bool
  updateAuthoritySigner : Bool
  details : Option Metadata.CollectionDetails

structure WithdrawArgs where
  amount : UInt64
  custodian : Option AccountInfo.Value

def Operation.Extra (resources : Resources) : Operation → Type
  | .associated _ _ | .deactivate => Unit
  | .memo => Solanalib.Runtime.Bytes
  | .metadata => MetadataArgs resources
  | .withdraw => WithdrawArgs

abbrev Context (resources : Resources) (operation : Operation) :=
  AnchorContextOperations.CpiValue operation.Accounts operation.profile.Program
    resources.InfoResource (List (List Solanalib.Runtime.Bytes))

structure Args (resources : Resources) (operation : Operation) where
  context : Context resources operation
  extra : operation.Extra resources

/-- All ordinary providers and the opaque whole invocation share one state. -/
structure Types where
  resources : Resources
  invoke : CpiRequest.Invocation resources.State AccountInfo.Value resources.ProgramError
    resources.Unwind resources.Terminal

abbrev Error (resources : Resources) (profile : Profile) :=
  AnchorErrorOperations.Error profile.storage resources.ProgramError
    resources.StringResource resources.BoxResource

abbrev Run (resources : Resources) (Arg Value : Type) :=
  Callback.Run resources.State Arg Value resources.Unwind resources.Terminal

def tailDrops {resources : Resources} {operation : Operation}
    (context : Context resources operation) :
    List (Owned.DropAction resources.State resources.Unwind resources.Terminal) :=
  [resources.infos.dropAction context.remainingAccounts] ++
    infoDrops resources (operation.profile.programOwners context.program)

def contextDrops {resources : Resources} {operation : Operation}
    (context : Context resources operation) :
    List (Owned.DropAction resources.State resources.Unwind resources.Terminal) :=
  infoDrops resources (operation.owners context.accounts) ++ tailDrops context

/-- A successful syscall reply is decoded by the shared target-selected PDA
operation. Its failed search takes the actual panic provider. -/
def buildAssociated (resources : Resources) (profile : Profile)
    (kind : CreateKind) (keys : AssociatedKeys) :
    Run resources Unit (Built resources) :=
  fun before _ => Callback.bind (resources.find profile)
    (fun address after => buildVectors resources (associatedInstruction kind keys address.1)
      after ()) before (associatedSeeds keys)

/-- The temporary key-reference collection ends at the instruction initializer.
The remaining-account vector itself is borrowed and remains owned by the context. -/
def buildMemo (resources : Resources) (remaining : resources.InfoResource) (memo :
  Solanalib.Runtime.Bytes) :
    Run resources Unit (Built resources) :=
  fun before _ outcome => match resources.infos.current before remaining with
    | none => False
    | some infos => Callback.bind resources.keys.fromList
      (fun keys after => Owned.scope resources.doubleUnwind [resources.keys.dropAction keys]
        (fun state (_ : Unit) final => match resources.keys.current state keys with
          | none => False
          | some values => buildVectors resources (memoInstruction memo values) state () final)
        after ()) before (infos.map AccountInfo.Value.key) outcome

/-- The exact source prefix before reading the owned DataV2 for argument
serialization. Every allocation/push/extend/serialization exit is explicit. -/
def metadataPrefix (resources : Resources) (keys : Metadata.Keys) (signer : Bool) :
    Run resources Unit (resources.MetaResource × resources.ByteResource) :=
  fun before _ => Callback.bind resources.metas.withCapacity
    (fun metas after => Owned.protect resources.doubleUnwind [resources.metas.dropAction metas]
      (fun state (_ : Unit) => Callback.bind
        (pushMetas resources metas (Metadata.metas keys signer))
        (fun _ pushed => Callback.bind resources.metas.extend
          (fun _ extended => Callback.map (fun data => (metas, data))
            (serializeBytes resources) extended .metadataDiscriminator)
          pushed (metas, [])) state ()) after ()) before 7

/-- Source continuation after the discriminator vector has been built. On a
failure, the newer local data vector drops before the older metadata vector. -/
def metadataTail (resources : Resources) (keys : Metadata.Keys) (args : MetadataArgs resources)
    (metas : resources.MetaResource) (data : resources.ByteResource) :
    Run resources Unit (Built resources) :=
  Owned.protect resources.doubleUnwind
    [resources.bytes.dropAction data, resources.metas.dropAction metas]
    (fun state (_ : Unit) final => match args.data.current state with
      | none => False
      | some value => Callback.bind (serializeBytes resources)
        (fun argumentBytes serialized => Owned.scope resources.doubleUnwind
          [resources.bytes.dropAction argumentBytes]
          (Callback.map (fun _ => ⟨⟨Metadata.programId, metas, data⟩,
            Metadata.instruction keys value args.isMutable args.updateAuthoritySigner args.details⟩)
            (fun state (_ : Unit) => resources.appendBytes state (data, argumentBytes)))
          serialized ()) state (.metadataArguments value args.isMutable args.details) final)

/-- The generated metadata constructor owns its DataV2 argument. It serializes
the discriminator and arguments separately, appends by moving bytes, drops the
emptied argument vector, then drops the original String/creator fields. -/
def buildMetadata (resources : Resources) (keys : Metadata.Keys) (args : MetadataArgs resources) :
    Run resources Unit (Built resources) :=
  Owned.scope resources.doubleUnwind args.data.drops <|
    fun before _ => Callback.bind (metadataPrefix resources keys args.updateAuthoritySigner)
      (fun allocated after => metadataTail resources keys args allocated.1 allocated.2 after ())
        before ()

/-- The derived account-struct method creates an empty vector and extends it
by one singleton clone vector for each source field. -/
def metadataFields (resources : Resources) (accounts : MetadataAccounts) :
    Run resources Unit resources.InfoResource :=
  fun before _ =>
    let (infos, after) := resources.infos.empty before
    Owned.protect resources.doubleUnwind [resources.infos.dropAction infos]
      (Callback.map (fun _ => infos) (accountFields resources infos accounts.owners)) after ()

/-- CpiContext then clones remaining accounts and finally its program. The
slice read happens only after the actual derived-field construction returns. -/
def metadataInfosTail (resources : Resources) (context : Context resources .metadata)
    (infos : resources.InfoResource) : Run resources Unit resources.InfoResource :=
  Owned.protect resources.doubleUnwind [resources.infos.dropAction infos]
    (fun fieldsDone (_ : Unit) final =>
      match resources.infos.current fieldsDone context.remainingAccounts with
      | none => False
      | some remaining => Callback.bind resources.cloneExtendInfos
        (fun _ extended => Callback.bind
          (AccountInfoRc.lift (AccountInfoRc.cloneCall resources.rc))
          (fun program cloned => Callback.map (fun _ => infos) resources.infos.push
            cloned (infos, program)) extended context.program)
        fieldsDone (infos, remaining) final)

def metadataInfos (resources : Resources) (context : Context resources .metadata) :
    Run resources Unit resources.InfoResource :=
  fun before _ => Callback.bind (metadataFields resources context.accounts)
    (fun infos after => metadataInfosTail resources context infos after ()) before ()

def build (resources : Resources) (operation : Operation) :
    Run resources (Args resources operation) (Built resources) :=
  match operation with
  | .associated profile kind => fun before args =>
      buildAssociated resources profile kind args.context.accounts.keys before ()
  | .memo => fun before args => buildMemo resources args.context.remainingAccounts args.extra
    before ()
  | .metadata => fun before args => buildMetadata resources
      args.context.accounts.keys args.extra before ()
  | .deactivate => fun before args =>
      let planned := deactivateInstruction args.context.accounts.stake.key
        args.context.accounts.staker.key
      buildStake resources planned.metas none .stakeDeactivate planned before ()
  | .withdraw => fun before args =>
      let accounts := args.context.accounts
      let base := withdrawInstruction accounts.stake.key accounts.withdrawer.key
        accounts.destination.key args.extra.amount none
      buildStake resources base.metas
        (args.extra.custodian.map (fun info => Instruction.accountMeta info.key true false))
        (.stakeWithdraw args.extra.amount)
        (withdrawInstruction accounts.stake.key accounts.withdrawer.key accounts.destination.key
          args.extra.amount (args.extra.custodian.map AccountInfo.Value.key)) before ()

/-- Conversion runs in the actual invocation return state. Legacy Borsh error
strings and inline/boxed Anchor storage remain those of the selected profile. -/
def invokeAndConvert (types : Types) (profile : Profile)
    (instruction : Built types.resources) (infos : List AccountInfo.Value)
    (signers : List (List Solanalib.Runtime.Bytes)) :
    Run types.resources Unit (Except (Error types.resources profile) Unit) :=
  fun before _ outcome => match observe types.resources before instruction with
    | none => False
    | some value => Callback.bind (fun state (_ : Unit) => types.invoke state ⟨value, infos,
      signers⟩)
      (fun result after final => match result with
        | .ok () => final = .returned (.ok ()) after
        | .error error => Callback.map Except.error
          (AccountInfoRc.lift (AnchorErrorOperations.fromProgram profile.storage
            types.resources.errors))
          after error final) before () outcome

/-- Read the actual current vector immediately before the whole-signature CPI
call. This is not a snapshot captured before an effectful provider. -/
def invokeVector (types : Types) (profile : Profile) (instruction : Built types.resources)
    (infos : types.resources.InfoResource) (signers : List (List Solanalib.Runtime.Bytes)) :
    Run types.resources Unit (Except (Error types.resources profile) Unit) :=
  fun before _ outcome => match types.resources.infos.current before infos with
    | none => False
    | some values => invokeAndConvert types profile instruction values signers before () outcome

/-- The five non-cloning move expressions cannot unwind. Their exact progress
is retained when vector construction fails before all fields have moved. -/
def withdrawLiteral (resources : Resources) (accounts : WithdrawAccounts) :
    resources.State → Outcome resources.State resources.InfoResource
      (Owned.Array.Failure × resources.Unwind) resources.Terminal → Prop :=
  resources.literalProvider.runDetailed 5 (fun state index outcome =>
    match accounts.moved[index]? with
    | some value => outcome = .returned value state
    | none => False)

def withdrawAfterBuild (types : Types) (args : Args types.resources .withdraw)
    (instruction : Built types.resources) :
    Run types.resources Unit (Except (Error types.resources .legacyInline) Unit) :=
  fun before _ outcome => ∃ literal,
    withdrawLiteral types.resources args.context.accounts before literal ∧
    match literal with
    | .returned infos after => Owned.scope types.resources.doubleUnwind
        ([types.resources.infos.dropAction infos] ++ instructionDrops types.resources instruction ++
          tailDrops args.context)
        (fun state (_ : Unit) =>
          let push : Run types.resources Unit Unit := match args.extra.custodian with
            | none => fun state _ final => final = .returned () state
            | some value => fun state _ => types.resources.infos.push state (infos, value)
          Callback.bind push
            (fun _ pushed => invokeVector types .legacyInline instruction infos
              args.context.signerSeeds pushed ()) state ()) after () outcome
    | .unwound failure after => Owned.cleanup types.resources.doubleUnwind
        (instructionDrops types.resources instruction ++
          infoDrops types.resources args.extra.custodian.toList ++
          infoDrops types.resources (args.context.accounts.unmoved failure.1.completed) ++
          tailDrops args.context) (.unwound failure.2 after) outcome
    | .terminated reason => outcome = .terminated reason

def afterBuild (types : Types) (operation : Operation) (args : Args types.resources operation)
    (instruction : Built types.resources) :
    Run types.resources Unit (Except (Error types.resources operation.profile) Unit) :=
  match operation with
  | .associated profile _ => Owned.scope types.resources.doubleUnwind
      (instructionDrops types.resources instruction ++
        infoDrops types.resources args.context.accounts.owners ++ tailDrops args.context)
      (invokeAndConvert types profile instruction args.context.accounts.owners
        args.context.signerSeeds)
  | .deactivate => Owned.scope types.resources.doubleUnwind
      (instructionDrops types.resources instruction ++
        infoDrops types.resources args.context.accounts.moved ++ tailDrops args.context)
      (invokeAndConvert types .legacyInline instruction args.context.accounts.moved
        args.context.signerSeeds)
  | .memo => Owned.scope types.resources.doubleUnwind
      (instructionDrops types.resources instruction ++ tailDrops args.context)
      (invokeVector types .legacyBoxed instruction args.context.remainingAccounts
        args.context.signerSeeds)
  | .metadata => fun before _ outcome => ∃ prepared,
      metadataInfos types.resources args.context before () prepared ∧
      match prepared with
      | .returned infos after => Owned.scope types.resources.doubleUnwind
          (instructionDrops types.resources instruction ++ [types.resources.infos.dropAction infos]
            ++
            contextDrops args.context)
          (invokeVector types .legacyBoxed instruction infos args.context.signerSeeds) after ()
            outcome
      | .unwound reason after => Owned.cleanup types.resources.doubleUnwind
          (instructionDrops types.resources instruction ++ contextDrops args.context)
          (.unwound reason after) outcome
      | .terminated reason => outcome = .terminated reason
  | .withdraw => withdrawAfterBuild types args instruction

/-- Only the unconsumed optional custodian remains outside the context when
the withdrawal instruction constructor unwinds. Metadata arguments are already
owned and cleaned by their consuming generated instruction constructor. -/
def buildFailureDrops (resources : Resources) (operation : Operation)
    (args : Args resources operation) :
    List (Owned.DropAction resources.State resources.Unwind resources.Terminal) :=
  (match operation with
    | .withdraw => infoDrops resources args.extra.custodian.toList
    | _ => []) ++ contextDrops args.context

/-- Source composition through local construction and cleanup. An external
call may return an error, unwind, terminate, or have no finite exit. Only its
whole signature is interpreted; no invoked body is evaluated. -/
def run (types : Types) (operation : Operation) :
    Run types.resources (Args types.resources operation)
      (Except (Error types.resources operation.profile) Unit) :=
  fun before args outcome => ∃ built,
    build types.resources operation before args built ∧
    match built with
    | .returned instruction after => afterBuild types operation args instruction after () outcome
    | .unwound reason after => Owned.cleanup types.resources.doubleUnwind
        (buildFailureDrops types.resources operation args) (.unwound reason after) outcome
    | .terminated reason => outcome = .terminated reason

end Solanalib.Specs.Core.AnchorSplSupport
