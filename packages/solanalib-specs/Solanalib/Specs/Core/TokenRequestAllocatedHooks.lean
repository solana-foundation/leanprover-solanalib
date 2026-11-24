/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedBase
public import Solanalib.Specs.Core.TokenRequestAllocatedCollect
public import Solanalib.Specs.Core.TokenRequestAllocatedSeeds

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

open AllocatedControl

/-- The higher-order standard collection dependency and actual opaque CPI
call remain explicit. Collection receives the exact borrow closure of this SDK;
it is not a supplied successful account-resolution postcondition. -/
structure Dependencies (types : Types) where
  /-- The actual std Result/Vec collection boundary, supplied the exact SDK closure. -/
  collect : AllocatedCollect.Provider types.Extra types.GuardResource types.Unwind types.Terminal
  /-- All finite exits of the actual opaque solana_cpi::invoke_signed call. -/
  invoke : CpiRequest.Invocation (World types.Extra) AccountInfo.Value Error
    types.Unwind types.Terminal

/-- A borrowed ExtraAccountMeta list retains its original range and iterator
length. Each record is observed through the live validation-data Ref later. -/
structure ExtraSlice where
  /-- The live validation-data Ref underlying this borrowed list. -/
  reference : DataRef
  /-- The fixed byte offset of the selected payload in validation data. -/
  start : Nat
  /-- The fixed byte length of the selected payload. -/
  byteLength : Nat
  /-- The active record count captured when the iterator is formed. -/
  count : Nat

/-- The exact borrowed range of the selected TLV payload. This is the ordinary
first-Execute lookup, after the separately modeled allocation-aware validator.
It does not repeat that validator after the discriminator vector is dropped. -/
def findExecuteRange : Nat → Bytes → Nat → Except Error (Nat × Nat)
  | 0, _, _ => .error .InvalidAccountData
  | fuel + 1, bytes, offset => do
    if bytes.length < 12 then throw .InvalidAccountData
    let tag := bytes.take 8
    let length := Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes 8 4)
    if tag = Hook.executeDiscriminator then
      if bytes.length < 12 + length then throw .InvalidAccountData
      return (offset + 12, length)
    if tag = List.replicate 8 0 then throw Hook.tlvTypeNotFound
    findExecuteRange fuel (bytes.drop (12 + length)) (offset + 12 + length)

/-- ListView checks happen once, before the source iterator is formed. The
Lean list is only a value observation used to obtain the admitted count; the
source does not allocate another vector of extra metadata here. -/
def extraSlice (types : Types) (reference : DataRef) : Run types ExtraSlice :=
  bind (inspect reference.read) fun bytes =>
  bind (result (findExecuteRange (bytes.length + 1) bytes 0)) fun range =>
  bind (result (Hook.decodeMetaList (Solanalib.Runtime.slice bytes range.1 range.2))) fun entries =>
    pure ⟨reference, range.1, range.2, entries.length⟩

/-- Later record reads keep the same borrowed payload and active prefix.
Changes to unrelated TLV headers do not silently select another payload. -/
def ExtraSlice.entryAt (types : Types) (slice : ExtraSlice) (index : Nat)
    (state : World types.Extra) : Option Hook.ExtraMeta := do
  let bytes ← slice.reference.read state
  if index < slice.count ∧ slice.start + slice.byteLength ≤ bytes.length ∧
      4 + 35 * (index + 1) ≤ slice.byteLength then
    (Hook.decodeExtraMeta (Solanalib.Runtime.slice bytes (slice.start + 4 + 35 * index)
      35)).toOption
  else none

/-- The source borrows the current account vector for iteration. Its length
and storage must stay valid for that iterator; individual items are read from
the actual callback state. -/
def infoIterator (types : Types) (resource : types.InfoResource) (length : Nat) :
    AllocatedCollect.Iterator types.Extra where
  length := length
  elementAt := fun state index => do
    let infos ← types.infos.current state resource
    if infos.length = length then infos[index]? else none

/-- Collection receives the source key-before-borrow closure. Its provider
owns partial collection cleanup and transfers a successful vector of Refs;
there is no invented SDK-level push or reserve schedule. -/
def collectRefs (types : Types) (deps : Dependencies types) (resource : types.InfoResource) :
    Run types types.GuardResource :=
  bind (inspect fun state => types.infos.current state resource) fun infos =>
    deps.collect.run (infoIterator types resource infos.length)
      (AllocatedCollect.borrowElement types.raise)

/-- The resolver closure observes the current collected vector and follows
every live Ref. Missing guards are representation failures, not absent source
account data: every successful source collection stored Some(data). -/
def guardObservations (types : Types) (resource : types.GuardResource)
    (state : World types.Extra) : Option Hook.Observations := do
  let entries ← types.guards.current state resource
  entries.mapM fun (key, reference) => do
    let bytes ← reference.read state
    return (key, some bytes)

/-- Every extra meta resolves while the collected Refs are owned, then drops
that actual vector before privilege reduction or additional-account lookup.
Seed/literal/reference-vector allocations use their own ordinary helper. -/
def resolveExtra (types : Types) (deps : Dependencies types)
    (execute : Prepared types) (slice : ExtraSlice) (index : Nat) : Run types
      Solanalib.Runtime.CpiMeta :=
  bind (collectRefs types deps execute.infos) fun references =>
    scope types.doubleUnwind [types.guards.dropAction references]
      (fun state => AllocatedSeeds.resolve types.seedOps types.doubleUnwind types.findPda
        { extraAt := slice.entryAt types index
          instructionAt := fun current => types.bytes.current current execute.instruction.data
          programAt := fun _ => some execute.instruction.programId
          accountsAt := guardObservations types references } state ())

/-- A selected account is cloned before the metadata push. If that push
unwinds, this local clone drops before the outer vectors. After a successful
push the owner moves into the info push, whose provider owns its cleanup. -/
def appendResolved (types : Types) (args : Onchain.Args) (execute : Prepared types)
    (resolved : Solanalib.Runtime.CpiMeta) : Run types Unit :=
  bind (inspect fun state => types.metas.current state execute.instruction.metas) fun previous =>
    let item := Hook.deescalate previous resolved
    match args.additional.find? (fun info => info.key == item.key) with
    | none => fail Hook.incorrectExtraAccount
    | some info =>
      bind (cloneInfo types info) fun cloned =>
      bind (moveOnOk types.doubleUnwind [dropInfo types cloned]
        (perform fun state => types.metas.push state (execute.instruction.metas, item))) fun _ =>
        perform fun state => types.infos.push state (execute.infos, cloned)

/-- The iterator visits the admitted prefix in order. Earlier appended
accounts participate in later resolution and privilege reduction. -/
def addExtraEntries (types : Types) (deps : Dependencies types) (args : Onchain.Args)
    (execute : Prepared types) (slice : ExtraSlice) : Nat → Nat → Run types Unit
  | 0, _ => pure ()
  | remaining + 1, index =>
    bind (resolveExtra types deps execute slice index) fun resolved =>
    bind (appendResolved types args execute resolved) fun _ =>
      addExtraEntries types deps args execute slice remaining (index + 1)

/-- The ordinary account-list helper validates the full TLV storage before
looking up Execute and forming its ListView. The caller owns the surrounding
validation-data Ref until this complete helper returns. -/
def addExtraList (types : Types) (deps : Dependencies types) (args : Onchain.Args)
    (execute : Prepared types) (reference : DataRef) : Run types Unit :=
  bind (fun state => AllocatedTlv.validate types.discriminators types.doubleUnwind
    reference.read state ()) fun _ =>
  bind (extraSlice types reference) fun slice =>
    addExtraEntries types deps args execute slice slice.count 0

/-- Execute packing uses an empty vector and two extend calls, followed by
the four-element metadata literal. It differs from the with-capacity constructor of
TokenInstruction::pack and retains that source distinction. -/
def executeInstruction (types : Types) (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey)
  :
    Run types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  fun before outcome =>
    let (data, after) := types.bytes.empty before
    moveOnOk types.doubleUnwind [types.bytes.dropAction data]
      (bind (perform fun state => types.bytes.extend state (data, Hook.executeDiscriminator)) fun _
        =>
       bind (perform fun state => types.bytes.extend state
         (data, Solanalib.Runtime.u64le args.amount)) fun _ =>
       bind (perform fun state => types.metas.fromList state
         ([args.source.key, args.mint.key, args.destination.key, args.authority.key].map
           fun key => Instruction.accountMeta key false false)) fun metas =>
         pure ⟨programId, metas, data⟩) after outcome

/-- The validation meta is appended before the Execute account array and
before borrowing validation data. -/
def executePrelude (types : Types) (args : Onchain.Args) (programId validationKey :
  Solanalib.Runtime.Pubkey) :
    Run types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  bind (executeInstruction types args programId) fun instruction =>
    moveOnOk types.doubleUnwind (instructionDrops types instruction)
      (bind (perform fun state => types.metas.push state
        (instruction.metas, Instruction.accountMeta validationKey false false)) fun _ =>
        pure instruction)

/-- Current extra metadata is copied before current extra AccountInfos are
cloned by their single extend_from_slice dependency. Only the suffix after
the five standard Execute entries is copied back. -/
def copyExtras (types : Types) (transfer execute : Prepared types) : Run types Unit :=
  bind (inspect fun state => do
    let items ← types.metas.current state execute.instruction.metas
    if 5 ≤ items.length then some (items.drop 5) else none) fun extraMetas =>
  bind (perform fun state => types.metas.extend state
    (transfer.instruction.metas, extraMetas)) fun _ =>
  bind (inspect fun state => do
    let infos ← types.infos.current state execute.infos
    if 5 ≤ infos.length then some (infos.drop 5) else none) fun extraInfos =>
    perform fun state => types.infos.extend state (transfer.infos, extraInfos)

/-- A readonly nonsigner meta precedes the corresponding AccountInfo clone
and vector push. This is used for validation and then the hook program. -/
def appendReadonly (types : Types) (prepared : Prepared types)
    (key : Solanalib.Runtime.Pubkey) (info : AccountInfo.Value) : Run types Unit :=
  bind (perform fun state => types.metas.push state
    (prepared.instruction.metas, Instruction.accountMeta key false false)) fun _ =>
    pushClonedInfo types prepared.infos info

/-- The validation PDA uses a fixed prefix and the complete key bytes of the mint. -/
def hookPdaInputs (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey) :
    Address.Syscall.PdaInputs :=
  ⟨[Hook.extraAccountMetasSeed, args.mint.key.bytes], programId⟩

/-- These two source seeds always fit the selected slice profile; no runtime
PDA seed-limit check or allocator success premise is introduced. -/
theorem hookPdaInputs_bounded (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey) :
    (hookPdaInputs args programId).Bounded := by
  refine ⟨?_, ?_⟩
  · change 2 < Solanalib.Runtime.U64_LIMIT
    decide +kernel
  intro seed member
  rcases List.mem_cons.mp member with same | tail
  · subst seed
    decide +kernel
  · have same := List.mem_singleton.mp tail
    subst seed
    rw [Solanalib.Runtime.Pubkey.length_eq]
    decide +kernel

/-- The actual PDA syscall and ordinary find wrapper precede program lookup,
which precedes optional validation lookup. Their state changes and failures
are retained; no Execute allocation is performed on these early errors. -/
def hookEntry (types : Types) (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey) :
    Run types (Solanalib.Runtime.Pubkey × AccountInfo.Value × Option AccountInfo.Value) :=
  bind (perform fun state => types.findPda state
    (hookPdaInputs args programId)) fun (validationKey, _) =>
    match args.additional.find? (fun info => info.key == programId) with
    | none => fail Hook.incorrectHookAccount
    | some program => pure (validationKey, program,
        args.additional.find? (fun info => info.key == validationKey))

/-- The helper consumes four AccountInfo arguments. Before their move into
the Execute array, exceptional cleanup drops those arguments. After the move,
the array constructor and the successful info vector own them instead. The
validation Ref ends before copying extras back; Execute locals then drop
before the final hook-program append. -/
def addHook (types : Types) (deps : Dependencies types) (args : Onchain.Args)
    (programId : Solanalib.Runtime.Pubkey) (transfer : Prepared types) : Run types Unit :=
  bind (moveOnOk types.doubleUnwind (argumentDrops types args)
    (hookEntry types args programId)) fun (validationKey, program, validation) =>
    match validation with
    | none => scope types.doubleUnwind (argumentDrops types args)
        (appendReadonly types transfer programId program)
    | some validationInfo =>
      bind (moveOnOk types.doubleUnwind (argumentDrops types args)
        (executePrelude types args programId validationKey)) fun instruction =>
      bind (executeInfos types args validationInfo instruction) fun infos =>
        let execute : Prepared types := ⟨instruction, infos⟩
        bind (scope types.doubleUnwind (instructionDrops types instruction)
          (scope types.doubleUnwind [types.infos.dropAction infos]
            (bind (withData types.raise types.doubleUnwind true validationInfo
              (addExtraList types deps args execute)) fun _ =>
             bind (copyExtras types transfer execute) fun _ =>
               appendReadonly types transfer validationKey validationInfo))) fun _ =>
          appendReadonly types transfer programId program

end Solanalib.Specs.Core.Token.OnchainAllocated
