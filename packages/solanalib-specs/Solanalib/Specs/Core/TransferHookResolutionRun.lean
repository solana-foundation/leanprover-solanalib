/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolutionTypes

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.TransferHookResolution

open Token (Error Bytes)
open Token.AllocatedControl

/-- A clone occurs before its owner moves into Vec::push. The selected push
binding owns that moved value, including its cleanup on a failed insertion. -/
def pushClonedInfo (types : Types) (resource : types.InfoResource)
    (info : AccountInfo.Value) : Run types Unit :=
  bind (cloneInfo types info) fun cloned =>
    perform fun state => types.infos.push state (resource, cloned)

/-- the first four literal expressions of Execute move the arguments of the helper;
the fifth creates one validation-account clone. Pure moves have no callbacks,
and the concrete Rc clone has no unwind exit. -/
def executeInfoAt (types : Types) (args : Args types) (validation : AccountInfo.Value) :
    Callback.Run (World types.Extra) Nat AccountInfo.Value types.Unwind types.Terminal :=
  fun state index outcome =>
    match index with
    | 0 => outcome = .returned args.source state
    | 1 => outcome = .returned args.mint state
    | 2 => outcome = .returned args.destination state
    | 3 => outcome = .returned args.authority state
    | 4 => AccountInfoRc.lift (AccountInfoRc.cloneCall types.rc) state validation outcome
    | _ => False

/-- Lifting the fixed Rc outcome vocabulary cannot introduce an unwind. -/
theorem rcLift_no_unwind (types : Types) (info : AccountInfo.Value)
    (before after : World types.Extra) (reason : types.Unwind)
    (execution : AccountInfoRc.lift (Unwind := types.Unwind)
      (AccountInfoRc.cloneCall types.rc) before info (.unwound reason after)) : False := by
  obtain ⟨produced, _, same⟩ := execution
  cases produced with
  | returned _ _ => cases same
  | unwound impossible _ => exact nomatch impossible
  | terminated _ => cases same

/-- No Execute expression can unwind after partially consuming an original
argument. Consequently the completed count exactly determines the originals
still owned by the surrounding source scope on a surviving constructor unwind. -/
theorem executeInfoAt_no_unwind (types : Types) (args : Args types)
    (validation : AccountInfo.Value) (before after : World types.Extra)
    (index : Nat) (reason : types.Unwind)
    (execution : executeInfoAt types args validation before index (.unwound reason after)) : False
      := by
  unfold executeInfoAt at execution
  split at execution
  all_goals first
    | exact rcLift_no_unwind types validation before after reason execution
    | cases execution

/-- Every surviving Execute-constructor unwind reports a completed prefix
within the five source expressions, and cannot originate in an expression.
These facts justify the remaining-original suffix used by the enclosing scope. -/
theorem executeLiteral_unwind_progress (types : Types) (args : Args types)
    (validation : AccountInfo.Value) (before after : World types.Extra)
    (failure : Owned.Array.Failure) (reason : types.Unwind)
    (execution : types.literalProvider.runDetailed 5 (executeInfoAt types args validation)
      before (.unwound (failure, reason) after)) :
    failure.completed ≤ 5 ∧ failure.site ≠ .evaluate := by
  have progress := Owned.Array.Trace.unwound_progress execution rfl (Nat.zero_le 5)
  refine ⟨progress.2.1, ?_⟩
  exact Owned.Array.Trace.unwound_not_evaluate
    (fun current index why final =>
      executeInfoAt_no_unwind types args validation current final index why) execution rfl

/-- Original arguments not yet moved into the partial array of Execute remain
caller-owned and drop in reverse declaration order, after the constructor
and all earlier locals of the inner source block have been cleaned. -/
def executeRemainder (types : Types) (args : Args types) (completed : Nat) :
    List (Owned.DropAction (World types.Extra) types.Unwind types.Terminal) :=
  ([args.source, args.mint, args.destination, args.authority].drop completed).reverse.map
    (dropInfo types)

/-- the literal constructor of Execute exposes progress for exact exceptional
cleanup: its evaluated elements/storage first, the earlier instruction local
next, and then still-unmoved arguments from the outer function scope. On
success the instruction remains owned and all evaluated owners transfer to
the vector. Terminal exits bypass every remaining cleanup. -/
def executeInfos (types : Types) (args : Args types) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    Run types types.InfoResource :=
  fun before outcome => ∃ detailed,
    types.literalProvider.runDetailed 5 (executeInfoAt types args validation) before detailed ∧
    match detailed with
    | .returned resource after => outcome = .returned (.ok resource) after
    | .unwound (failure, reason) after =>
      Owned.cleanup types.doubleUnwind
        (instructionDrops types instruction ++ executeRemainder types args failure.completed)
        (.unwound reason after) outcome
    | .terminated reason => outcome = .terminated reason


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
    if tag = Token.Hook.executeDiscriminator then
      if bytes.length < 12 + length then throw .InvalidAccountData
      return (offset + 12, length)
    if tag = List.replicate 8 0 then throw Token.Hook.tlvTypeNotFound
    findExecuteRange fuel (bytes.drop (12 + length)) (offset + 12 + length)

/-- spl-pod 0.5.1 checks physical storage before forming the active range.
Unlike the later ListView helper, a count exceeding capacity panics here. -/
def extraSlice (types : Types) (reference : DataRef) : Run types ExtraSlice :=
  bind (inspect reference.read) fun bytes =>
  bind (result (findExecuteRange (bytes.length + 1) bytes 0)) fun range =>
    match podAccess (Solanalib.Runtime.slice bytes range.1 range.2) with
    | .error (.inl error) => fail error
    | .error (.inr reason) => panic (fun state => types.raise state reason)
    | .ok count => pure ⟨reference, range.1, range.2, count⟩

/-- Later record reads keep the same borrowed payload and active prefix.
Changes to unrelated TLV headers do not silently select another payload. -/
def ExtraSlice.entryAt (types : Types) (slice : ExtraSlice) (index : Nat)
    (state : World types.Extra) : Option Token.Hook.ExtraMeta := do
  let bytes ← slice.reference.read state
  if index < slice.count ∧ slice.start + slice.byteLength ≤ bytes.length ∧
      4 + 35 * (index + 1) ≤ slice.byteLength then
    (Token.Hook.decodeExtraMeta (Solanalib.Runtime.slice bytes (slice.start + 4 + 35 * index)
      35)).toOption
  else none

/-- The source borrows the current account vector for iteration. Its length
and storage must stay valid for that iterator; individual items are read from
the actual callback state. -/
def infoIterator (types : Types) (resource : types.InfoResource) (length : Nat) :
    Token.AllocatedCollect.Iterator types.Extra where
  length := length
  elementAt := fun state index => do
    let infos ← types.infos.current state resource
    if infos.length = length then infos[index]? else none

/-- Each callback copies the key before acquiring the current shared data Ref.
Even a fixed-key extra collects all current infos before resolving anything. -/
def borrowElement (types : Types) :
    Callback.Run (World types.Extra) AccountInfo.Value (Except Error GuardElement)
      types.Unwind types.Terminal :=
  fun before info => bind (borrowData types info) (fun reference => pure (info.key, reference))
    before

/-- Source iterator order, short-circuiting and partial cleanup come from the
shared collection protocol with this exact closure; no resolution oracle is used. -/
def collectRefs (types : Types) (resource : types.InfoResource) : Run types types.GuardResource :=
  bind (inspect fun state => types.infos.current state resource) fun infos =>
    (Token.AllocatedCollect.protocolProvider types.collectProtocol).run
      (infoIterator types resource infos.length) (borrowElement types)

/-- The resolver closure observes the current collected vector and follows
every live Ref. Missing guards are representation failures, not absent source
account data: every successful source collection stored Some(data). -/
def guardObservations (types : Types) (resource : types.GuardResource)
    (state : World types.Extra) : Option Token.Hook.Observations := do
  let entries ← types.collection.current state resource
  entries.mapM fun (key, reference) => do
    let bytes ← reference.read state
    return (key, some bytes)

/-- Every extra meta resolves while the collected Refs are owned, then drops
that actual vector before privilege reduction or additional-account lookup.
Seed/literal/reference-vector allocations use their own ordinary helper. -/
def resolveExtra (types : Types)
    (execute : Execute types) (slice : ExtraSlice) (index : Nat) : Run types
      Solanalib.Runtime.CpiMeta :=
  bind (collectRefs types execute.infos) fun references =>
    scope types.doubleUnwind [dropReferences types references]
      (fun state => Token.AllocatedSeeds.resolve types.seedOps types.doubleUnwind types.findPda
        { extraAt := slice.entryAt types index
          instructionAt := fun current => types.bytes.current current execute.instruction.data
          programAt := fun _ => some execute.instruction.programId
          accountsAt := guardObservations types references } state ())

/-- A selected account is cloned before the metadata push. If that push
unwinds, this local clone drops before the outer vectors. After a successful
push the owner moves into the info push, whose provider owns its cleanup. -/
def appendResolved (types : Types) (args : Args types) (execute : Execute types)
    (resolved : Solanalib.Runtime.CpiMeta) : Run types Unit :=
  bind (inspect fun state => types.metas.current state execute.instruction.metas) fun previous =>
    let item := deescalate previous resolved
    match args.additional.find? (fun info => info.key == item.key) with
    | none => fail Token.Hook.incorrectExtraAccount
    | some info =>
      bind (cloneInfo types info) fun cloned =>
      bind (moveOnOk types.doubleUnwind [dropInfo types cloned]
        (perform fun state => types.metas.push state (execute.instruction.metas, item))) fun _ =>
        perform fun state => types.infos.push state (execute.infos, cloned)

/-- The iterator visits the admitted prefix in order. Earlier appended
accounts participate in later resolution and privilege reduction. -/
def addExtraEntries (types : Types) (args : Args types)
    (execute : Execute types) (slice : ExtraSlice) : Nat → Nat → Run types Unit
  | 0, _ => pure ()
  | remaining + 1, index =>
    bind (resolveExtra types execute slice index) fun resolved =>
    bind (appendResolved types args execute resolved) fun _ =>
      addExtraEntries types args execute slice remaining (index + 1)

/-- The ordinary account-list helper validates the full TLV storage before
looking up Execute and forming its POD slice. The caller owns the surrounding
validation-data Ref until this complete helper returns. -/
def addExtraList (types : Types) (args : Args types)
    (execute : Execute types) (reference : DataRef) : Run types Unit :=
  bind (fun state => Token.AllocatedTlv.validate types.discriminators types.doubleUnwind
    reference.read state ()) fun _ =>
  bind (extraSlice types reference) fun slice =>
    addExtraEntries types args execute slice slice.count 0

/-- Execute packing uses an empty vector and two extend calls, followed by
the four-element metadata literal. It differs from the with-capacity constructor of
TokenInstruction::pack and retains that source distinction. -/
def executeInstruction (types : Types) (args : Args types) (programId : Solanalib.Runtime.Pubkey) :
    Run types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  fun before outcome =>
    let (data, after) := types.bytes.empty before
    moveOnOk types.doubleUnwind [types.bytes.dropAction data]
      (bind (perform fun state => types.bytes.extend state (data, Token.Hook.executeDiscriminator))
        fun _ =>
       bind (perform fun state => types.bytes.extend state
         (data, Solanalib.Runtime.u64le args.amount.toNat)) fun _ =>
       bind (perform fun state => types.metas.fromList state
         ([args.source.key, args.mint.key, args.destination.key, args.authority.key].map
           fun key => Instruction.accountMeta key false false)) fun metas =>
         pure ⟨programId, metas, data⟩) after outcome

/-- The validation meta is appended before the Execute account array and
before borrowing validation data. -/
def executePrelude (types : Types) (args : Args types) (programId validationKey :
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
def copyExtras (types : Types) (transfer execute : Execute types) : Run types Unit :=
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
def appendReadonly (types : Types) (prepared : Execute types)
    (key : Solanalib.Runtime.Pubkey) (info : AccountInfo.Value) : Run types Unit :=
  bind (perform fun state => types.metas.push state
    (prepared.instruction.metas, Instruction.accountMeta key false false)) fun _ =>
    pushClonedInfo types prepared.infos info

/-- The validation PDA uses a fixed prefix and the complete key bytes of the mint. -/
def hookPdaInputs {types : Types} (args : Args types) (programId : Solanalib.Runtime.Pubkey) :
    Address.Syscall.PdaInputs :=
  ⟨[Token.Hook.extraAccountMetasSeed, args.mint.key.bytes], programId⟩

/-- These two source seeds always fit the selected slice profile; no runtime
PDA seed-limit check or allocator success premise is introduced. -/
theorem hookPdaInputs_bounded {types : Types} (args : Args types) (programId :
  Solanalib.Runtime.Pubkey) :
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
def hookEntry (types : Types) (args : Args types) (programId : Solanalib.Runtime.Pubkey) :
    Run types (Solanalib.Runtime.Pubkey × AccountInfo.Value × Option AccountInfo.Value) :=
  bind (perform fun state => types.findPda state
    (hookPdaInputs args programId)) fun (validationKey, _) =>
    match args.additional.find? (fun info => info.key == programId) with
    | none => fail Token.Hook.incorrectHookAccount
    | some program => pure (validationKey, program,
        args.additional.find? (fun info => info.key == validationKey))

/-- The helper consumes four AccountInfo arguments. Before their move into
the Execute array, exceptional cleanup drops those arguments. After the move,
the array constructor and the successful info vector own them instead. The
validation Ref ends before copying extras back; Execute locals then drop
before the final hook-program append. -/
def addHook (types : Types) (args : Args types)
    (programId : Solanalib.Runtime.Pubkey) (transfer : Execute types) : Run types Unit :=
  bind (moveOnOk types.doubleUnwind (argumentDrops types args)
    (hookEntry types args programId)) fun (validationKey, program, validation) =>
    match validation with
    | none => scope types.doubleUnwind (argumentDrops types args)
        (appendReadonly types transfer programId program)
    | some validationInfo =>
      bind (moveOnOk types.doubleUnwind (argumentDrops types args)
        (executePrelude types args programId validationKey)) fun instruction =>
      bind (executeInfos types args validationInfo instruction) fun infos =>
        let execute : Execute types := ⟨instruction, infos⟩
        bind (scope types.doubleUnwind (instructionDrops types instruction)
          (scope types.doubleUnwind [types.infos.dropAction infos]
            (bind (withData types validationInfo
              (addExtraList types args execute)) fun _ =>
             bind (copyExtras types transfer execute) fun _ =>
               appendReadonly types transfer validationKey validationInfo))) fun _ =>
          appendReadonly types transfer programId program

/-- All finite behaviors of the registered helper, on its exact argument list.
The caller retains its instruction and account-vector resources on every
nonterminal exit, including partial mutations before allocation unwinds. -/
def run (types : Types) :
    Callback.Run (World types.Extra) (Args types) (Except Error Unit) types.Unwind types.Terminal :=
  fun before args => addHook types args args.programId ⟨args.instruction, args.infos⟩ before

end Solanalib.Specs.Core.TransferHookResolution
