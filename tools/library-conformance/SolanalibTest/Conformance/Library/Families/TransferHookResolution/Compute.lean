/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TransferHookResolution.Primitives

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TransferHookResolution

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.TransferHookResolution
open Solanalib.Specs.Core.Token (Error Bytes)
open Solanalib.Specs.Core.Token.AllocatedControl (DataRef)
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
  (VecPrims RcPrims ArrayPrims NoAgain exists_bind_iff)
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainCollect (collectF collect_fn
  resolveF resolve_fn)
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainLiteral

variable {types : Types}

/-- Compute the checked borrow closure, retaining its copied key. -/
def borrowElementF (types : Types) (before : World types.Extra) (info : AccountInfo.Value) :=
  bindR (borrowDataF types info) (fun reference => pureR (info.key, reference)) before

theorem borrowElement_fn (types : Types) : Fn (borrowElement types) (borrowElementF types) :=
  fun before info outcome => bindR_fn (borrowData_fn types info) (fun _ => pureR_fn _) before
    outcome

def collectRefsF (P : Prims types) (resource : types.InfoResource) : RunF types types.GuardResource
  :=
  bindR (inspectR fun state => types.infos.current state resource) fun infos =>
    collectF P.collectFinishF P.collectRetireF P.dbl
      (infoIterator types resource infos.length) (borrowElementF types)

theorem collectRefs_fn (P : Prims types) (resource : types.InfoResource) :
    RFn (collectRefs types resource) (collectRefsF P resource) :=
  bindR_fn (inspectR_fn _) fun _ =>
    collect_fn (protocol := types.collectProtocol) P.collect_no_internal P.collectFinish_fn
      P.collectRetire_fn P.double_fn P.collect_order _ _ _ (borrowElement_fn types)

def dropReferencesF (P : Prims types) (resource : types.GuardResource) : DropF types :=
  fun before => (types.collection.current before resource).bind fun entries =>
    cleanupF P.dbl
      (entries.map (fun element => DataRef.dropF element.2) ++ [P.collectRetireF (some resource)
        entries])
      (.returned () before)

theorem dropReferences_fn (P : Prims types) (resource : types.GuardResource) :
    DFn (dropReferences types resource) (dropReferencesF P resource) := by
  intro before outcome
  apply exists_bind_iff (fun _ => Iff.rfl)
  intro entries _
  exact cleanup_fn P.double_fn _ _
    (All2.append (All2.map _ _ (fun element => DataRef.drop_fn element.2) entries)
      (.cons (P.collectRetire_fn (some resource) entries) .nil)) _ _

def extraSliceF (P : Prims types) (reference : DataRef) : RunF types ExtraSlice :=
  bindR (inspectR reference.read) fun bytes =>
  bindR (resultR (findExecuteRange (bytes.length + 1) bytes 0)) fun range =>
    match podAccess (Solanalib.Runtime.slice bytes range.1 range.2) with
    | .error (.inl error) => failR error
    | .error (.inr reason) => panicR (fun state => P.raiseF state reason)
    | .ok count => pureR ⟨reference, range.1, range.2, count⟩

theorem extraSlice_fn (P : Prims types) (reference : DataRef) :
    RFn (extraSlice types reference) (extraSliceF P reference) := by
  refine bindR_fn (inspectR_fn _) fun bytes => bindR_fn (resultR_fn _) fun range => ?_
  cases podAccess (Solanalib.Runtime.slice bytes range.1 range.2) with
  | ok count => exact pureR_fn _
  | error reason =>
    cases reason with
    | inl error => exact failR_fn error
    | inr reason => exact panicR_fn (fun before outcome => P.raise_fn before reason outcome)

/-- The resolver arguments of `resolveExtra`: the selected record, the
instruction bytes, the program key and the collected guard observations. -/
def resolveArgs (execute : Execute types) (slice : ExtraSlice) (index : Nat)
    (references : types.GuardResource) : Token.AllocatedSeeds.Args (World types.Extra) where
  extraAt := slice.entryAt types index
  instructionAt := fun current => types.bytes.current current execute.instruction.data
  programAt := fun _ => some execute.instruction.programId
  accountsAt := guardObservations types references

/-- `resolveExtra`, computed: collect the guards, then resolve in a scope that
drops the guard vector. -/
def resolveExtraF (P : Prims types) (execute : Execute types)
    (slice : ExtraSlice) (index : Nat) : RunF types Solanalib.Runtime.CpiMeta :=
  bindR (collectRefsF P execute.infos) fun references =>
    scopeR P.dbl [dropReferencesF P references]
      (fun s => resolveF P.seedBytes P.seeds P.seedRefs P.dbl (findPdaF P)
        (resolveArgs execute slice index references) s ())

/-- `resolveExtra types execute slice index` admits exactly
`resolveExtraF P execute slice index`. -/
theorem resolveExtra_fn (P : Prims types) (execute : Execute types)
    (slice : ExtraSlice) (index : Nat) :
    RFn (resolveExtra types execute slice index) (resolveExtraF P execute slice index) :=
  bindR_fn (collectRefs_fn P execute.infos) fun references =>
    scopeR_fn P.double_fn (.cons (dropReferences_fn P references) .nil)
      (call_fn (resolve_fn P.seedBytes P.seeds P.seedRefs P.double_fn (findPda_fn P)
        (resolveArgs execute slice index references)) ())

/-- `appendResolved`, computed: de-escalate against the current metadata,
select the additional account, clone it, push the metadata (dropping the
clone if that fails) and push the clone. -/
def appendResolvedF (P : Prims types) (args : Args types) (execute : Execute types)
    (resolved : Solanalib.Runtime.CpiMeta) : RunF types Unit :=
  bindR (inspectR fun state => types.metas.current state execute.instruction.metas) fun previous =>
    match args.additional.find? fun info =>
        info.key == (deescalate previous resolved).key with
    | none => failR Token.Hook.incorrectExtraAccount
    | some info =>
      bindR (cloneInfoF P info) fun cloned =>
      bindR (moveOnOkR P.dbl [dropInfoF P cloned]
        (performR fun s => P.metas.pushF s
          (execute.instruction.metas, deescalate previous resolved))) fun _ =>
        performR fun s => P.infos.pushF s (execute.infos, cloned)

/-- `appendResolved types args execute resolved` admits exactly
`appendResolvedF P args execute resolved`. -/
theorem appendResolved_fn (P : Prims types) (args : Args types) (execute : Execute types)
    (resolved : Solanalib.Runtime.CpiMeta) :
    RFn (appendResolved types args execute resolved) (appendResolvedF P args execute resolved) := by
  refine bindR_fn (inspectR_fn _) fun previous => ?_
  dsimp only
  cases args.additional.find? (fun info => info.key == (deescalate previous resolved).key) with
  | none => exact failR_fn _
  | some info =>
    exact bindR_fn (cloneInfo_fn P info) fun cloned =>
      bindR_fn (moveOnOkR_fn P.double_fn (.cons (dropInfo_fn P cloned) .nil)
        (performCall_fn P.metas.push_fn _)) fun _ => performCall_fn P.infos.push_fn _

/-- `addExtraEntries`, computed by the same recursion on the remaining count. -/
def addExtraEntriesF (P : Prims types) (args : Args types)
    (execute : Execute types) (slice : ExtraSlice) : Nat → Nat → RunF types Unit
  | 0, _ => pureR ()
  | remaining + 1, index =>
    bindR (resolveExtraF P execute slice index) fun resolved =>
    bindR (appendResolvedF P args execute resolved) fun _ =>
      addExtraEntriesF P args execute slice remaining (index + 1)

/-- `addExtraEntries types args execute slice remaining index` admits
exactly `addExtraEntriesF P args execute slice remaining index`. -/
theorem addExtraEntries_fn (P : Prims types) (args : Args types)
    (execute : Execute types) (slice : ExtraSlice) :
    ∀ remaining index, RFn (addExtraEntries types args execute slice remaining index)
      (addExtraEntriesF P args execute slice remaining index)
  | 0, _ => pureR_fn ()
  | remaining + 1, index =>
    bindR_fn (resolveExtra_fn P execute slice index) fun resolved =>
      bindR_fn (appendResolved_fn P args execute resolved) fun _ =>
        addExtraEntries_fn P args execute slice remaining (index + 1)

/-- `addExtraList`, computed from the computed TLV validator `validateF` and
the computed `extraSlice` (`sliceF`) of component (7a). -/
def addExtraListF (P : Prims types) (args : Args types)
    (execute : Execute types) (validateF : Token.AllocatedControl.DataRef → RunF types Unit)
    (sliceF : Token.AllocatedControl.DataRef → RunF types ExtraSlice)
    (reference : Token.AllocatedControl.DataRef) : RunF types Unit :=
  bindR (validateF reference) fun _ =>
  bindR (sliceF reference) fun slice =>
    addExtraEntriesF P args execute slice slice.count 0

/-- `addExtraList types args execute reference` admits exactly
`addExtraListF P args execute validateF sliceF reference`, given the
`RFn` lemmas of the TLV validator and of `extraSlice`. -/
theorem addExtraList_fn (P : Prims types) (args : Args types)
    (execute : Execute types) {validateF : Token.AllocatedControl.DataRef → RunF types Unit}
    (hv : ∀ reference, RFn (fun state => Token.AllocatedTlv.validate types.discriminators
      types.doubleUnwind reference.read state ()) (validateF reference))
    {sliceF : Token.AllocatedControl.DataRef → RunF types ExtraSlice}
    (hs : ∀ reference, RFn (extraSlice types reference) (sliceF reference))
    (reference : Token.AllocatedControl.DataRef) :
    RFn (addExtraList types args execute reference)
      (addExtraListF P args execute validateF sliceF reference) :=
  bindR_fn (hv reference) fun _ => bindR_fn (hs reference) fun slice =>
    addExtraEntries_fn P args execute slice slice.count 0

/-- The exit of `executeInfos` after the literal, computed: a returned vector
is `Ok`; an unwind cleans the instruction and the arguments not yet moved into
the literal (`Failure.completed`), and a terminal exit stays terminal. -/
def executeExitF (P : Prims types) (args : Args types)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    Outcome (World types.Extra) types.InfoResource (Owned.Array.Failure × types.Unwind)
      types.Terminal →
    Option (Outcome (World types.Extra) (Except Token.Error types.InfoResource) types.Unwind
      types.Terminal)
  | .returned resource after => some (.returned (.ok resource) after)
  | .unwound (failure, reason) after =>
    cleanupF P.dbl (instructionDropsF P instruction ++ executeRemainderF P args failure.completed)
      (.unwound reason after)
  | .terminated reason => some (.terminated reason)

/-- `executeInfos`, computed: the five-element literal of the four moved
arguments and a clone of the validation account, then `executeExitF`. -/
def executeInfosF (P : Prims types) (args : Args types) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    RunF types types.InfoResource :=
  fun s => (Owned.Array.runDetailedF P.array 5 (executeInfoAtF P args validation) s).bind
    (executeExitF P args instruction)

/-- `executeInfos types args validation instruction` admits exactly
`executeInfosF P args validation instruction` when the literal work never
answers `.again`. -/
theorem executeInfos_fn (P : Prims types)
    (args : Args types) (validation : AccountInfo.Value)
    (instruction : Instruction.OwnedValue types.MetaResource types.ByteResource) :
    RFn (executeInfos types args validation instruction)
      (executeInfosF P args validation instruction) := by
  have hd := Owned.Array.runDetailed_fn P.array P.noAgain (executeInfoAt_fn P args validation) 5
  have hc := fun completed => cleanup_fn (V := Except Token.Error types.InfoResource)
    P.double_fn _ _ (All2.append (instructionDrops_fn P instruction)
      (executeRemainder_fn P args completed))
  have hx : ∀ detailed o, (match detailed with
      | .returned resource after => o = .returned (.ok resource) after
      | .unwound (failure, reason) after =>
        Owned.cleanup types.doubleUnwind
          (instructionDrops types instruction ++ executeRemainder types args failure.completed)
          (.unwound reason after) o
      | .terminated reason => o = .terminated reason) ↔
      executeExitF P args instruction detailed = some o := by
    intro detailed o
    match detailed with
    | .returned resource after => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩
    | .unwound (failure, reason) after => exact hc failure.completed _ o
    | .terminated reason => exact ⟨fun e => by rw [e]; rfl, fun e => (Option.some.inj e).symm⟩
  intro s o
  constructor
  · rintro ⟨detailed, hdet, hm⟩
    show (Owned.Array.runDetailedF _ _ _ s).bind _ = _
    rw [(hd s detailed).1 hdet, Option.bind_some]
    exact (hx detailed o).1 hm
  · intro e
    cases hr : Owned.Array.runDetailedF P.array 5 (executeInfoAtF P args validation) s with
    | none => simp [executeInfosF, hr] at e
    | some detailed =>
      simp only [executeInfosF, hr, Option.bind_some] at e
      exact ⟨detailed, (hd s detailed).2 hr, (hx detailed o).2 e⟩

/-- `hookEntry`, computed: the PDA search over the fixed validation seeds, then
the program lookup (`IncorrectAccount` when absent) and the optional validation
lookup. -/
def hookEntryF (P : Prims types) (args : Args types) (programId : Solanalib.Runtime.Pubkey) :
    RunF types (Solanalib.Runtime.Pubkey × AccountInfo.Value × Option AccountInfo.Value) :=
  bindR (performR fun s => findPdaF P s (hookPdaInputs args programId))
    fun (validationKey, _) =>
    match args.additional.find? (fun info => info.key == programId) with
    | none => failR Token.Hook.incorrectHookAccount
    | some program => pureR (validationKey, program,
        args.additional.find? (fun info => info.key == validationKey))

/-- `hookEntry types args programId` admits exactly `hookEntryF P args programId`. -/
theorem hookEntry_fn (P : Prims types) (args : Args types) (programId : Solanalib.Runtime.Pubkey) :
    RFn (hookEntry types args programId) (hookEntryF P args programId) := by
  refine bindR_fn (performCall_fn (findPda_fn P) _) fun ⟨validationKey, _⟩ => ?_
  show RFn (match args.additional.find? (fun info => info.key == programId) with
      | none => _ | some program => _)
    (match args.additional.find? (fun info => info.key == programId) with
      | none => _ | some program => _)
  cases args.additional.find? (fun info => info.key == programId) with
  | none => exact failR_fn _
  | some program => exact pureR_fn _

/-! ## The Execute instruction -/

/-- `executeInstruction`, computed: an empty byte vector, two extends (the
Execute discriminator, then the amount) and the four-element metadata literal,
with the byte vector dropped on any exit but `Ok`. -/
def executeInstructionF (P : Prims types) (args : Args types) (programId :
  Solanalib.Runtime.Pubkey) :
    RunF types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  fun before =>
    let (data, after) := types.bytes.empty before
    moveOnOkR P.dbl [P.bytes.dropActionF data]
      (bindR (performR fun s => P.bytes.extendF s (data, Token.Hook.executeDiscriminator)) fun _ =>
       bindR (performR fun s => P.bytes.extendF s (data, Solanalib.Runtime.u64le
         args.amount.toNat)) fun _ =>
       bindR (performR fun s => P.metas.fromListF s
         ([args.source.key, args.mint.key, args.destination.key, args.authority.key].map
           fun key => Instruction.accountMeta key false false)) fun metas =>
         pureR ⟨programId, metas, data⟩) after

/-- `executeInstruction types args programId` admits exactly
`executeInstructionF P args programId`. -/
theorem executeInstruction_fn (P : Prims types) (args : Args types)
    (programId : Solanalib.Runtime.Pubkey) :
    RFn (executeInstruction types args programId) (executeInstructionF P args programId) := by
  intro s o
  unfold executeInstruction executeInstructionF
  generalize types.bytes.empty s = created
  obtain ⟨data, after⟩ := created
  exact moveOnOkR_fn P.double_fn (.cons (P.bytes.dropAction_fn data) .nil)
    (bindR_fn (performCall_fn P.bytes.extend_fn _) fun _ =>
      bindR_fn (performCall_fn P.bytes.extend_fn _) fun _ =>
        bindR_fn (performCall_fn P.metas.fromList_fn _) fun metas => pureR_fn _) after o

/-- `executePrelude`, computed: the Execute instruction, then the push of the
readonly validation meta, with the instruction dropped on any exit but `Ok`. -/
def executePreludeF (P : Prims types) (args : Args types)
    (programId validationKey : Solanalib.Runtime.Pubkey) :
    RunF types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  bindR (executeInstructionF P args programId) fun instruction =>
    moveOnOkR P.dbl (instructionDropsF P instruction)
      (bindR (performR fun s => P.metas.pushF s
        (instruction.metas, Instruction.accountMeta validationKey false false)) fun _ =>
        pureR instruction)

/-- `executePrelude types args programId validationKey` admits exactly
`executePreludeF P args programId validationKey`. -/
theorem executePrelude_fn (P : Prims types) (args : Args types)
    (programId validationKey : Solanalib.Runtime.Pubkey) :
    RFn (executePrelude types args programId validationKey)
      (executePreludeF P args programId validationKey) :=
  bindR_fn (executeInstruction_fn P args programId) fun instruction =>
    moveOnOkR_fn P.double_fn (instructionDrops_fn P instruction)
      (bindR_fn (performCall_fn P.metas.push_fn _) fun _ => pureR_fn instruction)

/-! ## Copying extras and appending readonly accounts -/

/-- `copyExtras`, computed: the metas after the five standard Execute entries
extend the metas of the transfer, then the AccountInfos after the first five extend
the AccountInfos of the transfer. A shorter or missing vector admits no outcome. -/
def copyExtrasF (P : Prims types) (transfer execute : Execute types) : RunF types Unit :=
  bindR (inspectR fun state => do
    let items ← types.metas.current state execute.instruction.metas
    if 5 ≤ items.length then some (items.drop 5) else none) fun extraMetas =>
  bindR (performR fun s => P.metas.extendF s (transfer.instruction.metas, extraMetas)) fun _ =>
  bindR (inspectR fun state => do
    let infos ← types.infos.current state execute.infos
    if 5 ≤ infos.length then some (infos.drop 5) else none) fun extraInfos =>
    performR fun s => P.infos.extendF s (transfer.infos, extraInfos)

/-- `copyExtras types transfer execute` admits exactly `copyExtrasF P transfer execute`. -/
theorem copyExtras_fn (P : Prims types) (transfer execute : Execute types) :
    RFn (copyExtras types transfer execute) (copyExtrasF P transfer execute) :=
  bindR_fn (inspectR_fn _) fun _ =>
    bindR_fn (performCall_fn P.metas.extend_fn _) fun _ =>
      bindR_fn (inspectR_fn _) fun _ => performCall_fn P.infos.extend_fn _

/-- `appendReadonly`, computed: push a readonly nonsigner meta for `key`, then
clone `info` and push the clone. -/
def appendReadonlyF (P : Prims types) (prepared : Execute types) (key : Solanalib.Runtime.Pubkey)
    (info : AccountInfo.Value) : RunF types Unit :=
  bindR (performR fun s => P.metas.pushF s
    (prepared.instruction.metas, Instruction.accountMeta key false false)) fun _ =>
    pushClonedInfoF P prepared.infos info

/-- `appendReadonly types prepared key info` admits exactly
`appendReadonlyF P prepared key info`. -/
theorem appendReadonly_fn (P : Prims types) (prepared : Execute types) (key :
  Solanalib.Runtime.Pubkey)
    (info : AccountInfo.Value) :
    RFn (appendReadonly types prepared key info) (appendReadonlyF P prepared key info) :=
  bindR_fn (performCall_fn P.metas.push_fn _) fun _ => pushClonedInfo_fn P prepared.infos info

/-! ## The helper -/

/-- `addHook`, computed, given the computed Execute account array
`executeInfosF` and the computed extra-account resolution `addExtraListF`.
The steps and their cleanup lists follow `addHook` one for one. -/
def addHookF (P : Prims types)
    (executeInfosF : Args types → AccountInfo.Value →
      Instruction.OwnedValue types.MetaResource types.ByteResource →
      RunF types types.InfoResource)
    (addExtraListF : Args types → Execute types → Token.AllocatedControl.DataRef → RunF types Unit)
    (args : Args types) (programId : Solanalib.Runtime.Pubkey) (transfer : Execute types) :
    RunF types Unit :=
  bindR (moveOnOkR P.dbl (argumentDropsF P args) (hookEntryF P args programId))
    fun (validationKey, program, validation) =>
    match validation with
    | none => scopeR P.dbl (argumentDropsF P args) (appendReadonlyF P transfer programId program)
    | some validationInfo =>
      bindR (moveOnOkR P.dbl (argumentDropsF P args)
        (executePreludeF P args programId validationKey)) fun instruction =>
      bindR (executeInfosF args validationInfo instruction) fun infos =>
        let execute : Execute types := ⟨instruction, infos⟩
        bindR (scopeR P.dbl (instructionDropsF P instruction)
          (scopeR P.dbl [P.infos.dropActionF infos]
            (bindR (withDataF P validationInfo
              (addExtraListF args execute)) fun _ =>
             bindR (copyExtrasF P transfer execute) fun _ =>
               appendReadonlyF P transfer validationKey validationInfo))) fun _ =>
          appendReadonlyF P transfer programId program

/-- `addHook types args programId transfer` admits exactly
`addHookF P executeInfosF addExtraListF args programId transfer`, given that
`executeInfos` and `addExtraList` admit exactly their computed forms at every
argument. -/
theorem addHook_fn (P : Prims types)
    {executeInfosF : Args types → AccountInfo.Value →
      Instruction.OwnedValue types.MetaResource types.ByteResource →
      RunF types types.InfoResource}
    (he : ∀ args validation instruction, RFn (executeInfos types args validation instruction)
      (executeInfosF args validation instruction))
    {addExtraListF : Args types → Execute types → Token.AllocatedControl.DataRef → RunF types Unit}
    (hx : ∀ args execute reference, RFn (addExtraList types args execute reference)
      (addExtraListF args execute reference))
    (args : Args types) (programId : Solanalib.Runtime.Pubkey) (transfer : Execute types) :
    RFn (addHook types args programId transfer)
      (addHookF P executeInfosF addExtraListF args programId transfer) := by
  refine bindR_fn (moveOnOkR_fn P.double_fn (argumentDrops_fn P args)
    (hookEntry_fn P args programId)) fun ⟨validationKey, program, validation⟩ => ?_
  cases validation with
  | none =>
    exact scopeR_fn P.double_fn (argumentDrops_fn P args)
      (appendReadonly_fn P transfer programId program)
  | some validationInfo =>
    exact bindR_fn (moveOnOkR_fn P.double_fn (argumentDrops_fn P args)
      (executePrelude_fn P args programId validationKey)) fun instruction =>
      bindR_fn (he args validationInfo instruction) fun infos =>
        bindR_fn (scopeR_fn P.double_fn (instructionDrops_fn P instruction)
          (scopeR_fn P.double_fn (.cons (P.infos.dropAction_fn infos) .nil)
            (bindR_fn (withData_fn P validationInfo _ _ (hx args ⟨instruction, infos⟩)) fun _ =>
             bindR_fn (copyExtras_fn P transfer ⟨instruction, infos⟩) fun _ =>
               appendReadonly_fn P transfer validationKey validationInfo))) fun _ =>
          appendReadonly_fn P transfer programId program


def fullRunF (P : Prims types) (before : World types.Extra) (args : Args types) :=
  addHookF P (executeInfosF P)
    (fun args execute reference => addExtraListF P args execute
      (fun reference state =>
        AllocatedTlv.validateF
          P.discriminators P.dbl reference.read state ())
      (extraSliceF P) reference)
    args args.programId ⟨args.instruction, args.infos⟩ before

/-- The complete executable checker is equivalent to the registered relation
at every supplied primitive input/output interpretation. Its finite traces
cover actual borrow, allocation, cleanup and source mutation order. -/
theorem fullRun_fn (P : Prims types) : Fn (run types) (fullRunF P) := by
  intro before args outcome
  exact addHook_fn P (executeInfos_fn P)
    (fun args execute reference => addExtraList_fn P args execute
      (fun reference => call_fn
        (AllocatedTlv.validate_fn
          P.discriminators P.double_fn reference.read) ())
      (extraSlice_fn P) reference)
    args args.programId ⟨args.instruction, args.infos⟩ before outcome

end SolanalibTest.Conformance.Library.Families.TransferHookResolution
