/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

/-!
# The transfer-hook helper of the Token-2022 onchain model, computed

`Token.OnchainAllocated.addHook` (spl-token-2022 11.0.0
`onchain::add_extra_accounts_for_execute_cpi`) finds the validation PDA and the
hook program among the additional accounts, builds the Execute instruction and
its account array, resolves the extra accounts from the validation data, copies
them back into the transfer and appends the validation and program accounts.
This module computes each of its steps over any `types` with a `P : Prims types`:

- `hookEntryF`: the PDA search (`OnchainPrims.findPdaF`) and the program and
  validation lookups;
- `executeInstructionF` and `executePreludeF`: the Execute instruction and the
  validation meta appended to it;
- `copyExtrasF`: the copy of the resolved extra metas and AccountInfos;
- `appendReadonlyF`: a readonly meta, then a cloned AccountInfo
  (`OnchainRc.pushClonedInfoF`);
- `addHookF`: the helper itself.

Two steps of `addHook` belong to other components: the Execute account array
(`executeInfos`, a literal-array constructor) and the extra-account resolution
(`addExtraList`, which runs the collection dependency). `addHookF` takes their
computed forms as arguments and `addHook_fn` takes their `RFn` lemmas as
hypotheses, quantified over every argument, so that the caller can supply the
lemmas of those components.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainHook

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

variable {types : Types} {deps : Dependencies types}

/-! ## Entry: PDA search and account lookups -/

/-- `hookEntry`, computed: the PDA search over the fixed validation seeds, then
the program lookup (`IncorrectAccount` when absent) and the optional validation
lookup. -/
def hookEntryF (P : Prims types) (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey) :
    RunF types (Solanalib.Runtime.Pubkey × AccountInfo.Value × Option AccountInfo.Value) :=
  bindR (performR fun s => findPdaF P s (hookPdaInputs args programId))
    fun (validationKey, _) =>
    match args.additional.find? (fun info => info.key == programId) with
    | none => failR Hook.incorrectHookAccount
    | some program => pureR (validationKey, program,
        args.additional.find? (fun info => info.key == validationKey))

/-- `hookEntry types args programId` admits exactly `hookEntryF P args programId`. -/
theorem hookEntry_fn (P : Prims types) (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey)
  :
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
def executeInstructionF (P : Prims types) (args : Onchain.Args) (programId :
  Solanalib.Runtime.Pubkey) :
    RunF types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  fun before =>
    let (data, after) := types.bytes.empty before
    moveOnOkR P.dbl [P.bytes.dropActionF data]
      (bindR (performR fun s => P.bytes.extendF s (data, Hook.executeDiscriminator)) fun _ =>
       bindR (performR fun s => P.bytes.extendF s (data, Solanalib.Runtime.u64le args.amount)) fun
         _ =>
       bindR (performR fun s => P.metas.fromListF s
         ([args.source.key, args.mint.key, args.destination.key, args.authority.key].map
           fun key => Instruction.accountMeta key false false)) fun metas =>
         pureR ⟨programId, metas, data⟩) after

/-- `executeInstruction types args programId` admits exactly
`executeInstructionF P args programId`. -/
theorem executeInstruction_fn (P : Prims types) (args : Onchain.Args)
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
def executePreludeF (P : Prims types) (args : Onchain.Args)
    (programId validationKey : Solanalib.Runtime.Pubkey) :
    RunF types (Instruction.OwnedValue types.MetaResource types.ByteResource) :=
  bindR (executeInstructionF P args programId) fun instruction =>
    moveOnOkR P.dbl (instructionDropsF P instruction)
      (bindR (performR fun s => P.metas.pushF s
        (instruction.metas, Instruction.accountMeta validationKey false false)) fun _ =>
        pureR instruction)

/-- `executePrelude types args programId validationKey` admits exactly
`executePreludeF P args programId validationKey`. -/
theorem executePrelude_fn (P : Prims types) (args : Onchain.Args)
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
def copyExtrasF (P : Prims types) (transfer execute : Prepared types) : RunF types Unit :=
  bindR (inspectR fun state => do
    let items ← types.metas.current state execute.instruction.metas
    if 5 ≤ items.length then some (items.drop 5) else none) fun extraMetas =>
  bindR (performR fun s => P.metas.extendF s (transfer.instruction.metas, extraMetas)) fun _ =>
  bindR (inspectR fun state => do
    let infos ← types.infos.current state execute.infos
    if 5 ≤ infos.length then some (infos.drop 5) else none) fun extraInfos =>
    performR fun s => P.infos.extendF s (transfer.infos, extraInfos)

/-- `copyExtras types transfer execute` admits exactly `copyExtrasF P transfer execute`. -/
theorem copyExtras_fn (P : Prims types) (transfer execute : Prepared types) :
    RFn (copyExtras types transfer execute) (copyExtrasF P transfer execute) :=
  bindR_fn (inspectR_fn _) fun _ =>
    bindR_fn (performCall_fn P.metas.extend_fn _) fun _ =>
      bindR_fn (inspectR_fn _) fun _ => performCall_fn P.infos.extend_fn _

/-- `appendReadonly`, computed: push a readonly nonsigner meta for `key`, then
clone `info` and push the clone. -/
def appendReadonlyF (P : Prims types) (prepared : Prepared types) (key : Solanalib.Runtime.Pubkey)
    (info : AccountInfo.Value) : RunF types Unit :=
  bindR (performR fun s => P.metas.pushF s
    (prepared.instruction.metas, Instruction.accountMeta key false false)) fun _ =>
    pushClonedInfoF P prepared.infos info

/-- `appendReadonly types prepared key info` admits exactly
`appendReadonlyF P prepared key info`. -/
theorem appendReadonly_fn (P : Prims types) (prepared : Prepared types) (key :
  Solanalib.Runtime.Pubkey)
    (info : AccountInfo.Value) :
    RFn (appendReadonly types prepared key info) (appendReadonlyF P prepared key info) :=
  bindR_fn (performCall_fn P.metas.push_fn _) fun _ => pushClonedInfo_fn P prepared.infos info

/-! ## The helper -/

/-- `addHook`, computed, given the computed Execute account array
`executeInfosF` and the computed extra-account resolution `addExtraListF`.
The steps and their cleanup lists follow `addHook` one for one. -/
def addHookF (P : Prims types)
    (executeInfosF : Onchain.Args → AccountInfo.Value →
      Instruction.OwnedValue types.MetaResource types.ByteResource →
      RunF types types.InfoResource)
    (addExtraListF : Onchain.Args → Prepared types → AllocatedControl.DataRef → RunF types Unit)
    (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey) (transfer : Prepared types) :
    RunF types Unit :=
  bindR (moveOnOkR P.dbl (argumentDropsF P args) (hookEntryF P args programId))
    fun (validationKey, program, validation) =>
    match validation with
    | none => scopeR P.dbl (argumentDropsF P args) (appendReadonlyF P transfer programId program)
    | some validationInfo =>
      bindR (moveOnOkR P.dbl (argumentDropsF P args)
        (executePreludeF P args programId validationKey)) fun instruction =>
      bindR (executeInfosF args validationInfo instruction) fun infos =>
        let execute : Prepared types := ⟨instruction, infos⟩
        bindR (scopeR P.dbl (instructionDropsF P instruction)
          (scopeR P.dbl [P.infos.dropActionF infos]
            (bindR (withDataR P.raiseF P.dbl true validationInfo
              (addExtraListF args execute)) fun _ =>
             bindR (copyExtrasF P transfer execute) fun _ =>
               appendReadonlyF P transfer validationKey validationInfo))) fun _ =>
          appendReadonlyF P transfer programId program

/-- `addHook types deps args programId transfer` admits exactly
`addHookF P executeInfosF addExtraListF args programId transfer`, given that
`executeInfos` and `addExtraList` admit exactly their computed forms at every
argument. -/
theorem addHook_fn (P : Prims types)
    {executeInfosF : Onchain.Args → AccountInfo.Value →
      Instruction.OwnedValue types.MetaResource types.ByteResource →
      RunF types types.InfoResource}
    (he : ∀ args validation instruction, RFn (executeInfos types args validation instruction)
      (executeInfosF args validation instruction))
    {addExtraListF : Onchain.Args → Prepared types → AllocatedControl.DataRef → RunF types Unit}
    (hx : ∀ args execute reference, RFn (addExtraList types deps args execute reference)
      (addExtraListF args execute reference))
    (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey) (transfer : Prepared types) :
    RFn (addHook types deps args programId transfer)
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
            (bindR_fn (withDataR_fn P.raise_fn P.double_fn true validationInfo
              (hx args ⟨instruction, infos⟩)) fun _ =>
             bindR_fn (copyExtras_fn P transfer ⟨instruction, infos⟩) fun _ =>
               appendReadonly_fn P transfer validationKey validationInfo))) fun _ =>
          appendReadonly_fn P transfer programId program

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainHook
