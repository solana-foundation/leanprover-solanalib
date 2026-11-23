/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainIndex
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainConstructor
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainLiteral
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainMultisig
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainMint
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainCollect
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainHook

/-!
# The computed Token-2022 onchain invocation

`Token.OnchainAllocated.invoke` is a relation. This module composes the
computed forms of its components into one function and proves that the
relation admits exactly the outcome that function computes.

**Generic part.** Over any `types` with a primitive bundle `P : Prims types`,
any dependencies with a bundle `D : DepPrims types deps`, and literal work that
never answers `.again`:
- `baseF P args` computes `base` (`base_fn`);
- `addHookF P D` computes `addHook`, from `OnchainLiteral.executeInfosF` and
  `OnchainCollect.addExtraListF` over the TLV validator and `extraSlice`
  (`addHook_fn`);
- `prepareF P D args` computes `prepare` (`prepare_fn`);
- `invokeR P D args` computes `invoke` (`invokeR_fn`).

**Closed index.** At `OnchainIndex.Index env`, `depPrims env` bundles the
protocol collection and the scripted CPI, and `invokeF env` is the computed
invocation of a record. `invoke_fn` is the target:
`invoke (Index env).types (Index env).dependencies a s o ↔ invokeF env s a = some o`.

Several components recurse by well-founded recursion (the literal trace, the
collection trace, the TLV validator and the seed unpacking), so `invokeF` is
meant for compiled evaluation, not for kernel reduction.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainAllocatedRun

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

/-! ## Generic composition -/

section Generic

variable {types : Types} {deps : Dependencies types}

/-- `base`, computed: the instruction constructor at the transfer plan, then,
in a `moveOnOkR` over the instruction drops, the four-element info literal and,
in a `moveOnOkR` over the drop of the info vector, the multisig signers. -/
def baseF (P : Prims types) (args : Onchain.Args) : RunF types (Prepared types) :=
  bindR (OnchainConstructor.runR P (OnchainAllocated.transferPlan args)) fun instruction =>
    moveOnOkR P.dbl (instructionDropsF P instruction)
      (bindR (OnchainLiteral.initialInfosF P args) fun infos =>
        let prepared : Prepared types := ⟨instruction, infos⟩
        moveOnOkR P.dbl [P.infos.dropActionF infos]
          (bindR (OnchainMultisig.addMultisigF P args prepared) fun _ => pureR prepared))

/-- `base types args` admits exactly `baseF P args` when the literal work never
answers `.again`. -/
theorem base_fn (P : Prims types) (hna : NoAgain types.infoLiteral) (args : Onchain.Args) :
    RFn (base types args) (baseF P args) :=
  bindR_fn (OnchainConstructor.runR_fn P (OnchainAllocated.transferPlan args)) fun instruction =>
    moveOnOkR_fn P.double_fn (instructionDrops_fn P instruction)
      (bindR_fn (OnchainLiteral.initialInfos_fn P hna args) fun infos =>
        moveOnOkR_fn P.double_fn (.cons (P.infos.dropAction_fn infos) .nil)
          (bindR_fn (OnchainMultisig.addMultisig_fn P args ⟨instruction, infos⟩) fun _ =>
            pureR_fn _))

/-- `addHook`, computed: `OnchainHook.addHookF` with the computed Execute
account array and the computed extra-account resolution over the TLV validator
and `extraSlice`. -/
def addHookF (P : Prims types) (D : DepPrims types deps) :
    Onchain.Args → Solanalib.Runtime.Pubkey → Prepared types → RunF types Unit :=
  OnchainHook.addHookF P (OnchainLiteral.executeInfosF P)
    (fun args execute reference => OnchainCollect.addExtraListF P D args execute
      (OnchainTlv.validateDataF P) (OnchainTlv.extraSliceF types) reference)

/-- `addHook types deps args programId transfer` admits exactly
`addHookF P D args programId transfer` when the literal work never answers
`.again`. -/
theorem addHook_fn (P : Prims types) (D : DepPrims types deps)
    (hna : NoAgain types.infoLiteral) (args : Onchain.Args) (programId : Solanalib.Runtime.Pubkey)
    (transfer : Prepared types) :
    RFn (addHook types deps args programId transfer) (addHookF P D args programId transfer) :=
  OnchainHook.addHook_fn P (fun a v i => OnchainLiteral.executeInfos_fn P hna a v i)
    (fun a e r => OnchainCollect.addExtraList_fn P D a e (OnchainTlv.validateData_fn P)
      (OnchainTlv.extraSlice_fn types) r) args programId transfer

/-- `prepare`, computed: `baseF` and `OnchainMint.beginMintF` under their
cleanup lists, then, with no hook, the scopes over the arguments and the mint
Ref; with a hook, the mint clone and `addHookF` under the nested scopes. -/
def prepareF (P : Prims types) (D : DepPrims types deps) (args : Onchain.Args) :
    RunF types (Prepared types) :=
  bindR (moveOnOkR P.dbl (argumentDropsF P args) (baseF P args)) fun prepared =>
  bindR (moveOnOkR P.dbl (argumentDropsF P args)
    (moveOnOkR P.dbl (preparedDropsF P prepared) (OnchainMint.beginMintF P args)))
    fun (mintReference, program) =>
    match program with
    | none => scopeR P.dbl (argumentDropsF P args)
        (scopeR P.dbl [DataRef.dropF mintReference] (pureR prepared))
    | some programId =>
      bindR (cloneInfoF P args.mint) fun mintClone =>
        scopeR P.dbl [dropInfoF P args.mint]
          (moveOnOkR P.dbl (preparedDropsF P prepared)
            (scopeR P.dbl [DataRef.dropF mintReference]
              (bindR (addHookF P D { args with mint := mintClone } programId prepared)
                fun _ => pureR prepared)))

/-- `prepare types deps args` admits exactly `prepareF P D args` when the
literal work never answers `.again`. -/
theorem prepare_fn (P : Prims types) (D : DepPrims types deps)
    (hna : NoAgain types.infoLiteral) (args : Onchain.Args) :
    RFn (prepare types deps args) (prepareF P D args) := by
  refine bindR_fn (moveOnOkR_fn P.double_fn (argumentDrops_fn P args) (base_fn P hna args))
    fun prepared => ?_
  refine bindR_fn (moveOnOkR_fn P.double_fn (argumentDrops_fn P args)
    (moveOnOkR_fn P.double_fn (preparedDrops_fn P prepared) (OnchainMint.beginMint_fn P args)))
    fun ⟨mintReference, program⟩ => ?_
  cases program with
  | none =>
    exact scopeR_fn P.double_fn (argumentDrops_fn P args)
      (scopeR_fn P.double_fn (.cons (DataRef.drop_fn mintReference) .nil) (pureR_fn prepared))
  | some programId =>
    exact bindR_fn (cloneInfo_fn P args.mint) fun mintClone =>
      scopeR_fn P.double_fn (.cons (dropInfo_fn P args.mint) .nil)
        (moveOnOkR_fn P.double_fn (preparedDrops_fn P prepared)
          (scopeR_fn P.double_fn (.cons (DataRef.drop_fn mintReference) .nil)
            (bindR_fn (addHook_fn P D hna _ programId prepared) fun _ => pureR_fn prepared)))

/-- `invoke`, computed: `prepareF`, then, in a scope over the prepared
vectors, the observation of the request and the computed CPI. -/
def invokeR (P : Prims types) (D : DepPrims types deps) (args : Onchain.Args) :
    RunF types Unit :=
  bindR (prepareF P D args) fun prepared =>
    scopeR P.dbl (preparedDropsF P prepared)
      (bindR (inspectR fun state => prepared.observe types state args.signers) fun request =>
        fun s => D.invokeF s request)

/-- `invoke types deps args` admits exactly `invokeR P D args` when the literal
work never answers `.again`. -/
theorem invokeR_fn (P : Prims types) (D : DepPrims types deps)
    (hna : NoAgain types.infoLiteral) (args : Onchain.Args) :
    RFn (invoke types deps args) (invokeR P D args) :=
  bindR_fn (prepare_fn P D hna args) fun prepared =>
    scopeR_fn P.double_fn (preparedDrops_fn P prepared)
      (bindR_fn (inspectR_fn _) fun request => call_fn D.invoke_fn request)

end Generic

/-! ## The closed index -/

/-- The dependency bundle of the closed index: the protocol collection
(`OnchainCollect.collectDepPrims` from the collection lemmas of the index) and the
scripted CPI `OnchainIndex.cpiF env`. -/
def depPrims (env : OnchainIndex.Env) :
    DepPrims (OnchainIndex.Index env).types (OnchainIndex.Index env).dependencies :=
  OnchainCollect.collectDepPrims (OnchainIndex.prims env) (protocol := OnchainIndex.collectProtocol)
    (OnchainIndex.collect_eq env) OnchainIndex.collectProtocol_internal rfl
    OnchainIndex.collectRetireF OnchainIndex.collectRetire_fn OnchainIndex.collectDouble_fn
    OnchainIndex.collectOrder_eq (OnchainIndex.cpiF env) (OnchainIndex.cpi_fn env)

/-- The computed invocation of a record: `invokeR` at the closed index
`OnchainIndex.Index env`, its primitives `OnchainIndex.prims env` and its
dependencies `depPrims env`, from the initial state `s` with the arguments `a`. -/
def invokeF (env : OnchainIndex.Env) :
    OnchainIndex.State → Onchain.Args →
      Option (Outcome OnchainIndex.State (Except Token.Error Unit) OnchainIndex.Unwind
        OnchainIndex.Terminal) :=
  fun s a => invokeR (OnchainIndex.prims env) (depPrims env) a s

/-- **The target.** At the closed index of a record, the invocation of the model
from state `s` with arguments `a` admits exactly the outcome `invokeF env s a`. -/
theorem invoke_fn (env : OnchainIndex.Env) :
    ∀ s a o, OnchainAllocated.invoke (OnchainIndex.Index env).types
      (OnchainIndex.Index env).dependencies a s o ↔ invokeF env s a = some o :=
  fun s a o => invokeR_fn (OnchainIndex.prims env) (depPrims env) (OnchainIndex.noAgain env) a s o

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainAllocatedRun
