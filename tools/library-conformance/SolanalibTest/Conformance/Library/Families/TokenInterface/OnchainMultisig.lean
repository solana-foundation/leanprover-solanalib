/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

/-!
# Multisig selection of the onchain model, computed

`Token.OnchainAllocated.addMultisig` recognises a multisig authority, clears
the signer flag of the authority in the constructed metadata, borrows the data of the
authority unchecked, reads the signer keys and appends each additional
account that matches one of them: a metadata push, then a cloned info push.
This module computes `addMultisig` and its four steps from a `Prims` bundle:

- `clearAuthoritySigner`: its witnesses are fixed by `metas.current`, the
  fourth slot and the graph `writeMetaF` of `writeMeta`, so its last conjunct,
  the exact current sequence after the write, is a decidable check;
- `isMultisig`: a `fromStep` whose step reads the owner through `ownerAt` at
  the state of the call;
- `appendMultisigSigners`, by recursion on the list of additional accounts;
- `addMultisig`, with the unchecked `withData` and the `multisigKeys` panic.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainMultisig

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainRc

variable {types : Types}

/-! ## The authority flag write -/

/-- `clearAuthoritySigner`, computed: the current metadata, its fourth slot,
the state after `writeMetaF`, and the check that the current metadata after
the write is the exact update. A failed check, an absent resource, slot or
write admits no outcome. -/
def clearAuthoritySignerF (P : Prims types) (resource : types.MetaResource) : RunF types Unit :=
  fun before =>
    (types.metas.current before resource).bind fun items =>
    items[3]?.bind fun item =>
    (P.writeMetaF before resource 3 { item with signerByte := 0 }).bind fun after =>
      if types.metas.current after resource = some (items.set 3 { item with signerByte := 0 })
      then some (.returned (.ok ()) after) else none

/-- `clearAuthoritySigner types resource` admits exactly
`clearAuthoritySignerF P resource`. -/
theorem clearAuthoritySigner_fn (P : Prims types) (resource : types.MetaResource) :
    RFn (clearAuthoritySigner types resource) (clearAuthoritySignerF P resource) := by
  intro s o
  unfold clearAuthoritySigner clearAuthoritySignerF
  constructor
  · rintro ⟨items, item, after, hc, hi, hw, ha, rfl⟩
    rw [hc, Option.bind_some, hi, Option.bind_some, (P.writeMeta_fn _ _ _ _ _).1 hw,
      Option.bind_some]
    simp only [ha, ↓reduceIte]
  · intro h
    cases hc : types.metas.current s resource with
    | none => rw [hc] at h; cases h
    | some items =>
      rw [hc, Option.bind_some] at h
      cases hi : items[3]? with
      | none => rw [hi] at h; cases h
      | some item =>
        rw [hi, Option.bind_some] at h
        cases hw : P.writeMetaF s resource 3 { item with signerByte := 0 } with
        | none => rw [hw] at h; cases h
        | some after =>
          rw [hw, Option.bind_some] at h
          by_cases ha : types.metas.current after resource =
              some (items.set 3 { item with signerByte := 0 })
          · simp only [ha, ↓reduceIte, Option.some.injEq] at h
            exact ⟨items, item, after, rfl, hi, (P.writeMeta_fn _ _ _ _ _).2 hw, ha, h.symm⟩
          · simp only [ha, ↓reduceIte] at h; cases h

/-! ## Recognition -/

/-- `isMultisig`, computed: the value-level test on the authority with the
owner read through `ownerAt` at the state of the call. -/
def isMultisigF (P : Prims types) (info : AccountInfo.Value) : RunF types Bool :=
  fun before => fromStepR P.raiseF
    (fun state => Onchain.isMultisig state
      { info with owner := types.ownerAt before.2 info.ownerRef }) before

/-- `isMultisig types info` admits exactly `isMultisigF P info`. -/
theorem isMultisig_fn (P : Prims types) (info : AccountInfo.Value) :
    RFn (isMultisig types info) (isMultisigF P info) := by
  intro s o
  exact fromStepR_fn P.raise_fn _ s o

/-! ## Appending the matching signers -/

/-- `appendMultisigSigners`, computed: for each additional account, read the
signer keys through the live data Ref; on a match push its metadata, then
push its clone. -/
def appendMultisigSignersF (P : Prims types) (prepared : Prepared types)
    (reference : AllocatedControl.DataRef) (count : Nat) :
    List AccountInfo.Value → RunF types Unit
  | [] => pureR ()
  | info :: rest =>
    bindR (inspectR (signerKeysAt types reference count)) fun keys =>
      if keys.contains info.key then
        bindR (performR fun s => P.metas.pushF s
          (prepared.instruction.metas, Instruction.accountMeta info.key true false)) fun _ =>
        bindR (pushClonedInfoF P prepared.infos info) fun _ =>
          appendMultisigSignersF P prepared reference count rest
      else appendMultisigSignersF P prepared reference count rest

/-- `appendMultisigSigners types prepared reference count additional` admits
exactly `appendMultisigSignersF P prepared reference count additional`. -/
theorem appendMultisigSigners_fn (P : Prims types) (prepared : Prepared types)
    (reference : AllocatedControl.DataRef) (count : Nat) :
    ∀ additional, RFn (appendMultisigSigners types prepared reference count additional)
      (appendMultisigSignersF P prepared reference count additional)
  | [] => pureR_fn ()
  | info :: rest =>
    bindR_fn (inspectR_fn _) fun _ =>
      iteR_fn _
        (fun _ => bindR_fn (performCall_fn P.metas.push_fn _) fun _ =>
          bindR_fn (pushClonedInfo_fn P prepared.infos info) fun _ =>
            appendMultisigSigners_fn P prepared reference count rest)
        (fun _ => appendMultisigSigners_fn P prepared reference count rest)

/-! ## Multisig selection -/

/-- `addMultisig`, computed: recognition; for a multisig authority, the flag
write, then the unchecked data borrow scoped around the key read and the
appended signers. -/
def addMultisigF (P : Prims types) (args : Onchain.Args) (prepared : Prepared types) :
    RunF types Unit :=
  bindR (isMultisigF P args.authority) fun recognized =>
    if !recognized then pureR ()
    else bindR (clearAuthoritySignerF P prepared.instruction.metas) fun _ =>
      withDataR P.raiseF P.dbl false args.authority fun reference =>
        bindR (inspectR reference.read) fun bytes =>
        bindR (fromStepR P.raiseF fun state => (Onchain.multisigKeys bytes, state)) fun keys =>
          appendMultisigSignersF P prepared reference keys.length args.additional

/-- `addMultisig types args prepared` admits exactly `addMultisigF P args prepared`. -/
theorem addMultisig_fn (P : Prims types) (args : Onchain.Args) (prepared : Prepared types) :
    RFn (addMultisig types args prepared) (addMultisigF P args prepared) :=
  bindR_fn (isMultisig_fn P args.authority) fun _ =>
    iteR_fn _ (fun _ => pureR_fn ()) fun _ =>
      bindR_fn (clearAuthoritySigner_fn P prepared.instruction.metas) fun _ =>
        withDataR_fn P.raise_fn P.double_fn false args.authority fun reference =>
          bindR_fn (inspectR_fn _) fun _ =>
            bindR_fn (fromStepR_fn P.raise_fn _) fun keys =>
              appendMultisigSigners_fn P prepared reference keys.length args.additional

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainMultisig
