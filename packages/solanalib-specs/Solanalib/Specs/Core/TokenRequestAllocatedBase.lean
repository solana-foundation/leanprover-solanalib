/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedLiteral
public import Solanalib.Specs.Core.TokenRequestAllocatedTlv

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated

open AllocatedControl

/-- The owner reference is read at the actual call state, after instruction
and account-vector allocations. Only token-owned accounts call data_len. -/
def isMultisig (types : Types) (info : AccountInfo.Value) : Run types Bool :=
  fun before outcome => fromStep types.raise
    (fun state => Onchain.isMultisig state
      { info with owner := types.ownerAt before.2 info.ownerRef }) before outcome

/-- This source expression clones an account before moving that new owner
into Vec::push. The push dependency owns cleanup of its moved argument on an
exceptional exit; the caller must not drop that owner a second time. -/
def pushClonedInfo (types : Types) (resource : types.InfoResource)
    (info : AccountInfo.Value) : Run types Unit :=
  bind (cloneInfo types info) fun cloned =>
    perform fun state => types.infos.push state (resource, cloned)

/-- The signers slice retains the count copied when the POD range was formed.
Its key contents are read through the live Ref on every filter call. -/
def signerKeysAt (types : Types) (reference : DataRef) (count : Nat)
    (state : World types.Extra) : Option (List Solanalib.Runtime.Pubkey) := do
  let bytes ← reference.read state
  if bytes.length = multisigLength ∧ count ≤ 11 then
    return (List.range count).map fun index =>
      Solanalib.Runtime.Pubkey.ofBytes (Solanalib.Runtime.slice bytes (3 + 32 * index) 32)
  else none

/-- The filter visits every additional account in order, preserving aliases
and duplicate signers. A metadata push precedes the clone
and info push of the matching account. Later predicates observe the actual state after those calls.
-/
def appendMultisigSigners (types : Types) (prepared : Prepared types)
    (reference : DataRef) (count : Nat) : List AccountInfo.Value → Run types Unit
  | [] => pure ()
  | info :: rest =>
    bind (inspect (signerKeysAt types reference count)) fun keys =>
      if keys.contains info.key then
        bind (perform fun state => types.metas.push state
          (prepared.instruction.metas, Instruction.accountMeta info.key true false)) fun _ =>
        bind (pushClonedInfo types prepared.infos info) fun _ =>
          appendMultisigSigners types prepared reference count rest
      else appendMultisigSigners types prepared reference count rest

/-- Recognition and the authority flag write precede the unchecked multisig
data borrow. POD length/range checks precede iteration; the data Ref is dropped
at the end of the source if block, including on error or unwind. -/
def addMultisig (types : Types) (args : Onchain.Args) (prepared : Prepared types) :
    Run types Unit :=
  bind (isMultisig types args.authority) fun recognized =>
    if !recognized then pure ()
    else bind (clearAuthoritySigner types prepared.instruction.metas) fun _ =>
      withData types.raise types.doubleUnwind false args.authority fun reference =>
        bind (inspect reference.read) fun bytes =>
        bind (fromStep types.raise fun state => (Onchain.multisigKeys bytes, state)) fun keys =>
          appendMultisigSigners types prepared reference keys.length args.additional

/-- Construct and mutate the two local vectors. Their resources move out on
Ok; an Err or unwind drops the current info vector before the instruction.
The enclosing function remains responsible for its four owned arguments. -/
def base (types : Types) (args : Onchain.Args) : Run types (Prepared types) :=
  bind (fun state => InstructionAllocated.run types.constructor state (transferPlan args))
    fun instruction =>
    moveOnOk types.doubleUnwind (instructionDrops types instruction)
      (bind (initialInfos types args) fun infos =>
        let prepared : Prepared types := ⟨instruction, infos⟩
        moveOnOk types.doubleUnwind [types.infos.dropAction infos]
          (bind (addMultisig types args prepared) fun _ => pure prepared))

/-- Base admission and initialization are checked before the source 3.0.0
padding allocation. The retained Ref supplies the actual tail observation to
that helper; the packed base itself is an owned, already decoded value. -/
def readMintHook (types : Types) (reference : DataRef) :
    Run types (Option Solanalib.Runtime.Pubkey) :=
  bind (inspect reference.read) fun bytes =>
    if extensionInputRejected mintLength bytes then fail .InvalidAccountData
    else bind (result (unpackMint (bytes.take mintLength))) fun _ =>
      bind (fun state => AllocatedTlv.mintTail types.paddingBytes types.doubleUnwind
        (fun current => (reference.read current).map (·.drop mintLength)) state ()) fun tlv =>
        pure (Onchain.hookProgram tlv)

/-- Mint borrowing begins after multisig preparation. On success its live
guard is returned for the entire hook-preparation scope. A parsing error or
unwind releases it immediately before outer vector/argument cleanup. -/
def beginMint (types : Types) (args : Onchain.Args) :
    Run types (DataRef × Option Solanalib.Runtime.Pubkey) :=
  bind (borrow types.raise true args.mint) fun reference =>
    moveOnOk types.doubleUnwind [reference.drop]
      (bind (readMintHook types reference) fun program => pure (reference, program))

end Solanalib.Specs.Core.Token.OnchainAllocated
