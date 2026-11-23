/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.World
import Solanalib.Specs.AnchorLang.accounts

/-!
# Key and dereference projections (`anchor_lang.accounts`)

The six projection families are registered as `returnsOf` of a field
projection, with an arbitrary ambient state. The checker takes as state the
input region read back and the probed lease of every cell, just before and
just after the call, so a record also checks that the projection changes no
account and holds no borrow. The wrapper is built from the account of the record
(entry `account` of the input) before the call.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor.Projections

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
  SolanalibTest.Conformance.Library.Runtime

/-- The ambient state: region read back and the lease of every cell. -/
abbrev Ambient := Region × List Lease

def asAmbient (j : Json) : Result Ambient := do
  pure (← region (← field j "region"), ← asList asLease (← field j "leases"))

def ambientJson (_ : Ambient) : Json := Json.str "<ambient state>"

def projIndex (Payload : Type) : ProjectionIndex := ⟨Ambient, Payload⟩

/-- Decide a projection registered as `returnsOf` (by `rfl`). -/
def decideProjection {A V : Type} [DecidableEq V]
    (relation : Ambient → A → Outcome Ambient V Empty Empty → Prop) (project : A → V)
    (evaluated : relation = returnsOf (fun before args => (project args, before)))
    (c : Case) (args : A) (value : Json → Result V) (render : V → Json) : Result Verdict := do
  let before ← asAmbient (← field c.state "before")
  decideReturns relation (fun before args => (project args, before)) evaluated before args value
    asAmbient
    render ambientJson c.outcome

def entry (c : Case) : Result (LoaderInput × AccountInfo.Value) := do
  let input ← loaderInput (← field c.state "input")
  pure (input, ← infoAt input (← natField c.args "account"))

def asPayload (j : Json) : Result UInt64 := asU64 j

def infoKeyChecker : Checker := ofModel
  ("anchor_lang::accounts::account_info::<impl anchor_lang::Key for \
    solana_account_info::AccountInfo<'_>>::key") ([])
  "Solanalib.Specs.AnchorLang.AccountInfo.key_run"
  fun c => do
    let (_, info) ← entry c
    decideProjection (V := Solanalib.Runtime.Pubkey)
      (Solanalib.Specs.AnchorLang.AccountInfo.key_run (projIndex Unit)) infoKey rfl c info
      asPubkey pubkeyJson

def loaderKeyChecker : Checker := ofModel
  ("<anchor_lang::accounts::account_loader::AccountLoader<'_, T> as anchor_lang::Key>::key")
  ([("T", "conformance_anchor::script::Zc")])
  "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.key_run"
  fun c => do
    let (_, info) ← entry c
    decideProjection (V := Solanalib.Runtime.Pubkey)
      (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.key_run (projIndex Unit))
      (loaderKey (Payload := Unit)) rfl c ⟨info⟩ asPubkey pubkeyJson

def signerKeyChecker : Checker := ofModel
  ("<anchor_lang::accounts::signer::Signer<'_> as anchor_lang::Key>::key") ([])
  "Solanalib.Specs.AnchorLang.accounts.signer.Signer.key_run"
  fun c => do
    let (_, info) ← entry c
    decideProjection (V := Solanalib.Runtime.Pubkey)
      (Solanalib.Specs.AnchorLang.accounts.signer.Signer.key_run (projIndex Unit)) signerKey rfl c
      ⟨info⟩ asPubkey pubkeyJson

def accountDerefChecker : Checker := ofModel
  ("<anchor_lang::accounts::account::Account<'_, T> as core::ops::deref::Deref>::deref") ([(
    "T",
  "conformance_anchor::script::Scripted")])
  "Solanalib.Specs.AnchorLang.accounts.account.Account.deref_run"
  fun c => do
    let (_, info) ← entry c
    let value ← asPayload (← field c.args "value")
    decideProjection (V := UInt64) (Solanalib.Specs.AnchorLang.accounts.account.Account.deref_run
      (projIndex UInt64))
      (accountDeref (Payload := UInt64)) rfl c ⟨value, info⟩ asPayload (fun v => toJson v.toNat)

def interfaceAccountDerefChecker : Checker := ofModel
  ("<anchor_lang::accounts::interface_account::InterfaceAccount<'_, T> as \
    core::ops::deref::Deref>::deref") ([("T", "conformance_anchor::script::Scripted")])
  "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.deref_run"
  fun c => do
    let (_, info) ← entry c
    let value ← asPayload (← field c.args "value")
    let owner ← keyField c.args "owner"
    decideProjection (V := UInt64)
      (Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.deref_run (projIndex
        UInt64))
      (interfaceAccountDeref (Payload := UInt64)) rfl c ⟨⟨value, info⟩, owner⟩ asPayload
      (fun v => toJson v.toNat)

def interfaceDerefChecker : Checker := ofModel
  ("<anchor_lang::accounts::interface::Interface<'info, T> as \
    core::ops::deref::Deref>::deref")
  ([("T", "conformance_anchor::accounts::AnyProgram")])
  "Solanalib.Specs.AnchorLang.accounts.interface.Interface.deref_run"
  fun c => do
    let (_, info) ← entry c
    decideProjection (V := AccountInfo.Value)
      (Solanalib.Specs.AnchorLang.accounts.interface.Interface.deref_run (projIndex Unit))
      (interfaceDeref (Tag := Unit)) rfl c ⟨⟨info⟩⟩ asInfo infoJson

/-- The two copies of the record of the input agree. The checker builds the account
from the account list (`state.input`) and takes the ambient state from the
region read back before the call (`state.before`); the frame rule of the runner
compares the region after the call with `state.input`. So `state.before` must be
the read-back of `state.input`: every field (`observeWorld`: marker 255, flags,
the original data length, key, owner, lamports, data, rent epoch, duplicates,
instruction data, program id), zero alignment padding, spare bytes and
duplicate padding, the account count, one lease per cell and the same syscall
state. The leases are only in `state.before` (a record may hold a borrow
across the call). -/
def beforeAgrees (c : Case) : Result Bool := do
  let (input, world) ← asWorld c.state
  let b ← field c.state "before"
  let r ← field b "region"
  let (reg, leases) ← asAmbient b
  let entries := (← (← field r "accounts").getArr?).toList
  let zero (j : Json) (k : String) : Result Bool := do pure ((← asBytes (← field j k)).all (· == 0))
  let raw ← entries.allM fun e => do
    if (e.getObjVal? "duplicate_of").toOption.isSome then zero e "padding"
    else pure ((← zero e "alignment_padding") && (← zero e "spare"))
  let count ← natField r "count"
  let expected := observeWorld input (inputOwners input) world
  pure (decide (reg = expected.region) && leases.length == expected.leases.length && raw &&
    count == entries.length && (← field b "syscalls") == (← field c.state "syscalls"))

def checkers : List Checker := [infoKeyChecker, loaderKeyChecker, signerKeyChecker,
  accountDerefChecker,
  interfaceAccountDerefChecker, interfaceDerefChecker].map
    (withFrame [("no syscalls", noSyscalls), ("before agrees with input", beforeAgrees)])

end SolanalibTest.Conformance.Library.Families.Anchor.Projections
