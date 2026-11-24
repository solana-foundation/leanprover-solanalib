/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Common
import SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
import SolanalibTest.Conformance.Library.Families.TokenInterface.Fees
import Solanalib.Specs.SplToken2022Interface.Extensions

/-!
# Extension unpacking, lookup, listing and sizing (spl-token-2022-interface 3.1.1)

Four Rust functions, seven registered models:

* `try_calculate_account_len_from_mint_data`: the pure reference
  `calculateAccountLengthReference`, decided as its graph.
* `BaseStateWithExtensions::get_extension_types` at `S = Mint, Account`: the
  pure list observation `getExtensionTypesReference` (state: the TLV bytes)
  and the operational family `get_extension_types_operational_run`, decided at
  the registered reader `extensionTypeReaderReference bytes` (the TLV
  bytes of the record, the vector ledger, from the empty ledger) through `types_fn`; the
  returned vector is read through the `current` of the ledger.
* `BaseStateWithExtensions::get_extension` at `S` and `V`: the default-lookup
  observation `get_extension_run` (graph of a function, by `rfl`) and the
  operational getter `get_extension_operational_run` at the index
  `⟨representation, defaultExtensionByteProvider⟩` through `getter_iff`.
  `V = TransferFeeConfig` uses the registered `transferFeeConfigRepresentation`;
  other `V` use a raw-bytes representation with the tag of `V` and size (alignment
  one, as for every production extension).
* `StateWithExtensions::<S>::unpack` at `S = Mint, Account`: the value
  observation `unpack_run` at `mintExtensionParser`/`accountExtensionParser`
  (graph lemma `unpackStateWithExtensions_iff` of the model) and the
  operational family `unpack_operational_run` at
  `mintExtensionUnpacker`/`accountExtensionUnpacker` through `unpack_iff`.
  The record keeps the returned TLV reference as `null` (the static
  empty literal of the source) or the offset and length of the input range.

Where two models observe one function, one checker decides both.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.SplToken2022Interface.extension
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional

def extensionType (j : Json) : Result ExtensionType := do
  let n ← asUInt 16 j
  match ExtensionType.decode n with
  | some t => pure t
  | none => throw s!"unknown extension type {n}"

def typesJson (types : List ExtensionType) : Json :=
  Json.arr (types.map fun t => Lean.toJson t.tag).toArray

/-! ## Account length -/

theorem account_len_evaluated :
    account_len.calculateAccountLengthReference =
      fun s a => (calculateAccountLengthFromMint a.mintData a.additional, s) := rfl

def accountLenChecker : Checker where
  function :=
    "spl_token_2022_interface::extension::account_len::try_calculate_account_len_from_mint_\
      data"
  generics := []
  reference :=
    "Solanalib.Specs.SplToken2022Interface.extension.account_len.calculateAccountLengthRefe\
      rence"
  decides :=
    ["Solanalib.Specs.SplToken2022Interface.extension.account_len.calculateAccountLengthRef\
      erence"]
  check := fun c => do
    let args : account_len.Arguments :=
      ⟨← asBytes (← field c.args "mint_data"), ← listField c.args "additional" extensionType⟩
    decideReturns (returnsOf account_len.calculateAccountLengthReference)
      account_len.calculateAccountLengthReference rfl (← unitState c.state) args
      (resultOf fun j => j.getNat?) unitState (resultJson Lean.toJson) (fun _ => Json.null)
        c.outcome

/-! ## Type listing -/

abbrev Ledger := Owned.VectorState ExtensionType
abbrev TOut := Outcome Ledger (Except Token.Error Nat) Empty Empty

def dblE (_ : Ledger) (o : Empty) (_ : Empty) : Empty := o

theorem doubleE_fn : ∀ s o l t, (fun (_ : Ledger) (_ _ : Empty) (_ : Empty) => False) s o l t ↔ t =
  dblE s o l :=
  fun _ o _ _ => o.elim

def collectF (len : Nat) (byteAt : Ledger → Fin len → UInt8) (resource offset : Nat) (before :
  Ledger) :
    Option TOut :=
  match _h : nextExtension ((currentExtensionBytes len byteAt before).drop offset) with
  | .done => some (.returned (.ok resource) before)
  | .invalid => cleanupF dblE [fun st => retireF st resource] (.returned (.error
    .InvalidAccountData) before)
  | .next kind consumed _ =>
    (modifyF before resource (· ++ [kind])).bind fun pushed =>
      match pushed with
      | .returned () after => collectF len byteAt resource (offset + consumed) after
      | .unwound r after => cleanupF dblE [fun st => retireF st resource] (.unwound r after)
      | .terminated r => some (.terminated r)
termination_by len - offset
decreasing_by
  have geometry := nextExtension_next_geometry _ _ _ _ (by assumption)
  simp only [List.length_drop, currentExtensionBytes_length] at geometry
  omega

theorem drops_fn (resource : Nat) :
    All2 DFn [(Owned.vectorReference : Owned.VectorOps Ledger ExtensionType Nat Empty
      Empty).dropAction resource]
      [fun st => retireF st resource] :=
  .cons (fun s o => retire_fn s resource o) .nil

theorem collect_fn (len : Nat) (byteAt : Ledger → Fin len → UInt8) (resource offset : Nat)
    (before : Ledger) (o : TOut) :
    collectCurrentExtensionTypes Owned.vectorReference (fun _ _ _ _ => False) resource len byteAt
      offset before o ↔ collectF len byteAt resource offset before = some o := by
  cases hs : nextExtension ((currentExtensionBytes len byteAt before).drop offset) with
  | done =>
    have hl : collectF len byteAt resource offset before = some (.returned (.ok resource) before)
      := by
      rw [collectF]; split <;> simp_all
    have hr : collectCurrentExtensionTypes Owned.vectorReference (fun _ _ _ _ => False) resource len
        byteAt offset before o ↔ o = .returned (.ok resource) before := by
      rw [collectCurrentExtensionTypes]; split <;> simp_all
    rw [hl, hr]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | invalid =>
    have hl : collectF len byteAt resource offset before =
        cleanupF dblE [fun st => retireF st resource] (.returned (.error .InvalidAccountData)
          before) := by
      rw [collectF]; split <;> simp_all
    have hr : collectCurrentExtensionTypes Owned.vectorReference (fun _ _ _ _ => False) resource len
        byteAt offset before o ↔ Owned.cleanup (fun _ _ _ _ => False)
          [(Owned.vectorReference : Owned.VectorOps Ledger ExtensionType Nat Empty
            Empty).dropAction resource]
          (.returned (.error .InvalidAccountData) before) o := by
      rw [collectCurrentExtensionTypes]; split <;> simp_all
    rw [hl, hr]
    exact cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _
  | next kind consumed tail =>
    rw [collectCurrentExtensionTypes_next_iff _ _ _ _ _ _ _ kind consumed tail o hs]
    have hl : collectF len byteAt resource offset before =
        (modifyF before resource (· ++ [kind])).bind fun pushed =>
          match pushed with
          | .returned () after => collectF len byteAt resource (offset + consumed) after
          | .unwound r after => cleanupF dblE [fun st => retireF st resource] (.unwound r after)
          | .terminated r => some (.terminated r) := by
      rw [collectF]; split <;> simp_all
    rw [hl]
    constructor
    · rintro ⟨pushed, hp, hm⟩
      rw [(modify_fn before resource (· ++ [kind]) pushed).1 hp, Option.bind_some]
      cases pushed with
      | returned u after =>
        cases u; exact (collect_fn len byteAt resource (offset + consumed) after o).1 hm
      | unwound r _ => exact r.elim
      | terminated r => exact r.elim
    · intro h
      cases hm : modifyF before resource (· ++ [kind]) with
      | none => rw [hm] at h; cases h
      | some pushed =>
        rw [hm, Option.bind_some] at h
        refine ⟨pushed, (modify_fn before resource (· ++ [kind]) pushed).2 hm, ?_⟩
        cases pushed with
        | returned u after =>
          cases u; exact (collect_fn len byteAt resource (offset + consumed) after o).2 h
        | unwound r _ => exact r.elim
        | terminated r => exact r.elim
termination_by len - offset
decreasing_by
  all_goals
    have geometry := nextExtension_next_geometry _ _ _ _ hs
    simp only [List.length_drop, currentExtensionBytes_length] at geometry
    omega

abbrev Reader (bytes : Bytes) : CurrentExtensionTypeReader :=
  extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty) bytes

def typesF (bytes : Bytes) : Option TOut :=
  collectF bytes.length (fun _ index => bytes[index.val]) 0 0 [some []]

/-- At the registered reader for these bytes, from the empty ledger, the
operational listing admits exactly `typesF`. -/
theorem types_fn (bytes : Bytes) (o : TOut) :
    BaseStateWithExtensions.get_extension_types_operational_run (Reader bytes) [] () o ↔
      typesF bytes = some o := by
  show (∃ accessed, accessed = Outcome.returned () [] ∧ _) ↔ _
  constructor
  · rintro ⟨accessed, rfl, h⟩
    exact (collect_fn _ _ 0 0 [some []] o).1 h
  · intro h
    exact ⟨_, rfl, (collect_fn _ _ 0 0 [some []] o).2 h⟩

def typesObs : TOut → Option (Except Token.Error (List ExtensionType))
  | .returned (.ok r) s => (s.current r).map .ok
  | .returned (.error e) _ => some (.error e)
  | .unwound r _ => r.elim
  | .terminated r => r.elim

theorem types_admits_iff (bytes : Bytes) (recorded : Except Token.Error (List ExtensionType)) :
    (∃ o, BaseStateWithExtensions.get_extension_types_operational_run (Reader bytes) [] () o ∧
      typesObs o = some recorded) ↔ (typesF bytes).bind typesObs = some recorded := by
  constructor
  · rintro ⟨o, ho, hobs⟩
    rw [(types_fn bytes o).1 ho]
    exact hobs
  · intro h
    cases hf : typesF bytes with
    | none => rw [hf] at h; cases h
    | some o =>
      rw [hf] at h
      exact ⟨o, (types_fn bytes o).2 hf, h⟩

theorem types_evaluated :
    BaseStateWithExtensions.getExtensionTypesReference = fun s _ => (getExtensionTypes s, s) := rfl

def tlvState (j : Json) : Result Bytes := do asBytes (← field j "tlv")

def typesChecker (s : String) : Checker :=
  pairChecker "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension_\
    types"
    [("S", s)]
    "Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_\
      types_operational_run"
    "Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.getExtensionTy\
      pesReference" fun c => do
    let bytes ← tlvState c.state
    let _ ← unitState c.args
    let expected := returnedJson (resultJson typesJson (getExtensionTypes bytes))
      (Json.mkObj [("tlv", bytesJson bytes)])
    match ← (← field c.outcome "exit").getStr? with
    | "returned" =>
      let result ← resultOf (fun j => do (← j.getArr?).toList.mapM extensionType) (← field
        c.outcome "result")
      let after ← tlvState (← field c.outcome "state")
      have : Decidable (∃ o, BaseStateWithExtensions.get_extension_types_operational_run (Reader
        bytes) [] () o ∧
          typesObs o = some result) := decidable_of_iff _ (types_admits_iff bytes result).symm
      let operationalOk := decide (∃ o,
        BaseStateWithExtensions.get_extension_types_operational_run (Reader bytes) [] () o ∧
          typesObs o = some result)
      let valueOk := decide (returnsOf BaseStateWithExtensions.getExtensionTypesReference bytes ()
        (Outcome.returned (Unwind := Empty) (Terminal := Empty) result after))
      return (operationalOk, valueOk, expected)
    | _ => return (false, false, expected)

/-! ## Lookup -/

/-- A representation index with decidable equality of its observed values. -/
structure Rep where
  rust : String
  representation : ExtensionRepresentation
  decEq : DecidableEq representation.Value
  parse : Json → Result representation.Value
  render : representation.Value → Json

def rawRep (rust : String) (kind : ExtensionType) (size : Nat) : Rep where
  rust := rust
  representation := ⟨Bytes, ⟨kind, size, 1⟩, id⟩
  decEq := inferInstanceAs (DecidableEq Bytes)
  parse := fun j => do asBytes (← field j "bytes")
  render := fun b => Json.mkObj [("bytes", bytesJson b)]

def feeConfigRep : Rep where
  rust := "spl_token_2022_interface::extension::transfer_fee::TransferFeeConfig"
  representation := transferFeeConfigRepresentation
  decEq := inferInstanceAs (DecidableEq TransferFeeConfig)
  parse := fun j => do Fees.transferFeeConfig (← field j "value")
  render := fun v => Json.mkObj [("value", Fees.transferFeeConfigJson v)]

def accountTypeOf : String → ExtensionAccountType
  | "spl_token_2022_interface::state::Account" => .account
  | _ => .mint

/-- With the default byte provider, the operational getter admits exactly the
default lookup and cast, with the receiver unchanged. -/
theorem getter_iff (representation : ExtensionRepresentation) (receiver : ExtensionReceiver)
    (o : Outcome ExtensionReceiver
      (Except Token.Error (TypedExtensionReference LocatedExtensionView representation.Value))
        Empty Empty) :
    BaseStateWithExtensions.get_extension_operational_run ⟨representation,
      defaultExtensionByteProvider⟩
        receiver () o ↔
      Outcome.returned (getDefaultExtension representation receiver) receiver = o := by
  constructor
  · rintro ⟨called, hc, rfl⟩
    cases called with
    | returned v st =>
      have e : (defaultExtensionBytes receiver representation.pod, receiver) = (v, st) := hc
      cases e
      cases hd : defaultExtensionBytes receiver representation.pod <;>
        simp [getDefaultExtension, hd, finishExtensionGetter, Except.bind] <;> rfl
    | unwound r _ => exact r.elim
    | terminated r => exact r.elim
  · intro h
    rw [← h]
    exact getDefaultExtension_execution representation receiver

theorem get_extension_evaluated (representation : ExtensionRepresentation) :
    BaseStateWithExtensions.get_extension_run representation =
      returnsOf fun before _ =>
        (getRepresentedExtension representation before.accountType before.address before.bytes,
          before) :=
  rfl

def receiverState (accountType : ExtensionAccountType) (j : Json) : Result ExtensionReceiver := do
  pure ⟨accountType, ← natField j "address", ← tlvState j⟩

def getterChecker (s : String) (rep : Rep) : Checker :=
  pairChecker "spl_token_2022_interface::extension::BaseStateWithExtensions::get_extension" [(
    "S",
    s), ("V", rep.rust)]
    "Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_\
      operational_run"
    "Solanalib.Specs.SplToken2022Interface.extension.BaseStateWithExtensions.get_extension_\
      run" fun
      c => do
    let r := rep.representation
    have : DecidableEq r.Value := rep.decEq
    let receiver ← receiverState (accountTypeOf s) c.state
    let _ ← unitState c.args
    let slice : ExtensionSlice := ⟨receiver.accountType, receiver.address, receiver.bytes⟩
    let renderTyped : TypedExtensionReference LocatedExtensionView r.Value → Json := fun t =>
      Json.mergeObj (Json.mkObj [("offset", Lean.toJson t.reference.view.offset),
        ("bytes", bytesJson t.reference.view.bytes)]) (rep.render t.value)
    let expected := returnedJson (resultJson renderTyped (getDefaultExtension r receiver))
      (Json.mkObj [("tlv", bytesJson receiver.bytes), ("address", Lean.toJson receiver.address)])
    match ← (← field c.outcome "exit").getStr? with
    | "returned" =>
      let after ← receiverState (accountTypeOf s) (← field c.outcome "state")
      let result ← resultOf (fun j => do
          let offset ← natField j "offset"
          let bytes ← asBytes (← field j "bytes")
          pure ((⟨offset, bytes⟩ : ExtensionView), ← rep.parse j)) (← field c.outcome
            "result")
      let typed := result.map fun (view, value) =>
        (⟨⟨receiver.address, view⟩, value⟩ : TypedExtensionReference LocatedExtensionView r.Value)
      let plain := result.map fun (view, value) => (⟨view, value⟩ : ExtensionReference r.Value)
      let operational : Outcome ExtensionReceiver _ Empty Empty := .returned typed after
      have : Decidable (BaseStateWithExtensions.get_extension_operational_run ⟨r,
        defaultExtensionByteProvider⟩
          receiver () operational) :=
        @decidable_of_iff _ _ (getter_iff r receiver operational).symm
          (instDecidableEqOutcome (S := ExtensionReceiver)
            (V := Except Token.Error (TypedExtensionReference LocatedExtensionView r.Value))
            (U := Empty) (T := Empty) _ _)
      let operationalOk := decide (BaseStateWithExtensions.get_extension_operational_run
        ⟨r, defaultExtensionByteProvider⟩ receiver () operational)
      let afterSlice : ExtensionSlice := ⟨after.accountType, after.address, after.bytes⟩
      have : Decidable (BaseStateWithExtensions.get_extension_run r slice ()
          (.returned plain afterSlice)) := by
        rw [get_extension_evaluated]
        exact instDecidableReturnsOf (State := ExtensionSlice)
          (Value := Except Token.Error (ExtensionReference r.Value)) _ _ _ _
      let observationOk := decide (BaseStateWithExtensions.get_extension_run r slice ()
        (.returned plain afterSlice))
      return (operationalOk, observationOk, expected)
    | _ => return (false, false, expected)

/-! ## Unpacking -/

def optKey (j : Json) : Result (Option Solanalib.Runtime.Pubkey) := asOption pubkey j

def mint (j : Json) : Result Mint := do
  pure ⟨← optKey (← field j "mint_authority"), ← uintField 64 j "supply",
    UInt8.ofNat (← uintField 8 j "decimals"), ← boolField j "is_initialized",
    ← optKey (← field j "freeze_authority")⟩

def mintJson (m : Mint) : Json := Json.mkObj [
  ("mint_authority", optionJson pubkeyJson m.mintAuthority), ("supply", Lean.toJson m.supply),
  ("decimals", Lean.toJson m.decimals.toNat), ("is_initialized", Json.bool m.isInitialized),
  ("freeze_authority", optionJson pubkeyJson m.freezeAuthority)]

def accountState : String → Result AccountState
  | "Uninitialized" => pure .uninitialized
  | "Initialized" => pure .initialized
  | "Frozen" => pure .frozen
  | other => throw s!"unknown AccountState {other}"

def accountStateJson : AccountState → Json
  | .uninitialized => "Uninitialized"
  | .initialized => "Initialized"
  | .frozen => "Frozen"

def account (j : Json) : Result Account := do
  pure ⟨← keyField j "mint", ← keyField j "owner", ← uintField 64 j "amount",
    ← optKey (← field j "delegate"), ← accountState (← (← field j "state").getStr?),
    ← asOption (asUInt 64) (← field j "is_native"), ← uintField 64 j "delegated_amount",
    ← optKey (← field j "close_authority")⟩

def accountJson (a : Account) : Json := Json.mkObj [
  ("mint", pubkeyJson a.mint), ("owner", pubkeyJson a.owner), ("amount", Lean.toJson a.amount),
  ("delegate", optionJson pubkeyJson a.delegate), ("state", accountStateJson a.state),
  ("is_native", optionJson Lean.toJson a.nativeAmount), ("delegated_amount", Lean.toJson
    a.delegatedAmount),
  ("close_authority", optionJson pubkeyJson a.closeAuthority)]

/-- With a pure codec and trivial destructor, the operational unpack relation
admits exactly the dropless total result. -/
theorem unpack_iff {Base : Type} (baseLength : Nat) (accountType : ExtensionAccountType)
    (decode : Bytes → Except Token.Error Base) (bytes : Bytes)
    (o : Outcome Unit (Except Token.Error (ExtensionUnpacked Base Bytes)) Empty Empty) :
    unpackExtensionOperational (pureDroplessExtensionUnpacker baseLength accountType decode) ()
      bytes o ↔
      Outcome.returned (unpackDroplessExtension baseLength accountType decode bytes) () = o := by
  constructor
  · intro h
    by_cases rejected : extensionInputRejected baseLength bytes
    · have rejected' : bytes.length = multisigLength ∨ bytes.length < baseLength := rejected
      unfold unpackExtensionOperational at h
      simp only [rejected', ↓reduceIte] at h
      rw [h]
      simp [unpackDroplessExtension, rejected]
    · have admitted : ¬ (bytes.length = multisigLength ∨ bytes.length < baseLength) := rejected
      unfold unpackExtensionOperational at h
      simp only [admitted, ↓reduceIte] at h
      obtain ⟨parsed, hp, hf⟩ := h
      cases parsed with
      | returned v st =>
        cases st
        have e : decode ((bytes.drop 0).take baseLength) = v := (Prod.mk.inj hp).1
        simp only [List.drop_zero] at e
        cases v with
        | error err =>
          simp only [finishExtensionUnpack] at hf
          rw [hf]
          simp [unpackDroplessExtension, rejected, e, Except.bind]
        | ok base =>
          cases hl : unpackExtensionTailReference
              (pureDroplessExtensionUnpacker baseLength accountType decode) () bytes with
          | ok tlv =>
            simp only [finishExtensionUnpack, hl] at hf
            rw [hf]
            simp [unpackDroplessExtension, rejected, e, hl, Except.bind, Except.map]
          | error err =>
            simp only [finishExtensionUnpack, hl] at hf
            obtain ⟨dropped, hd, rfl⟩ := hf
            cases dropped with
            | returned u st =>
              cases u; cases st
              simp [finishExtensionBaseDrop, unpackDroplessExtension, rejected, e, hl, Except.bind,
                Except.map]
            | unwound r _ => exact r.elim
            | terminated r => exact r.elim
      | unwound r _ => exact r.elim
      | terminated r => exact r.elim
  · intro h
    rw [← h]
    exact unpackDroplessExtension_executes baseLength accountType decode bytes

def tailRef (input : Bytes) (j : Json) : Result (ExtensionTailReference Bytes) :=
  match j with
  | .null => pure .empty
  | _ => do pure (.borrowed ⟨input, ← natField j "offset", ← natField j "length"⟩)

def tailRefJson : ExtensionTailReference Bytes → Json
  | .empty => Json.null
  | .borrowed r => Json.mkObj [("offset", Lean.toJson r.offset), ("length", Lean.toJson r.length)]

def tailBytes (input : Bytes) : ExtensionTailReference Bytes → Bytes
  | .empty => []
  | .borrowed r => (input.drop r.offset).take r.length

/-- A base type `S` with its two registered indices. -/
structure BaseType where
  rust : String
  Base : Type
  decEq : DecidableEq Base
  parse : Json → Result Base
  render : Base → Json
  baseLength : Nat
  accountType : ExtensionAccountType
  decode : Bytes → Except Token.Error Base

def mintBase : BaseType where
  rust := "spl_token_2022_interface::state::Mint"
  Base := Mint
  decEq := inferInstance
  parse := mint
  render := mintJson
  baseLength := mintLength
  accountType := .mint
  decode := unpackMint

def accountBase : BaseType where
  rust := "spl_token_2022_interface::state::Account"
  Base := Account
  decEq := inferInstance
  parse := account
  render := accountJson
  baseLength := accountLength
  accountType := .account
  decode := unpackAccount

def unpackChecker (b : BaseType) : Checker :=
  pairChecker "spl_token_2022_interface::extension::StateWithExtensions::<'data, S>::unpack" [(
    "S",
    b.rust)]
    "Solanalib.Specs.SplToken2022Interface.extension.StateWithExtensions.unpack_operational\
      _run"
    "Solanalib.Specs.SplToken2022Interface.extension.StateWithExtensions.unpack_run" fun c => do
    have := b.decEq
    let _ ← unitState c.state
    let input ← asBytes (← field c.args "input")
    let computed := unpackDroplessExtension b.baseLength b.accountType b.decode input
    let expected := returnedJson (resultJson (fun (u : ExtensionUnpacked b.Base Bytes) =>
      Json.mkObj [("base", b.render u.base), ("tlv", tailRefJson u.tlv)]) computed) Json.null
    match ← (← field c.outcome "exit").getStr? with
    | "returned" =>
      let _ ← unitState (← field c.outcome "state")
      let result ← resultOf (fun j => do
        pure ((⟨← b.parse (← field j "base"), ← tailRef input (← field j "tlv")⟩ :
          ExtensionUnpacked b.Base Bytes))) (← field c.outcome "result")
      let operational : Outcome Unit (Except Token.Error (ExtensionUnpacked b.Base Bytes)) Empty
        Empty :=
        .returned result ()
      have : Decidable (StateWithExtensions.unpack_operational_run
          (pureDroplessExtensionUnpacker b.baseLength b.accountType b.decode) () input operational)
            :=
        decidable_of_iff _ (unpack_iff b.baseLength b.accountType b.decode input operational).symm
      let operationalOk := decide (StateWithExtensions.unpack_operational_run
        (pureDroplessExtensionUnpacker b.baseLength b.accountType b.decode) () input operational)
      let value : Outcome Unit (Except Token.Error (Token.StateWithExtensions b.Base)) Empty Empty
        :=
        .returned (result.map fun u => ⟨u.base, tailBytes input u.tlv⟩) ()
      have : Decidable (StateWithExtensions.unpack_run
          (pureExtensionBaseParser b.baseLength b.accountType b.decode) () input value) :=
        decidable_of_iff _ ((unpackStateWithExtensions_iff b.baseLength b.accountType b.decode
          input value).trans
          ⟨fun h => h.symm, fun h => h.symm⟩).symm
      let valueOk := decide (StateWithExtensions.unpack_run
        (pureExtensionBaseParser b.baseLength b.accountType b.decode) () input value)
      return (operationalOk, valueOk, expected)
    | _ => return (false, false, expected)

/-- The indices decided above are the registered samples (Mint) and their
Account counterparts. -/
theorem mint_indices :
    StateWithExtensions.unpack_operational_sample =
        pureDroplessExtensionUnpacker mintLength .mint unpackMint ∧
      StateWithExtensions.unpack_sample = pureExtensionBaseParser mintLength .mint unpackMint :=
  ⟨rfl, rfl⟩

theorem account_indices :
    accountExtensionUnpacker = pureDroplessExtensionUnpacker accountLength .account unpackAccount ∧
      accountExtensionParser = pureExtensionBaseParser accountLength .account unpackAccount :=
  ⟨rfl, rfl⟩

def MINT := "spl_token_2022_interface::state::Mint"
def ACCOUNT := "spl_token_2022_interface::state::Account"

def getters : List Checker := [
  getterChecker MINT feeConfigRep,
  getterChecker ACCOUNT (rawRep
    "spl_token_2022_interface::extension::transfer_fee::TransferFeeAmount"
    .transferFeeAmount 8),
  getterChecker MINT (rawRep
    "spl_token_2022_interface::extension::mint_close_authority::MintCloseAuthority"
    .mintCloseAuthority 32),
  getterChecker MINT (rawRep
    "spl_token_2022_interface::extension::non_transferable::NonTransferable"
    .nonTransferable 0),
  getterChecker MINT (rawRep "spl_token_2022_interface::extension::transfer_hook::TransferH\
    ook"
    .transferHook 64),
  getterChecker ACCOUNT (rawRep
    "spl_token_2022_interface::extension::immutable_owner::ImmutableOwner"
    .immutableOwner 0),
  getterChecker ACCOUNT (rawRep "spl_token_2022_interface::extension::memo_transfer::MemoTr\
    ansfer"
    .memoTransfer 1),
  getterChecker ACCOUNT feeConfigRep,
  getterChecker MINT (rawRep "spl_token_2022_interface::extension::transfer_fee::TransferFe\
    eAmount"
    .transferFeeAmount 8)]

def checkers : List Checker :=
  [accountLenChecker, typesChecker MINT, typesChecker ACCOUNT] ++ getters ++
    [unpackChecker mintBase, unpackChecker accountBase]

end SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions
