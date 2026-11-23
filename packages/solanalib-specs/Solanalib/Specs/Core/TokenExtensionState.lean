/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtension
public import Solanalib.Specs.Core.TokenState
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- A decoded base with the original, still unparsed TLV tail. -/
structure StateWithExtensions (Value : Type) where
  /-- The value returned by the base parser. -/
  base : Value
  /-- The unchanged TLV tail, validated only on demand. -/
  tlv : Bytes
  deriving DecidableEq, Repr

/-- The source checks the multisig length before invoking its base parser. -/
def extensionInputRejected (baseLength : Nat) (bytes : Bytes) : Prop :=
  bytes.length = multisigLength ∨ bytes.length < baseLength

/-- Length rejection is computable without examining base contents. -/
instance (baseLength : Nat) (bytes : Bytes) :
    Decidable (extensionInputRejected baseLength bytes) := inferInstanceAs
  (Decidable (bytes.length = multisigLength ∨ bytes.length < baseLength))

/-- Validate only extension-layout padding and the account marker. Empty rest
means an unextended account. TLV entry validation remains deferred until lookup
or iteration, matching StateWithExtensions::unpack. -/
def unpackExtensionTail (baseLength : Nat) (accountType : ExtensionAccountType)
    (rest : Bytes) : Except Error Bytes :=
  if rest.isEmpty then .ok []
  else
    let padding := accountLength - baseLength
    if rest.length < padding + 1 then .error .InvalidAccountData
    else if (rest.take padding).any (· != 0) then .error .InvalidAccountData
    else if rest[padding]? = some accountType.tag then .ok (rest.drop (padding + 1))
    else .error .InvalidAccountData

/-- Base errors precede extension-layout errors; successful bases retain the
exact tail resulting from padding and marker validation. -/
def finishExtensionBase {Value : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (bytes : Bytes)
    (result : Except Error Value) : Except Error (StateWithExtensions Value) :=
  match result with
  | .error error => .error error
  | .ok base => (unpackExtensionTail baseLength accountType (bytes.drop baseLength)).map
      (fun tlv => ⟨base, tlv⟩)

/-- Reusable unpacking with an explicit pure base parser. No base validation
is guessed: the supplied parser is run on exactly the checked base prefix. -/
def unpackStateWithExtensions {Value : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Value)
    (bytes : Bytes) : Except Error (StateWithExtensions Value) :=
  if extensionInputRejected baseLength bytes then .error .InvalidAccountData
  else finishExtensionBase baseLength accountType bytes (decode (bytes.take baseLength))

/-- The selected packed Mint instance uses all COption and Boolean checks of
the shared SPL decoder before testing extension-layout padding and marker. -/
def unpackMintWithExtensions (bytes : Bytes) : Except Error (StateWithExtensions Mint) :=
  unpackStateWithExtensions mintLength .mint unpackMint bytes

/-- The selected packed Account instance validates all base fields and accepts
both initialized and frozen accounts. -/
def unpackAccountWithExtensions (bytes : Bytes) : Except Error (StateWithExtensions Account) :=
  unpackStateWithExtensions accountLength .account unpackAccount bytes

/-- The account-sizing helper uses PodMint, whose nonzero initialization check
does not validate COption tags or restrict its Boolean byte to one. -/
def unpackPodMintWithExtensions (bytes : Bytes) : Except Error (StateWithExtensions MintRaw) :=
  unpackStateWithExtensions mintLength .mint unpackPodMint bytes

/-- A generic BaseState/Pack instance supplies its exact constants and the
actual finite exits of S::unpack. This is an explicit model input. A Rust binding
must establish equality to those source constants and parser exits; an assumed
successful result is not a substitute. -/
structure ExtensionBaseParser where
  /-- State observed before and after a generic source parser call. -/
  State : Type
  /-- The logical observation of the parsed source S value. -/
  Value : Type
  /-- The possible unwind reasons of the parser. -/
  Unwind : Type
  /-- The possible terminal reasons of the parser. -/
  Terminal : Type
  /-- The exact S::SIZE_OF value. -/
  byteLength : Nat
  /-- The exact S::ACCOUNT_TYPE value. -/
  accountType : ExtensionAccountType
  /-- All finite exits of the supplied S::unpack interpretation. -/
  parse : State → Bytes →
    Outcome State (Except Error Value) Unwind Terminal → Prop

/-- Wrap a pure base codec as its actual return relation. This supplies no Rust
body theorem; it is used to instantiate the generic mathematical interface. -/
def pureExtensionBaseParser {Value : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Value) :
    ExtensionBaseParser where
  State := Unit
  Value := Value
  Unwind := Empty
  Terminal := Empty
  byteLength := baseLength
  accountType := accountType
  parse := returnsOf (fun state bytes => (decode bytes, state))

/-- The packed Mint instantiation. -/
def mintExtensionParser : ExtensionBaseParser :=
  pureExtensionBaseParser mintLength .mint unpackMint

/-- The packed token-account instantiation. -/
def accountExtensionParser : ExtensionBaseParser :=
  pureExtensionBaseParser accountLength .account unpackAccount

/-- The PodMint instantiation used specifically for account sizing. -/
def podMintExtensionParser : ExtensionBaseParser :=
  pureExtensionBaseParser mintLength .mint unpackPodMint

/-- Transform the actual outcome of the base parser. Its effects and exit kind are
preserved; extension-layout checking occurs only after a successful return. -/
def finishExtensionOutcome (parser : ExtensionBaseParser) (bytes : Bytes) :
    Outcome parser.State (Except Error parser.Value) parser.Unwind parser.Terminal →
      Outcome parser.State (Except Error (StateWithExtensions parser.Value))
        parser.Unwind parser.Terminal
  | .returned result state => .returned
      (finishExtensionBase parser.byteLength parser.accountType bytes result) state
  | .unwound reason state => .unwound reason state
  | .terminated reason => .terminated reason

/-- The generic unpack relation. A rejected length calls no parser. Otherwise
every permitted exit comes from a call on the exact base prefix, followed only
by the extension-tail processing of the source. An empty callback relation produces
no invented return, unwind or terminal exit. -/
def unpackExtensionState (parser : ExtensionBaseParser) (before : parser.State)
    (bytes : Bytes)
    (outcome : Outcome parser.State (Except Error (StateWithExtensions parser.Value))
      parser.Unwind parser.Terminal) : Prop :=
  if extensionInputRejected parser.byteLength bytes then
    outcome = .returned (.error .InvalidAccountData) before
  else ∃ baseOutcome,
    parser.parse before (bytes.take parser.byteLength) baseOutcome ∧
    outcome = finishExtensionOutcome parser bytes baseOutcome

/-- Length rejection has exactly the documented error and unchanged state,
independently of whether the base callback has any finite execution. -/
theorem unpackExtensionState_rejected (parser : ExtensionBaseParser)
    (before : parser.State) (bytes : Bytes)
    (outcome : Outcome parser.State (Except Error (StateWithExtensions parser.Value))
      parser.Unwind parser.Terminal)
    (rejected : extensionInputRejected parser.byteLength bytes) :
    unpackExtensionState parser before bytes outcome ↔
      outcome = .returned (.error .InvalidAccountData) before := by
  simp [unpackExtensionState, rejected]

/-- An admitted base-parser error is returned before testing malformed padding
or TLV bytes and retains the state actually returned by the callback. -/
theorem unpackExtensionState_base_error (parser : ExtensionBaseParser)
    (before after : parser.State) (bytes : Bytes) (error : Error)
    (admitted : ¬ extensionInputRejected parser.byteLength bytes)
    (called : parser.parse before (bytes.take parser.byteLength) (.returned (.error error) after)) :
    unpackExtensionState parser before bytes (.returned (.error error) after) := by
  simp only [unpackExtensionState, admitted, ↓reduceIte]
  exact ⟨.returned (.error error) after, called, rfl⟩

/-- Unwinding from a generic parser propagates its actual state and reason. -/
theorem unpackExtensionState_unwound (parser : ExtensionBaseParser)
    (before after : parser.State) (bytes : Bytes) (reason : parser.Unwind)
    (admitted : ¬ extensionInputRejected parser.byteLength bytes)
    (called : parser.parse before (bytes.take parser.byteLength) (.unwound reason after)) :
    unpackExtensionState parser before bytes (.unwound reason after) := by
  simp only [unpackExtensionState, admitted, ↓reduceIte]
  exact ⟨.unwound reason after, called, rfl⟩

/-- A terminal callback exit carries no invented post-state. -/
theorem unpackExtensionState_terminated (parser : ExtensionBaseParser)
    (before : parser.State) (bytes : Bytes) (reason : parser.Terminal)
    (admitted : ¬ extensionInputRejected parser.byteLength bytes)
    (called : parser.parse before (bytes.take parser.byteLength) (.terminated reason)) :
    unpackExtensionState parser before bytes (.terminated reason) := by
  simp only [unpackExtensionState, admitted, ↓reduceIte]
  exact ⟨.terminated reason, called, rfl⟩

/-- The generic relation has the exact pure-codec execution, for every codec
and byte string. This connects the concrete Mint/Account instantiations to it. -/
theorem unpackStateWithExtensions_execution {Value : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Value)
    (bytes : Bytes) :
    unpackExtensionState (pureExtensionBaseParser baseLength accountType decode) () bytes
      (.returned (unpackStateWithExtensions baseLength accountType decode bytes) ()) := by
  by_cases rejected : extensionInputRejected baseLength bytes
  · simp [unpackExtensionState, pureExtensionBaseParser, unpackStateWithExtensions, rejected]
  · simp only [unpackExtensionState, pureExtensionBaseParser, rejected, ↓reduceIte]
    exact ⟨.returned (decode (bytes.take baseLength)) (), rfl,
      by simp [unpackStateWithExtensions, rejected, finishExtensionOutcome]⟩

/-- The generic interface also excludes every extra pure-codec exit. -/
theorem unpackStateWithExtensions_iff {Value : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Value)
    (bytes : Bytes)
    (outcome : Outcome Unit (Except Error (StateWithExtensions Value)) Empty Empty) :
    unpackExtensionState (pureExtensionBaseParser baseLength accountType decode) () bytes outcome ↔
      outcome = .returned (unpackStateWithExtensions baseLength accountType decode bytes) () := by
  constructor
  · intro run
    by_cases rejected : extensionInputRejected baseLength bytes
    · simpa [unpackExtensionState, pureExtensionBaseParser, unpackStateWithExtensions, rejected]
        using run
    · simp only [unpackExtensionState, pureExtensionBaseParser, rejected, ↓reduceIte] at run
      obtain ⟨baseOutcome, called, finished⟩ := run
      cases baseOutcome with
      | returned result state =>
        cases state
        change (decode (bytes.take baseLength), ()) = (result, ()) at called
        have same : decode (bytes.take baseLength) = result := (Prod.mk.inj called).1
        simpa only [unpackStateWithExtensions, rejected, ↓reduceIte, finishExtensionOutcome,
          pureExtensionBaseParser, same] using finished
      | unwound reason state => cases reason
      | terminated reason => cases reason
  · intro same
    subst outcome
    exact unpackStateWithExtensions_execution baseLength accountType decode bytes

end Solanalib.Specs.Core.Token
