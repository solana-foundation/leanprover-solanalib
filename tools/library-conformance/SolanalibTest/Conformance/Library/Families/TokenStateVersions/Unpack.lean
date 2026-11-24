/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Operational

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Unpack

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

abbrev Ledger := Owned.VectorState UInt8
abbrev Tail := Except Token.Error (ExtensionTailReference Bytes)

/-- The logical slot of the temporary is retired after comparing the old padding. -/
def paddingF (baseLength : Nat) (before : Ledger) (bytes : Bytes) : Bool × Ledger :=
  let zeros := List.replicate (accountLength - baseLength) (0 : UInt8)
  (((bytes.drop baseLength).take (accountLength - baseLength) == zeros),
    (before ++ [some zeros]).set before.length none)

theorem padding_iff {Base : Type} (baseLength : Nat) (accountType : ExtensionAccountType)
    (decode : Bytes → Except Token.Error Base) (before : Ledger) (bytes : Bytes)
    (o : Outcome Ledger Bool Empty Empty) :
    Legacy.paddingMatches (Legacy.referenceUnpacker baseLength accountType decode) before bytes o ↔
      o = .returned (paddingF baseLength before bytes).1 (paddingF baseLength before bytes).2 := by
  let zeros := List.replicate (accountLength - baseLength) (0 : UInt8)
  have current : Owned.VectorState.current (before ++ [some zeros]) before.length = some zeros :=
    Owned.VectorState.allocate_current before zeros
  constructor
  · rintro ⟨created, called, continued⟩
    cases created with
    | returned resource after =>
      change before.allocate zeros = (resource, after) at called
      have same := Prod.mk.inj called
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨values, observed, dropped, calledDrop, final⟩ := continued
      change Owned.VectorState.current (before ++ [some zeros]) before.length = some values
        at observed
      have sameValues := Option.some.inj (current.symm.trans observed)
      subst values
      obtain ⟨actual, _, rfl⟩ := calledDrop
      simpa only [Owned.cleanup, Legacy.referenceUnpacker, ExtensionUnpacker.inputBytes,
        currentExtensionBytes, List.ofFn_getElem, paddingF, zeros] using final
    | unwound reason _ => exact reason.elim
    | terminated reason => exact reason.elim
  · intro eq
    rw [eq]
    have run := Legacy.paddingMatches_returned
      (Legacy.referenceUnpacker baseLength accountType decode) before
      (before ++ [some zeros]) ((before ++ [some zeros]).set before.length none)
      bytes before.length zeros rfl current ⟨zeros, current, rfl⟩
    simpa only [Legacy.referenceUnpacker, ExtensionUnpacker.inputBytes,
      currentExtensionBytes, List.ofFn_getElem, paddingF, zeros] using run

/-- Marker lookup reads the input after the comparison temporary is destroyed. -/
def tailF {Base : Type} (requiresTlvByte : Bool) (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Token.Error Base)
    (before : Ledger) (bytes : Bytes) : Tail × Ledger :=
  let restLength := bytes.length - baseLength
  if restLength = 0 then (.ok .empty, before)
  else if Legacy.tailTooShort requiresTlvByte (accountLength - baseLength) restLength then
    (.error .InvalidAccountData, before)
  else
    let compared := paddingF baseLength before bytes
    (Legacy.markedTail (Legacy.referenceUnpacker baseLength accountType decode)
      compared.2 bytes compared.1, compared.2)

theorem tail_iff {Base : Type} (requiresTlvByte : Bool) (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Token.Error Base)
    (before : Ledger) (bytes : Bytes) (o : Outcome Ledger Tail Empty Empty) :
    Legacy.unpackTail requiresTlvByte (Legacy.referenceUnpacker baseLength accountType decode)
      before bytes o ↔
      o = .returned (tailF requiresTlvByte baseLength accountType decode before bytes).1
        (tailF requiresTlvByte baseLength accountType decode before bytes).2 := by
  unfold Legacy.unpackTail tailF
  dsimp only [Legacy.referenceUnpacker]
  change (if bytes.length - baseLength = 0 then _ else _) ↔ _
  by_cases bare : bytes.length - baseLength = 0
  · simp only [bare, ↓reduceIte]
  · simp only [bare, ↓reduceIte]
    by_cases short : Legacy.tailTooShort requiresTlvByte (accountLength - baseLength)
      (bytes.length - baseLength)
    · simp only [short, ↓reduceIte]
    · simp only [short, ↓reduceIte]
      constructor
      · rintro ⟨mapped, ⟨compared, hc, rfl⟩, final⟩
        rw [(padding_iff baseLength accountType decode before bytes compared).1 hc] at final
        exact final.symm
      · intro eq
        subst o
        let compared := paddingF baseLength before bytes
        exact ⟨.returned (compared.1, compared.2) compared.2,
          ⟨.returned compared.1 compared.2,
            (padding_iff baseLength accountType decode before bytes _).2 rfl, rfl⟩, rfl⟩

abbrev ResultValue (Base : Type) := Except Token.Error (ExtensionUnpacked Base Bytes)

/-- The native sample has a fixed base codec and a dropless base value. Its
padding vector still has the complete allocation and retirement state. -/
def unpackF {Base : Type} (requiresTlvByte : Bool) (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Token.Error Base)
    (before : Ledger) (bytes : Bytes) : ResultValue Base × Ledger :=
  if bytes.length = multisigLength ∨ bytes.length < baseLength then
    (.error .InvalidAccountData, before)
  else match decode (bytes.take baseLength) with
    | .error error => (.error error, before)
    | .ok base =>
      let tailed := tailF requiresTlvByte baseLength accountType decode before bytes
      (tailed.1.map (fun tlv => ⟨base, tlv⟩), tailed.2)

theorem unpack_iff {Base : Type} (requiresTlvByte : Bool) (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Token.Error Base)
    (before : Ledger) (bytes : Bytes) (o : Outcome Ledger (ResultValue Base) Empty Empty) :
    Legacy.unpack requiresTlvByte (Legacy.referenceUnpacker baseLength accountType decode)
      before bytes o ↔
      o = .returned (unpackF requiresTlvByte baseLength accountType decode before bytes).1
        (unpackF requiresTlvByte baseLength accountType decode before bytes).2 := by
  unfold Legacy.unpack unpackF
  dsimp only [Legacy.referenceUnpacker]
  change (if bytes.length = multisigLength ∨ bytes.length < baseLength then _ else _) ↔ _
  by_cases rejected : bytes.length = multisigLength ∨ bytes.length < baseLength
  · simp only [rejected, ↓reduceIte]
  · simp only [rejected, ↓reduceIte]
    simp only [List.drop_zero, exists_eq_left]
    cases hp : decode (bytes.take baseLength) with
    | error error => simp only [Legacy.finishUnpack]
    | ok base =>
      simp only [Legacy.finishUnpack]
      constructor
      · rintro ⟨tailed, called, final⟩
        have ht := (tail_iff requiresTlvByte baseLength accountType decode before bytes tailed).1
          called
        subst tailed
        cases hs : (tailF requiresTlvByte baseLength accountType decode before bytes).1 with
        | ok tail => simpa only [hs, Outcome.map, Except.map] using final
        | error error =>
          simp only [hs, Outcome.map, Except.map] at final ⊢
          obtain ⟨dropped, calledDrop, rest⟩ := final
          change dropped = .returned () _ at calledDrop
          subst dropped
          exact rest
      · intro eq
        subst o
        let tailed := tailF requiresTlvByte baseLength accountType decode before bytes
        refine ⟨.returned tailed.1 tailed.2,
          (tail_iff requiresTlvByte baseLength accountType decode before bytes _).2 rfl, ?_⟩
        cases hs : tailed.1 with
        | ok tail => rfl
        | error error =>
          simp only [Outcome.map, Except.map]
          exact ⟨.returned () tailed.2, rfl, rfl⟩

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Unpack
