/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions
import Solanalib.Specs.SplToken2022.Extensions

/-! Computable graphs of the registered legacy operational families. The
graphs specialize their dependency providers; they do not prove Rust bodies
or replace an allocator by an assumed universally successful implementation. -/

set_option autoImplicit false

open Solanalib.Specs.SplToken2022

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.Operational

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions (Ledger dblE doubleE_fn
  drops_fn)

abbrev IOut := Outcome Ledger (Except Token.Error (Nat × Nat)) Empty Empty
abbrev TOut := Outcome Ledger (Except Token.Error Nat) Empty Empty

/-- Old scanning computes the actual push before the payload bounds check. -/
def collectF (len : Nat) (byteAt : Ledger → Fin len → UInt8) (resource offset : Nat)
    (before : Ledger) : Option IOut :=
  match Legacy.header ((currentExtensionBytes len byteAt before).drop offset) with
  | .done => some (.returned (.ok (resource, offset)) before)
  | .invalid => cleanupF dblE [fun st => retireF st resource]
      (.returned (.error .InvalidAccountData) before)
  | .entry kind =>
    (modifyF before resource (· ++ [kind])).bind fun pushed =>
      match pushed with
      | .returned () after =>
        let next := Legacy.payloadEnd (currentExtensionBytes len byteAt after) offset
        if next ≤ len then collectF len byteAt resource next after
        else cleanupF dblE [fun st => retireF st resource]
          (.returned (.error .InvalidAccountData) after)
      | .unwound r after => cleanupF dblE [fun st => retireF st resource] (.unwound r after)
      | .terminated r => some (.terminated r)
termination_by len - offset
decreasing_by
  have progress := Legacy.payloadEnd_progress (currentExtensionBytes len byteAt after) offset
  omega

/-- The graph retains the complete vector ledger and used byte count. -/
theorem collect_fn (len : Nat) (byteAt : Ledger → Fin len → UInt8) (resource offset : Nat)
    (before : Ledger) (o : IOut) :
    Legacy.collectInfo Owned.vectorReference (fun _ _ _ _ => False) resource len byteAt
      offset before o ↔ collectF len byteAt resource offset before = some o := by
  cases hs : Legacy.header ((currentExtensionBytes len byteAt before).drop offset) with
  | done =>
    rw [Legacy.collectInfo, hs, collectF, hs]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | invalid =>
    rw [Legacy.collectInfo, hs, collectF, hs]
    exact cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _
  | entry kind =>
    rw [Legacy.collectInfo, hs, collectF, hs]
    dsimp only
    constructor
    · rintro ⟨pushed, hp, hm⟩
      rw [(modify_fn before resource (· ++ [kind]) pushed).1 hp, Option.bind_some]
      cases pushed with
      | returned u after =>
        cases u
        by_cases within : Legacy.payloadEnd (currentExtensionBytes len byteAt after) offset ≤ len
        · simp only [within, ↓reduceIte] at hm ⊢
          exact (collect_fn len byteAt resource
            (Legacy.payloadEnd (currentExtensionBytes len byteAt after) offset) after o).1 hm
        · simp only [within, ↓reduceIte] at hm ⊢
          exact (cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _).1 hm
      | unwound r _ => exact r.elim
      | terminated r => exact r.elim
    · intro h
      cases hp : modifyF (U := Empty) (T := Empty) before resource (· ++ [kind]) with
      | none => rw [hp] at h; cases h
      | some pushed =>
        rw [hp, Option.bind_some] at h
        refine ⟨pushed, (modify_fn before resource (· ++ [kind]) pushed).2 hp, ?_⟩
        cases pushed with
        | returned u after =>
          cases u
          by_cases within : Legacy.payloadEnd (currentExtensionBytes len byteAt after) offset ≤ len
          · simp only [within, ↓reduceIte] at h ⊢
            exact (collect_fn len byteAt resource
              (Legacy.payloadEnd (currentExtensionBytes len byteAt after) offset) after o).2 h
          · simp only [within, ↓reduceIte] at h ⊢
            exact (cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _).2 h
        | unwound r _ => exact r.elim
        | terminated r => exact r.elim
termination_by len - offset
decreasing_by
  all_goals
    have progress := Legacy.payloadEnd_progress (currentExtensionBytes len byteAt after) offset
    omega

/-- The registered closed reader varies only in the immutable source bytes. -/
abbrev Reader (bytes : Bytes) : CurrentExtensionTypeReader :=
  extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty) bytes

/-- Empty construction creates a fresh logical vector identity. -/
def infoF (bytes : Bytes) (before : Ledger) : Option IOut :=
  collectF bytes.length (fun _ index => bytes[index.val]) before.length 0 (before ++ [some []])

theorem info_fn (bytes : Bytes) (before : Ledger) (o : IOut) :
    Legacy.getInfo (Reader bytes) before () o ↔ infoF bytes before = some o :=
  collect_fn _ _ _ _ _ _

/-- The result projection keeps its still-owned vector in the final ledger. -/
def typesF (bytes : Bytes) (before : Ledger) : Option TOut :=
  (infoF bytes before).map Legacy.retainTypes

theorem types_fn (bytes : Bytes) (before : Ledger) (o : TOut) :
    extension.BaseStateWithExtensions.get_extension_types_run
      (Reader bytes) before () o ↔ typesF bytes before = some o := by
  show (∃ accessed, accessed = Outcome.returned () before ∧ _) ↔ _
  constructor
  · rintro ⟨accessed, rfl, scanned, hs, rfl⟩
    unfold typesF
    rw [(info_fn bytes before scanned).1 hs]
    rfl
  · intro h
    unfold typesF at h
    cases hs : infoF bytes before with
    | none => rw [hs] at h; cases h
    | some scanned =>
      rw [hs] at h
      exact ⟨_, rfl, scanned, (info_fn bytes before scanned).2 hs, (Option.some.inj h).symm⟩

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.Operational
