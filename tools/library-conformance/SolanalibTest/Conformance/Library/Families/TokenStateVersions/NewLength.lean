/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Operational

set_option autoImplicit false

open Solanalib.Specs.SplToken2022

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.NewLength

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.Extensions (Ledger dblE doubleE_fn
  drops_fn)

abbrev Out := Outcome Ledger (Except Token.Error Nat) Empty Empty

/-- The explicit VariableLenPack implementation of the native caller returns its
recorded size or Custom(9); it never serializes metadata or enters CPI. -/
def index (bytes : Bytes) : Legacy.NewLength where
  reader := Operational.Reader bytes
  NewReference := Nat × Bool
  getPackedLen := fun before args outcome =>
    outcome = .returned (if args.2 then .error (.Custom 9) else .ok args.1) before
  kind := ⟨.tokenMetadata, by decide⟩
  accountType := .mint

def fromTlvF (bytes : Bytes) (length : Nat) (before : Ledger) : Option Out :=
  (Operational.infoF bytes before).bind fun scanned =>
    match scanned with
    | .returned (.error error) after => some (.returned (.error error) after)
    | .returned (.ok (resource, used)) after =>
      cleanupF dblE [fun st => retireF st resource]
        (.returned (.ok (Legacy.newLengthValue .tokenMetadata .mint used length bytes)) after)
    | .unwound reason after => some (.unwound reason after)
    | .terminated reason => some (.terminated reason)

theorem fromTlv_fn (bytes : Bytes) (length : Nat) (before : Ledger) (o : Out) :
    Legacy.sizeFromTlv (index bytes) before () length o ↔ fromTlvF bytes length before = some o :=
      by
  unfold Legacy.sizeFromTlv fromTlvF
  dsimp only [index, Operational.Reader, extensionTypeReaderReference]
  constructor
  · rintro ⟨scanned, called, continued⟩
    rw [(Operational.info_fn bytes before scanned).1 called, Option.bind_some]
    cases scanned with
    | returned result after =>
      cases result with
      | error error => rw [continued]
      | ok pair =>
        obtain ⟨resource, used⟩ := pair
        have cleaned := (cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _).1 continued
        simpa only [index, Operational.Reader, extensionTypeReaderReference,
          currentExtensionBytes, List.ofFn_getElem] using cleaned
    | unwound reason _ => exact reason.elim
    | terminated reason => exact reason.elim
  · intro h
    cases hs : Operational.infoF bytes before with
    | none => rw [hs] at h; cases h
    | some scanned =>
      rw [hs, Option.bind_some] at h
      refine ⟨scanned, (Operational.info_fn bytes before scanned).2 hs, ?_⟩
      cases scanned with
      | returned result after =>
        cases result with
        | error error => exact (Option.some.inj h).symm
        | ok pair =>
          obtain ⟨resource, used⟩ := pair
          apply (cleanup_fn doubleE_fn _ _ (drops_fn resource) _ _).2
          simpa only [index, Operational.Reader, extensionTypeReaderReference,
            currentExtensionBytes, List.ofFn_getElem] using h
      | unwound reason _ => exact reason.elim
      | terminated reason => exact reason.elim

def runF (bytes : Bytes) (before : Ledger) (args : Nat × Bool) : Option Out :=
  if args.2 then some (.returned (.error (.Custom 9)) before)
  else fromTlvF bytes args.1 before

theorem run_fn (bytes : Bytes) (before : Ledger) (args : Nat × Bool) (o : Out) :
    extension.BaseStateWithExtensions.try_get_new_account_len_for_variable_len_extension_run
      (index bytes) before args o ↔ runF bytes before args = some o := by
  change Legacy.getNewLength (index bytes) before args o ↔ _
  unfold Legacy.getNewLength runF
  dsimp only [index, Operational.Reader, extensionTypeReaderReference]
  simp only [exists_eq_left]
  cases failed : args.2 with
  | true => simp only [↓reduceIte, Option.some.injEq]; exact eq_comm
  | false =>
    simpa only [Bool.false_eq_true, ↓reduceIte, index, Operational.Reader,
      extensionTypeReaderReference] using fromTlv_fn bytes args.1 before o

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.NewLength
