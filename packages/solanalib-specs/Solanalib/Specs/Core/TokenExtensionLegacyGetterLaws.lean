/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacy

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

/-- A successful old lookup selects one actual contiguous range from its
input. The relative offset counts the same prefix whose bytes are retained. -/
theorem findExtension_parts (wanted : ExtensionType) (offset : Nat) (bytes : Bytes)
    (view : ExtensionView) (found : findExtension wanted offset bytes = .ok view) :
    ∃ leading trailing : Bytes, bytes = leading ++ view.bytes ++ trailing ∧
      view.offset = offset + leading.length ∧ 4 ≤ leading.length := by
  cases bytes with
  | nil => simp [findExtension] at found
  | cons low rest =>
    cases rest with
    | nil => simp [findExtension] at found
    | cons high rest =>
      cases rest with
      | nil => simp [findExtension] at found
      | cons lenLow rest =>
        cases rest with
        | nil => simp [findExtension] at found
        | cons lenHigh rest =>
          rw [findExtension.eq_def wanted offset (low :: high :: lenLow :: lenHigh :: rest)]
            at found
          dsimp only at found
          split at found
          · cases found
          · rename_i kind decoded
            split at found
            · split at found
              · cases found
                refine ⟨[low, high, lenLow, lenHigh], rest.drop (tlvU16 lenLow lenHigh), ?_, rfl,
                  by simp⟩
                simp only [List.cons_append, List.nil_append]
                exact congrArg (fun tail => low :: high :: lenLow :: lenHigh :: tail)
                  (List.take_append_drop (tlvU16 lenLow lenHigh) rest).symm
              · cases found
            · split at found
              · cases found
              · split at found
                · cases found
                · obtain ⟨leading, trailing, selected, address, header⟩ :=
                    findExtension_parts wanted (offset + 4 + tlvU16 lenLow lenHigh)
                      (rest.drop (tlvU16 lenLow lenHigh)) view found
                  have lengths := congrArg List.length selected
                  simp only [List.length_drop, List.length_append] at lengths
                  have fits : tlvU16 lenLow lenHigh ≤ rest.length := by omega
                  refine ⟨[low, high, lenLow, lenHigh] ++ rest.take (tlvU16 lenLow lenHigh) ++
                    leading,
                    trailing, ?_, ?_, ?_⟩
                  · have restParts : rest = rest.take (tlvU16 lenLow lenHigh) ++
                        (leading ++ view.bytes ++ trailing) := by
                      rw [← selected]
                      exact (List.take_append_drop _ _).symm
                    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
                      congrArg (fun tail => low :: high :: lenLow :: lenHigh :: tail) restParts
                  · simp only [List.length_append, List.length_cons, List.length_nil,
                      List.length_take, Nat.min_eq_left fits]
                    omega
                  · simp only [List.length_append, List.length_cons, List.length_nil]
                    omega
termination_by bytes.length
decreasing_by simp_all only [List.length_cons, List.length_drop]; omega

/-- The concrete old traversal produces only these ordinary error variants;
provider allocation and cleanup exits are not involved in this pure lookup. -/
def GetterError (error : Error) : Prop :=
  error = .InvalidArgument ∨ error = .InvalidAccountData ∨ error = .Custom 20 ∨ error = .Custom 48

theorem findExtension_error (wanted : ExtensionType) (offset : Nat) (bytes : Bytes)
    (error : Error) (found : findExtension wanted offset bytes = .error error) : GetterError error
      := by
  cases bytes with
  | nil =>
    simp only [findExtension] at found
    cases found
    exact Or.inr (Or.inl rfl)
  | cons low rest =>
    cases rest with
    | nil =>
      simp only [findExtension] at found
      cases found
      exact Or.inr (Or.inl rfl)
    | cons high rest =>
      cases rest with
      | nil =>
        simp only [findExtension] at found
        cases found
        exact Or.inr (Or.inl rfl)
      | cons lenLow rest =>
        cases rest with
        | nil =>
          simp only [findExtension] at found
          cases found
          exact Or.inr (Or.inl rfl)
        | cons lenHigh rest =>
          rw [findExtension.eq_def wanted offset (low :: high :: lenLow :: lenHigh :: rest)]
            at found
          dsimp only at found
          split at found
          · cases found; exact Or.inr (Or.inl rfl)
          · split at found
            · split at found
              · cases found
              · cases found; exact Or.inr (Or.inl rfl)
            · split at found
              · cases found; exact Or.inr (Or.inr (Or.inr rfl))
              · split at found
                · cases found; exact Or.inr (Or.inr (Or.inl rfl))
                · exact findExtension_error wanted (offset + 4 + tlvU16 lenLow lenHigh)
                    (rest.drop (tlvU16 lenLow lenHigh)) error found
termination_by bytes.length
decreasing_by simp_all only [List.length_cons, List.length_drop]; omega

/-- A concrete default byte result carries the same base address and an
actual in-bounds source range. No source child permission follows just from
these mathematical address facts. -/
theorem defaultBytes_success (receiver : ExtensionReceiver) (pod : ExtensionPod)
    (selected : LocatedExtensionView)
    (found : defaultExtensionBytes receiver pod = .ok selected) :
    selected.baseAddress = receiver.address ∧
      ∃ leading trailing : Bytes, receiver.bytes = leading ++ selected.view.bytes ++ trailing ∧
        selected.view.offset = leading.length ∧ 4 ≤ leading.length := by
  unfold defaultExtensionBytes at found
  split at found
  · cases searched : findExtension pod.kind 0 receiver.bytes with
    | error error => simp [searched, Except.map] at found
    | ok view =>
      simp only [searched, Except.map, Except.ok.injEq] at found
      subst selected
      obtain ⟨leading, trailing, parts, offset, header⟩ :=
        findExtension_parts pod.kind 0 receiver.bytes view searched
      exact ⟨rfl, leading, trailing, parts, by simpa only [Nat.zero_add] using offset, header⟩
  · cases found

theorem defaultBytes_error (receiver : ExtensionReceiver) (pod : ExtensionPod) (error : Error)
    (found : defaultExtensionBytes receiver pod = .error error) : GetterError error := by
  unfold defaultExtensionBytes at found
  split at found
  · cases searched : findExtension pod.kind 0 receiver.bytes with
    | error issue =>
      simp only [searched, Except.map, Except.error.injEq] at found
      subst issue
      exact findExtension_error pod.kind 0 receiver.bytes error searched
    | ok view => simp [searched, Except.map] at found
  · cases found; exact Or.inr (Or.inl rfl)

/-- The complete concrete getter retains the selected slice identity, its
exact Pod width, its checked alignment and its typed byte observation. -/
theorem getDefaultExtension_ok (representation : ExtensionRepresentation)
    (receiver : ExtensionReceiver)
    (typed : TypedExtensionReference LocatedExtensionView representation.Value)
    (found : getDefaultExtension representation receiver = .ok typed) :
    defaultExtensionBytes receiver representation.pod = .ok typed.reference ∧
      typed.reference.view.bytes.length = representation.pod.byteLength ∧
      (typed.reference.baseAddress + typed.reference.view.offset) %
        representation.pod.alignment = 0 ∧
      typed.value = representation.observe typed.reference.view.bytes := by
  unfold getDefaultExtension at found
  cases selected : defaultExtensionBytes receiver representation.pod with
  | error error => simp [selected, Except.bind] at found
  | ok reference =>
    simp only [selected, Except.bind] at found
    obtain ⟨width, aligned, rfl⟩ :=
      (castExtensionReference_ok_iff defaultByteProvider representation receiver reference
        typed).mp found
    exact ⟨rfl, width, aligned, rfl⟩

/-- Casting can add only InvalidArgument to the old traversal errors. This
fact justifies the reached scalar error codec without forbidding any input. -/
theorem getDefaultExtension_error (representation : ExtensionRepresentation)
    (receiver : ExtensionReceiver) (error : Error)
    (found : getDefaultExtension representation receiver = .error error) : GetterError error := by
  unfold getDefaultExtension at found
  cases selected : defaultExtensionBytes receiver representation.pod with
  | error issue =>
    simp only [selected, Except.bind, Except.error.injEq] at found
    subst issue
    exact defaultBytes_error receiver representation.pod error selected
  | ok reference =>
    simp only [selected, Except.bind] at found
    unfold castExtensionReference at found
    split at found
    · split at found
      · cases found
      · cases found; exact Or.inl rfl
    · cases found; exact Or.inl rfl

end Solanalib.Specs.Core.Token.Legacy
