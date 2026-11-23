/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsLog
public import Solanalib.Specs.Core.AnchorErrorOperationsWitnesses

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- A primitive counting interpretation for every selected ProgramError and
storage profile. It has two preexisting diagnostic owners and allocates owner2;
the three reached actions leave the actual final counter5. -/
abbrev logSampleAt (profile : ProgramProfile) (storage : Storage) : LogTypes profile where
  State := Nat
  StringResource := Nat
  BoxResource := Nat
  Unwind := Empty
  Terminal := Empty
  storage := storage
  currentBox := fun _ box => if box = 0 then some (.anchor ⟨0, 100, 1, none, none⟩) else none
  cloneString := match profile with
    | .legacy _ => fun before _ outcome => outcome = .returned before (before + 1)
    | .modern => ()
  format := fun before _ outcome => outcome = .returned before (before + 1)
  logString := fun before _ outcome => outcome = .returned () (before + 1)
  logLiteral := fun before _ outcome => outcome = .returned () (before + 1)
  logPubkey := fun before _ outcome => outcome = .returned () (before + 1)
  dropString := fun before _ outcome => outcome = .returned () (before + 1)
  double := AnchorErrorOwned.noDouble

def logReceiverAt (profile : ProgramProfile) : (storage : Storage) → (logSampleAt profile
  storage).Error
  | .inline => .anchor ⟨0, 100, 1, none, none⟩
  | .boxed => ⟨0⟩

theorem logPayload_executionAt (profile : ProgramProfile) (storage : Storage) :
    payloadLog (logSampleAt profile storage) 2 (.anchor ⟨0, 100, 1, none, none⟩)
      (.returned () 5) := by
  refine ⟨.returned () 5, ?_, rfl⟩
  exact ⟨.returned 2 3, ⟨_, rfl, rfl⟩, .returned () 4, rfl,
    .returned () 5, ⟨_, rfl, rfl⟩, rfl⟩

theorem log_executionAt (profile : ProgramProfile) (storage : Storage) :
    FamilyHasExecution (logFamily profile) logRun (logSampleAt profile storage) := by
  refine ⟨(2 : Nat), logReceiverAt profile storage, .returned () (5 : Nat), trivial, ?_⟩
  cases storage with
  | inline => exact logPayload_executionAt profile .inline
  | boxed => exact ⟨.anchor ⟨0, 100, 1, none, none⟩, rfl, logPayload_executionAt profile .boxed⟩

/-- On an actual host log unwind the temporary is still cleaned; the unwind reason of the consumed
dependency survives normal String destruction unchanged. -/
theorem formatLog_unwind {profile : ProgramProfile} (types : LogTypes profile)
    (before allocated logged after : types.State)
    (request : FormatRequest types.StringResource (profile.Value types.StringResource))
    (resource : types.StringResource) (reason : types.Unwind)
    (formatted : types.format before request (.returned resource allocated))
    (failed : types.logString allocated resource (.unwound reason logged))
    (dropped : types.dropString logged resource (.returned () after)) :
    formatLog types before request (.unwound reason after) := by
  exact ⟨.returned resource allocated, ⟨_, formatted, rfl⟩, .unwound reason logged, failed,
    .returned () after, ⟨_, dropped, rfl⟩, rfl⟩

end Solanalib.Specs.Core.AnchorErrorOperations
