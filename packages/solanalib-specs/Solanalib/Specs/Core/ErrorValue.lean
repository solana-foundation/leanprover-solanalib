/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramError
public import Solanalib.Specs.Core

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.SdkValue

/-- The exact, total status decoding table already shared by SDK callers. -/
def errorFromStatusContract : Solanalib.Contracts.Model Unit UInt64 ProgramError.Value :=
  .returning (fun _ _ => True)
    (fun before status result after => after = before ∧
      result = ProgramError.V3_0_1.fromStatus status)

/-- An ordinary error value is a return, including for raw status zero. -/
def errorFromStatusModel (before : Unit) (status : UInt64) : ProgramError.Value × Unit :=
  (ProgramError.V3_0_1.fromStatus status, before)

theorem errorFromStatusReference : errorFromStatusContract.RealizedBy errorFromStatusModel :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem errorFromStatusSatisfiable : errorFromStatusContract.Satisfiable := ⟨(), 0, trivial⟩

/-- Encode a builtin in the upper word, with the separate custom-zero sentinel. -/
def errorToStatusContract : Solanalib.Contracts.Model Unit ProgramError.Value UInt64 :=
  .returning (fun _ _ => True)
    (fun before error result after => after = before ∧
      result = ProgramError.V3_0_1.toStatus error)

/-- Total error encoding, without a runtime success interpretation. -/
def errorToStatusModel (before : Unit) (error : ProgramError.Value) : UInt64 × Unit :=
  (ProgramError.V3_0_1.toStatus error, before)

theorem errorToStatusReference : errorToStatusContract.RealizedBy errorToStatusModel :=
  fun _ _ _ => ⟨rfl, rfl⟩

theorem errorToStatusSatisfiable : errorToStatusContract.Satisfiable :=
  ⟨(), .custom 0, trivial⟩

end Solanalib.Specs.Core.SdkValue
