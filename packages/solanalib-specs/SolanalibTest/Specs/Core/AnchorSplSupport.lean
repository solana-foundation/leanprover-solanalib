/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorSpl.Support

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorSplSupport

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport

/-- Deref returns a field reference whose later read follows the live parent. -/
theorem deref_reads_updated_parent :
    FieldReference.Reads (derefSample .tokenAccount).access (fun _ value => value)
      (some { tokenSample with amount := 99 }) (⟨(), ()⟩ : DerefResult (derefSample .tokenAccount))
      { tokenSample with amount := 99 } := ⟨rfl, rfl⟩

theorem deref_rejects_expired_parent :
    ¬ FieldReference.Reads (derefSample .tokenAccount).access (fun _ value => value)
      none (⟨(), ()⟩ : DerefResult (derefSample .tokenAccount)) tokenSample := by
  intro read
  cases read.1

end SolanalibTest.Specs.Core.AnchorSplSupport
