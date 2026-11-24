/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorViews.Bindings

/-! The native fixture supplies valid Rust references, so its JSON cannot
fabricate a missing loan. These theorems check rejection outside each decided
admission, including a shared source loan supplied to a mutable operation. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

theorem infoReadyBorrowed_missing (effects : Effects) :
    infoReadyBorrowed (⟨[], []⟩, effects) guard = false := rfl

theorem keyReady_missing (effects : Effects) : keyReady (⟨[], []⟩, effects) guard = false := rfl

theorem cloneReadyBorrowed_missing (mode : Nat) (effects : Effects) :
    cloneReadyBorrowed mode (⟨[], []⟩, effects) guard = false := rfl

theorem infoCloneReadyBorrowed_missing (effects : Effects) :
    infoCloneReadyBorrowed (⟨[], []⟩, effects) guard = false := rfl

theorem mutableReady_shared (debug : Bool) (s : Snapshot) (value : Nat) :
    mutableReady debug (makeWorld value s (some .shared) false) guard = false := rfl

theorem lamportsReady_wrong_cell (effects : Effects) :
    lamportsReady (⟨[⟨.data [], policy⟩], []⟩, effects)
      ⟨toInfo effects.account, false, false⟩ = false := rfl


end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

theorem moveReadyBorrowed_missing (effects : Effects) :
    moveReadyBorrowed (⟨[], []⟩, effects) handle = false := rfl

end SolanalibTest.Conformance.Library.Families.AnchorViews

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews

theorem infoReadyOwned_missing (effects : Effects) :
    infoReadyOwned (⟨[], []⟩, effects) guard = false := rfl

theorem payloadReady_missing (effects : Effects) : payloadReady (⟨[], []⟩, effects) guard = false
  := rfl

theorem setReady_shared (mode : Nat) (s : Snapshot) (value replacement : Nat) :
    setReady mode (makeWorld value s (some .shared) false) (guard, replacement) = false := rfl

end SolanalibTest.Conformance.Library.Families.AnchorViews
