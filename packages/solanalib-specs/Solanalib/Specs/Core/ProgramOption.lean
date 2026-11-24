/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramOption

universe u

/-- The two logical variants of `COption<T>` in the SDK. This mathematical
value does not assert a physical C enum layout or consume its payload. -/
inductive Value (T : Type u) where
  /-- The absent variant contains no payload. -/
  | none
  /-- The present variant stores one payload. -/
  | some (value : T)
  deriving DecidableEq, Repr

/-- Inspect the variant while leaving every payload untouched. -/
def isSome {T : Type u} : Value T → Bool
  | .none => false
  | .some _ => true

theorem isSome_iff {T : Type u} (option : Value T) :
    isSome option = true ↔ ∃ value, option = .some value := by
  cases option <;> simp [isSome]

end Solanalib.Specs.Core.ProgramOption
