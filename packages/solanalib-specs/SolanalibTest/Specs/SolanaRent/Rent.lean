/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaRent.Rent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaRent.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem fractional_threshold_truncates_after_rounding :
    Solanalib.Specs.SolanaRent.Rent.minimum_balance .release (⟨5, 0x3ff8000000000000, 50⟩, 1) =
      .returned 967 .release := rfl

theorem nan_threshold_returns_zero :
    Sysvar.rent300Minimum .release ⟨5, 0x7ff8000000000001, 50⟩ 1 = .ok 0 := rfl

theorem positive_infinity_saturates :
    Sysvar.rent300Minimum .release ⟨5, Float64.positiveInfinity, 50⟩ 1 =
      .ok 18446744073709551615 := rfl

theorem release_addition_wraps_before_float :
    Sysvar.rent300Minimum .release ⟨1, Sysvar.thresholdOne, 0⟩ 18446744073709551615 =
      .ok 127 := rfl

theorem checked_addition_panics_before_float :
    Sysvar.rent300Minimum .checked ⟨1, Sysvar.thresholdOne, 0⟩ 18446744073709551615 =
      .error .additionOverflow := rfl

theorem burn_percent_does_not_enter_calculation :
    Sysvar.rent300Minimum .release ⟨5, 0x3ff8000000000000, 0⟩ 1 =
      Sysvar.rent300Minimum .release ⟨5, 0x3ff8000000000000, 255⟩ 1 := rfl

end SolanalibTest.Specs.SolanaRent.Rent
