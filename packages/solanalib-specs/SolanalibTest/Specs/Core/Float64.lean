/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Float64

@[expose] public section

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Float64

open Solanalib.Specs.Core.Float64

theorem integer_exact : fromUInt64 17 = 0x4031000000000000 := by decide

theorem integer_first_tie_rounds_down :
    fromUInt64 9007199254740993 = 0x4340000000000000 := by decide

theorem integer_next_tie_rounds_up :
    fromUInt64 9007199254740995 = 0x4340000000000002 := by decide

theorem integer_max_rounds_to_two_to_64 :
    fromUInt64 18446744073709551615 = 0x43f0000000000000 := by decide

theorem multiply_normal :
    multiply 0x3ff8000000000000 0x4004000000000000 = 0x400e000000000000 := by decide

theorem subnormal_half_even_zero :
    multiply 1 0x3fe0000000000000 = 0 := by decide

theorem subnormal_tie_rounds_up :
    multiply 3 0x3fe0000000000000 = 2 := by decide

theorem subnormal_boundary_becomes_normal :
    multiply 0x000fffffffffffff 0x3ff0000000000001 = 0x0010000000000000 := by decide

theorem multiply_overflow :
    multiply 0x7fefffffffffffff 0x4000000000000000 = positiveInfinity := by decide

theorem zero_times_infinity_is_nan : multiply 0 positiveInfinity = quietNaN := by decide

theorem negative_zero_is_preserved :
    multiply 0x8000000000000000 0x4000000000000000 = 0x8000000000000000 := by decide

theorem nan_cast_is_zero : toUInt64 0x7ff8000000000123 = 0 := by decide

theorem negative_cast_is_zero : toUInt64 0xbff8000000000000 = 0 := by decide

theorem positive_infinity_saturates :
    toUInt64 positiveInfinity = 18446744073709551615 := by decide

theorem fractional_cast_truncates : toUInt64 0x400e000000000000 = 3 := by decide

theorem separate_rounding_is_observable :
    multiplyUInt64ThenCast 9007199254740993 0x3ff0000000000000 = 9007199254740992 := by decide

theorem rate_then_fractional_threshold :
    multiplyUInt64ThenCast 645 0x3ff8000000000000 = 967 := by decide

end SolanalibTest.Specs.Core.Float64
