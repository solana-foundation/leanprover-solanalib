/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.Rent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem threshold_two_integer_branch :
    Sysvar.rent102Try .release ⟨3480, Sysvar.thresholdTwo⟩ 0 = .ok (.ok 890880) := rfl

theorem current_rate_guard_rejects :
    Sysvar.rent102Try .release ⟨879598564934, Sysvar.thresholdTwo⟩ 0 =
      .ok (.error .invalidArgument) := rfl

theorem source_order_allows_threshold_one_large_rate :
    Sysvar.rent102Try .release ⟨18446744073709551615, Sysvar.thresholdOne⟩ 0 =
      .ok (.ok 18446744073709551488) := rfl

theorem checked_large_rate_panics :
    Sysvar.rent102Try ⟨.checked, false⟩ ⟨18446744073709551615, Sysvar.thresholdOne⟩ 0 =
      .error .multiplicationOverflow := rfl

theorem nondefault_bpf_threshold_panics :
    Sysvar.rent102Try ⟨.release, true⟩ ⟨1, 0x3ff8000000000000⟩ 0 =
      .error .bpfFloatingPoint := rfl

theorem nondefault_nonbpf_threshold_uses_float :
    Sysvar.rent102Try .release ⟨1, 0x3ff8000000000000⟩ 0 = .ok (.ok 192) := rfl

theorem length_error_precedes_bpf_panic :
    Sysvar.rent102Try ⟨.release, true⟩ ⟨1, 0x3ff8000000000000⟩ 10485761 =
      .ok (.error .invalidArgument) := rfl

theorem selected_panic_can_unwind :
    Solanalib.Specs.Pinocchio.sysvars.rent.Rent.threshold_rate.try_minimum_balance
      ⟨⟨false, .unwind⟩, true⟩ (⟨1, 0x3ff8000000000000⟩, 0) =
      .unwound .bpfFloatingPoint ⟨⟨false, .unwind⟩, true⟩ := rfl

end SolanalibTest.Specs.Pinocchio.Rent

namespace SolanalibTest.Specs.Pinocchio.Rent

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem rate_only_calculation :
    Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.try_minimum_balance () (⟨6960⟩, 0) =
      (.ok 890880, ()) := rfl

theorem maximum_rate_is_allowed :
    Sysvar.rent111Try ⟨1759197129867⟩ 10485760 = .ok 18446744073706816896 := rfl

theorem above_maximum_rate_rejected :
    Sysvar.rent111Try ⟨1759197129868⟩ 0 = .error .invalidArgument := rfl

theorem above_maximum_length_rejected :
    Sysvar.rent111Try ⟨1⟩ 10485761 = .error .invalidArgument := rfl

end SolanalibTest.Specs.Pinocchio.Rent
