/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PythSolanaReceiverSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PythSolanaReceiverSdk

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Oracle.Pyth

/-- Build exact-width price inputs while varying the time checks. -/
def timed (published : Int64) (age : UInt64) (now : Int) : Args :=
  { sampleArgs with
    update := { sampleUpdate with message := { sampleUpdate.message with publishTime := published }
      }
    maximumAge := age
    clock := { sampleArgs.clock with unixTimestamp := now } }

theorem inclusive_age_boundary :
    evaluate sampleArgs = .ok (.ok sampleUpdate.message.toPrice) := rfl

theorem one_second_stale :
    evaluate (timed 100 20 121) = .ok (.error .priceTooOld) := rfl

theorem future_price_is_not_rejected :
    evaluate (timed 300 0 100) =
      .ok (.ok { sampleUpdate.message.toPrice with publishTime := 300 }) := rfl

theorem positive_timestamp_addition_saturates :
    evaluate (timed 9223372036854775802 10 9223372036854775807) =
      .ok (.ok { sampleUpdate.message.toPrice with publishTime := 9223372036854775802 }) := rfl

theorem negative_timestamp_uses_signed_comparison :
    evaluate (timed (-20) 10 (-10)) =
      .ok (.ok { sampleUpdate.message.toPrice with publishTime := -20 }) := rfl

theorem maximum_converted_age_does_not_wrap :
    evaluate (timed (-9223372036854775808) 9223372036854775807 (-1)) =
      .ok (.ok { sampleUpdate.message.toPrice with publishTime := -9223372036854775808 }) := rfl

theorem age_overflow_is_panic :
    evaluate (timed 100 9223372036854775808 120) = .error .maximumAgeConversion := rfl

theorem abort_strategy_has_no_return_value :
    run true (7 : Nat) (timed 100 9223372036854775808 120) =
      .terminated .maximumAgeConversion := rfl

theorem unwind_strategy_preserves_framed_state :
    run false (7 : Nat) (timed 100 9223372036854775808 120) =
      .unwound .maximumAgeConversion (7 : Nat) := rfl

theorem verification_precedes_feed_and_age :
    evaluate { (timed 100 9223372036854775808 120) with
      requiredVerification := .full, feedId := Solanalib.Runtime.Pubkey.ofNat 1 } =
      .ok (.error .insufficientVerificationLevel) := rfl

theorem feed_precedes_age :
    evaluate { (timed 100 9223372036854775808 120) with feedId := Solanalib.Runtime.Pubkey.ofNat 1
      } =
      .ok (.error .mismatchedFeedId) := rfl

theorem full_verification_satisfies_every_level (level : VerificationLevel) :
    VerificationLevel.full.gte level = true := rfl

open Solanalib.Specs.PythSolanaReceiverSdk.price_update.PriceUpdateV2

/-- An unused slot outside the range of Rust does not exclude the exact
mathematical family execution. This clock has no Rust representation. -/
theorem abstract_slot_retains_exact_family_return :
    let args := { sampleArgs with clock := { sampleArgs.clock with slot := 2^64 } }
    ¬ Sysvar.clockValid args.clock ∧
      (get_price_no_older_than_with_custom_verification_level_contract.contract
        get_price_no_older_than_with_custom_verification_level_sample).requires (7 : Nat) args ∧
      get_price_no_older_than_with_custom_verification_level_run
        get_price_no_older_than_with_custom_verification_level_sample (7 : Nat) args
        (.returned (.ok sampleUpdate.message.toPrice) (7 : Nat)) := by
  refine ⟨?_, True.intro, rfl⟩
  unfold Sysvar.clockValid sampleArgs Solanalib.Runtime.U64_LIMIT
  decide

/-- An abstract timestamp above i64 MAX remains an admitted stale-price
execution; the mathematical model neither clips it nor erases the exit. -/
theorem abstract_timestamp_retains_exact_family_error :
    let args := timed 100 20 (2^63)
    ¬ Sysvar.clockValid args.clock ∧
      (get_price_no_older_than_with_custom_verification_level_contract.contract
        get_price_no_older_than_with_custom_verification_level_sample).requires (7 : Nat) args ∧
      get_price_no_older_than_with_custom_verification_level_run
        get_price_no_older_than_with_custom_verification_level_sample (7 : Nat) args
        (.returned (.error .priceTooOld) (7 : Nat)) := by
  refine ⟨?_, True.intro, rfl⟩
  unfold Sysvar.clockValid timed sampleArgs Solanalib.Runtime.U64_LIMIT
  decide

end SolanalibTest.Specs.PythSolanaReceiverSdk
