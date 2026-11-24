/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Sysvar

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Oracle.Pyth

universe u

/-- Verification levels keep the actual byte-sized signature count. -/
inductive VerificationLevel where
  /-- The recorded number of checked guardian signatures. -/
  | partialVerification (signatures : UInt8)
  /-- The update is tagged as fully verified. -/
  | full
  deriving DecidableEq, Repr

/-- Full verification dominates every level; partial levels compare counts. -/
def VerificationLevel.gte : VerificationLevel → VerificationLevel → Bool
  | .full, _ => true
  | .partialVerification _, .full => false
  | .partialVerification actual, .partialVerification required => decide (required ≤ actual)

/-- The complete value returned by the selected getter. -/
structure Price where
  /-- Signed price mantissa. -/
  price : Int64
  /-- Absolute confidence radius at the same decimal exponent. -/
  confidence : UInt64
  /-- Decimal exponent applied to the mantissa and confidence radius. -/
  exponent : Int32
  /-- Signed Unix time of publication. -/
  publishTime : Int64
  deriving DecidableEq, Repr

/-- The message retains its unused previous/EMA fields as well as the fields
read by this getter. No freshness or signature truth is inherent in this type. -/
structure PriceFeedMessage where
  /-- The exact 32-byte feed identifier. -/
  feedId : Solanalib.Runtime.Pubkey
  /-- Current signed price mantissa. -/
  price : Int64
  /-- Current confidence radius. -/
  confidence : UInt64
  /-- Decimal scale shared by price and confidence values. -/
  exponent : Int32
  /-- The signed publication time of the current update. -/
  publishTime : Int64
  /-- Retained predecessor time, unused by this getter. -/
  previousPublishTime : Int64
  /-- Retained exponential moving average, unused by this getter. -/
  emaPrice : Int64
  /-- Retained confidence for the moving average, unused by this getter. -/
  emaConfidence : UInt64
  deriving DecidableEq, Repr

/-- The immutable account value after a separate deserialization/owner check.
This getter itself does not check ownership, the authority or the posted slot. -/
structure PriceUpdate where
  /-- Retained write authority; this getter performs no authority check. -/
  writeAuthority : Solanalib.Runtime.Pubkey
  /-- The level compared with the requested minimum of the caller. -/
  verification : VerificationLevel
  /-- Complete supplied price message. -/
  message : PriceFeedMessage
  /-- Retained posting slot, unused by this getter. -/
  postedSlot : UInt64
  deriving DecidableEq, Repr

/-- The error variants of the SDK, without an assumed Anchor error conversion. -/
inductive GetPriceError where
  /-- The saturating publication-plus-age deadline is before the clock. -/
  | priceTooOld
  /-- SDK variant used by the separate TWAP getter. -/
  | invalidWindowSize
  /-- The requested feed differs from the message feed. -/
  | mismatchedFeedId
  /-- The supplied verification level is weaker than requested. -/
  | insufficientVerificationLevel
  /-- SDK variant used by feed-ID parsing. -/
  | feedIdMustBe32Bytes
  /-- SDK variant used by hexadecimal feed-ID parsing. -/
  | feedIdNonHexCharacter
  deriving DecidableEq, Repr

/-- A failed u64-to-i64 conversion is unwrapped by the selected Rust function. -/
inductive Panic where
  /-- The u64 age of the caller cannot be represented as a nonnegative i64. -/
  | maximumAgeConversion
  deriving DecidableEq, Repr

/-- Value arguments with the shared canonical mathematical clock. Relating a
clock to Rust requires its fields to fit the source integer widths; evaluation
is also defined for abstract clocks outside those widths. -/
structure Args where
  /-- Immutable decoded price-update account value. -/
  update : PriceUpdate
  /-- Shared canonical clock; this getter reads only its Unix timestamp. -/
  clock : Sysvar.Clock
  /-- Requested age in seconds before the checked signed conversion of the source. -/
  maximumAge : UInt64
  /-- Requested feed identifier. -/
  feedId : Solanalib.Runtime.Pubkey
  /-- Minimum acceptable verification level. -/
  requiredVerification : VerificationLevel

/-- Only these four fields become the returned Price. -/
def PriceFeedMessage.toPrice (message : PriceFeedMessage) : Price :=
  ⟨message.price, message.confidence, message.exponent, message.publishTime⟩

/-- The upper-saturating signed addition after the age conversion succeeds.
The second operand is nonnegative, so lower saturation cannot occur. -/
def expiresAt (message : PriceFeedMessage) (maximumAge : UInt64) : Int :=
  min (2^63 - 1) (message.publishTime.toInt + (maximumAge.toNat : Int))

/-- Exact check order: verification, feed equality, unwrapped age conversion,
then the inclusive saturating freshness comparison. Future prices are allowed. -/
def evaluate (args : Args) : Except Panic (Except GetPriceError Price) :=
  if !args.update.verification.gte args.requiredVerification then
    .ok (.error .insufficientVerificationLevel)
  else if args.update.message.feedId ≠ args.feedId then
    .ok (.error .mismatchedFeedId)
  else if 2^63 ≤ args.maximumAge.toNat then
    .error .maximumAgeConversion
  else if expiresAt args.update.message args.maximumAge < args.clock.unixTimestamp then
    .ok (.error .priceTooOld)
  else .ok (.ok args.update.message.toPrice)

/-- The finite reference exit in a selected panic strategy. The getter only
reads its value arguments; a surrounding abstract state is framed unchanged. -/
def run {State : Type u} (aborts : Bool) (before : State) (args : Args) :
    Outcome State (Except GetPriceError Price) Panic Panic :=
  match evaluate args with
  | .ok result => .returned result before
  | .error reason => if aborts then .terminated reason else .unwound reason before

/-- Verification failure wins even when the feed and maximum age are invalid. -/
theorem verification_first (args : Args)
    (insufficient : args.update.verification.gte args.requiredVerification = false) :
    evaluate args = .ok (.error .insufficientVerificationLevel) := by
  simp [evaluate, insufficient]

/-- A feed mismatch precedes the possible age-conversion panic. -/
theorem feed_before_age (args : Args)
    (verified : args.update.verification.gte args.requiredVerification = true)
    (mismatched : args.update.message.feedId ≠ args.feedId) :
    evaluate args = .ok (.error .mismatchedFeedId) := by
  simp [evaluate, verified, mismatched]

/-- A huge age is not converted into an ordinary stale-price error. -/
theorem age_conversion_panics (args : Args)
    (verified : args.update.verification.gte args.requiredVerification = true)
    (matched : args.update.message.feedId = args.feedId)
    (tooLarge : 2^63 ≤ args.maximumAge.toNat) :
    evaluate args = .error .maximumAgeConversion := by
  simp [evaluate, verified, matched, tooLarge]

/-- Inclusive freshness accepts the supplied price after all earlier checks. -/
theorem fresh_price (args : Args)
    (verified : args.update.verification.gte args.requiredVerification = true)
    (matched : args.update.message.feedId = args.feedId)
    (ageBound : args.maximumAge.toNat < 2^63)
    (fresh : args.clock.unixTimestamp ≤ expiresAt args.update.message args.maximumAge) :
    evaluate args = .ok (.ok args.update.message.toPrice) := by
  simp [evaluate, verified, matched, Nat.not_le_of_gt ageBound, Int.not_lt_of_ge fresh]

/-- A nonzero, partially verified update for concrete model executions. -/
def sampleUpdate : PriceUpdate :=
  ⟨.zero, .partialVerification 5, ⟨.zero, 4700, 23, -2, 100, 80, 4690, 29⟩, 17⟩

/-- A boundary-age sample uses the canonical clock and passes at equality. -/
def sampleArgs : Args :=
  ⟨sampleUpdate, ⟨20, 0, 0, 0, 120⟩, 20, .zero, .partialVerification 5⟩

end Solanalib.Specs.Core.Oracle.Pyth
