/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

/-!
# The Mint borrow and hook read, computed

After multisig preparation, the onchain model borrows the data of the Mint
(`beginMint`) and reads its transfer-hook program (`readMintHook`). The read
admits the Mint length, unpacks the base and parses the tail with
`AllocatedTlv.mintTail`, the allocation-aware parser of token-interface
3.0.0. That parser builds the temporary 83-byte zero vector (`vec![0; 83]`)
with `fromList`, compares it with the current padding, and drops it before it
reads the marker (`compareMintPadding`, `mintAfterPadding`).

This module computes these relations. The three TLV helpers are generic over
any vector dependency with a `VecPrims` bundle and any observation of the
tail; the model instantiates them at `types.paddingBytes` and the tail of the retained
Ref. `readMintHook` and `beginMint` are computed over any
`P : Prims types`.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainMint

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

/-! ## The 3.0.0 Mint tail parser -/

section Tail

variable {S Res U T : Type}

/-- `AllocatedTlv.mintAfterPadding`, computed. A failed comparison reads
nothing; on equality, the marker and tail come from the current slice. -/
def AllocatedTlv.mintAfterPaddingF (observe : S → Option Bytes) (byteLength : Nat) (equal : Bool)
    (before : S) : Option (Outcome S (Except Token.Error Bytes) U T) :=
  if equal then
    (AllocatedTlv.sliceAtF observe byteLength before).map fun bytes =>
      .returned
        (if bytes[AllocatedTlv.mintPaddingLength]? = some 1 then
          .ok (bytes.drop (AllocatedTlv.mintPaddingLength + 1)) else .error .InvalidAccountData)
        before
  else some (.returned (.error .InvalidAccountData) before)

/-- `AllocatedTlv.mintAfterPadding observe byteLength equal before` admits
exactly `AllocatedTlv.mintAfterPaddingF observe byteLength equal before`. -/
theorem AllocatedTlv.mintAfterPadding_fn (observe : S → Option Bytes) (byteLength : Nat)
    (equal : Bool) (before : S) :
    OFn (AllocatedTlv.mintAfterPadding (Unwind := U) (Terminal := T) observe byteLength equal
      before)
      (AllocatedTlv.mintAfterPaddingF observe byteLength equal before) := by
  intro o
  unfold AllocatedTlv.mintAfterPadding AllocatedTlv.mintAfterPaddingF
  cases equal with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩
  | true =>
    simp only [↓reduceIte]
    constructor
    · rintro ⟨bytes, hs, rfl⟩
      rw [(AllocatedTlv.sliceAt_fn observe byteLength before bytes).1 hs]
      rfl
    · intro e
      cases hs : AllocatedTlv.sliceAtF observe byteLength before with
      | none => rw [hs] at e; cases e
      | some bytes =>
        rw [hs] at e
        exact ⟨bytes, (AllocatedTlv.sliceAt_fn observe byteLength before bytes).2 hs,
          (Option.some.inj e).symm⟩

/-- `AllocatedTlv.compareMintPadding`, computed: compare the padding of the current slice with the
current temporary vector, drop that vector with `cleanupF`
on the returned Boolean, then finish with `mintAfterPaddingF`. -/
def AllocatedTlv.compareMintPaddingF {ops : Owned.VectorOps S UInt8 Res U T} (h : VecPrims ops)
    (dbl : S → U → U → T) (observe : S → Option Bytes) (byteLength : Nat) (resource : Res)
    (before : S) : Option (Outcome S (Except Token.Error Bytes) U T) :=
  (AllocatedTlv.sliceAtF observe byteLength before).bind fun bytes =>
  (ops.current before resource).bind fun zeroes =>
  (cleanupF dbl [h.dropActionF resource]
      (.returned (bytes.take AllocatedTlv.mintPaddingLength == zeroes) before)).bind
    (thenOpt · (AllocatedTlv.mintAfterPaddingF observe byteLength))

/-- `AllocatedTlv.compareMintPadding ops double observe byteLength resource before`
admits exactly `AllocatedTlv.compareMintPaddingF h dbl observe byteLength resource before`. -/
theorem AllocatedTlv.compareMintPadding_fn {ops : Owned.VectorOps S UInt8 Res U T}
    (h : VecPrims ops) {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) (observe : S → Option Bytes)
    (byteLength : Nat) (resource : Res) (before : S) :
    OFn (AllocatedTlv.compareMintPadding ops double observe byteLength resource before)
      (AllocatedTlv.compareMintPaddingF h dbl observe byteLength resource before) := by
  have hc := cleanup_fn (V := Bool) hd [ops.dropAction resource] [h.dropActionF resource]
    (.cons (h.dropAction_fn resource) .nil)
  intro o
  constructor
  · rintro ⟨bytes, zeroes, hs, hz, dropped, hdrop, hm⟩
    show (AllocatedTlv.sliceAtF observe byteLength before).bind _ = some o
    simp only [(AllocatedTlv.sliceAt_fn observe byteLength before bytes).1 hs, hz,
      (hc _ dropped).1 hdrop, Option.bind_some]
    cases dropped with
    | returned equal after =>
      exact (AllocatedTlv.mintAfterPadding_fn observe byteLength equal after o).1 hm
    | unwound r after => exact (congrArg some hm).symm
    | terminated r => exact (congrArg some hm).symm
  · intro e
    change (AllocatedTlv.sliceAtF observe byteLength before).bind _ = some o at e
    cases hs : AllocatedTlv.sliceAtF observe byteLength before with
    | none => rw [hs] at e; cases e
    | some bytes =>
      simp only [hs, Option.bind_some] at e
      cases hz : ops.current before resource with
      | none => rw [hz] at e; cases e
      | some zeroes =>
        simp only [hz, Option.bind_some] at e
        cases hcl : cleanupF dbl [h.dropActionF resource]
            (.returned (bytes.take AllocatedTlv.mintPaddingLength == zeroes) before) with
        | none => rw [hcl] at e; cases e
        | some dropped =>
          simp only [hcl, Option.bind_some] at e
          refine ⟨bytes, zeroes, (AllocatedTlv.sliceAt_fn observe byteLength before bytes).2 hs,
            hz, dropped, (hc _ dropped).2 hcl, ?_⟩
          cases dropped with
          | returned equal after =>
            exact (AllocatedTlv.mintAfterPadding_fn observe byteLength equal after o).2 e
          | unwound r after => exact (Option.some.inj e).symm
          | terminated r => exact (Option.some.inj e).symm

/-- `AllocatedTlv.mintTail`, computed: an empty tail returns `[]`, a short one
fails, and a long one builds the 83-byte zero vector with `fromList` and hands
it to `compareMintPaddingF`. -/
def AllocatedTlv.mintTailF {ops : Owned.VectorOps S UInt8 Res U T} (h : VecPrims ops)
    (dbl : S → U → U → T) (observe : S → Option Bytes) :
    S → Unit → Option (Outcome S (Except Token.Error Bytes) U T) :=
  fun before _ => (observe before).bind fun bytes =>
    if bytes.isEmpty then some (.returned (.ok []) before)
    else if bytes.length < AllocatedTlv.mintPaddingLength + 1 then
      some (.returned (.error .InvalidAccountData) before)
    else (h.fromListF before (List.replicate AllocatedTlv.mintPaddingLength 0)).bind
      (thenOpt · fun resource after =>
        AllocatedTlv.compareMintPaddingF h dbl observe bytes.length resource after)

/-- `AllocatedTlv.mintTail ops double observe` admits exactly
`AllocatedTlv.mintTailF h dbl observe`. -/
theorem AllocatedTlv.mintTail_fn {ops : Owned.VectorOps S UInt8 Res U T} (h : VecPrims ops)
    {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) (observe : S → Option Bytes) :
    Fn (AllocatedTlv.mintTail ops double observe) (AllocatedTlv.mintTailF h dbl observe) := by
  intro before u o
  have branch : ∀ bytes : Bytes,
      (if bytes.isEmpty then o = .returned (.ok []) before
        else if bytes.length < AllocatedTlv.mintPaddingLength + 1 then
          o = .returned (.error .InvalidAccountData) before
        else Callback.bind ops.fromList
          (fun resource after result =>
            AllocatedTlv.compareMintPadding ops double observe bytes.length resource after result)
          before (List.replicate AllocatedTlv.mintPaddingLength 0) o) ↔
      (if bytes.isEmpty then some (.returned (.ok []) before)
        else if bytes.length < AllocatedTlv.mintPaddingLength + 1 then
          some (.returned (.error .InvalidAccountData) before)
        else (h.fromListF before (List.replicate AllocatedTlv.mintPaddingLength 0)).bind
          (thenOpt · fun resource after =>
            AllocatedTlv.compareMintPaddingF h dbl observe bytes.length resource after)) =
        some o := by
    intro bytes
    by_cases he : bytes.isEmpty = true
    · simp only [he, ↓reduceIte]
      exact ⟨fun e => by rw [e], fun e => (Option.some.inj e).symm⟩
    · by_cases hl : bytes.length < AllocatedTlv.mintPaddingLength + 1
      · simp only [he, hl, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun e => by rw [e], fun e => (Option.some.inj e).symm⟩
      · simp only [he, hl, Bool.false_eq_true, ↓reduceIte]
        exact bind_fn h.fromList_fn
          (fun resource after =>
            AllocatedTlv.compareMintPadding_fn h hd observe bytes.length resource after)
          before _ o
  constructor
  · rintro ⟨bytes, hb, hm⟩
    show (observe before).bind _ = some o
    rw [hb, Option.bind_some]
    exact (branch bytes).1 hm
  · intro e
    change (observe before).bind _ = some o at e
    cases hb : observe before with
    | none => rw [hb] at e; cases e
    | some bytes =>
      rw [hb, Option.bind_some] at e
      exact ⟨bytes, hb, (branch bytes).2 e⟩

end Tail

/-! ## The Mint borrow -/

variable {types : Types}

/-- `readMintHook`, computed: admit the length, unpack the base, parse the
tail of the retained Ref with `AllocatedTlv.mintTailF` at `types.paddingBytes`,
and read the hook program from the TLV bytes. -/
def readMintHookF (P : Prims types) (reference : AllocatedControl.DataRef) :
    RunF types (Option Solanalib.Runtime.Pubkey) :=
  bindR (inspectR reference.read) fun bytes =>
    if extensionInputRejected mintLength bytes then failR .InvalidAccountData
    else bindR (resultR (unpackMint (bytes.take mintLength))) fun _ =>
      bindR (fun state => AllocatedTlv.mintTailF P.paddingBytes P.dbl
          (fun current => (reference.read current).map (·.drop mintLength)) state ())
        fun tlv => pureR (Onchain.hookProgram tlv)

/-- `readMintHook types reference` admits exactly `readMintHookF P reference`. -/
theorem readMintHook_fn (P : Prims types) (reference : AllocatedControl.DataRef) :
    RFn (readMintHook types reference) (readMintHookF P reference) :=
  bindR_fn (inspectR_fn _) fun _ =>
    iteR_fn _ (fun _ => failR_fn _) fun _ =>
      bindR_fn (resultR_fn _) fun _ =>
        bindR_fn (call_fn (AllocatedTlv.mintTail_fn P.paddingBytes P.double_fn _) ()) fun tlv =>
          pureR_fn (Onchain.hookProgram tlv)

/-- `beginMint`, computed: the checked Mint borrow, then `readMintHookF` in a
`moveOnOkR` that releases the Ref on an error or an unwind. -/
def beginMintF (P : Prims types) (args : Onchain.Args) :
    RunF types (AllocatedControl.DataRef × Option Solanalib.Runtime.Pubkey) :=
  bindR (borrowR P.raiseF true args.mint) fun reference =>
    moveOnOkR P.dbl [DataRef.dropF reference]
      (bindR (readMintHookF P reference) fun program => pureR (reference, program))

/-- `beginMint types args` admits exactly `beginMintF P args`. -/
theorem beginMint_fn (P : Prims types) (args : Onchain.Args) :
    RFn (beginMint types args) (beginMintF P args) :=
  bindR_fn (borrowR_fn P.raise_fn true args.mint) fun reference =>
    moveOnOkR_fn P.double_fn (.cons (DataRef.drop_fn reference) .nil)
      (bindR_fn (readMintHook_fn P reference) fun program => pureR_fn (reference, program))

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainMint
