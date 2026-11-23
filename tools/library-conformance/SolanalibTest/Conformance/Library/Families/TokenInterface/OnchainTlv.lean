/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

/-!
# The TLV validator and the ExtraAccountMeta list of the onchain model, computed

Component (7a) of `Token.OnchainAllocated.invoke`. The account-list helper
`addExtraList` first runs the allocation-aware TLV validator
`AllocatedTlv.validate` over the validation data, then selects the Execute
payload with `extraSlice`, and later reads each record through
`ExtraSlice.entryAt`. This module computes the three of them.

- `AllocatedTlv.validateFromF` computes the validation loop. Its recursion
  mirrors the `termination_by byteLength - offset` of the model, and
  `AllocatedTlv.validateFrom_fn` is proved by the same well-founded recursion.
- `AllocatedTlv.validateF`/`AllocatedTlv.validate_fn` add the empty vector
  and its scope cleanup, over any vector bundle `VecPrims ops`.
- `validateDataF`/`validateData_fn` state the same at `types`, in the exact
  form `addExtraList` uses:

  ```lean
  fun state => AllocatedTlv.validate
    types.discriminators types.doubleUnwind reference.read state ()
  ```

- `extraSliceF`/`extraSlice_fn` compute `extraSlice` from the control
  combinators of `OnchainControl`.
- `ExtraSlice.entryAt` is already a function of the state. `ExtraSlice.entryAtF`
  is its byte-level body, and `ExtraSlice.entryAt_eq` factors it through the
  live read of the reference.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.OnchainAllocated
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainControl
open SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainPrims

/-! ## Helpers -/

/-- A model exit stated as an equation is the computed `some` of that exit. -/
theorem eq_iff_some {α : Type} (o x : α) : o = x ↔ some x = some o :=
  ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩

section Tlv

variable {S Res U T : Type}

/-! ## The validation loop -/

/-- `AllocatedTlv.validateFrom`, computed from the computed vector push. It
follows the model step for step: the slice is observed with its fixed length,
a complete nonzero discriminator and length slot are checked before the push,
and the payload length is read from the state after the push. The recursion
is on `byteLength - offset`, as in the model; every step consumes at least
its twelve-byte header. -/
def AllocatedTlv.validateFromF (pushF : S → Res × Bytes → Option (Outcome S Unit U T))
    (observe : S → Option Bytes) (resource : Res) (byteLength offset : Nat) (before : S) :
    Option (Outcome S (Except Token.Error Unit) U T) :=
  (AllocatedTlv.sliceAtF observe byteLength before).bind fun bytes =>
    if offset < byteLength then
      if byteLength < offset + 8 then
        some (.returned
          (if (bytes.drop offset).all (· == 0) then .ok () else .error .InvalidAccountData)
          before)
      else
        let discriminator := Solanalib.Runtime.slice bytes offset 8
        if discriminator = AllocatedTlv.emptyDiscriminator then some (.returned (.ok ()) before)
        else if byteLength < offset + 12 then
          some (.returned (.error .InvalidAccountData) before)
        else
          (pushF before (resource, discriminator)).bind fun pushed =>
            match pushed with
            | .returned () after =>
              (AllocatedTlv.sliceAtF observe byteLength after).bind fun current =>
                let endIndex := offset + 12 + Solanalib.Runtime.leNat (Solanalib.Runtime.slice
                  current (offset + 8) 4)
                if byteLength < endIndex then some (.returned (.error .InvalidAccountData) after)
                else AllocatedTlv.validateFromF pushF observe resource byteLength endIndex after
            | .unwound reason after => some (.unwound reason after)
            | .terminated reason => some (.terminated reason)
    else some (.returned (.ok ()) before)
termination_by byteLength - offset
decreasing_by omega

/-- `AllocatedTlv.validateFrom ops observe resource byteLength offset before`
admits exactly `AllocatedTlv.validateFromF pushF …`, when `ops.push` admits
exactly `pushF`. Proved by the well-founded recursion of the model. -/
theorem AllocatedTlv.validateFrom_fn {ops : Owned.VectorOps S Bytes Res U T}
    {pushF : S → Res × Bytes → Option (Outcome S Unit U T)} (hp : Fn ops.push pushF)
    (observe : S → Option Bytes) (resource : Res) (byteLength offset : Nat) (before : S) :
    OFn (AllocatedTlv.validateFrom ops observe resource byteLength offset before)
      (AllocatedTlv.validateFromF pushF observe resource byteLength offset before) := by
  intro outcome
  rw [AllocatedTlv.validateFrom, AllocatedTlv.validateFromF]
  refine exists_bind_iff (AllocatedTlv.sliceAt_fn observe byteLength before) fun bytes _ => ?_
  by_cases h1 : offset < byteLength
  · simp only [h1, ↓reduceIte]
    by_cases h2 : byteLength < offset + 8
    · simp only [h2, ↓reduceIte]
      exact eq_iff_some _ _
    · simp only [h2, ↓reduceIte]
      by_cases h3 : Solanalib.Runtime.slice bytes offset 8 = AllocatedTlv.emptyDiscriminator
      · simp only [h3, ↓reduceIte]
        exact eq_iff_some _ _
      · simp only [h3, ↓reduceIte]
        by_cases h4 : byteLength < offset + 12
        · simp only [h4, ↓reduceIte]
          exact eq_iff_some _ _
        · simp only [h4, ↓reduceIte]
          refine exists_bind_iff (fun pushed => hp before _ pushed) fun pushed _ => ?_
          cases pushed with
          | returned u after =>
            cases u
            refine exists_bind_iff (AllocatedTlv.sliceAt_fn observe byteLength after)
              fun current _ => ?_
            by_cases h5 : byteLength < offset + 12 +
                Solanalib.Runtime.leNat (Solanalib.Runtime.slice current (offset + 8) 4)
            · simp only [h5, ↓reduceIte]
              exact eq_iff_some _ _
            · simp only [h5, ↓reduceIte]
              exact AllocatedTlv.validateFrom_fn hp observe resource byteLength _ after outcome
          | unwound reason after => exact eq_iff_some _ _
          | terminated reason => exact eq_iff_some _ _
  · simp only [h1, ↓reduceIte]
    exact eq_iff_some _ _
termination_by byteLength - offset
decreasing_by omega

/-! ## The validator -/

/-- `AllocatedTlv.validate`, computed from a vector bundle and the computed
double-unwind policy: observe the slice, construct the empty vector, run the
loop over it and drop it on every exit but a terminal one. -/
def AllocatedTlv.validateF {ops : Owned.VectorOps S Bytes Res U T} (h : VecPrims ops)
    (dbl : S → U → U → T) (observe : S → Option Bytes) :
    S → Unit → Option (Outcome S (Except Token.Error Unit) U T) :=
  fun before _ => (observe before).bind fun bytes =>
    (AllocatedTlv.validateFromF h.pushF observe (ops.empty before).1 bytes.length 0
      (ops.empty before).2).bind (cleanupF dbl [h.dropActionF (ops.empty before).1])

/-- `AllocatedTlv.validate ops double observe` admits exactly
`AllocatedTlv.validateF h dbl observe`. -/
theorem AllocatedTlv.validate_fn {ops : Owned.VectorOps S Bytes Res U T} (h : VecPrims ops)
    {double : Owned.DoubleUnwind S U T} {dbl : S → U → U → T}
    (hd : ∀ s o l t, double s o l t ↔ t = dbl s o l) (observe : S → Option Bytes) :
    Fn (AllocatedTlv.validate ops double observe) (AllocatedTlv.validateF h dbl observe) := by
  intro before _ outcome
  refine exists_bind_iff (fun _ => Iff.rfl) fun bytes _ => ?_
  exact exists_bind_iff
    (AllocatedTlv.validateFrom_fn h.push_fn observe _ bytes.length 0 _) fun pending _ =>
      cleanup_fn hd _ _ (.cons (h.dropAction_fn _) .nil) pending outcome

end Tlv

/-! ## At the types of the model -/

variable {types : Types}

/-- The validation step of `addExtraList`, computed: the TLV validator over
the discriminator vectors, reading the validation data through `reference`. -/
def validateDataF (P : Prims types) (reference : AllocatedControl.DataRef) : RunF types Unit :=
  fun s => AllocatedTlv.validateF P.discriminators P.dbl reference.read s ()

/-- The validation step of `addExtraList`, in its exact model form, admits
exactly `validateDataF P reference`. -/
theorem validateData_fn (P : Prims types) (reference : AllocatedControl.DataRef) :
    RFn (fun state => AllocatedTlv.validate types.discriminators types.doubleUnwind
      reference.read state ()) (validateDataF P reference) :=
  call_fn (AllocatedTlv.validate_fn P.discriminators P.double_fn reference.read) ()

/-- `extraSlice`, computed: read the validation data, find the Execute
payload, decode its ExtraAccountMeta list once and keep its range and count. -/
def extraSliceF (types : Types) (reference : AllocatedControl.DataRef) :
    RunF types ExtraSlice :=
  bindR (inspectR reference.read) fun bytes =>
  bindR (resultR (findExecuteRange (bytes.length + 1) bytes 0)) fun range =>
  bindR (resultR (Hook.decodeMetaList (Solanalib.Runtime.slice bytes range.1 range.2))) fun entries
    =>
    pureR ⟨reference, range.1, range.2, entries.length⟩

/-- `extraSlice types reference` admits exactly `extraSliceF types reference`. -/
theorem extraSlice_fn (types : Types) (reference : AllocatedControl.DataRef) :
    RFn (extraSlice types reference) (extraSliceF types reference) :=
  bindR_fn (inspectR_fn _) fun _ =>
  bindR_fn (resultR_fn _) fun _ =>
  bindR_fn (resultR_fn _) fun _ =>
    pureR_fn _

/-- The record lookup of `ExtraSlice.entryAt` on the validation data `bytes`:
the record `index` of the selected payload, if it lies in the active prefix and
in the payload, and the payload lies in the data. -/
def ExtraSlice.entryAtF (slice : ExtraSlice) (index : Nat) (bytes : Bytes) :
    Option Hook.ExtraMeta :=
  if index < slice.count ∧ slice.start + slice.byteLength ≤ bytes.length ∧
      4 + 35 * (index + 1) ≤ slice.byteLength then
    (Hook.decodeExtraMeta (Solanalib.Runtime.slice bytes (slice.start + 4 + 35 * index)
      35)).toOption
  else none

/-- `ExtraSlice.entryAt` is already a function of the state: the live read of
the reference of the slice, followed by `ExtraSlice.entryAtF`. -/
theorem ExtraSlice.entryAt_eq (slice : ExtraSlice) (index : Nat) (state : World types.Extra) :
    slice.entryAt types index state =
      (slice.reference.read state).bind (ExtraSlice.entryAtF slice index) := rfl

end SolanalibTest.Conformance.Library.Families.TokenInterface.OnchainTlv
