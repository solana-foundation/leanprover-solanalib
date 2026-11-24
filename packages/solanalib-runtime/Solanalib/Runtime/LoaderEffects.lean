/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Context

@[expose] public section

/-!
# Cache effects of opaque loader-v3 management

The account operations, authority checks, code verification and native calls of
the loader remain opaque. A supplied successful loader behavior must satisfy
their source contracts. This module determines the mandatory cache effect of
that success from the original instruction and account state; it does not infer
success from an instruction tag or replace those contracts.

Agave 4.3.2 writes an `Unloaded` entry after DeployWithMaxDataLen, Upgrade and
ExtendProgram, and a `Closed` entry after closing ProgramData. Other successful
loader-v3 instructions do not write the program cache. Classification uses the
original ProgramData state because Close overwrites that state before returning.
-/

namespace Solanalib.Runtime

/-- Resolve an instruction-account position without inventing an address for a
missing account. Successful source loader operations have all required indices. -/
def loaderAccountKey (before : TxState) (frame : Frame) (position : Nat) : Option Pubkey := do
  let account ← frame.accounts[position]?
  before.keys[account.txIdx]?

/-- The fixed-width bincode discriminant, when its four bytes are present. -/
def loaderDiscriminant (data : Bytes) : Option Nat :=
  if 4 ≤ data.length then some (leNat (data.take 4)) else none

/-- A classified successful operation either preserves the direct cache state
or performs one required write. Failed classification is distinct from preservation. -/
inductive LoaderV3CacheAction where
  | preserve
  | write (key : Pubkey) (entry : ModifiedProgram)
  deriving DecidableEq, Repr

/-- Classify the cache effect of a successful Agave 4.3.2 loader-v3 operation.
The slot is the actual clock sysvar slot, also required by the deployment helper
to equal the slot of the transaction cache. This helper classifies effects;
complete source decoding, authority, funding and verification remain success
premises. A missing required cache target cannot be classified as preservation. -/
def loaderV3CacheAction (clockSlot : Nat) (before : TxState) (frame : Frame) :
    Option LoaderV3CacheAction := do
  let tag ← loaderDiscriminant frame.data
  match tag with
  | 0 | 1 | 4 | 7 => some .preserve
  | 2 => return .write (← loaderAccountKey before frame 2) (.unloaded clockSlot)
  | 3 | 6 => return .write (← loaderAccountKey before frame 1) (.unloaded clockSlot)
  | 5 =>
    let account ← frame.accounts[0]?
    let closed ← before.accts[account.txIdx]?
    match ← loaderDiscriminant closed.data with
    | 0 | 1 => some .preserve
    | 3 => return .write (← loaderAccountKey before frame 3) (.closed clockSlot)
    | _ => none
  | _ => none

/-- The direct write selected by a successful loader effect classification. -/
def loaderV3CacheEffect (clockSlot : Nat) (before : TxState) (frame : Frame) :
    Option (Pubkey × ModifiedProgram) := do
  match ← loaderV3CacheAction clockSlot before frame with
  | .preserve => none
  | .write key entry => some (key, entry)

/-- The cache part of the opaque loader result contract. A successful operation
must have a classified action; `none` cannot silently admit a successful
cache-changing instruction whose target is missing. This is not a proof of
the remaining loader success conditions. Error results retain their opaque
source error rather than assigning a new error precedence to this classifier. -/
def LoaderV3ResultContract (clockSlot : Nat) (before : TxState) (frame : Frame) :
    Except InstrError TxState → Prop
  | .error _ => True
  | .ok _ => (loaderV3CacheAction clockSlot before frame).isSome = true

/-- Apply the mandatory loader cache write after its opaque account effects.
Nested native calls already contribute their own modifications to `after`. -/
def applyLoaderV3Effect (clockSlot : Nat) (before : TxState) (frame : Frame)
    (after : TxState) : TxState :=
  match loaderV3CacheEffect clockSlot before frame with
  | none => after
  | some (key, entry) =>
    { after with modifiedPrograms := after.modifiedPrograms.store key entry }

/-- A successful loader return carries its cache write. Terminal failures keep
their error; transaction processing discards all modifications on failure. -/
def finishLoaderV3 (clockSlot : Nat) (before : TxState) (frame : Frame)
    (result : Except InstrError TxState) : Except InstrError TxState :=
  result.map (applyLoaderV3Effect clockSlot before frame)

@[simp] theorem applyLoaderV3Effect_keys (slot : Nat) (before after : TxState) (frame : Frame) :
    (applyLoaderV3Effect slot before frame after).keys = after.keys := by
  unfold applyLoaderV3Effect
  split <;> rfl

@[simp] theorem applyLoaderV3Effect_accts (slot : Nat) (before after : TxState) (frame : Frame) :
    (applyLoaderV3Effect slot before frame after).accts = after.accts := by
  unfold applyLoaderV3Effect
  split <;> rfl

@[simp] theorem applyLoaderV3Effect_lamportsDelta
    (slot : Nat) (before after : TxState) (frame : Frame) :
    (applyLoaderV3Effect slot before frame after).lamportsDelta = after.lamportsDelta := by
  unfold applyLoaderV3Effect
  split <;> rfl

@[simp] theorem applyLoaderV3Effect_stack (slot : Nat) (before after : TxState) (frame : Frame) :
    (applyLoaderV3Effect slot before frame after).stack = after.stack := by
  unfold applyLoaderV3Effect
  split <;> rfl

@[simp] theorem applyLoaderV3Effect_topIndex (slot : Nat) (before after : TxState) (frame : Frame) :
    (applyLoaderV3Effect slot before frame after).topIndex = after.topIndex := by
  unfold applyLoaderV3Effect
  split <;> rfl

@[simp] theorem applyLoaderV3Effect_touched (slot : Nat) (before after : TxState) (frame : Frame) :
    (applyLoaderV3Effect slot before frame after).touched = after.touched := by
  unfold applyLoaderV3Effect
  split <;> rfl

theorem finishLoaderV3_ok {slot : Nat} {before after : TxState} {frame : Frame}
    {result : Except InstrError TxState}
    (finished : finishLoaderV3 slot before frame result = .ok after) :
    ∃ returned, result = .ok returned ∧ after = applyLoaderV3Effect slot before frame returned := by
  cases result with
  | error error => cases finished
  | ok returned => exact ⟨returned, rfl, Except.ok.inj finished |>.symm⟩

/-- Every successful classified cache write is present after loader return,
independently of the opaque account effects. -/
theorem applyLoaderV3Effect_lookup {slot : Nat} {before after : TxState} {frame : Frame}
    {key : Pubkey} {entry : ModifiedProgram}
    (effect : loaderV3CacheEffect slot before frame = some (key, entry)) :
    (applyLoaderV3Effect slot before frame after).modifiedPrograms.lookup key = some entry := by
  simp [applyLoaderV3Effect, effect]

end Solanalib.Runtime
