/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpi

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Memory

open Solanalib.Runtime

/-- Copied input memory is read during callee synchronization. Configuration
L updates transaction accounts without changing that byte buffer. -/
theorem updateCalleeOne_buffer_L {profile : Profile} {context : InvCtx}
    {before after : InvState} {account : Translated} (copied : context.cfg = .L)
    (returned : updateCalleeOne profile context before account = .ok after) :
    after.buf = before.buf := by
  unfold updateCalleeOne at returned
  simp only [copied] at returned
  split at returned
  · cases returned
  · split at returned
    · cases returned
    · rename_i middle dataStep
      have buffer : middle.buf = before.buf := by
        split at dataStep
        · cases dataStep
        · cases dataStep
          rfl
      split at returned
      · cases returned
      · cases returned
        exact buffer

theorem updateCallee_buffer_L {profile : Profile} {context : InvCtx}
    (copied : context.cfg = .L) :
    ∀ {accounts : List Translated} {before after : InvState},
      updateCallee profile context before accounts = .ok after → after.buf = before.buf := by
  intro accounts
  induction accounts with
  | nil => intro _ _ returned; cases returned; rfl
  | cons account rest ih =>
    intro before after returned
    unfold updateCallee at returned
    split at returned
    · cases returned
    · rename_i middle step
      exact (ih returned).trans (updateCalleeOne_buffer_L copied step)

/-- A returned local length is the exact callee account length. -/
theorem updateCallerOne_length {profile : Profile} {context : InvCtx}
    {before after : InvState} {account : Translated} {length : Nat}
    (returned : updateCallerOne profile context before account = .ok (after, length)) :
    length = (before.ts.acct account.t).data.length := by
  unfold updateCallerOne at returned
  simp only at returned
  split at returned
  · cases returned
  · split at returned <;> cases returned <;> rfl

/-- Only selected, callee-writable entries create local length writes. This
does not add a write for an unused AccountInfo merely because its old length
appears in the ordinary answer encoding. -/
theorem updateCaller_lengths {profile : Profile} {context : InvCtx}
    {P : Nat → Nat → Prop} :
    ∀ {accounts : List Translated} {before after : InvState} {lengths : List (Nat × Nat)},
      (∀ account ∈ accounts, account.calleeWritable = true →
        ∀ first last length, updateCallerOne profile context first account = .ok (last, length) →
          P account.infoIdx length) →
      updateCaller profile context before accounts = .ok (after, lengths) →
      ∀ output ∈ lengths, P output.1 output.2 := by
  intro accounts
  induction accounts with
  | nil => intro _ _ _ _ returned; cases returned; simp
  | cons account rest ih =>
    intro before after lengths each returned
    unfold updateCaller at returned
    split at returned
    · exact ih (fun next member => each next (List.mem_cons_of_mem account member)) returned
    · rename_i writes
      have writable : account.calleeWritable = true := by
        cases h : account.calleeWritable <;> simp_all
      split at returned
      · cases returned
      · rename_i middle length step
        split at returned
        · cases returned
        · rename_i final tail finished
          cases returned
          intro output member
          rcases List.mem_cons.mp member with rfl | member
          · exact each account (List.mem_cons_self ..) writable before middle length step
          · exact ih (fun next member => each next (List.mem_cons_of_mem account member))
              finished output member

/-- Concrete serialized destinations fit the owned input region. The data
extent includes both the original view and the permitted growth reserve, since
shrinking clears the former suffix. These are input layout facts, independent
of a future callee result. -/
structure RestoreBounds (profile : Profile) (context : InvCtx) (size : Nat)
    (account : Translated) : Prop where
  lamports : account.inRegion = true →
    account.ser.offset + context.abi.lamportsOff + 8 ≤ size
  owner : account.inRegion = true →
    account.ser.offset + context.abi.ownerOff account.ser.entryLen + 32 ≤ size
  length : account.inRegion = true → account.ser.offset + context.abi.lenOff + 8 ≤ size
  original : account.inRegion = true → context.dataStart account.ser + account.info.dataLen ≤ size
  reserved : account.inRegion = true → context.dataStart account.ser +
    (account.ser.entryLen + callerMaxIncrease profile context) ≤ size

/-- The fixed runtime rejects a result larger than the reserved region before
a successful copyback can be produced. -/
theorem returned_data_bounded {profile : Profile} {context : InvCtx}
    {before after : InvState} {account : Translated} {length : Nat}
    (checks : profile.features.pointerChecks = true)
    (returned : updateCallerOne profile context before account = .ok (after, length)) :
    (before.ts.acct account.t).data.length ≤
      account.ser.entryLen + callerMaxIncrease profile context := by
  unfold updateCallerOne at returned
  simp only [checks, Bool.true_or, Bool.and_true] at returned
  split at returned
  · cases returned
  · rename_i bounded
    exact Nat.le_of_not_gt (by simpa only [decide_eq_true_eq] using bounded)

/-- A successful runtime copyback fits the same physical byte footprint.
Its proof keeps the conditional suffix clearing and length write of the runtime. -/
theorem updateCallerOne_buffer_length {profile : Profile} {context : InvCtx}
    {before after : InvState} {account : Translated} {length : Nat}
    (checks : profile.features.pointerChecks = true)
    (bounds : RestoreBounds profile context before.buf.length account)
    (returned : updateCallerOne profile context before account = .ok (after, length)) :
    after.buf.length = before.buf.length := by
  have dataBound := returned_data_bounded checks returned
  unfold updateCallerOne at returned
  simp only at returned
  split at returned
  · cases returned
  · split at returned
    · cases returned
      rfl
    · rename_i inside
      have inRegion : account.inRegion = true := by
        cases h : account.inRegion <;> simp_all
      let value := before.ts.acct account.t
      let base := writeAt (writeAt before.buf (account.ser.offset + context.abi.lamportsOff)
        (u64le value.lamports)) (account.ser.offset + context.abi.ownerOff account.ser.entryLen)
        value.owner.bytes
      have lamports : (writeAt before.buf (account.ser.offset + context.abi.lamportsOff)
          (u64le value.lamports)).length = before.buf.length :=
        length_writeAt (by simpa only [u64le, length_leBytes] using bounds.lamports inRegion)
      have baseLength : base.length = before.buf.length := by
        dsimp only [base]
        rw [length_writeAt (by
          simpa only [lamports, Pubkey.length_eq] using bounds.owner inRegion), lamports]
      let cleared := if value.data.length < account.info.dataLen && context.cfg != .D then
        writeAt base (context.dataStart account.ser + value.data.length)
          (List.replicate (account.info.dataLen - value.data.length) 0) else base
      have clearedLength : cleared.length = before.buf.length := by
        dsimp only [cleared]
        split
        · rw [length_writeAt, baseLength]
          have := bounds.original inRegion
          simp only [List.length_replicate, baseLength]
          have : value.data.length < account.info.dataLen := by
            rename_i condition
            simp only [Bool.and_eq_true, decide_eq_true_eq] at condition
            exact condition.1
          omega
        · exact baseLength
      let metadata := if account.info.dataLen != value.data.length then
        writeAt cleared (account.ser.offset + context.abi.lenOff) (u64le value.data.length)
        else base
      have metadataLength : metadata.length = before.buf.length := by
        dsimp only [metadata]
        split
        · have fits : account.ser.offset + context.abi.lenOff + (u64le value.data.length).length ≤
              cleared.length := by
            simpa only [u64le, length_leBytes, clearedLength] using (bounds.length inRegion)
          rw [length_writeAt fits, clearedLength]
        · exact baseLength
      let bytes := if context.cfg != .D then
        writeAt metadata (context.dataStart account.ser) value.data else metadata
      have bytesLength : bytes.length = before.buf.length := by
        dsimp only [bytes]
        split
        · rw [length_writeAt, metadataLength]
          rw [metadataLength]
          have := bounds.reserved inRegion
          change context.dataStart account.ser + (before.ts.acct account.t).data.length ≤
            before.buf.length
          omega
        · exact metadataLength
      cases returned
      exact bytesLength

/-- The complete ordered copyback preserves the same region size. Repeated
metas do not create a second allocation or a separately realized after-state. -/
theorem updateCaller_buffer_length {profile : Profile} {context : InvCtx}
    (checks : profile.features.pointerChecks = true) :
    ∀ {accounts : List Translated} {before after : InvState} {lengths : List (Nat × Nat)},
      (∀ account ∈ accounts, RestoreBounds profile context before.buf.length account) →
      updateCaller profile context before accounts = .ok (after, lengths) →
      after.buf.length = before.buf.length := by
  intro accounts
  induction accounts with
  | nil => intro before after lengths _ returned; cases returned; rfl
  | cons account rest ih =>
    intro before after lengths bounds returned
    unfold updateCaller at returned
    split at returned
    · exact ih (fun next member => bounds next (List.mem_cons_of_mem account member)) returned
    · split at returned
      · cases returned
      · rename_i middle length updated
        have same := updateCallerOne_buffer_length checks (bounds account (List.mem_cons_self ..))
          updated
        split at returned
        · cases returned
        · rename_i final tail finished
          cases returned
          have restBounds : ∀ next ∈ rest, RestoreBounds profile context middle.buf.length next :=
            by
            intro next member
            rw [same]
            exact bounds next (List.mem_cons_of_mem account member)
          exact (ih restBounds finished).trans same

end Solanalib.Specs.Core.OpaqueCpi.Memory
