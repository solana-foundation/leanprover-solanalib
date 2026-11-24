/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestHooks
public import Solanalib.Specs.Core.AccountInfo

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.TransferHookResolution

open Token (Error Bytes)

/-- The local panic sites reached by the reviewed transfer-hook helper.
The unwind or terminal behavior of the target is supplied at those actual sites. -/
inductive Panic where
  /-- The `PodSlice::data` of the source indexes past its physically stored records. -/
  | podSliceBounds (requested capacity : Nat)
  /-- The ordinary pubkey wrapper panics after an unsuccessful PDA syscall. -/
  | noViableProgramAddress
  deriving DecidableEq, Repr

/-- Resolver 0.9.0 reduces each requested privilege against the union of
the privileges of the same key in the current Execute instruction. A new key
keeps both requests. This differs from the later always-nonsigner resolver. -/
def deescalate (previous : List Solanalib.Runtime.CpiMeta) (item : Solanalib.Runtime.CpiMeta) :
  Solanalib.Runtime.CpiMeta :=
  let aliases := previous.filter (fun prior => prior.key == item.key)
  { item with
    signerByte := if aliases.isEmpty || aliases.any (fun prior => prior.signerByte != 0)
      then item.signerByte else 0
    writableByte := if aliases.isEmpty || aliases.any (fun prior => prior.writableByte != 0)
      then item.writableByte else 0 }

/-- Privilege reduction leaves the resolved address intact. -/
theorem deescalate_key (previous : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta) :
    (deescalate previous item).key = item.key := rfl

/-- A genuinely new account retains its requested signer and writable flags. -/
theorem deescalate_new (previous : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta)
    (fresh : previous.filter (fun prior => prior.key == item.key) = []) :
    deescalate previous item = item := by
  simp [deescalate, fresh]

/-- The source consults every alias in the current instruction. A signer
request is removed only when aliases exist and none of them is a signer. -/
theorem deescalate_signer (previous : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta) :
    (deescalate previous item).signerByte =
      if (previous.filter (fun prior => prior.key == item.key)).isEmpty ||
          (previous.filter (fun prior => prior.key == item.key)).any
            (fun prior => prior.signerByte != 0)
      then item.signerByte else 0 := rfl

/-- The corresponding writable check is independent of the signer check. -/
theorem deescalate_writable (previous : List Solanalib.Runtime.CpiMeta) (item :
  Solanalib.Runtime.CpiMeta) :
    (deescalate previous item).writableByte =
      if (previous.filter (fun prior => prior.key == item.key)).isEmpty ||
          (previous.filter (fun prior => prior.key == item.key)).any
            (fun prior => prior.writableByte != 0)
      then item.writableByte else 0 := rfl

/-- The first matching AccountInfo is selected, preserving aliases and the order of the
source slice. Equal keys need not identify equal data or lamport cells. -/
def findAccount (accounts : List AccountInfo.Value) (key : Solanalib.Runtime.Pubkey) :
    Option AccountInfo.Value :=
  accounts.find? (fun account => account.key == key)

/-- A matching head wins even if a later equal-key AccountInfo has different
borrow identities, flags or current bytes. -/
theorem findAccount_head (account : AccountInfo.Value) (rest : List AccountInfo.Value) :
    findAccount (account :: rest) account.key = some account := by
  simp [findAccount]

/-- `PodSlice<ExtraAccountMeta>::unpack` in spl-pod 0.5.1 checks the four-byte
count slot and the complete physical payload size. It does not check the
declared count against capacity; that later check belongs to `data()` and
panics, rather than returning a ProgramError. All reached POD alignments are
one. The result is the declared count and physical record capacity. -/
def podHeader (bytes : Bytes) : Except Error (Nat × Nat) := do
  if bytes.length < 4 then throw (.Custom 1)
  let payload := bytes.length - 4
  if payload % 35 ≠ 0 then
    throw (if payload / 35 = 0 then .Custom 1 else .Custom 2)
  return (Solanalib.Runtime.leNat (bytes.take 4), payload / 35)

/-- The local zero-copy range access follows successful PodSlice unpacking.
It distinguishes ordinary malformed-storage errors from the bounds
panic of the source, including a nonzero count in an empty physical payload. -/
def podAccess (bytes : Bytes) : Except (Error ⊕ Panic) Nat := do
  let (count, capacity) ← (podHeader bytes).mapError Sum.inl
  if capacity < count then throw (.inr (.podSliceBounds count capacity))
  return count

/-- A short POD buffer is an ordinary error, before any count is read. -/
theorem podHeader_short (bytes : Bytes) (short : bytes.length < 4) :
    podHeader bytes = .error (.Custom 1) := by
  unfold podHeader
  rw [ite_eq_left short]
  rfl

/-- A complete POD allocation with an oversized declared count reaches the
source bounds panic, not the later resolver or a buffer-size ProgramError. -/
theorem podAccess_bounds (bytes : Bytes) (count capacity : Nat)
    (header : podHeader bytes = .ok (count, capacity)) (over : capacity < count) :
    podAccess bytes = .error (.inr (.podSliceBounds count capacity)) := by
  unfold podAccess
  rw [header]
  change ((if capacity < count then Except.error (.inr (.podSliceBounds count capacity))
    else Except.ok count) : Except (Error ⊕ Panic) Nat) = _
  rw [ite_eq_left over]

/-- A valid active prefix can be empty and can leave unused physical records.
The source visits only the count selected here. -/
theorem podAccess_ok (bytes : Bytes) (count capacity : Nat)
    (header : podHeader bytes = .ok (count, capacity)) (fits : count ≤ capacity) :
    podAccess bytes = .ok count := by
  unfold podAccess
  rw [header]
  change ((if capacity < count then Except.error (.inr (.podSliceBounds count capacity))
    else Except.ok count) : Except (Error ⊕ Panic) Nat) = _
  rw [ite_eq_right (Nat.not_lt.mpr fits)]

/-- Program metadata appended to the caller is always readonly and nonsigner;
the chosen AccountInfo itself retains all of its original flags and aliases. -/
def readonlyMeta (key : Solanalib.Runtime.Pubkey) : Solanalib.Runtime.CpiMeta :=
  Instruction.accountMeta key false false

/-- Existing caller instruction bytes and its program ID are independent of
the Execute instruction used for resolution. Only these ordered metadata
suffixes are appended to the caller. -/
def appendedMetas (extra : List Solanalib.Runtime.CpiMeta) (validation : Option
  Solanalib.Runtime.Pubkey)
    (program : Solanalib.Runtime.Pubkey) : List Solanalib.Runtime.CpiMeta :=
  extra ++ validation.toList.map readonlyMeta ++ [readonlyMeta program]

/-- With no validation account, the helper adds only the hook program. -/
theorem appendedMetas_no_validation (program : Solanalib.Runtime.Pubkey) :
    appendedMetas [] none program = [readonlyMeta program] := rfl

/-- With validation, every resolved extra precedes validation, which precedes
the hook program. Neither of the four standard Execute accounts is appended. -/
theorem appendedMetas_validation (extra : List Solanalib.Runtime.CpiMeta)
    (validation program : Solanalib.Runtime.Pubkey) :
    appendedMetas extra (some validation) program =
      extra ++ [readonlyMeta validation, readonlyMeta program] := by
  simp [appendedMetas, List.append_assoc]

end Solanalib.Specs.Core.TransferHookResolution
