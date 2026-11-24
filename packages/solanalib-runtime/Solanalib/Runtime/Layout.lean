/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Borrowed

@[expose] public section

/-!
# The input buffer

The serialization of an instruction into the input buffer of an SBF program, in the aligned
layout of loaders v2, v3 and v4 (ABI v1) and the unaligned layout of loader v1 (ABI v0),
following `serialize_parameters_for_abiv1` and `serialize_parameters_for_abiv0` in Agave 4.3.2.
Offsets are relative to byte 0 of the buffer, whose VM address is `MM_INPUT_START`. In
configuration D the data and the realloc region are not part of the host buffer, and the VM
addresses of all fields are the same in the three configurations within the corresponding ABI.
The model keeps the bytes of configuration L in every configuration and routes the data regions
of configuration D to the accounts (cf. `Solanalib.Runtime.Memory`). The selected source
correspondence is configuration L; see
[serialization and read-back](../../source-notes/agave-4.3.2.md#serialization-and-read-back) and
[memory](../../source-notes/agave-4.3.2.md#memory) for the other configurations. -/

namespace Solanalib.Runtime

/-- The two layouts of the input buffer. -/
inductive Abi where
  /-- The unaligned layout of programs owned by `bpf_loader_deprecated`. -/
  | v0
  /-- The aligned layout of all other programs. -/
  | v1
  deriving DecidableEq, Repr

/-- The layout selected by the owner of the program account in
`serialize_parameters`, Agave 4.3.2. -/
def abiOfOwner (owner : Pubkey) : Abi :=
  if owner = Ids.bpfLoaderDeprecated then .v0 else .v1

/-- `(8 - n mod 8) mod 8`, the alignment padding after `n` data bytes. -/
def pad8 (n : Nat) : Nat := (8 - n % 8) % 8

/-- The serialized rent epoch: `u64::MAX` unconditionally in Agave 4.3.2.
The profile retains the historical gate for 3.1.12. -/
def rentEpochField (p : Profile) (a : Account) : Nat :=
  if p.rentEpochMasked then U64_MAX else a.rentEpoch

/-- The 8 header bytes of an aligned record: marker, flags and four zero bytes. -/
def headerV1 (signer writable executable : Bool) : Bytes :=
  [NON_DUP_MARKER, boolByte signer, boolByte writable, boolByte executable, 0, 0, 0, 0]

/-- The aligned record of a non-duplicate account
(`serialize_parameters_for_abiv1`, Agave 4.3.2). -/
def recordV1 (signer writable : Bool) (key : Pubkey) (a : Account) (rentEpoch : Nat) : Bytes :=
  headerV1 signer writable a.executable ++ (key.bytes ++ (a.owner.bytes ++ (u64le a.lamports ++
    (u64le a.data.length ++ (a.data ++
      (List.replicate (MAX_PERMITTED_DATA_INCREASE + pad8 a.data.length) 0 ++ u64le rentEpoch))))))

/-- The unaligned record of a non-duplicate account
(`serialize_parameters_for_abiv0`, Agave 4.3.2). -/
def recordV0 (signer writable : Bool) (key : Pubkey) (a : Account) (rentEpoch : Nat) : Bytes :=
  [NON_DUP_MARKER, boolByte signer, boolByte writable] ++ (key.bytes ++ (u64le a.lamports ++
    (u64le a.data.length ++ (a.data ++ (a.owner.bytes ++ (boolByte a.executable :: u64le
      rentEpoch))))))

/-- The record of a duplicate: the index of the first occurrence, padded to 8 bytes in
the aligned layout (`serialize_parameters_for_abiv1` and
`serialize_parameters_for_abiv0`, Agave 4.3.2). -/
def dupRecord : Abi → Nat → Bytes
  | .v1, k => UInt8.ofNat k :: List.replicate 7 0
  | .v0, k => [UInt8.ofNat k]

/-- The role of an instruction account in the buffer. -/
inductive Slot where
  | dup (first : Nat)
  | acct (ia : InstrAcct)
  deriving DecidableEq, Repr

/-- The slot of instruction account `j`: a duplicate refers to the first occurrence. -/
def slotOf (f : Frame) (j : Nat) (ia : InstrAcct) : Slot :=
  match f.firstIdx ia.txIdx with
  | some k => if k < j then .dup k else .acct ia
  | none => .acct ia

theorem slotOf_acct {f : Frame} {j : Nat} {ia ia' : InstrAcct} (h : slotOf f j ia = .acct ia') :
    ia' = ia := by
  unfold slotOf at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- The slots of an instruction. -/
def slots (f : Frame) : List Slot := f.accounts.mapIdx (slotOf f)

/-- The record of a slot. -/
def slotRecord (abi : Abi) (p : Profile) (ts : TxState) : Slot → Bytes
  | .dup k => dupRecord abi k
  | .acct ia =>
    match abi with
    | .v1 => recordV1 ia.signer ia.writable (ts.key ia.txIdx) (ts.acct ia.txIdx)
        (rentEpochField p (ts.acct ia.txIdx))
    | .v0 => recordV0 ia.signer ia.writable (ts.key ia.txIdx) (ts.acct ia.txIdx)
        (rentEpochField p (ts.acct ia.txIdx))

/-- The records of an instruction, in instruction order. -/
def records (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) : List Bytes :=
  (slots f).map (slotRecord abi p ts)

/-- The offset of the record of instruction account `j`. -/
def recordOffset (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) (j : Nat) : Nat :=
  8 + prefixLen (records abi p ts f) j

/-- The offset of the instruction data; r2 holds `MM_INPUT_START` plus this offset. -/
def instrDataOffset (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) : Nat :=
  8 + (records abi p ts f).flatten.length + 8

/-- The buffer without the account pointer array of SIMD-0449. -/
def serializeBody (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) : Bytes :=
  u64le f.accounts.length ++ ((records abi p ts f).flatten ++
    (u64le f.data.length ++ (f.data ++ (ts.key f.programIdx).bytes)))

/-- The record offset of the first occurrence of instruction account `j`. -/
def firstOffset (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) (j : Nat) : Nat :=
  match (slots f)[j]? with
  | some (.dup k) => recordOffset abi p ts f k
  | _ => recordOffset abi p ts f j

/-- The account pointer array of SIMD-0449: one VM address per instruction account,
duplicates included (`serialize_parameters_for_abiv1`, Agave 4.3.2). -/
def pointerArray (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) : Bytes :=
  ((List.range f.accounts.length).map fun j =>
    u64le (MM_INPUT_START + firstOffset abi p ts f j)).flatten

/-- The raw input-buffer layout. Program entry uses `serializationAccountCheck`
before this encoding; `serializeChecked` exposes their combined boundary. -/
def serialize (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) : Bytes :=
  match abi with
  | .v1 =>
    if p.accountPointerArray then
      serializeBody abi p ts f ++ (List.replicate (pad8 (serializeBody abi p ts f).length) 0 ++
        pointerArray abi p ts f)
    else serializeBody abi p ts f
  | .v0 => serializeBody abi p ts f

/-- Admission to input serialization counts instruction account references,
including duplicates. Agave 4.3.2 checks this before choosing ABI v0 or v1
(`program-runtime/src/serialization.rs:253-256`). -/
def serializationAccountCheck (frame : Frame) : Except InstrError Unit :=
  if MAX_ACCOUNTS_PER_INSTRUCTION < frame.accounts.length then .error .MaxAccountsExceeded
  else .ok ()

theorem serializationAccountCheck_ok_iff (frame : Frame) :
    serializationAccountCheck frame = .ok () ↔ frame.accounts.length ≤ MAX_ACCOUNTS_PER_INSTRUCTION
      := by
  unfold serializationAccountCheck
  split <;> simp_all

theorem serializationAccountCheck_exceeded {frame : Frame}
    (exceeded : MAX_ACCOUNTS_PER_INSTRUCTION < frame.accounts.length) :
    serializationAccountCheck frame = .error .MaxAccountsExceeded := by
  simp [serializationAccountCheck, exceeded]

/-- The checked program-input serialization boundary. `serialize` remains the
byte-layout function used once this admission check has succeeded. -/
def serializeChecked (abi : Abi) (profile : Profile) (state : TxState) (frame : Frame) :
    Except InstrError Bytes := do
  serializationAccountCheck frame
  pure (serialize abi profile state frame)

theorem serializeChecked_ok {abi : Abi} {profile : Profile} {state : TxState} {frame : Frame}
    (admitted : frame.accounts.length ≤ MAX_ACCOUNTS_PER_INSTRUCTION) :
    serializeChecked abi profile state frame = .ok (serialize abi profile state frame) := by
  simp [serializeChecked, serializationAccountCheck, Nat.not_lt.mpr admitted]
  rfl

theorem serializeChecked_exceeded {abi : Abi} {profile : Profile} {state : TxState} {frame : Frame}
    (exceeded : MAX_ACCOUNTS_PER_INSTRUCTION < frame.accounts.length) :
    serializeChecked abi profile state frame = .error .MaxAccountsExceeded := by
  simp [serializeChecked, serializationAccountCheck, exceeded]
  rfl

/-! ## Positions of the accounts -/

/-- The serialized position of an instruction account, fixed for the invocation: the
record offset and the data length at serialization, which Agave keeps as
`SerializedAccountMetadata::original_data_len`. See
[serialization](../../source-notes/agave-4.3.2.md#serialization-and-read-back). -/
structure SerAcct where
  pos : Nat
  ia : InstrAcct
  slot : Slot
  offset : Nat
  entryLen : Nat
  deriving DecidableEq, Repr

/-- The positions of all instruction accounts. -/
def layout (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) : List SerAcct :=
  f.accounts.mapIdx fun j ia =>
    { pos := j, ia := ia, slot := slotOf f j ia, offset := recordOffset abi p ts f j,
      entryLen := (ts.acct ia.txIdx).data.length }

/-- The offset of the lamports in a record. -/
def Abi.lamportsOff : Abi → Nat
  | .v1 => 72
  | .v0 => 35

/-- The offset of the data-length field in a record. -/
def Abi.lenOff : Abi → Nat
  | .v1 => 80
  | .v0 => 43

/-- The offset of the data in a record. -/
def Abi.dataOff : Abi → Nat
  | .v1 => 88
  | .v0 => 51

/-- The offset of the owner in a record whose data had `len` bytes at serialization. -/
def Abi.ownerOff (abi : Abi) (len : Nat) : Nat :=
  match abi with
  | .v1 => 40
  | .v0 => 51 + len

/-- The offset of the key in a record. -/
def Abi.keyOff : Abi → Nat
  | .v1 => 8
  | .v0 => 3

/-- The address space reserved for the data of an account with `len` bytes at entry:
the realloc region exists only in the aligned layout. See
[memory](../../source-notes/agave-4.3.2.md#memory). -/
def Abi.reserved (abi : Abi) (len : Nat) : Nat :=
  match abi with
  | .v1 => len + MAX_PERMITTED_DATA_INCREASE
  | .v0 => len

/-- The maximal growth of an account in one instruction: 10 KiB, and none for a
loader-v1 program, whose `deserialize_parameters_for_abiv0` ignores the length field. -/
def Abi.maxIncrease (abi : Abi) : Nat :=
  match abi with
  | .v1 => MAX_PERMITTED_DATA_INCREASE
  | .v0 => 0

/-! ## Field placement -/

theorem length_headerV1 (s w e : Bool) : (headerV1 s w e).length = 8 := rfl

theorem length_recordV1 (s w : Bool) (k : Pubkey) (a : Account) (re : Nat) :
    (recordV1 s w k a re).length = 96 + a.data.length + MAX_PERMITTED_DATA_INCREASE + pad8
      a.data.length := by
  simp [recordV1, headerV1, k.length_eq, a.owner.length_eq, u64le]
  omega

theorem slice_serialize_record {abi : Abi} {p : Profile} {ts : TxState} {f : Frame} {j k n : Nat}
    (hj : j < (records abi p ts f).length) (h : k + n ≤ (records abi p ts f)[j].length) :
    slice (serialize abi p ts f) (recordOffset abi p ts f j + k) n =
      slice (records abi p ts f)[j] k n := by
  have hle := prefixLen_le_length hj
  have hbody : slice (serializeBody abi p ts f) (recordOffset abi p ts f j + k) n =
      slice (records abi p ts f)[j] k n := by
    unfold serializeBody recordOffset
    rw [slice_append_right (by simp only [u64le, length_leBytes]; omega)]
    simp only [u64le, length_leBytes]
    rw [show 8 + prefixLen (records abi p ts f) j + k - 8 = prefixLen (records abi p ts f) j + k
      by omega]
    rw [slice_append_left (by omega)]
    exact slice_flatten hj h
  have hlen : recordOffset abi p ts f j + k + n ≤ (serializeBody abi p ts f).length := by
    unfold serializeBody recordOffset
    simp only [List.length_append, u64le, length_leBytes]
    omega
  unfold serialize
  cases abi with
  | v0 => exact hbody
  | v1 =>
    simp only
    split
    · rw [slice_append_left hlen]; exact hbody
    · exact hbody

theorem slots_length (f : Frame) : (slots f).length = f.accounts.length := by
  simp [slots]

theorem records_length (abi : Abi) (p : Profile) (ts : TxState) (f : Frame) :
    (records abi p ts f).length = f.accounts.length := by
  simp [records, slots_length]

theorem slots_getElem (f : Frame) (j : Nat) (hj : j < (slots f).length) :
    (slots f)[j] = slotOf f j (f.accounts[j]'(by simpa [slots_length] using hj)) := by
  simp [slots]

/-- The four bytes at offset 4 of an aligned record are zero. -/
theorem recordV1_padding (s w : Bool) (k : Pubkey) (a : Account) (re : Nat) :
    slice (recordV1 s w k a re) 4 4 = [0, 0, 0, 0] := by
  unfold recordV1
  rw [slice_append_left (by simp [headerV1])]
  rfl

/-- The fields of the record of a non-duplicate account in the aligned layout. -/
theorem recordV1_fields (s w : Bool) (k : Pubkey) (a : Account) (re : Nat) :
    slice (recordV1 s w k a re) 0 1 = [NON_DUP_MARKER] ∧
    slice (recordV1 s w k a re) 8 32 = k.bytes ∧
    slice (recordV1 s w k a re) 40 32 = a.owner.bytes ∧
    slice (recordV1 s w k a re) 72 8 = u64le a.lamports ∧
    slice (recordV1 s w k a re) 80 8 = u64le a.data.length ∧
    slice (recordV1 s w k a re) 88 a.data.length = a.data := by
  have hk := k.length_eq
  have ho := a.owner.length_eq
  have h8 : ∀ x, (u64le x).length = 8 := fun x => by simp [u64le]
  have hh := length_headerV1 s w a.executable
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · unfold recordV1
    rw [slice_append_right (by omega), hh, slice_append_left (by omega), ← hk, slice_all]
  · unfold recordV1
    rw [slice_append_right (by omega), slice_append_right (by simp only [hh, hk]; omega),
      slice_append_left (by simp only [hh, hk, ho]; omega)]
    simp only [hh, hk]
    exact slice_zero_of_length ho
  · unfold recordV1
    rw [slice_append_right (by omega), slice_append_right (by simp only [hh, hk]; omega),
      slice_append_right (by simp only [hh, hk, ho]; omega),
      slice_append_left (by simp only [hh, hk, ho, h8]; omega)]
    simp only [hh, hk, ho]
    exact slice_zero_of_length (h8 a.lamports)
  · unfold recordV1
    rw [slice_append_right (by omega), slice_append_right (by simp only [hh, hk]; omega),
      slice_append_right (by simp only [hh, hk, ho]; omega),
      slice_append_right (by simp only [hh, hk, ho, h8]; omega),
      slice_append_left (by simp only [hh, hk, ho, h8]; omega)]
    simp only [hh, hk, ho, h8]
    exact slice_zero_of_length (h8 a.data.length)
  · unfold recordV1
    rw [slice_append_right (by omega), slice_append_right (by simp only [hh, hk]; omega),
      slice_append_right (by simp only [hh, hk, ho]; omega),
      slice_append_right (by simp only [hh, hk, ho, h8]; omega),
      slice_append_right (by simp only [hh, hk, ho, h8]; omega),
      slice_append_left (by simp only [hh, hk, ho, h8]; omega)]
    simp only [hh, hk, ho, h8]
    exact slice_zero_of_length rfl

end Solanalib.Runtime
