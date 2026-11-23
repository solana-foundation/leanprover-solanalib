/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address
public import Solanalib.Runtime.Syscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Instruction

universe u v

abbrev Meta := _root_.Solanalib.Runtime.CpiMeta
abbrev Value := _root_.Solanalib.Runtime.CpiInstruction

/-- Boolean SDK flags become canonical 0/1 flag values. The argument order is
the signer flag of the Rust AccountMeta constructor followed by writability. -/
def accountMeta (key : _root_.Solanalib.Runtime.Pubkey) (isSigner isWritable : Bool) : Meta where
  key := key
  signerByte := if isSigner then 1 else 0
  writableByte := if isWritable then 1 else 0

/-- A borrowed instruction meta retains the address-reference identity and
the two copied flags. In particular, callbacks need not be assumed to preserve
the observation obtained by following that reference in a later state. -/
structure RefMeta (AddressRef : Type u) where
  address : AddressRef
  isSigner : Bool
  isWritable : Bool

/-- Observe a retained reference at an explicitly chosen state/interpretation.
The caller supplies `keyAt`; this operation assumes no stability across calls. -/
def RefMeta.observe {AddressRef : Type u}
    (keyAt : AddressRef → _root_.Solanalib.Runtime.Pubkey) (entry : RefMeta AddressRef) : Meta :=
  accountMeta (keyAt entry.address) entry.isSigner entry.isWritable

@[simp] theorem RefMeta.observe_key {AddressRef : Type u}
    (keyAt : AddressRef → _root_.Solanalib.Runtime.Pubkey) (entry : RefMeta AddressRef) :
    (entry.observe keyAt).key = keyAt entry.address := rfl

@[simp] theorem RefMeta.observe_flags {AddressRef : Type u}
    (keyAt : AddressRef → _root_.Solanalib.Runtime.Pubkey) (entry : RefMeta AddressRef) :
    ((entry.observe keyAt).signerByte, (entry.observe keyAt).writableByte) =
      (if entry.isSigner then 1 else 0, if entry.isWritable then 1 else 0) := rfl

/-- Instruction construction preserves account order, repetitions and all data. -/
def make (programId : _root_.Solanalib.Runtime.Pubkey) (accounts : List Meta)
    (data : _root_.Solanalib.Runtime.Bytes) : Value := ⟨programId, accounts, data⟩

/-- An instruction retains the exact two vector-resource handles moved into
it. Resource validity and ownership belong to the explicit vector providers;
this carrier does not manufacture a separation or allocation proof. -/
structure OwnedValue (MetaResource : Type u) (ByteResource : Type v) where
  programId : _root_.Solanalib.Runtime.Pubkey
  metas : MetaResource
  data : ByteResource

/-- Read both retained vectors in the supplied current state. No snapshot of
the earlier contents of either vector is substituted for these observations. -/
def OwnedValue.observe {MetaResource : Type u} {ByteResource : Type v}
    (metasAt : MetaResource → Option (List Meta))
    (bytesAt : ByteResource → Option _root_.Solanalib.Runtime.Bytes)
    (instruction : OwnedValue MetaResource ByteResource) : Option Value := do
  let accounts ← metasAt instruction.metas
  let data ← bytesAt instruction.data
  pure (make instruction.programId accounts data)

theorem OwnedValue.observe_of_current {MetaResource : Type u} {ByteResource : Type v}
    (metasAt : MetaResource → Option (List Meta))
    (bytesAt : ByteResource → Option _root_.Solanalib.Runtime.Bytes)
    (instruction : OwnedValue MetaResource ByteResource)
    (accounts : List Meta) (data : _root_.Solanalib.Runtime.Bytes)
    (hm : metasAt instruction.metas = some accounts)
    (hd : bytesAt instruction.data = some data) :
    instruction.observe metasAt bytesAt =
      some (make instruction.programId accounts data) := by
  simp [OwnedValue.observe, hm, hd]

/-- The value observation of a fixed-size array. Its size can be zero. -/
structure ArrayValue (α : Type) where
  size : Nat
  values : List α
  length_eq : values.length = size

abbrev Seed := _root_.Solanalib.Runtime.Bytes
abbrev Signer := List Seed

def seedFromSlice (bytes : _root_.Solanalib.Runtime.Bytes) : Seed := bytes
def seedFromArray (array : ArrayValue UInt8) : Seed := array.values
def signerFromSlice (seeds : List Seed) : Signer := seeds
def signerFromArray (array : ArrayValue Seed) : Signer := array.values

@[simp] theorem make_metas (programId : _root_.Solanalib.Runtime.Pubkey) (accounts : List Meta)
    (data : _root_.Solanalib.Runtime.Bytes) : (make programId accounts data).metas = accounts := rfl

@[simp] theorem make_data (programId : _root_.Solanalib.Runtime.Pubkey) (accounts : List Meta)
    (data : _root_.Solanalib.Runtime.Bytes) : (make programId accounts data).data = data := rfl

/-- The public key of the System program. -/
def systemProgramId : _root_.Solanalib.Runtime.Pubkey := .zero

/-- The bincode u32 instruction tag followed by a little-endian u64. Bounds on
Rust integer arguments belong to the versioned constructor contracts. -/
def systemAmountData (tag amount : Nat) : _root_.Solanalib.Runtime.Bytes :=
  _root_.Solanalib.Runtime.u32le tag ++ _root_.Solanalib.Runtime.u64le amount

def systemTransfer (fromAddress toAddress : _root_.Solanalib.Runtime.Pubkey) (lamports : Nat) :
    Value :=
  make systemProgramId [accountMeta fromAddress true true, accountMeta toAddress false true]
    (systemAmountData 2 lamports)

def systemAllocate (address : _root_.Solanalib.Runtime.Pubkey) (space : Nat) : Value :=
  make systemProgramId [accountMeta address true true] (systemAmountData 8 space)

def systemAssign (address owner : _root_.Solanalib.Runtime.Pubkey) : Value :=
  make systemProgramId [accountMeta address true true] (_root_.Solanalib.Runtime.u32le 1 ++
    owner.bytes)

/-- `ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL`, decoded as 32 bytes. -/
def associatedTokenProgramId : _root_.Solanalib.Runtime.Pubkey :=
  .ofNat 0x8c97258f4e2489f1bb3d1029148e0d830b5a1399daff1084048e7bd8dbe9f859

/-- The helper only constructs this request. The supplied System/Token program
addresses are preserved; it neither validates them nor creates an account. -/
def associatedTokenCreateIdempotent (funding account wallet mint systemProgram tokenProgram :
    _root_.Solanalib.Runtime.Pubkey) : Value :=
  make associatedTokenProgramId
    [accountMeta funding true true, accountMeta account false true,
      accountMeta wallet false false, accountMeta mint false false,
      accountMeta systemProgram false false, accountMeta tokenProgram false false]
    [1]

end Solanalib.Specs.Core.Instruction
