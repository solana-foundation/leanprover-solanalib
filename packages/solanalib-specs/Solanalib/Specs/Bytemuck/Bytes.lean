/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Bytemuck

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Bytemuck

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The source `bytemuck::PodCastError` of this version. -/
abbrev PodCastError := Solanalib.Specs.Core.Bytemuck.PodCastError

/-- `try_from_bytes::<T>` for every `T: AnyBitPattern`, indexed by the layout of `T` and decoding.
The slice length is checked before the alignment of the
slice address. Success returns a reference at the input address whose value is
decoded from the slice bytes. No state changes and no panic path exists. -/
def try_from_bytes_contract : Family where
  Index := Bytemuck.Decoding
  State := fun _ => Unit
  Args := fun _ => Bytemuck.SliceRef
  Value := fun decoding => Except PodCastError (Bytemuck.TypedRef decoding.Value)
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun decoding => .returning (fun _ _ => True)
    (fun before s result after => Bytemuck.TryFromBytesPost decoding s result ∧ after = before)

/-- The executable reference: `Bytemuck.tryFromBytes`, without a state change. -/
def try_from_bytes_model (decoding : Bytemuck.Decoding) (before : Unit)
    (s : Bytemuck.SliceRef) : Except PodCastError (Bytemuck.TypedRef decoding.Value) × Unit :=
  (Bytemuck.tryFromBytes decoding s, before)

/-- The graph of the executable reference at every index. -/
def try_from_bytes_run : FamilyRun try_from_bytes_contract := fun decoding =>
  returnsOf (try_from_bytes_model decoding)

/-- The registered sample: little-endian `u64` with alignment eight. -/
def try_from_bytes_sample : try_from_bytes_contract.Index := Bytemuck.Sample.u64Decoding

theorem try_from_bytes_reference : FamilyReference try_from_bytes_contract try_from_bytes_run := by
  intro decoding before s outcome _ execution
  cases outcome with
  | returned result after =>
    cases execution
    exact ⟨Bytemuck.tryFromBytes_post decoding s, rfl⟩
  | unwound reason _ => exact execution.elim
  | terminated reason => exact execution.elim

theorem try_from_bytes_satisfiable :
    FamilySatisfiable try_from_bytes_contract try_from_bytes_sample :=
  ⟨(), (⟨16, [1, 0, 0, 0, 0, 0, 0, 0]⟩ : Bytemuck.SliceRef), trivial⟩

theorem try_from_bytes_has_execution :
    FamilyHasExecution try_from_bytes_contract try_from_bytes_run try_from_bytes_sample :=
  ⟨(), (⟨16, [1, 0, 0, 0, 0, 0, 0, 0]⟩ : Bytemuck.SliceRef),
    .returned (.ok ⟨16, (1 : UInt64)⟩) (), trivial,
    show try_from_bytes_model Bytemuck.Sample.u64Decoding () ⟨16, [1, 0, 0, 0, 0, 0, 0, 0]⟩ =
      (.ok ⟨16, (1 : UInt64)⟩, ()) from rfl⟩

end Solanalib.Specs.Bytemuck

namespace Solanalib.Specs.Bytemuck.zeroable.Zeroable

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Default `Zeroable::zeroed::<T>` for every `T: Zeroable`, indexed by the layout of `T` and the
value stored by a valid pattern. It returns the value whose
`size_of::<T>()` bytes are all zero and changes no state. -/
def zeroed_contract : Family where
  Index := Bytemuck.Decoding
  State := fun _ => Unit
  Args := fun _ => Unit
  Value := fun decoding => decoding.Value
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun decoding => .returning (fun _ _ => True)
    (fun before _ value after =>
      value = decoding.decode (Bytemuck.zeroBytes decoding.layout) ∧ after = before)

/-- The executable reference: `Bytemuck.zeroed`, without a state change. -/
def zeroed_model (decoding : Bytemuck.Decoding) (before : Unit) (_ : Unit) :
    decoding.Value × Unit :=
  (Bytemuck.zeroed decoding, before)

/-- The graph of the executable reference at every index. -/
def zeroed_run : FamilyRun zeroed_contract := fun decoding =>
  returnsOf (zeroed_model decoding)

/-- The registered sample: little-endian `u64`. -/
def zeroed_sample : zeroed_contract.Index := Bytemuck.Sample.u64Decoding

theorem zeroed_reference : FamilyReference zeroed_contract zeroed_run := by
  intro decoding before args outcome _ execution
  cases outcome with
  | returned value after =>
    cases execution
    exact ⟨rfl, rfl⟩
  | unwound reason _ => exact execution.elim
  | terminated reason => exact execution.elim

theorem zeroed_satisfiable : FamilySatisfiable zeroed_contract zeroed_sample :=
  ⟨(), (), trivial⟩

theorem zeroed_has_execution :
    FamilyHasExecution zeroed_contract zeroed_run zeroed_sample :=
  ⟨(), (), .returned (0 : UInt64) (), trivial,
    show zeroed_model Bytemuck.Sample.u64Decoding () () = ((0 : UInt64), ()) by decide⟩

end Solanalib.Specs.Bytemuck.zeroable.Zeroable

namespace Solanalib.Specs.Bytemuck

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- `bytes_of::<T>` for every `T: NoUninit`, indexed by the layout and byte encoding of `T`. The
returned slice has the address of the reference and exactly the `size_of::<T>()` bytes of the value,
empty for a zero-sized `T`. No state changes;
the source cast never fails, so every exit is an ordinary return. -/
def bytes_of_contract : Family where
  Index := Bytemuck.Encoding
  State := fun _ => Unit
  Args := fun encoding => Bytemuck.TypedRef encoding.Value
  Value := fun _ => Bytemuck.SliceRef
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun encoding => .returning (fun _ _ => True)
    (fun before t slice after =>
      slice.address = t.address ∧ slice.bytes = encoding.encode t.value ∧ after = before)

/-- The executable reference: `Bytemuck.bytesOf`, without a state change. -/
def bytes_of_model (encoding : Bytemuck.Encoding) (before : Unit)
    (t : Bytemuck.TypedRef encoding.Value) : Bytemuck.SliceRef × Unit :=
  (Bytemuck.bytesOf encoding t, before)

/-- The graph of the executable reference at every index. -/
def bytes_of_run : FamilyRun bytes_of_contract := fun encoding =>
  returnsOf (bytes_of_model encoding)

/-- The registered sample: `u64` with little-endian bytes. -/
def bytes_of_sample : bytes_of_contract.Index := Bytemuck.Sample.u64Encoding

theorem bytes_of_reference : FamilyReference bytes_of_contract bytes_of_run := by
  intro encoding before t outcome _ execution
  cases outcome with
  | returned slice after =>
    cases execution
    exact ⟨rfl, rfl, rfl⟩
  | unwound reason _ => exact execution.elim
  | terminated reason => exact execution.elim

theorem bytes_of_satisfiable : FamilySatisfiable bytes_of_contract bytes_of_sample :=
  ⟨(), (⟨16, 0x0807060504030201⟩ : Bytemuck.TypedRef UInt64), trivial⟩

theorem bytes_of_has_execution :
    FamilyHasExecution bytes_of_contract bytes_of_run bytes_of_sample :=
  ⟨(), (⟨16, 0x0807060504030201⟩ : Bytemuck.TypedRef UInt64),
    .returned ⟨16, [1, 2, 3, 4, 5, 6, 7, 8]⟩ (), trivial,
    show bytes_of_model Bytemuck.Sample.u64Encoding () ⟨16, 0x0807060504030201⟩ =
      (⟨16, [1, 2, 3, 4, 5, 6, 7, 8]⟩, ()) by decide⟩

end Solanalib.Specs.Bytemuck
