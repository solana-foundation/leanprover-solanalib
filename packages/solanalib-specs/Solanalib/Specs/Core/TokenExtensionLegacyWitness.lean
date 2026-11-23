/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacyUnpack
public import Solanalib.Specs.Core.TokenExtensionLegacySize
public import Solanalib.Specs.Core.TokenExtensionLegacyNewLength
public import Solanalib.Specs.Core.TokenExtensionKey

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solanalib.Specs.Core.Token.Legacy

open Owned

/-- Constant input bytes, the actual pure base codec, a trivial concrete base
destructor, and the finite vector ledger give a complete mathematical provider.
The operational family remains generic over other parsers and destructors. -/
def referenceUnpacker {Base : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base) : Unpacker where
  base :=
    { State := VectorState UInt8
      Reference := Bytes
      Base := Base
      Unwind := Empty
      Terminal := Empty
      length := List.length
      byteAt := fun _ bytes index => bytes[index.val]
      baseLength := baseLength
      accountType := accountType
      parse := fun before region outcome =>
        outcome = .returned (decode ((region.origin.drop region.offset).take region.length)) before
      dropBase := fun before _ outcome => outcome = .returned () before }
  Resource := Nat
  bytes := vectorReference
  doubleUnwind := fun _ _ _ _ => False

/-- The actual packed Mint decoder instantiates the older unpack family. -/
def mintUnpacker : Unpacker := referenceUnpacker mintLength .mint unpackMint

/-- A nonempty TLV tail after a complete initialized Mint and its padding. -/
def mintSampleBytes : Bytes :=
  List.replicate 45 0 ++ [1] ++ List.replicate 119 0 ++ [1, 0]

/-- The full base decoded from the sample, with no assumed parser return. -/
def mintSampleBase : Mint := ⟨none, 0, 0, true, none⟩

/-- Both older profiles execute the real Mint decoder, construct and destroy
the padding vector, and retain the exact one-byte input subrange in the result. -/
theorem mintSample_executes (requiresTlvByte : Bool) :
    unpack requiresTlvByte mintUnpacker [] mintSampleBytes
      (.returned (.ok ⟨mintSampleBase, .borrowed ⟨mintSampleBytes, 166, 1⟩⟩) [none]) := by
  apply unpack_success requiresTlvByte mintUnpacker [] [] [none] mintSampleBytes
    mintSampleBase (.borrowed ⟨mintSampleBytes, 166, 1⟩)
  · decide +kernel
  · rfl
  · have comparison : paddingMatches mintUnpacker [] mintSampleBytes (.returned true [none]) := by
      apply paddingMatches_returned mintUnpacker [] [some (List.replicate 83 0)] [none]
        mintSampleBytes (0 : Nat) (List.replicate 83 0)
      · rfl
      · rfl
      · exact ⟨List.replicate 83 0, rfl, rfl⟩
    have tail := unpackTail_compared requiresTlvByte mintUnpacker [] [none] mintSampleBytes true
      (by decide +kernel) (by cases requiresTlvByte <;> decide +kernel) comparison
    exact tail

/-- One nonempty fixed type exercises vector allocation, deduplication,
arithmetic, and destruction in the sizing sample. -/
def sizeSampleInput : List Kind := [⟨.immutableOwner, by decide⟩]

/-- The explicit packed Mint size parameter supplies the empty-input case too. -/
def sizeSample : Sizer := ⟨typeArrayReference, mintLength⟩

/-- A complete normal build of the temporary deduplication vector. -/
theorem sizeSample_build :
    buildVector .deduplicate typeArrayReference sizeSampleInput (0 : Nat) 0 [some []]
      (.returned (0 : Nat) [some [.immutableOwner]]) := by
  apply buildVector_step (after := [some [.immutableOwner]]) (bound := by decide +kernel)
    (values := [])
  · rfl
  · exact ⟨.returned () [some [.immutableOwner]], ⟨[], rfl, rfl⟩, rfl⟩
  · apply buildVector_done
    decide +kernel

/-- The sample result is 166 + 4, with its temporary allocation retired. -/
theorem sizeSample_executes :
    calculateAccountLength sizeSample [] sizeSampleInput (.returned (.ok 170) [none]) := by
  change if (sizeSampleInput : List Kind).length = 0 then _ else _
  rw [ite_eq_right (by decide +kernel)]
  refine ⟨.returned (0 : Nat) [some [.immutableOwner]], sizeSample_build,
    [.immutableOwner], rfl, .returned (.ok 4) [none], ?_, rfl⟩
  refine ⟨.returned () [none], ⟨[.immutableOwner], rfl, rfl⟩, ?_⟩
  rfl

/-- A complete required-init sample keeps a two-push contribution twice,
separated by a fee requirement. This is not an empty-list existence witness. -/
theorem requiredSample_executes :
    requiredInit typeArrayReference [] requiredSample
      (.returned (0 : Nat) [some (requiredInitValue requiredSample)]) := by
  change buildVector .required typeArrayReference requiredSample (0 : Nat) 0 [some []] _
  apply buildVector_required_step (after := [some [.nonTransferableAccount, .immutableOwner]])
    (bound := by decide +kernel)
  · refine ⟨.returned () [some [.nonTransferableAccount]], ⟨[], rfl, rfl⟩,
      .returned () [some [.nonTransferableAccount, .immutableOwner]],
      ⟨[.nonTransferableAccount], rfl, rfl⟩, rfl⟩
  · apply buildVector_required_step
      (after := [some [.nonTransferableAccount, .immutableOwner, .transferFeeAmount]])
      (bound := by decide +kernel)
    · exact ⟨.returned () [some [.nonTransferableAccount, .immutableOwner, .transferFeeAmount]],
        ⟨[.nonTransferableAccount, .immutableOwner], rfl, rfl⟩, rfl⟩
    · apply buildVector_required_step (after := [some (requiredInitValue requiredSample)])
        (bound := by decide +kernel)
      · refine ⟨.returned () [some [.nonTransferableAccount, .immutableOwner,
          .transferFeeAmount, .nonTransferableAccount]],
          ⟨[.nonTransferableAccount, .immutableOwner, .transferFeeAmount], rfl, rfl⟩,
          .returned () [some (requiredInitValue requiredSample)],
          ⟨[.nonTransferableAccount, .immutableOwner, .transferFeeAmount, .nonTransferableAccount],
            rfl, rfl⟩, rfl⟩
      · apply buildVector_done
        decide +kernel

/-- A declared two-byte variable extension is valid TLV without decoding its
payload as metadata. The size helper only requires its TLV framing. -/
def newLengthSampleBytes : Bytes := [19, 0, 2, 0, 7, 8]

/-- The exact requested packed length is supplied by a normal mathematical
trait-method interpretation; it does not prove a Rust serializer. -/
def newLengthSample : NewLength where
  reader := extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty) newLengthSampleBytes
  NewReference := Nat
  getPackedLen := fun before length outcome => outcome = .returned (.ok length) before
  kind := ⟨.tokenMetadata, by decide⟩
  accountType := .mint

/-- The variable-size sample executes its actual nonempty type-vector scan. -/
theorem newLengthSample_scans :
    getInfo newLengthSample.reader [] ()
      (.returned (.ok ((0 : Nat), 6)) [some [.tokenMetadata]]) := by
  change collectInfo
    (vectorReference : VectorOps (VectorState ExtensionType) ExtensionType Nat Empty Empty)
    (fun _ _ _ _ => False) 0 newLengthSampleBytes.length
    (fun _ index => newLengthSampleBytes[index.val]) 0 [some []] _
  apply collectInfo_push (after := [some [.tokenMetadata]]) (kind := .tokenMetadata)
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · decide +kernel
  · apply collectInfo_done
    decide +kernel

/-- Replacing a six-byte entry by a sixteen-byte entry yields 182 bytes, and
the temporary type vector is destroyed before the result is returned. -/
theorem newLengthSample_executes :
    getNewLength newLengthSample [] (12 : Nat) (.returned (.ok 182) [none]) := by
  refine ⟨.returned () [], rfl, .returned (.ok 12) [], rfl,
    .returned (.ok ((0 : Nat), 6)) [some [.tokenMetadata]], newLengthSample_scans,
    .returned () [none], ⟨[.tokenMetadata], rfl, rfl⟩, ?_⟩
  change (Outcome.returned (.ok 182) [none] : Outcome (VectorState ExtensionType)
    (Except Error Nat) Empty Empty) = .returned (.ok (newLengthValue .tokenMetadata .mint 6 12
      newLengthSampleBytes)) [none]
  simp [newLengthValue, oldExtensionLength, findExtension, decodeType, ExtensionType.decode,
    ExtensionType.accountType, tlvU16, newLengthSampleBytes, addHeader, accountLength,
    saturatingSizeAdd, adjustMultisigLength, multisigLength, Solanalib.Runtime.U64_MAX]

end Solanalib.Specs.Core.Token.Legacy
