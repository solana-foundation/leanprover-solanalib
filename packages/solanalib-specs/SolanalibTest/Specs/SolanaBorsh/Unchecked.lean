/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaBorsh.Unchecked

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaBorsh

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem unchecked_accepts_trailing_bytes :
    Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_run
      Solanalib.Specs.SolanaBorsh.v1.try_from_slice_unchecked_sample
      (4 : Nat) [12, 99, 3] (.returned (.ok (12 : UInt8)) (5 : Nat)) :=
  ⟨.returned (.ok (12 : UInt8), [99, 3]) (5 : Nat), rfl, rfl⟩

theorem unchecked_empty_error_changes_callback_state :
    Borsh.tryFromSliceUnchecked (Callback.ofFunction Borsh.byteDeserializer)
      4 [] (.returned (.error .unexpectedEof) 5) :=
  ⟨.returned (.error .unexpectedEof, []) 5, rfl, rfl⟩

theorem unchecked_does_not_invent_success :
    ¬ Borsh.tryFromSliceUnchecked (Callback.ofFunction Borsh.byteDeserializer)
      4 [] (.returned (.ok 0) 5) := by
  rw [Borsh.unchecked_returned_iff]
  rintro ⟨remaining, impossible⟩
  cases impossible

def unwindAfterRead (state : Nat) (_ : Solanalib.Runtime.Bytes) :
    Outcome Nat (Except Nat Nat × Solanalib.Runtime.Bytes) String String :=
  .unwound "decode" (state + 3)

theorem unchecked_forwards_unwind_state :
    Borsh.tryFromSliceUnchecked (Callback.ofFunction unwindAfterRead)
      4 [12, 99] (.unwound "decode" 7) :=
  ⟨.unwound "decode" 7, rfl, rfl⟩

def terminalWriter (_ : Solanalib.Runtime.Bytes) (_ : Solanalib.Runtime.Bytes) :
    Outcome Solanalib.Runtime.Bytes (Except Nat Unit) String String := .terminated "io-abor\
      t"

theorem byte_writer_forwards_terminal :
    Borsh.serializeBytes (Callback.ofFunction terminalWriter)
      [1] [9, 8] (.terminated "io-abort") := rfl

def partialWriter (state bytes : Solanalib.Runtime.Bytes) :
    Outcome Solanalib.Runtime.Bytes (Except Nat Unit) String String :=
  .returned (.error 6) (state ++ bytes.take 1)

theorem byte_writer_preserves_partial_error :
    Borsh.serializeBytes (Callback.ofFunction partialWriter)
      [1] [9, 8] (.returned (.error 6) [1, 9]) := rfl

theorem bind_unwind_does_not_run_continuation :
    Outcome.bind (.unwound "first" 7 : Outcome Nat Nat String String)
      (fun value state => .returned (value + 1) (state + 100)) =
      .unwound "first" 7 := rfl

end SolanalibTest.Specs.SolanaBorsh
