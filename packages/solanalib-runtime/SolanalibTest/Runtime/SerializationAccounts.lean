/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Exec

@[expose] public section

set_option maxRecDepth 10000

open Solanalib.Runtime

namespace SolanalibTest.Runtime.SerializationAccountsTest

/-- Every entry refers to the same account: the serialization limit counts
references, not distinct transaction-account identities. -/
def repeated (count : Nat) : Frame :=
  { programIdx := 0, accounts := List.replicate count ⟨0, false, false⟩, data := [] }

theorem accepts_255_references : serializationAccountCheck (repeated 255) = .ok () := by
  simp [serializationAccountCheck, repeated, MAX_ACCOUNTS_PER_INSTRUCTION]

theorem rejects_256_references :
    serializationAccountCheck (repeated 256) = .error .MaxAccountsExceeded := by
  simp [serializationAccountCheck, repeated, MAX_ACCOUNTS_PER_INSTRUCTION]

theorem rejected_before_abi_selection (abi : Abi) (profile : Profile) (state : TxState) :
    serializeChecked abi profile state (repeated 256) = .error .MaxAccountsExceeded := by
  apply serializeChecked_exceeded
  simp [repeated, MAX_ACCOUNTS_PER_INSTRUCTION]

theorem admitted_encoding_unchanged (abi : Abi) (profile : Profile) (state : TxState) :
    serializeChecked abi profile state (repeated 255) = .ok (serialize abi profile state (repeated
      255)) := by
  apply serializeChecked_ok
  simp [repeated, MAX_ACCOUNTS_PER_INSTRUCTION]

/-- CPI instruction-size rejection occurs at a different boundary and uses a
syscall abort, rather than the serializer-specific instruction error. -/
theorem cpi_count_rejection_is_distinct :
    translateIx ⟨default, List.replicate 256 ⟨default, 0, 0⟩, []⟩ =
      .error .ProgramFailedToComplete := by
  simp [translateIx, MAX_CPI_INSTRUCTION_ACCOUNTS]

end SolanalibTest.Runtime.SerializationAccountsTest
