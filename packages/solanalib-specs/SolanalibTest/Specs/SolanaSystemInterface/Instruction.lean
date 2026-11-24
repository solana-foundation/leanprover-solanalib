/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSystemInterface

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSystemInterface

open Solanalib.Specs.SolanaSystemInterface.instruction

def transferArgs : TransferArgs := ⟨.zero, .zero, 0x0102030405060708⟩

theorem transfer_exact_tag_and_little_endian_amount :
    (transfer_model () transferArgs).1.data = [2, 0, 0, 0, 8, 7, 6, 5, 4, 3, 2, 1] := rfl

theorem transfer_keeps_duplicate_keys_and_distinct_flags :
    (transfer_model () transferArgs).1.metas =
      [⟨.zero, 1, 1⟩, ⟨.zero, 0, 1⟩] := rfl

def createArgs : CreateAccountArgs :=
  ⟨.zero, _root_.Solanalib.Runtime.Pubkey.ofNat 2, 7, 32, _root_.Solanalib.Runtime.Pubkey.ofNat 9⟩

theorem create_account_exact_data :
    (create_account_model () createArgs).1.data =
      [0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0] ++
        createArgs.owner.bytes := rfl

theorem create_account_account_order_and_flags :
    (create_account_model () createArgs).1.metas =
      [⟨createArgs.fromAddress, 1, 1⟩, ⟨createArgs.toAddress, 1, 1⟩] := rfl

end SolanalibTest.Specs.SolanaSystemInterface
