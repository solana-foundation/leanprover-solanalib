/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaInstruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaInstruction

open Solanalib.Specs.SolanaInstruction

theorem writable_non_signer_constructor :
    (AccountMeta.new_model () (.zero, false)).1 =
      (⟨.zero, 0, 1⟩ : _root_.Solanalib.Runtime.CpiMeta) := rfl

theorem readonly_signer_constructor :
    (AccountMeta.new_readonly_model () (.zero, true)).1 =
      (⟨.zero, 1, 0⟩ : _root_.Solanalib.Runtime.CpiMeta) := rfl

/-- Two metas for the same address remain two ordered entries with distinct
flags, and the instruction retains embedded zero bytes. -/
theorem construction_keeps_duplicates_flags_and_data :
    Solanalib.Specs.Core.Instruction.make .zero
      [(AccountMeta.new_model () (.zero, false)).1,
        (AccountMeta.new_readonly_model () (.zero, true)).1] [9, 0, 7] =
      (⟨.zero, [⟨.zero, 0, 1⟩, ⟨.zero, 1, 0⟩], [9, 0, 7]⟩ :
        _root_.Solanalib.Runtime.CpiInstruction) := rfl

end SolanalibTest.Specs.SolanaInstruction
