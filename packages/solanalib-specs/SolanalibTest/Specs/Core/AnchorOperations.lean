/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorContextOperations
public import Solanalib.Specs.Core.AnchorErrorCodeTables
public import Solanalib.Specs.Core.AnchorCodec

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core AnchorCodec AnchorErrorOperations

/-- A short write changes its fitting prefix and advances the cursor. -/
theorem short_write_keeps_mutation :
    (writeStep ⟨[0, 0, 0], 1⟩ [8, 9, 10]).writer = ⟨[0, 8, 9], 3⟩ ∧
    (writeStep ⟨[0, 0, 0], 1⟩ [8, 9, 10]).count = 2 := by decide

/-- An empty offered slice still reaches zero-byte memcpy when space remains;
an exhausted destination skips that dependency. -/
theorem empty_copy_and_exhaustion_differ :
    (writeStep ⟨[4], 0⟩ []).copy = some ⟨0, 1, [], 0⟩ ∧
    (writeStep ⟨[4], 1⟩ []).copy = none := by decide

/-- A reached copy may terminate, even when its byte count is zero. -/
abbrev terminatingCopy : WriteTypes :=
  { writeSample with copy := fun _ _ outcome => outcome = .terminated 17 }

/-- Empty input at exhausted capacity reaches neither copy nor error creation.
The same copy provider terminates if the destination still has capacity. -/
theorem exhausted_empty_write_skips_terminal_copy :
    (writeAllFamily.contract terminatingCopy).requires ⟨⟨[4], 1⟩, []⟩ [] ∧
    writeAllRun terminatingCopy ⟨⟨[4], 1⟩, []⟩ []
      (.returned (.ok ()) ⟨⟨[4], 1⟩, []⟩) :=
  ⟨trivial, ⟨.returned () [], rfl, rfl⟩⟩

theorem empty_write_with_capacity_keeps_terminal_copy :
    (writeAllFamily.contract terminatingCopy).requires ⟨⟨[4], 0⟩, []⟩ [] ∧
    writeAllRun terminatingCopy ⟨⟨[4], 0⟩, []⟩ [] (.terminated 17) :=
  ⟨trivial, ⟨.terminated 17, rfl, rfl⟩⟩

/-- An actual copy terminal cannot be presented as a returned result with an
invented post-state, whether the caller selects success or an ordinary error. -/
theorem terminal_copy_cannot_return
    (result : Except Borsh.IoError Unit) (after : WriteState (List WriteEvent)) :
    ¬ writeAllRun terminatingCopy ⟨⟨[4], 0⟩, []⟩ [9] (.returned result after) := by
  rintro ⟨copied, called, returned⟩
  change copied = .terminated 17 at called
  cases called
  cases returned

/-- Exhaustion skips even a terminating copy provider, then constructs the
ordinary WriteZero error without changing the old bytes or cursor. -/
theorem exhausted_nonempty_write_keeps_diagnostic_effect :
    writeAllRun terminatingCopy ⟨⟨[4], 1⟩, []⟩ [9]
      (.returned (.error Borsh.writeZeroError)
        ⟨⟨[4], 1⟩, [.errorCreated Borsh.writeZeroError]⟩) := by
  refine ⟨.returned () [], rfl, ?_⟩
  change Callback.map Except.error
    ((ambientFocus terminatingCopy.State).lift terminatingCopy.makeError)
    ⟨⟨[4], 1⟩, []⟩ Borsh.writeZeroError _
  refine ⟨.returned Borsh.writeZeroError
    ⟨⟨[4], 1⟩, [.errorCreated Borsh.writeZeroError]⟩, ?_, rfl⟩
  exact ⟨.returned Borsh.writeZeroError [.errorCreated Borsh.writeZeroError], rfl, rfl⟩

/-- Similar release tables cannot supply the diagnostic wording of one another. -/
theorem instruction_message_changed :
    CodeTables.v0_27_0[0].number = CodeTables.v0_32_1[0].number ∧
    CodeTables.v0_27_0[0].message ≠ CodeTables.v0_32_1[0].message := by decide

theorem released_code_counts :
    CodeTables.v0_27_0.size = 56 ∧ CodeTables.v0_29_0.size = 60 ∧
    CodeTables.v0_32_1.size = 77 ∧ CodeTables.v1_0_2.size = 77 ∧
    CodeTables.v1_1_2.size = 80 := by decide

open AnchorContextOperations

/-- Replacing a borrowed signer descriptor preserves all owned fields, including
the remaining-vector identity and its current contents. -/
theorem signer_replacement_keeps_current_vector :
    withSignerRun cpiSample.toCpiTypes [some [4]] (⟨7, 8, 0, [1]⟩, [2, 2])
      (.returned ⟨7, 8, 0, [2, 2]⟩ [some [4]]) := rfl

/-- A constructor allocates a fresh logical empty owner in a nonempty vector
state; it preserves an existing live vector and an already retired slot. -/
theorem signer_constructor_preserves_existing_vector_owners :
    (newWithSignerFamily.contract cpiSample).requires [some [4], none] cpiSampleArgs ∧
    (newWithSignerFamily.contract cpiSample).post [some [4], none] cpiSampleArgs
      (.returned ⟨42, 41, 2, [7, 7, 9]⟩ [some [4], none, some []]) := by
  have ready : EmptyReady cpiSample [some [4], none] :=
    ⟨Owned.vectorReference_laws.empty_current _, Owned.vectorReference_laws.empty_fresh _⟩
  exact ⟨ready, newWithSigner_reference cpiSample _ _ _ ready rfl⟩

def reusedEmpty : NewTypes :=
  { cpiSample with remaining := { cpiSample.remaining with empty := fun before => (0, before) } }

/-- An existing empty vector is still owned. Its zero length does not allow
the constructor to issue its logical identity a second time. -/
theorem existing_empty_owner_is_not_fresh :
    ¬ (newWithSignerFamily.contract reusedEmpty).requires [some []] cpiSampleArgs := by
  intro ready
  have fresh := ready.fresh
  change some [] = (none : Option (List Nat)) at fresh
  cases fresh

end SolanalibTest.Specs.Core.AnchorOperations
