/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.SplTokenMetadataInterface.Models

public import Solanalib.Specs.SplTokenMetadataInterface

@[expose] public section

open Solanalib.Contracts.Model

namespace SolanalibTest.Specs.SplTokenMetadataInterface

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token.MetadataInitialize

/-- The witness executes the source constructor and all five owned lifetimes. -/
theorem complete_construction : run Sample.index Sample.initial Sample.args
    (.returned Sample.returnedValue Sample.final) := Sample.executes

/-- Borsh counts bytes, so the non-ASCII symbol contributes two bytes. -/
theorem utf8_length_and_order : Sample.text.encoded =
    [1, 0, 0, 0, 78, 2, 0, 0, 0, 206, 163, 3, 0, 0, 0, 117, 114, 105] := by
  simp only [Text.encoded, Text.bytes, Sample.text, String.toUTF8_eq_toByteArray]
  decide +kernel

/-- Every moved input String and the empty serialization temporary is retired. -/
theorem local_cleanup_keeps_only_instruction :
    Sample.final.1[0]? = some none ∧ Sample.final.1[1]? = some none ∧
      Sample.final.1[2]? = some none ∧ Sample.final.1[4]? = some none ∧
      Sample.index.vectors.bytes.current Sample.final Sample.returnedValue.data =
        some (discriminator ++ Sample.text.encoded) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Updating the actual owner changes the text of the reached serializer. -/
theorem serializer_reads_current_owner :
    currentText Sample.index
      (Sample.initial.1.set 0 (some "changed".toUTF8.data.toList), Sample.initial.2)
        Sample.args.owners =
      some ⟨"changed", "Σ", "uri"⟩ := by
  simp only [currentText, Sample.index, Sample.stringCurrent, Sample.initial, Sample.args,
    Sample.text,
    String.toUTF8_eq_toByteArray]
  decide +kernel

/-- An absent owner cannot be replaced by a cached initial text snapshot. -/
theorem serializer_missing_owner_unwinds :
    Sample.toVec (Sample.initial.1.set 1 none, Sample.initial.2) Sample.args.owners =
       .unwound 98 (Sample.initial.1.set 1 none, Sample.initial.2) := by
  have nameDecoded : String.fromUTF8? ⟨"N".toByteArray.data⟩ = some "N" := by decide +kernel
  simp [Sample.toVec, Sample.readText, Sample.stringCurrent, Sample.initial, Sample.args,
    Sample.text, Owned.VectorState.current, nameDecoded]

/-- The constructor keeps all four positions even when two keys alias. -/
theorem metadata_alias_preserved :
    (metas Sample.args).length = 4 ∧
      ((metas Sample.args).map (·.signerByte)) = [0, 0, 0, 1] ∧
      ((metas Sample.args).map (·.key))[0]? = ((metas Sample.args).map (·.key))[1]? := by
        decide +kernel

end SolanalibTest.Specs.SplTokenMetadataInterface
