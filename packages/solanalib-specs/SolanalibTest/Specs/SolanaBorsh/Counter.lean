/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

import Solanalib.Specs.SolanaBorsh.PackedLen
import Solanalib.Specs.SolanaBorsh.Capabilities

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaBorsh.Counter

open Solanalib.Contracts.Model Solanalib.Specs.Core BorshPackedLen

inductive Control where
  | writes (sizes : List Nat)
  | caught
  | done
  | loop

abbrev index (checked : Bool) : Index where
  State := List Nat
  Value := List Nat
  Error := Nat
  Unwind := Nat
  Terminal := Nat
  Control := Control
  EffectArg := Nat
  EffectValue := Unit
  wordBits := 2
  checkedOverflow := checked
  start := Control.writes
  command := fun
    | .writes [] => .done (.ok ())
    | .writes (size :: rest) => .write (List.replicate size 0)
        (fun | .ok _ => .writes rest | .error _ => .caught)
    | .caught => .effect 88 (fun _ => .done)
    | .done => .done (.ok ())
    | .loop => .advance .loop
  effects := Callback.ofFunction fun before tag => .returned () (before ++ [tag])
  overflow := Callback.ofFunction fun before _ => .unwound 77 (before ++ [77])

def executable (checked : Bool) : Executable (index checked) where
  effects := fun before tag => .returned () (before ++ [tag])
  overflow := fun before _ => .unwound (77 : Nat) (before ++ [77])
  effects_eq := rfl
  overflow_eq := rfl

-- After writing three bytes, the checked overflow is caught. Its failed write
-- does not change the private counter, and callback effects survive the catch.
example : Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run (index true) [] [3, 2]
    (.returned (.ok 3) [77, 88]) :=
  runFuel_sound (index true) (executable true) 4 (.writes [3, 2]) 0 [] _ rfl

example : ¬ Runs (index true) (.writes [3, 2]) 0 [] (.returned (.ok 1) [77, 88]) := by
  intro ran
  have exact := (runFuel_graph (index true) (executable true) 4 (.writes [3, 2]) 0 []
    (.returned (.ok 3) [77, 88]) rfl _).mp ran
  cases exact

-- The unchecked build wraps only the private count, without an overflow effect.
example : Solanalib.Specs.SolanaBorsh.v0_10.get_instance_packed_len_run (index false) [] [3, 2]
    (.returned (.ok 1) []) :=
  runFuel_sound (index false) (executable false) 3 (.writes [3, 2]) 0 [] _ rfl

-- Fuel exhaustion does not manufacture a Rust error or terminal outcome.
example : runFuel (index true) (executable true) 10 .loop 0 [] = none := rfl

-- The empty write_all default does not call the underlying writer.
example : (writeAll [] (fun (_ : Except Nat Unit) => Control.done) :
    Command Control Nat Unit Nat Nat) = .advance .done := rfl

def cratesIo : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def selectedBuild : Versioning.Build where
  package := "solana-borsh"
  version := "2.2.1"
  source := cratesIo
  dependencies := [⟨"borsh", "0.10.4", cratesIo⟩]

theorem compatible_packed_length_identities :
    ["2.2.1", "2.2.2", "2.9.0"].all (fun version => decide
      ((Solanalib.Specs.SolanaBorsh.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .v0_10_get_instance_packed_len =
        [⟨"solana-borsh", version, "solana_borsh::v0_10::get_instance_packed_len",
          "solana_borsh::v0_10::get_instance_packed_len"⟩])) = true := by decide +kernel

theorem compatible_counter_provider_admitted :
    (Solanalib.Specs.SolanaBorsh.Capabilities.catalog.forBuild { selectedBuild with
      version := "2.2.2"
      dependencies := [⟨"borsh", "0.10.5", cratesIo⟩] }).identities .v0_10_get_instance_packed_len
        ≠ [] := by
  decide +kernel

theorem outside_packed_length_range_rejected :
    ["2.2.0", "3.0.0", "2.2.2-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaBorsh.Capabilities.catalog.forBuild
        { selectedBuild with version := version }).identities .v0_10_get_instance_packed_len = []))
          = true := by
  decide +kernel

theorem incompatible_counter_providers_rejected :
    ["0.10.3", "0.11.0", "1.6.0", "0.10.5-rc.1"].all (fun version => decide
      ((Solanalib.Specs.SolanaBorsh.Capabilities.catalog.forBuild { selectedBuild with
        version := "2.2.2"
        dependencies := [⟨"borsh", version, cratesIo⟩] }).identities .v0_10_get_instance_packed_len
          = [])) =
      true := by decide +kernel

theorem unresolved_counter_providers_rejected :
    [[], [⟨"borsh", "0.10.5", cratesIo⟩, ⟨"borsh", "1.6.0", cratesIo⟩],
      [⟨"borsh", "0.10.5", ⟨"git", "https://example.invalid/borsh", "fork"⟩⟩]].all (fun dependencies =>
        decide ((Solanalib.Specs.SolanaBorsh.Capabilities.catalog.forBuild
          { selectedBuild with version := "2.2.2", dependencies := dependencies }).identities
            .v0_10_get_instance_packed_len = [])) = true := by decide +kernel

end SolanalibTest.Specs.SolanaBorsh.Counter
