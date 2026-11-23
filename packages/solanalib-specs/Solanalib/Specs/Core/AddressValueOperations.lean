/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Operations

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-! Pure key observations. Source storage and ABI obligations belong to the physical memory
interpretation; no SDK, standard-library or application body is proved. -/

def valueContract {Args Result : Type} (f : Args → Result) :
    Solanalib.Contracts.Model Unit Args Result :=
  .returning (fun _ _ => True) (fun before args result after =>
    result = f args ∧ after = before)

def valueModel {Args Result : Type} (f : Args → Result) (before : Unit) (args : Args) :
    Result × Unit := (f args, before)

theorem valueReference {Args Result : Type} (f : Args → Result) :
    (valueContract f).RealizedBy (valueModel f) := fun _ _ _ => ⟨rfl, rfl⟩

theorem valueSatisfiable {Args Result : Type} (f : Args → Result) (sample : Args) :
    (valueContract f).Satisfiable := ⟨(), sample, trivial⟩

/-- the derived array order of Rust compares unsigned bytes from first to last. -/
def compareBytes : Solanalib.Runtime.Bytes → Solanalib.Runtime.Bytes → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else compareBytes xs ys

def compare (args : Value × Value) : Ordering := compareBytes args.1.bytes args.2.bytes

theorem compareBytes_self (bytes : Solanalib.Runtime.Bytes) : compareBytes bytes bytes = .eq := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih => simp [compareBytes, ih]

theorem compare_self (value : Value) : compare (value, value) = .eq :=
  compareBytes_self value.bytes

end Solanalib.Specs.Core.Address.Operations
