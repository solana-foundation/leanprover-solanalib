/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserialize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.EntryDeserialize.Pinocchio

/-- Initialized slots carry stable pointer tokens. Newly written tokens are the unique-header
offsets; a source binding must map them to the input pointer plus that offset, retaining provenance.
Existing suffix tokens may designate other allocations and keep their original interpretation.
`none` is uninitialized; the untouched suffix survives a shorter subsequent call. -/
structure State where
  bytes : Solanalib.Runtime.Bytes
  outputs : List (Option Nat)
  deriving DecidableEq, Repr

structure Result where
  views : Views
  count : Nat
  deriving DecidableEq, Repr

/-- The const generic is at most MAX_TX_ACCOUNTS. The actual source writes slot zero
before any capacity test for a nonempty input, so MAX_ACCOUNTS = 0 then is inadmissible.
This is a mathematical memory-bound condition, separate from pointer/provenance ownership. -/
def Admitted (maximum : Nat) (before : State) : Prop :=
  maximum ≤ 254 ∧ before.outputs.length = maximum ∧
    ∃ parsed, parse before.bytes = some parsed ∧ parsed.slots.length ≤ 254 ∧
      (parsed.slots = [] ∨ 0 < maximum)

/-- Fill exactly the returned prefix, retain the suffix, and leave every input byte alone.
Excess entries are still parsed to locate the instruction data and program id. -/
def execute (maximum : Nat) (before : State) : Option (Result × State) := do
  let parsed ← parse before.bytes
  let count := min parsed.slots.length maximum
  let initialized := (parsed.accounts.take count).map (fun account => some account.offset)
  pure (⟨parsed.views, count⟩, { before with outputs := initialized ++ before.outputs.drop count })

/-- The source const generic, lifted to the universe of the common family. -/
structure Index : Type 1 where
  maximum : Nat

def family : Family where
  Index := Index
  State := fun _ => State
  Args := fun _ => Unit
  Value := fun _ => Result
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun index => .returning (fun before _ => Admitted index.maximum before)
    (fun before _ result after => execute index.maximum before = some (result, after))

def run : FamilyRun family := fun index before _ outcome =>
  match outcome with
  | .returned result after => execute index.maximum before = some (result, after)
  | .unwound impossible _ | .terminated impossible => nomatch impossible

theorem reference : FamilyReference family run := by
  intro maximum before args outcome _ step
  cases outcome with
  | returned result after => exact step
  | unwound impossible _ | terminated impossible => nomatch impossible

def sample : Index := ⟨0⟩

theorem hasExecution : FamilyHasExecution family run sample := by
  refine ⟨⟨emptyBytes, []⟩, (), .returned ⟨⟨16, .zero, 16, []⟩, 0⟩ ⟨emptyBytes, []⟩,
    ⟨by decide, rfl, ⟨_, parse_empty, by decide, Or.inl rfl⟩⟩, ?_⟩
  simp [run, execute, sample, parse_empty, Parsed.views, Parsed.instructionOffset,
    Parsed.accounts]
  rfl

theorem satisfiable : FamilySatisfiable family sample := hasExecution.satisfiable

/-- The source-call post retains the input bytes even when accounts were skipped. -/
theorem input_preserved (maximum : Nat) (before after : State) (result : Result)
    (returned : (family.contract ⟨maximum⟩).post before () (.returned result after)) :
    after.bytes = before.bytes := by
  change execute maximum before = some (result, after) at returned
  unfold execute at returned
  cases hp : parse before.bytes with
  | none => simp [hp] at returned
  | some parsed =>
    simp [hp] at returned
    rcases returned with ⟨_, rfl⟩
    rfl

/-- Parsing none of the accounts must still locate the instruction/program views correctly. -/
theorem empty_capacity (before : State) (parsed : Parsed)
    (parsedBytes : parse before.bytes = some parsed) :
    execute 0 before = some (⟨parsed.views, 0⟩, before) := by
  simp [execute, parsedBytes, Parsed.accounts]

/-- Capacity zero is not permission to pass a nonempty serialized input. -/
theorem zero_capacity_requires_empty (before : State) (admitted : Admitted 0 before) :
    ∃ parsed, parse before.bytes = some parsed ∧ parsed.slots = [] := by
  obtain ⟨_, _, parsed, hp, _, h⟩ := admitted
  exact ⟨parsed, hp, h.resolve_right (by omega)⟩

/-- The output prefix is determined by all parsed slots, independent of any old suffix. -/
theorem returned_fields (maximum : Nat) (before after : State) (result : Result)
    (parsed : Parsed) (parsedBytes : parse before.bytes = some parsed)
    (returned : (family.contract ⟨maximum⟩).post before () (.returned result after)) :
    result = ⟨parsed.views, min parsed.slots.length maximum⟩ ∧
      after = { before with outputs :=
        ((parsed.accounts.take (min parsed.slots.length maximum)).map
          (fun account => some account.offset) ++
        before.outputs.drop (min parsed.slots.length maximum)) } := by
  change execute maximum before = some (result, after) at returned
  simp [execute, parsedBytes] at returned
  exact ⟨returned.1.symm, by simpa using returned.2.symm⟩

/-- A successful deserializer never changes the capacity of the output array of the caller. -/
theorem output_length (maximum : Nat) (before after : State) (result : Result)
    (admitted : Admitted maximum before)
    (returned : (family.contract ⟨maximum⟩).post before () (.returned result after)) :
    after.outputs.length = before.outputs.length := by
  obtain ⟨_, capacity, parsed, parsedBytes, _, _⟩ := admitted
  obtain ⟨_, rfl⟩ := returned_fields maximum before after result parsed parsedBytes returned
  simp only [List.length_append, List.length_map, List.length_take, Parsed.accounts,
    List.length_drop]
  rw [Nat.min_eq_left (Nat.min_le_left _ _)]
  omega

end Solanalib.Specs.Core.EntryDeserialize.Pinocchio
