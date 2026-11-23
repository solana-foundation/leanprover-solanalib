/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import SolanalibTest.Conformance.Library.BorshVecHeap
import Solanalib.Specs.Core.InstructionClone
import Solanalib.Specs.Core.InstructionSystemExtended

/-!
The native profiles observe finite successful allocations and allocator-null
aborts. This index has no serializer error or unwind: the concrete data are
finite fixed-width fields and valid strings. The generic registered families
retain their independent error, unwind, cleanup and terminal providers.

Logical vector slots are fresh even for empty vectors; empty vectors require
no physical allocation. Observations read the current slots, including the
borrowed clone source. The native driver separately asserts distinct nonempty
buffers and absence of source mutation after mutating a returned clone.
-/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.InstructionExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh
open SolanalibTest.Conformance.Library.Families.Instructions

abbrev Value := Instruction.OwnedValue Nat Nat

structure State where
  metas : List (Option (List Instruction.Meta)) := []
  bytes : List (Option Solanalib.Runtime.Bytes) := []
  allocations : Nat := 0
  source : Option Value := none

def metasAt (state : State) (resource : Nat) : Option (List Instruction.Meta) :=
  state.metas[resource]?.bind id

def bytesAt (state : State) (resource : Nat) : Option Solanalib.Runtime.Bytes :=
  state.bytes[resource]?.bind id

abbrev Out (A : Type) := Outcome State A Empty String

/-- One physical request at the selected call site. A null allocator result
is terminal and supplies no invented post-state. -/
def allocate {A : Type} (failAt : Option Nat) (needed : Bool) (state : State)
    (value : A) (update : State → State) : Out A :=
  if needed && failAt == some (state.allocations + 1) then .terminated "allocation"
  else .returned value (update { state with
    allocations := state.allocations + if needed then 1 else 0 })

def metaFromList (failAt : Option Nat) (state : State) (values : List Instruction.Meta) : Out Nat :=
  allocate failAt (!values.isEmpty) state state.metas.length
    (fun after => { after with metas := after.metas ++ [some values] })

def byteFromList (failAt : Option Nat) (state : State) (values : Solanalib.Runtime.Bytes) : Out Nat
  :=
  allocate failAt (!values.isEmpty) state state.bytes.length
    (fun after => { after with bytes := after.bytes ++ [some values] })

def pushMeta (failAt : Option Nat) (state : State) (args : Nat × Instruction.Meta) : Out Unit :=
  match metasAt state args.1 with
  | none => .terminated "invalid metadata resource"
  | some values => allocate failAt true state ()
      (fun after => { after with metas := after.metas.set args.1 (some (values ++ [args.2])) })

def retireMeta (state : State) (resource : Nat) : State :=
  { state with metas := state.metas.set resource none }

def retireByte (state : State) (resource : Nat) : State :=
  { state with bytes := state.bytes.set resource none }

def metaVec (failAt : Option Nat) : Owned.VectorOps State Instruction.Meta Nat Empty String where
  current := metasAt
  empty := fun state => (state.metas.length, { state with metas := state.metas ++ [some []] })
  withCapacity := Callback.ofFunction fun _ _ => .terminated "uncalled with_capacity"
  fromList := Callback.ofFunction (metaFromList failAt)
  push := Callback.ofFunction (pushMeta failAt)
  extend := Callback.ofFunction fun _ _ => .terminated "uncalled extend"
  drop := Callback.ofFunction fun state resource => .returned () (retireMeta state resource)

def byteVec (failAt : Option Nat) : Owned.VectorOps State UInt8 Nat Empty String where
  current := bytesAt
  empty := fun state => (state.bytes.length, { state with bytes := state.bytes ++ [some []] })
  withCapacity := Callback.ofFunction fun _ _ => .terminated "uncalled with_capacity"
  fromList := Callback.ofFunction (byteFromList failAt)
  push := Callback.ofFunction fun _ _ => .terminated "uncalled push"
  extend := Callback.ofFunction fun _ _ => .terminated "uncalled extend"
  drop := Callback.ofFunction fun state resource => .returned () (retireByte state resource)

def doubleUnwind : Owned.DoubleUnwind State Empty String := fun _ impossible => nomatch impossible

theorem onUnwind_iff {S V T : Type} (double : Owned.DoubleUnwind S Empty T)
    (cleanup : List (Owned.DropAction S Empty T)) (pending final : Outcome S V Empty T) :
    Owned.onUnwind double cleanup pending final ↔ pending = final := by
  cases pending with
  | returned value state => exact eq_comm
  | unwound impossible _ => exact impossible.elim
  | terminated reason => exact (Owned.onUnwind_terminated double cleanup reason final).trans eq_comm

theorem protect_iff {S A V T : Type} (double : Owned.DoubleUnwind S Empty T)
    (cleanup : List (Owned.DropAction S Empty T)) (run : Callback.Run S A V Empty T)
    (before : S) (args : A) (final : Outcome S V Empty T) :
    Owned.protect double cleanup run before args final ↔ run before args final := by
  simp only [Owned.protect, onUnwind_iff]
  constructor
  · rintro ⟨_, h, rfl⟩; exact h
  · intro h; exact ⟨final, h, rfl⟩

theorem bind_graph {S A V N U T : Type} (run : Callback.Run S A V U T)
    (next : V → S → Outcome S N U T → Prop)
    (f : S → A → Outcome S V U T) (g : V → S → Outcome S N U T)
    (first : ∀ s a o, run s a o ↔ f s a = o)
    (later : ∀ v s o, next v s o ↔ g v s = o)
    (before : S) (args : A) (outcome : Outcome S N U T) :
    Callback.bind run next before args outcome ↔ Outcome.bind (f before args) g = outcome := by
  simp only [Callback.bind, first, later]
  constructor
  · rintro ⟨_, rfl, h⟩
    cases hf : f before args <;> simpa only [hf, Outcome.bind, eq_comm] using h
  · intro h
    refine ⟨_, rfl, ?_⟩
    cases hf : f before args <;> simpa only [hf, Outcome.bind, eq_comm] using h

def types : InstructionSystemExtended.Types := ⟨State, Nat, Nat, Empty, Empty, String⟩

abbrev Encode (Data : Type) := State → Data → Solanalib.Runtime.Bytes

def providers {Data : Type} (failAt : Option Nat) (encode : Encode Data) :
    InstructionBuilder.Providers (types.builder Data) where
  metaVec := metaVec failAt
  byteVec := byteVec failAt
  serialize := Callback.ofFunction fun before (_, data) =>
    Outcome.map Except.ok (byteFromList failAt before (encode before data))
  unwrapFailure := fun _ impossible => nomatch impossible
  doubleUnwind := doubleUnwind

def buildFn {Data : Type} (failAt : Option Nat) (encode : Encode Data)
    (programId : Solanalib.Runtime.Pubkey) (data : Data) (metas : Nat) (before : State) : Out Value
      :=
  Outcome.map (fun bytes => ⟨programId, metas, bytes⟩)
    (byteFromList failAt before (encode before data))

theorem build_graph {Data : Type} (failAt : Option Nat) (encode : Encode Data)
    (format : InstructionBuilder.Format) (programId : Solanalib.Runtime.Pubkey)
    (data : Data) (metas : Nat) (before : State) (outcome : Out Value) :
    InstructionBuilder.run (types.builder Data) format before
      ⟨programId, data, metas, providers failAt encode⟩ outcome ↔
      buildFn failAt encode programId data metas before = outcome := by
  unfold InstructionBuilder.run
  refine (protect_iff _ _ _ _ _ _).trans ?_
  simp only [InstructionBuilder.rawRun, providers, Callback.bind, Callback.ofFunction]
  cases h : byteFromList failAt before (encode before data) with
  | returned bytes after => simp [h, buildFn, Outcome.map, eq_comm] <;> rfl
  | unwound impossible _ => exact impossible.elim
  | terminated reason => simp [h, buildFn, Outcome.map, eq_comm] <;> rfl

def valueJson (state : State) (value : Value) : Json :=
  match value.observe (metasAt state) (bytesAt state) with
  | some observed => instructionJson observed
  | none => Json.str "unavailable owned instruction"

def sourceJson (state : State) : Json :=
  match state.source with
  | some source => valueJson state source
  | none => Json.null

def outcomeJson (borrowed : Bool) : Out Value → Json
  | .returned value state => returnedJson (valueJson state value)
      (if borrowed then sourceJson state else Json.null)
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => Json.mkObj [("exit", Json.str "terminated"), ("reason", Json.str reason)]

def observed (borrowed : Bool) (outcome : Out Value) (recorded : Json) : Bool :=
  outcomeJson borrowed outcome == recorded

def failure (args : Json) : Result (Option Nat) := do
  match ← field args "fail_at" with
  | .null => pure none
  | value => pure (some (← value.getNat?))

end SolanalibTest.Conformance.Library.Families.InstructionExtensions
