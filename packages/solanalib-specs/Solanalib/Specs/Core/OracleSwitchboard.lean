/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfo
public import Solanalib.Specs.Core.BorrowValid

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Oracle.Switchboard

/-- Both recorded 64-bit layout choices give the same 3200-byte payload, but
they require different alignment for its i128-containing structures. -/
inductive Layout where
  /-- The 8-byte i128 alignment used by the Solana model profile. -/
  | i128Align8
  /-- The 16-byte i128 alignment of the recorded host profile. -/
  | i128Align16
  deriving DecidableEq, Repr

/-- Maximum field alignment under the explicitly selected layout. -/
def Layout.alignment : Layout → Nat
  | .i128Align8 => 8
  | .i128Align16 => 16

/-- The complete repr(C) payload size, excluding the account discriminator. -/
def payloadSize : Nat := 3200

/-- The exact eight-byte discriminator in the pinned Switchboard SDK. -/
def discriminator : Solanalib.Runtime.Bytes := [196, 27, 108, 196, 10, 215, 219, 40]

/-- Only these ordinary SDK errors can be produced by the selected parser. -/
inductive ParseError where
  /-- The discriminator is absent or differs from the expected eight bytes. -/
  | invalidDiscriminator
  /-- The account lacks the complete payload extent. -/
  | invalidData
  /-- The checked payload cannot satisfy its selected alignment. -/
  | accountDeserializeError
  deriving DecidableEq, Repr

/-- Reuse the same identified RefCell contents and views as AccountInfo.
The parser consumes an existing guard; it never acquires a new one. -/
abbrev State := AccountInfo.State

/-- A typed mapped reference retains the identity and current generation of the guard.
The record contains no snapshot of the account bytes of the feed. -/
structure FeedRef where
  /-- The current token of the original lease after mapping. -/
  guard : Borrow.Guard
  /-- The layout admitted by the successful cast. -/
  layout : Layout
  deriving DecidableEq, Repr

/-- `dataAddress` is the address of the input slice, supplied by an eventual
memory binding. A ghost account identity does not determine its alignment. -/
structure Args where
  /-- The already acquired guard; the Rust argument binds it to a shared reference. -/
  guard : Borrow.Guard
  /-- The explicit target layout used for the cast. -/
  layout : Layout
  /-- The actual modeled beginning of the input slice. -/
  dataAddress : Nat
  deriving DecidableEq, Repr

/-- A current byte view records its offset in the common backing cell. -/
structure Data where
  /-- Beginning of this view within the backing data cell. -/
  offset : Nat
  /-- Current bytes of the input view. -/
  bytes : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

/-- Observe the current byte slice of the live guard, rejecting malformed model
representations rather than supplying substitute data. -/
def read (state : State) (guard : Borrow.Guard) : Option Data := do
  let (view, content) ← (Borrow.current state guard).toOption
  let bytes ← (AccountInfo.projectBytes view content).toOption
  let offset := match view with | .whole => 0 | .bytesRange offset _ => offset
  pure ⟨offset, bytes⟩

/-- Protocol validity and a readable live input suffice for mathematical
progress and token retirement. Shared mode and physical slice bounds belong
to the separate Rust argument interpretation. -/
def Ready (state : State) (args : Args) : Prop :=
  state.Valid ∧ ∃ slot data,
    state.resolve args.guard = some slot ∧ read state args.guard = some data

/-- Exact local validation order, including the redundant sliced-length check.
All payload bit patterns are valid for the pinned repr(C) Pod structure; the
remaining `try_from_bytes` rejection is the actual payload-address alignment. -/
def prepare (args : Args) (data : Data) : Except ParseError AccountInfo.View :=
  if data.bytes.length < discriminator.length then .error .invalidDiscriminator
  else if data.bytes.take 8 ≠ discriminator then .error .invalidDiscriminator
  else if data.bytes.length < payloadSize + 8 then .error .invalidData
  else if ((data.bytes.drop 8).take payloadSize).length ≠ payloadSize then
    .error .invalidData
  else if (args.dataAddress + 8) % args.layout.alignment ≠ 0 then
    .error .accountDeserializeError
  else .ok (.bytesRange (data.offset + 8) payloadSize)

/-- Ordinary rejection drops exactly the input guard. Successful mapping
consumes its generation and keeps the same lease at the payload range. -/
def finish (state : State) (args : Args) (choice : Except ParseError AccountInfo.View) :
    Option (Except ParseError FeedRef × State) :=
  match choice with
  | .error error => match Borrow.release state args.guard with
    | (.ok (), after) => some (.error error, after)
    | (.error _, _) => none
  | .ok view => match Borrow.transfer state args.guard view with
    | (.ok guard, after) => some (.ok ⟨guard, args.layout⟩, after)
    | (.error _, _) => none

/-- A finite parser reference. `none` denotes an invalid supplied model guard,
not an SDK return value; the Ready premise excludes such representations. -/
def parse (state : State) (args : Args) : Option (Except ParseError FeedRef × State) := do
  let data ← read state args.guard
  finish state args (prepare args data)

/-- A successful local validation maps exactly the supplied live guard. -/
theorem parse_prepared (state : State) (args : Args) (data : Data) (view : AccountInfo.View)
    (slot : Borrow.Slot AccountInfo.View)
    (readable : read state args.guard = some data)
    (prepared : prepare args data = .ok view)
    (live : state.resolve args.guard = some slot) :
    parse state args = some
      (.ok ⟨⟨args.guard.id, args.guard.generation + 1⟩, args.layout⟩,
        (Borrow.transfer state args.guard view).2) := by
  simp [parse, readable, prepared, finish, Borrow.transfer_live live]

/-- A live guard supplies a finite finish for either a successful validation
or an ordinary validation error. -/
theorem finish_exists (state : State) (args : Args) (choice : Except ParseError AccountInfo.View)
    (slot : Borrow.Slot AccountInfo.View) (live : state.resolve args.guard = some slot) :
    ∃ result after, finish state args choice = some (result, after) := by
  cases choice with
  | error error => simp [finish, Borrow.release_live live]
  | ok view => simp [finish, Borrow.transfer_live live view]

/-- Every admitted input has a finite ordinary reference execution; no generic
progress assumption is being smuggled into the reference relation. -/
theorem parse_exists (state : State) (args : Args) (ready : Ready state args) :
    ∃ result after, parse state args = some (result, after) := by
  obtain ⟨_, slot, data, live, readable⟩ := ready
  simpa [parse, readable] using finish_exists state args (prepare args data) slot live

/-- Both finish branches preserve the borrow-state invariant and retire the
input token. A successful map makes its advanced generation the only live one. -/
theorem finish_valid_consumes (state : State) (args : Args)
    (choice : Except ParseError AccountInfo.View) (result : Except ParseError FeedRef)
    (after : State) (slot : Borrow.Slot AccountInfo.View)
    (valid : state.Valid) (live : state.resolve args.guard = some slot)
    (executed : finish state args choice = some (result, after)) :
    after.Valid ∧ after.resolve args.guard = none := by
  cases choice with
  | error error =>
    have same : (Borrow.release state args.guard).2 = after := by
      simpa [finish, Borrow.release_live live] using congrArg (Option.map Prod.snd) executed
    rw [← same]
    exact ⟨Borrow.release_valid valid args.guard, Borrow.release_consumes live⟩
  | ok view =>
    have same : (Borrow.transfer state args.guard view).2 = after := by
      simpa [finish, Borrow.transfer_live live view] using congrArg (Option.map Prod.snd) executed
    rw [← same]
    exact ⟨Borrow.transfer_valid valid args.guard view, Borrow.transfer_consumes live view⟩

/-- Every parser result from an admitted input preserves the borrow-state
invariant and prevents reuse of the consumed input generation. -/
theorem parse_valid_consumes (state : State) (args : Args)
    (result : Except ParseError FeedRef) (after : State)
    (ready : Ready state args) (executed : parse state args = some (result, after)) :
    after.Valid ∧ after.resolve args.guard = none := by
  obtain ⟨valid, slot, data, live, readable⟩ := ready
  exact finish_valid_consumes state args (prepare args data) result after slot valid live
    (by simpa [parse, readable] using executed)

/-- Mapping and rejection both preserve every backing account cell. -/
theorem finish_cells (state : State) (args : Args) (choice : Except ParseError AccountInfo.View)
    (result : Except ParseError FeedRef) (after : State)
    (executed : finish state args choice = some (result, after)) :
    after.cells = state.cells := by
  cases choice with
  | error error =>
      cases step : Borrow.release state args.guard with
      | mk returned next =>
        cases returned with
        | error reason => simp [finish, step] at executed
        | ok acknowledgement =>
          cases acknowledgement
          have same : next = after := by
            simpa [finish, step] using congrArg (Option.map Prod.snd) executed
          subst after
          simpa only [step] using Borrow.release_cells state args.guard
  | ok view =>
      cases step : Borrow.transfer state args.guard view with
      | mk returned next =>
        cases returned with
        | error reason => simp [finish, step] at executed
        | ok guard =>
          have same : next = after := by
            simpa [finish, step] using congrArg (Option.map Prod.snd) executed
          subst after
          simpa only [step] using Borrow.transfer_cells state args.guard view

/-- Parsing never mutates feed bytes, lamports or other backing cells. -/
theorem parse_cells (state : State) (args : Args) (result : Except ParseError FeedRef)
    (after : State) (executed : parse state args = some (result, after)) :
    after.cells = state.cells := by
  cases readable : read state args.guard with
  | none => simp [parse, readable] at executed
  | some data =>
      exact finish_cells state args (prepare args data) result after
        (by simpa [parse, readable] using executed)

/-- A free mathematical cell world, independent of any physical RefCell allocation. -/
def freeState (bytes : Solanalib.Runtime.Bytes) : State :=
  ⟨[⟨.data bytes, .refCell 64⟩, ⟨.lamports 42, .refCell 64⟩], []⟩

/-- Obtain the input guard through the common acquisition operation. -/
def sampleState (bytes : Solanalib.Runtime.Bytes) : State :=
  (Borrow.acquire (freeState bytes) ⟨0⟩ .shared .whole).2

/-- The witness includes extra trailing bytes; parse takes exactly the payload. -/
def sampleBytes : Solanalib.Runtime.Bytes := discriminator ++ List.replicate payloadSize 0 ++ [99,
  88]

/-- The discriminator is exactly the width copied by the source. -/
theorem discriminator_length : discriminator.length = 8 := rfl

/-- Compute the extent of the large fixture without expanding its replicated payload. -/
theorem sampleBytes_length : sampleBytes.length = 3210 := by
  simp only [sampleBytes, List.length_append, List.length_replicate,
    discriminator_length, payloadSize, List.length_cons, List.length_nil]

/-- The accepted fixture starts with the exact source discriminator. -/
theorem sampleBytes_prefix : sampleBytes.take 8 = discriminator := by
  rw [sampleBytes, List.append_assoc]
  exact List.take_left' discriminator_length

/-- The returned view excludes both discriminator and extra trailing bytes. -/
theorem sampleBytes_payload : (sampleBytes.drop 8).take payloadSize =
    List.replicate payloadSize 0 := by
  rw [sampleBytes, List.append_assoc, List.drop_left' discriminator_length]
  exact List.take_left' (List.length_replicate ..)

/-- The guard is already shared, and the payload address is aligned for Solana. -/
def sampleArgs : Args := ⟨⟨0, 0⟩, .i128Align8, 4096⟩

/-- The validity of the input follows from the generic acquisition invariant. -/
theorem sampleState_valid (bytes : Solanalib.Runtime.Bytes) : (sampleState bytes).Valid :=
  Borrow.acquire_valid (Borrow.State.valid_empty_slots _) _ _ _

end Solanalib.Specs.Core.Oracle.Switchboard
