/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SysvarAccount
public import Solanalib.Specs.Core.AccountViewFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionsSysvar

/-- The selected `Instructions<Ref<[u8]>>` owns the original identified shared
guard. It is not a copied byte snapshot or a model of arbitrary effectful Deref. -/
structure Instructions where
  /-- The original shared acquisition, including its current ownership generation. -/
  guard : AccountView.Guard
  deriving DecidableEq, Repr

/-- The raw instruction pointer remains tied to its originating guard. -/
structure IntrospectedInstruction where
  /-- Receiver whose live captured slice supplies the pointer base. -/
  source : Instructions
  /-- Byte offset from that captured slice base. -/
  offset : Nat
  deriving DecidableEq, Repr

/-- A borrowed Address region tied to the same receiver, without copying its bytes. -/
structure ProgramIdRef where
  /-- The original receiver retained by this borrowed reference. -/
  source : Instructions
  /-- Start of the 32-byte address relative to the captured slice. -/
  offset : Nat
  deriving DecidableEq, Repr

/-- A borrowed data slice retaining its receiver, start and decoded extent. -/
structure DataRef where
  /-- The original receiver retained by this borrowed slice. -/
  source : Instructions
  /-- First data byte relative to the captured slice base. -/
  offset : Nat
  /-- The data length decoded when this reference is formed. -/
  length : Nat
  deriving DecidableEq, Repr

/-- Current bytes through the guard, with an empty fallback on an invalid or
consumed token. Interpreting the observation as a Rust reference read requires
a separate live-guard and access binding. -/
def Instructions.bytes (state : AccountView.State) (source : Instructions) :
  Solanalib.Runtime.Bytes :=
  (AccountView.guardRead state source.guard).toOption.getD []

/-- Constructor checks the key first, then shared acquisition. It performs no
serialization check, including no minimum-size or offset-table check. -/
def tryFrom (state : AccountView.State) (handle : AccountView.Handle) :
    Except ProgramError.Value Instructions × AccountView.State :=
  if (state.account handle).metadata.address ≠ Solanalib.Runtime.Ids.sysvarInstructions then
    (.error .unsupportedSysvar, state)
  else
    let acquired := AccountView.acquire state handle .shared
    (match acquired.1 with
      | .ok guard => .ok ⟨guard⟩
      | .error _ => .error .accountBorrowFailed, acquired.2)

/-- Dropping the owning Ref consumes the same guard; there is no copy-back. -/
def release (state : AccountView.State) (source : Instructions) :=
  Borrow.release state source.guard

/-- Total little-endian observation of the available two-byte prefix; source use requires the
checked read. -/
def word (bytes : Solanalib.Runtime.Bytes) (offset : Nat) : Nat := Solanalib.Runtime.leNat
  (Solanalib.Runtime.slice bytes offset 2)

/-- Read the mathematical count from the current bytes of the receiver. -/
def numInstructions (state : AccountView.State) (source : Instructions) : Nat :=
  word (source.bytes state) 0

/-- Unchanged total footer observation, including its fallback outside source admission. -/
def currentIndex (state : AccountView.State) (source : Instructions) : UInt16 :=
  let bytes := source.bytes state
  UInt16.ofNat (word bytes (bytes.length - 2))

/-- Unchanged count check and raw offset lookup; source admission excludes undefined table accesses.
-/
def instructionAt (state : AccountView.State) (args : Instructions × UInt64) :
    Except ProgramError.Value IntrospectedInstruction :=
  if numInstructions state args.1 ≤ args.2.toNat then .error .invalidInstructionData
  else .ok ⟨args.1, word (args.1.bytes state) (2 + 2 * args.2.toNat)⟩

/-- Current entry account-count observation from its raw offset. -/
def numAccounts (state : AccountView.State) (instruction : IntrospectedInstruction) : Nat :=
  word (instruction.source.bytes state) instruction.offset

/-- Program-id offset after the two-byte count and 33-byte metadata entries. -/
def programOffset (state : AccountView.State) (instruction : IntrospectedInstruction) : Nat :=
  instruction.offset + 2 + 33 * numAccounts state instruction

/-- Form the raw borrowed program pointer; complete source readability is established by the
contract. -/
def programId (state : AccountView.State) (instruction : IntrospectedInstruction) : ProgramIdRef :=
  ⟨instruction.source, programOffset state instruction⟩

/-- Observe current program bytes through the retained source guard. -/
def ProgramIdRef.bytes (state : AccountView.State) (reference : ProgramIdRef) :
  Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.slice (reference.source.bytes state) reference.offset 32

/-- A checked mathematical conversion to the canonical 32-byte value. It
does not pad a short or stale observation into a fabricated address. -/
def ProgramIdRef.value? (state : AccountView.State) (reference : ProgramIdRef) :
    Option Solanalib.Runtime.Pubkey :=
  let bytes := reference.bytes state
  if length : bytes.length = 32 then some ⟨bytes, length⟩ else none

/-- Position of the two-byte data length after the program address. -/
def dataLengthOffset (state : AccountView.State) (instruction : IntrospectedInstruction) : Nat :=
  programOffset state instruction + 32

/-- Form the raw borrowed data descriptor from the current length word. -/
def data (state : AccountView.State) (instruction : IntrospectedInstruction) : DataRef :=
  let offset := dataLengthOffset state instruction
  ⟨instruction.source, offset + 2, word (instruction.source.bytes state) offset⟩

/-- Observe current data through the retained guard, without a copied snapshot. -/
def DataRef.bytes (state : AccountView.State) (reference : DataRef) : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.slice (reference.source.bytes state) reference.offset reference.length

/-- The signed pointer-offset limit of the selected 64-bit target. -/
def ISIZE_LIMIT : Nat := 2^63

/-- The actual shared lease of the receiver and complete captured slice are still
readable in the current allocation. No unrelated lamport, owner, or other-cell
invariant is required. Physical placement and permissions interpret this pool. -/
def Instructions.Ready (source : Instructions) (state : AccountView.State) : Prop :=
  ∃ slot cell, state.resolve source.guard = some slot ∧
    state.lookupCell slot.cell = some cell ∧ slot.mode = .shared ∧
    slot.view.offset + slot.view.length ≤ cell.value.backing.length ∧
    slot.view.length < ISIZE_LIMIT

/-- Check the current captured slice before a source dereference. This rejects
stale guards and truncated backing; it neither changes state nor fabricates a
Rust error. The view offset is retained for the alignment of the native table. -/
def Instructions.checkedView (source : Instructions) (state : AccountView.State) :
    Option (AccountView.Slice × Solanalib.Runtime.Bytes) := do
  let slot ← state.resolve source.guard
  let cell ← state.lookupCell slot.cell
  if slot.mode = .shared ∧ slot.view.offset + slot.view.length ≤ cell.value.backing.length ∧
      slot.view.length < ISIZE_LIMIT then
    some (slot.view, cell.value.read slot.view)
  else none

/-- A complete two-byte source load. Only the native u16 table passes
alignment two; `[u8; 2]` loads require alignment one, including odd offsets. -/
def checkedWord (view : AccountView.Slice) (bytes : Solanalib.Runtime.Bytes)
    (offset alignment : Nat) : Option Nat :=
  if offset + 2 ≤ bytes.length ∧ (view.offset + offset) % alignment = 0 then
    some (word bytes offset)
  else none

/-- A successful check proves the length of the actual byte read, its decoded
u16 bound, and the required alignment of that precise access. -/
theorem checkedWord_reads {view : AccountView.Slice} {bytes : Solanalib.Runtime.Bytes}
    {offset alignment value : Nat} (read : checkedWord view bytes offset alignment = some value) :
    (Solanalib.Runtime.slice bytes offset 2).length = 2 ∧
      value = Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes offset 2) ∧ value < 65536 ∧
      (view.offset + offset) % alignment = 0 := by
  unfold checkedWord at read
  split at read
  next safe =>
    cases read
    have length := Solanalib.Runtime.length_slice_of_le safe.1
    have bound := Solanalib.Runtime.leNat_lt (Solanalib.Runtime.slice bytes offset 2)
    exact ⟨length, rfl, by simpa [word, length] using bound, safe.2⟩
  next => contradiction

/-- Resolve the live identity and read its actual full bytes. This result
excludes both the invalid-guard empty fallback and truncated captured views. -/
theorem Instructions.Ready.checked {source : Instructions} {state : AccountView.State}
    (ready : source.Ready state) :
    ∃ slot, state.resolve source.guard = some slot ∧
      source.checkedView state = some (slot.view, source.bytes state) ∧
      (source.bytes state).length = slot.view.length := by
  obtain ⟨slot, cell, live, present, mode, bound, length⟩ := ready
  have observed : source.bytes state = cell.value.read slot.view := by
    simp [Instructions.bytes, AccountView.guardRead, Borrow.current, live, present, Except.map,
      Except.toOption]
  refine ⟨slot, live, ?_, ?_⟩
  · simp [Instructions.checkedView, live, present, mode, bound, length, observed]
  · rw [observed]
    exact Solanalib.Runtime.length_slice_of_le bound

/-- Successful checking exposes the same live read, its full captured length,
and the signed slice bound. No entry serialization is asserted. -/
theorem Instructions.checkedView_reads {source : Instructions} {state : AccountView.State}
    {view : AccountView.Slice} {bytes : Solanalib.Runtime.Bytes}
    (read : source.checkedView state = some (view, bytes)) :
    AccountView.guardRead state source.guard = .ok bytes ∧ bytes.length = view.length ∧
      view.length < ISIZE_LIMIT := by
  unfold Instructions.checkedView at read
  cases live : state.resolve source.guard with
  | none => simp [live] at read
  | some slot =>
    rw [live] at read
    change (state.lookupCell slot.cell).bind _ = some (view, bytes) at read
    cases present : state.lookupCell slot.cell with
    | none => simp [present] at read
    | some cell =>
      rw [present] at read
      change (if slot.mode = .shared ∧
        slot.view.offset + slot.view.length ≤ cell.value.backing.length ∧
        slot.view.length < ISIZE_LIMIT then some (slot.view, cell.value.read slot.view) else none) =
        some (view, bytes) at read
      split at read
      next safe =>
        cases read
        refine ⟨?_, Solanalib.Runtime.length_slice_of_le safe.2.1, safe.2.2⟩
        simp [AccountView.guardRead, Borrow.current, live, present, Except.map]
      next => contradiction

/-- Current-index subtraction and its footer load are defined in the captured
slice. Slice liveness is checked separately from its serialization length. -/
def currentIndexReady (state : AccountView.State) (source : Instructions) : Prop :=
  source.Ready state ∧ 2 ≤ (source.bytes state).length

/-- Checked interpretation of the raw footer observer; no zero fallback is
allowed at a claimed source-function execution. -/
def checkedCurrentIndex (state : AccountView.State) (source : Instructions) : Option UInt16 := do
  let (view, bytes) ← source.checkedView state
  if 2 ≤ bytes.length then
    (checkedWord view bytes (bytes.length - 2) 1).map UInt16.ofNat
  else none

/-- The exact raw current index is obtained from a defined complete footer load. -/
theorem currentIndex_checked (state : AccountView.State) (source : Instructions)
    (ready : currentIndexReady state source) :
    checkedCurrentIndex state source = some (currentIndex state source) := by
  obtain ⟨slot, _, checked, _⟩ := ready.1.checked
  simp [checkedCurrentIndex, checked, ready.2, checkedWord, currentIndex, Nat.mod_one]

/-- Offset relative to the selected two-aligned AccountView data allocation.
This is a binding to that base placement, not an invented numeric address. -/
def tableAligned (state : AccountView.State) (source : Instructions) (offset : Nat) : Prop :=
  match state.resolve source.guard with
  | none => False
  | some slot => (slot.view.offset + offset) % 2 = 0

/-- Count bytes are required on every normal entry. Table alignment, table
extent and pointer formation are required only when the count admits the index.
The returned instruction may be one-past; it is not yet a readable entry. -/
def instructionAtReady (state : AccountView.State) (args : Instructions × UInt64) : Prop :=
  args.1.Ready state ∧ 2 ≤ (args.1.bytes state).length ∧
    (args.2.toNat < numInstructions state args.1 →
      tableAligned state args.1 (2 + 2 * args.2.toNat) ∧
      2 + 2 * args.2.toNat + 2 ≤ (args.1.bytes state).length ∧
      word (args.1.bytes state) (2 + 2 * args.2.toNat) ≤ (args.1.bytes state).length)

/-- Checked count/table loads followed by a bounded pointer construction,
with the same out-of-range error before any table access. -/
def checkedInstructionAt (state : AccountView.State) (args : Instructions × UInt64) :
    Option (Except ProgramError.Value IntrospectedInstruction) := do
  let (view, bytes) ← args.1.checkedView state
  let count ← checkedWord view bytes 0 1
  if count ≤ args.2.toNat then some (.error .invalidInstructionData)
  else
    let offset ← checkedWord view bytes (2 + 2 * args.2.toNat) 2
    if offset ≤ bytes.length then some (.ok ⟨args.1, offset⟩) else none

/-- The unchanged lookup result has a complete checked execution under its
branch-sensitive source domain. -/
theorem instructionAt_checked (state : AccountView.State) (args : Instructions × UInt64)
    (ready : instructionAtReady state args) :
    checkedInstructionAt state args = some (instructionAt state args) := by
  obtain ⟨slot, live, checked, _⟩ := ready.1.checked
  have count : checkedWord slot.view (args.1.bytes state) 0 1 =
      some (numInstructions state args.1) := by
    simp [checkedWord, ready.2.1, numInstructions, Nat.mod_one]
  simp only [checkedInstructionAt, checked]
  change (checkedWord slot.view (args.1.bytes state) 0 1).bind _ = _
  rw [count]
  change (if numInstructions state args.1 ≤ args.2.toNat then _ else _) = _
  by_cases outside : numInstructions state args.1 ≤ args.2.toNat
  · simp [outside, instructionAt]
  · obtain ⟨aligned, extent, pointer⟩ := ready.2.2 (Nat.lt_of_not_ge outside)
    have alignment : (slot.view.offset + (2 + 2 * args.2.toNat)) % 2 = 0 := by
      simpa [tableAligned, live] using aligned
    simp [outside, checkedWord, extent, alignment, pointer, instructionAt]

/-- The count read and full returned Address must fit the actual captured
slice. No alignment-two premise is imposed on either byte-array access. -/
def programIdReady (state : AccountView.State) (instruction : IntrospectedInstruction) : Prop :=
  instruction.source.Ready state ∧
    instruction.offset + 2 ≤ (instruction.source.bytes state).length ∧
    programOffset state instruction + 32 ≤ (instruction.source.bytes state).length

/-- Decode the current count and form only a complete borrowed Address region. -/
def checkedProgramId (state : AccountView.State) (instruction : IntrospectedInstruction) :
    Option ProgramIdRef := do
  let (view, bytes) ← instruction.source.checkedView state
  let count ← checkedWord view bytes instruction.offset 1
  let offset := instruction.offset + 2 + 33 * count
  if offset + 32 ≤ bytes.length then some ⟨instruction.source, offset⟩ else none

/-- Source admission yields the exact borrowed pointer and all 32 current
bytes, not merely a pointer whose later `value?` could fail. -/
theorem programId_checked (state : AccountView.State) (instruction : IntrospectedInstruction)
    (ready : programIdReady state instruction) :
    checkedProgramId state instruction = some (programId state instruction) ∧
      ((programId state instruction).bytes state).length = 32 := by
  obtain ⟨slot, _, checked, _⟩ := ready.1.checked
  constructor
  · have count : checkedWord slot.view (instruction.source.bytes state) instruction.offset 1 =
        some (numAccounts state instruction) := by
      simp [checkedWord, ready.2.1, numAccounts, Nat.mod_one]
    simp only [checkedProgramId, checked]
    change (checkedWord slot.view (instruction.source.bytes state) instruction.offset 1).bind _ = _
    rw [count]
    change (if programOffset state instruction + 32 ≤ (instruction.source.bytes state).length
      then some (programId state instruction) else none) = _
    simp [ready.2.2]
  · exact Solanalib.Runtime.length_slice_of_le ready.2.2

/-- Both scalar reads and the complete decoded payload fit the current captured
slice. Empty data permits a one-past slice after its real length read. -/
def dataReady (state : AccountView.State) (instruction : IntrospectedInstruction) : Prop :=
  instruction.source.Ready state ∧
    instruction.offset + 2 ≤ (instruction.source.bytes state).length ∧
    dataLengthOffset state instruction + 2 ≤ (instruction.source.bytes state).length ∧
    dataLengthOffset state instruction + 2 + word (instruction.source.bytes state)
      (dataLengthOffset state instruction) ≤ (instruction.source.bytes state).length

/-- Decode from actual count and data-length bytes before forming the full
borrowed data slice; no truncated list is promoted to a successful reference. -/
def checkedData (state : AccountView.State) (instruction : IntrospectedInstruction) : Option
  DataRef := do
  let (view, bytes) ← instruction.source.checkedView state
  let count ← checkedWord view bytes instruction.offset 1
  let lengthOffset := instruction.offset + 2 + 33 * count + 32
  let length ← checkedWord view bytes lengthOffset 1
  if lengthOffset + 2 + length ≤ bytes.length then
    some ⟨instruction.source, lengthOffset + 2, length⟩
  else none

/-- Every admitted data result has its exact decoded length and complete
current payload, with the same original guard. -/
theorem data_checked (state : AccountView.State) (instruction : IntrospectedInstruction)
    (ready : dataReady state instruction) :
    checkedData state instruction = some (data state instruction) ∧
      ((data state instruction).bytes state).length = (data state instruction).length := by
  obtain ⟨slot, _, checked, _⟩ := ready.1.checked
  constructor
  · have count : checkedWord slot.view (instruction.source.bytes state) instruction.offset 1 =
        some (numAccounts state instruction) := by
      simp [checkedWord, ready.2.1, numAccounts, Nat.mod_one]
    have length : checkedWord slot.view (instruction.source.bytes state)
        (dataLengthOffset state instruction) 1 =
        some (word (instruction.source.bytes state) (dataLengthOffset state instruction)) := by
      simp [checkedWord, ready.2.2.1, Nat.mod_one]
    simp only [checkedData, checked]
    change (checkedWord slot.view (instruction.source.bytes state) instruction.offset 1).bind _ = _
    rw [count]
    change (checkedWord slot.view (instruction.source.bytes state)
      (dataLengthOffset state instruction) 1).bind _ = _
    rw [length]
    change (if dataLengthOffset state instruction + 2 +
      word (instruction.source.bytes state) (dataLengthOffset state instruction) ≤
      (instruction.source.bytes state).length then some (data state instruction) else none) = _
    simp [ready.2.2.2]
  · exact Solanalib.Runtime.length_slice_of_le ready.2.2.2

/-- The key read has an actual cell. Only a successful matching-key borrow
forms the data slice, so only that reached branch needs its backing and signed
length bounds. Short and empty data are admitted; serialization is not checked. -/
def constructorReady (state : AccountView.State) (handle : AccountView.Handle) : Prop :=
  ∃ cell, state.lookupCell handle = some cell ∧
    (cell.value.metadata.address = Solanalib.Runtime.Ids.sysvarInstructions →
      ∀ guard after, AccountView.acquire state handle .shared = (.ok guard, after) →
        cell.value.dataLen ≤ cell.value.backing.length ∧ cell.value.dataLen < ISIZE_LIMIT)

/-- Check key-read identity and the actual successful borrowed result. Borrow
failure and wrong-key error retain their source order and original states. -/
def checkedTryFrom (state : AccountView.State) (handle : AccountView.Handle) :
    Option (Except ProgramError.Value Instructions × AccountView.State) := do
  let _ ← state.lookupCell handle
  let (result, after) := tryFrom state handle
  match result with
  | .error error => some (.error error, after)
  | .ok source => (source.checkedView after).map fun _ => (.ok source, after)

/-- On the admitted source domain every raw constructor result survives
checking, including short-slice acquisition and all ordinary errors. -/
theorem constructor_checked (state : AccountView.State) (handle : AccountView.Handle)
    (ready : constructorReady state handle) :
    checkedTryFrom state handle = some (tryFrom state handle) := by
  obtain ⟨cell, present, bounds⟩ := ready
  have account := AccountView.State.account_of_lookup present
  by_cases key : cell.value.metadata.address = Solanalib.Runtime.Ids.sysvarInstructions
  · cases acquired : AccountView.acquire state handle .shared with
    | mk result after =>
      cases result with
      | error error => simp [checkedTryFrom, present, tryFrom, account, key, acquired]
      | ok guard =>
        have extent := bounds key guard after acquired
        have success := AccountView.acquire_protocol_success acquired
        obtain ⟨live, cells, _, _⟩ := Borrow.acquire_success success
        have presentAfter : after.lookupCell handle = some cell := by
          simpa [Borrow.State.lookupCell, cells] using present
        have readable : (Instructions.mk guard).Ready after := by
          refine ⟨⟨handle, .shared, 0, cell.value.whole⟩, cell, ?_, presentAfter, rfl, ?_, ?_⟩
          · simpa [account] using live
          · simpa [AccountView.Account.whole] using extent.1
          · exact extent.2
        obtain ⟨slot, _, checked, _⟩ := readable.checked
        simp [checkedTryFrom, present, tryFrom, account, key, acquired, checked]
  · simp [checkedTryFrom, present, tryFrom, account, key]

/-- A successful admitted constructor returns the actual live readable Ref
with its complete current captured length; it does not promise decoder bounds. -/
theorem constructor_success_readable (state after : AccountView.State)
    (handle : AccountView.Handle) (source : Instructions) (ready : constructorReady state handle)
    (success : tryFrom state handle = (.ok source, after)) :
    ∃ view bytes, source.checkedView after = some (view, bytes) ∧
      AccountView.guardRead after source.guard = .ok bytes ∧
      bytes.length = view.length ∧ view.length < ISIZE_LIMIT := by
  have checked := constructor_checked state handle ready
  obtain ⟨cell, present, _⟩ := ready
  simp only [checkedTryFrom, present, success] at checked
  change (source.checkedView after).map
    (fun _ => ((Except.ok source : Except ProgramError.Value Instructions), after)) =
    some ((Except.ok source : Except ProgramError.Value Instructions), after) at checked
  cases read : source.checkedView after with
  | none => simp [read] at checked
  | some pair =>
    exact ⟨pair.1, pair.2, rfl, Instructions.checkedView_reads read⟩

theorem constructor_wrong_key (state : AccountView.State) (handle : AccountView.Handle)
    (wrong : (state.account handle).metadata.address ≠ Solanalib.Runtime.Ids.sysvarInstructions) :
    tryFrom state handle = (.error .unsupportedSysvar, state) := by
  unfold tryFrom
  split
  · rfl
  · contradiction

theorem instructionAt_out_of_range (state : AccountView.State) (source : Instructions)
    (index : UInt64) (outside : numInstructions state source ≤ index.toNat) :
    instructionAt state (source, index) = .error .invalidInstructionData := by
  simp only [instructionAt, outside, ite_true]

theorem programId_keeps_guard (state : AccountView.State)
    (instruction : IntrospectedInstruction) :
    (programId state instruction).source.guard = instruction.source.guard := rfl

theorem data_keeps_guard (state : AccountView.State) (instruction : IntrospectedInstruction) :
    (data state instruction).source.guard = instruction.source.guard := rfl

theorem programId_bytes_length (state : AccountView.State)
    (instruction : IntrospectedInstruction)
    (extent : programOffset state instruction + 32 ≤ (instruction.source.bytes state).length) :
    ((programId state instruction).bytes state).length = 32 :=
  Solanalib.Runtime.length_slice_of_le extent

theorem data_bytes_length (state : AccountView.State)
    (instruction : IntrospectedInstruction)
    (extent : (data state instruction).offset + (data state instruction).length ≤
      (instruction.source.bytes state).length) :
    ((data state instruction).bytes state).length = (data state instruction).length :=
  Solanalib.Runtime.length_slice_of_le extent

namespace Witness

/-- One instruction, one metadata entry, nonempty data, and the current-index
footer. Distinct repeated bytes make key/program/data ordering observable. -/
def bytes : Solanalib.Runtime.Bytes :=
  Solanalib.Runtime.u16le 1 ++ Solanalib.Runtime.u16le 4 ++ Solanalib.Runtime.u16le 1 ++ [3] ++
    List.replicate 32 17 ++ List.replicate 32 34 ++ Solanalib.Runtime.u16le 3 ++ [4, 5, 6] ++
    Solanalib.Runtime.u16le 0

/-- A mathematical account containing the nonempty serialized witness. -/
def account : AccountView.Account :=
  { AccountView.Account.empty with
    metadata := ⟨Solanalib.Runtime.Ids.sysvarInstructions, false, false, false⟩
    dataLen := bytes.length
    entryLen := bytes.length
    backing := bytes }

/-- The witness account before acquiring its shared slice. -/
def initial : AccountView.State := Sysvar.Witness.singleAccount account
/-- The witness account with the original shared guard live. -/
def borrowed : AccountView.State := Sysvar.Witness.singleGuard account .shared
/-- The receiver owning that shared witness guard. -/
def source : Instructions := ⟨Sysvar.Witness.guard⟩
/-- The witness instruction pointer at offset four. -/
def instruction : IntrospectedInstruction := ⟨source, 4⟩

/-- The concrete receiver denotes the complete live captured slice. -/
theorem source_ready : source.Ready borrowed := by
  refine ⟨_, _, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

/-- The constructor witness admits real slice formation without assuming a
serialization check in the constructor. -/
theorem constructor_ready : constructorReady initial Sysvar.Witness.handle := by
  refine ⟨_, rfl, ?_⟩
  intro _ guard after _
  exact ⟨by decide, by decide⟩

/-- Footer readiness for the nonempty serialized witness. -/
theorem current_ready : currentIndexReady borrowed source := ⟨source_ready, by decide⟩

/-- Actual count, native-table alignment and pointer extent for the witness. -/
theorem instruction_ready : instructionAtReady borrowed (source, 0) := by
  refine ⟨source_ready, by decide, ?_⟩
  intro _
  exact ⟨by change (0 + (2 + 2 * (0 : UInt64).toNat)) % 2 = 0; decide, by decide, by decide⟩

/-- Both count and returned program bytes are present. -/
theorem program_ready : programIdReady borrowed instruction :=
  ⟨source_ready, by decide, by decide⟩

/-- Both scalar loads and all nonempty data bytes are present. -/
theorem data_ready : dataReady borrowed instruction :=
  ⟨source_ready, by decide, by decide, by decide⟩

end Witness

end Solanalib.Specs.Core.InstructionsSysvar
