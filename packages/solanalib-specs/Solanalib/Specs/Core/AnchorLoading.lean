/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorAccount
public import Solanalib.Specs.Core.BorrowMap
public import Solanalib.Specs.Core.AccountInfoDataAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorAccount

/-- Finite local panic causes in the selected Loader mapping closure. -/
inductive LoadPanic where
  /-- The selected checked usize addition overflows. -/
  | lengthOverflow
  /-- The selected byte range is outside the current slice. -/
  | sliceBounds
  /-- The current payload address fails the typed alignment check. -/
  | castAlignment
  deriving DecidableEq, Repr

/-- The associated discriminator and target layout of the type are explicit model
parameters. `Pod`/`ZeroCopy` binding supplies the interpretation of the mapped
bytes as `Payload`; this model never invents a decoded value. -/
structure LoadIndex where
  /-- Rust type interpreted by the zero-copy payload binding. -/
  Payload : Type
  /-- The associated source discriminator bytes. -/
  discriminator : _root_.Solanalib.Runtime.Bytes
  /-- The source payload size in bytes. -/
  byteSize : Nat
  /-- The source payload alignment used by the cast check. -/
  alignment : Nat
  /-- Whether the selected source addition checks overflow. -/
  overflowChecks : Bool

/-- A mapped typed borrow retains the common guard token. Its actual projection
is read from the world, so future permitted writes are visible. -/
structure Mapped (Payload : Type) where
  /-- The transferred token naming the current byte projection. -/
  guard : Borrow.Guard
  deriving DecidableEq, Repr

/-- The data address is explicit binding evidence used only for the actual
bytemuck alignment check. It is not manufactured from an account identity. -/
structure LoadArgs (index : LoadIndex) where
  /-- The selected target-width and panic policy. -/
  profile : AccountInfo.Profile
  /-- The borrowed account alias, without a decoded payload. -/
  loader : Loader index.Payload
  /-- The actual base address supplied by the source binding. -/
  dataAddress : Nat

/-- Project the account and its profile for shared AccountInfo operations. -/
def LoadArgs.infoArgs {index : LoadIndex} (args : LoadArgs index) : AccountInfo.Args :=
  ⟨args.profile, args.loader.info⟩

/-- Only the discriminator prefix is checked before mapping; enough bytes for
that prefix do not imply enough bytes or alignment for the payload. -/
def discriminatorCheck (discriminator bytes : _root_.Solanalib.Runtime.Bytes) : Except Error Unit :=
  if bytes.length < discriminator.length then .error (error .discriminatorNotFound)
  else if bytes.take discriminator.length ≠ discriminator then .error (error .discriminatorMismatch)
  else .ok ()

/-- Value errors, state-bearing mapping unwind, and terminal mapping abort. -/
abbrev LoadOutcome (index : LoadIndex) :=
  Outcome AccountInfo.State (Except Error (Mapped index.Payload)) LoadPanic LoadPanic

/-- Checked errors before `Ref::map`/`RefMut::map` release the local guard. -/
def loadError (index : LoadIndex) (state : AccountInfo.State) (guard : Borrow.Guard)
    (error : Error) : Option (LoadOutcome index) :=
  match Borrow.release state guard with
  | (.ok (), after) => some (.returned (.error error) after)
  | (.error _, _) => none

/-- Both frozen `Ref::map` and `RefMut::map` evaluate their closure before moving
the owned borrow field. On unwind the local guard is released; abort supplies
no post-state. This is a source-bound model choice, not a stdlib body proof. -/
def loadPanic (index : LoadIndex) (profile : AccountInfo.Profile)
    (state : AccountInfo.State) (guard : Borrow.Guard) (reason : LoadPanic) :
    Option (LoadOutcome index) :=
  if profile.aborts then some (.terminated reason)
  else match Borrow.release state guard with
    | (.ok (), after) => some (.unwound reason after)
    | (.error _, _) => none

/-- The mapping closure checks usize addition, slice bounds and the actual
payload address alignment. Successful mapping consumes the old generation and
keeps the same lease with its exact byte-range descriptor. -/
def mapLoaded (index : LoadIndex) (args : LoadArgs index) (state : AccountInfo.State)
    (guard : Borrow.Guard) (bytes : _root_.Solanalib.Runtime.Bytes) : Option (LoadOutcome index) :=
  let offset := index.discriminator.length
  let endOffset := index.byteSize + offset
  if 2^args.profile.wordBits ≤ endOffset then
    loadPanic index args.profile state guard
      (if index.overflowChecks then .lengthOverflow else .sliceBounds)
  else if bytes.length < endOffset then loadPanic index args.profile state guard .sliceBounds
  else if (args.dataAddress + offset) % index.alignment ≠ 0 then
    loadPanic index args.profile state guard .castAlignment
  else
    match Borrow.transfer state guard (.bytesRange offset index.byteSize) with
    | (.error _, _) => none
    | (.ok mapped, after) => some (.returned (.ok ⟨mapped⟩) after)

/-- Source order for `load` and `load_mut`: the latter checks writable metadata
first, then acquires; both check the prefix before entering the mapping closure.
There is no owner check on either load operation. -/
def load (mode : Borrow.Mode) (index : LoadIndex)
    (state : AccountInfo.State) (args : LoadArgs index) : Option (LoadOutcome index) :=
  if mode = .exclusive ∧ args.loader.info.isWritable = false then
    some (.returned (.error (error .notMutable)) state)
  else
    let (result, during) := AccountInfo.tryBorrow mode args.loader.info.data state
    match result with
    | .error failure => some (.returned (.error (programError failure)) during)
    | .ok guard =>
      match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => none
      | .ok (_, .data bytes) =>
        match discriminatorCheck index.discriminator bytes with
        | .error failure => loadError index during guard failure
        | .ok () => mapLoaded index args during guard bytes

/-- Only a reached successful data acquisition needs a typed current read.
The mutable metadata rejection happens before that acquisition. Payload-size
and alignment failures remain modeled mapping panics, not admission failures. -/
def LoadReady (mode : Borrow.Mode) {index : LoadIndex}
    (state : AccountInfo.State) (args : LoadArgs index) : Prop :=
  if mode = .exclusive ∧ args.loader.info.isWritable = false then True
  else AccountInfo.DataBorrow.Ready mode state args.loader.info.data

/-- A mapping return exposes its actual readable byte projection and consumes
the input generation. Unwind also consumes that input; abort has no state. -/
def MappingExit (index : LoadIndex) (guard : Borrow.Guard) : LoadOutcome index → Prop
  | .returned (.error _) _ => False
  | .returned (.ok mapped) after =>
    after.resolve guard = none ∧ ∃ bytes,
      Borrow.deref AccountInfo.projectBytes after mapped.guard = (.ok (.ok bytes), after) ∧
      bytes.length = index.byteSize
  | .unwound _ after => after.resolve guard = none
  | .terminated _ => True

private theorem loadPanic_complete {index : LoadIndex} {state : AccountInfo.State}
    {guard : Borrow.Guard} {slot : Borrow.Slot AccountInfo.View}
    (live : state.resolve guard = some slot) (profile : AccountInfo.Profile)
    (reason : LoadPanic) :
    ∃ outcome, loadPanic index profile state guard reason = some outcome ∧
      MappingExit index guard outcome := by
  unfold loadPanic
  split
  · exact ⟨.terminated reason, rfl, trivial⟩
  · rw [Borrow.release_live live]
    exact ⟨.unwound reason _, rfl,
      by simpa only [MappingExit, Borrow.release_live live] using Borrow.release_consumes live⟩

/-- Mapping from the actual current data always has a finite local result.
All source-local panics remain outcomes; successful transfer exposes exactly
the current bounded slice rather than an assumed decoded payload. -/
theorem mapLoaded_complete {index : LoadIndex} (args : LoadArgs index)
    {state : AccountInfo.State} {guard : Borrow.Guard} {view : AccountInfo.View}
    {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current state guard = .ok (view, .data bytes)) :
    ∃ outcome, mapLoaded index args state guard bytes = some outcome ∧
      MappingExit index guard outcome := by
  cases live : state.resolve guard with
  | none => simp [Borrow.current, live] at current
  | some slot =>
    cases present : state.lookupCell slot.cell with
    | none => simp [Borrow.current, live, present] at current
    | some cell =>
      have observed : (slot.view, cell.value) = (view, .data bytes) := by
        simpa only [Borrow.current, live, present, Except.ok.injEq] using current
      have value : cell.value = .data bytes := congrArg Prod.snd observed
      unfold mapLoaded
      dsimp only
      split
      · exact loadPanic_complete live args.profile _
      · split
        · exact loadPanic_complete live args.profile _
        next enough =>
          split
          · exact loadPanic_complete live args.profile _
          · rw [Borrow.transfer_live live]
            refine ⟨.returned (.ok ⟨⟨guard.id, guard.generation + 1⟩⟩) _, rfl, ?_⟩
            have bounded : index.discriminator.length + index.byteSize ≤ bytes.length := by omega
            have read := Borrow.transfer_current live present
              (.bytesRange index.discriminator.length index.byteSize)
            rw [value] at read
            have consumed := Borrow.transfer_consumes live
              (.bytesRange index.discriminator.length index.byteSize)
            refine ⟨?_, (bytes.drop index.discriminator.length).take index.byteSize, ?_, ?_⟩
            · simpa only [Borrow.transfer_live live] using consumed
            · simpa only [Borrow.transfer_live live] using
                (show Borrow.deref AccountInfo.projectBytes
                  (Borrow.transfer state guard (.bytesRange index.discriminator.length
                    index.byteSize)).2
                  ⟨guard.id, guard.generation + 1⟩ =
                    (.ok (.ok ((bytes.drop index.discriminator.length).take index.byteSize)),
                      (Borrow.transfer state guard (.bytesRange index.discriminator.length
                        index.byteSize)).2) from
                  by simp only [Borrow.deref, read, AccountInfo.projectBytes, ite_eq_left bounded])
            · simp only [List.length_take, List.length_drop]
              omega

/-- Every admitted input has a complete local load result. This uses the
selected-data condition before the actual discriminator read, then proves the
real release or mapping succeeds; no reference execution is assumed. -/
theorem load_complete {mode : Borrow.Mode} {index : LoadIndex}
    {state : AccountInfo.State} {args : LoadArgs index}
    (ready : LoadReady mode state args) :
    ∃ outcome, load mode index state args = some outcome := by
  unfold load
  split
  · exact ⟨_, rfl⟩
  next allowed =>
    have typed : AccountInfo.DataBorrow.Ready mode state args.loader.info.data := by
      simpa only [LoadReady, ite_eq_right allowed] using ready
    cases acquired : AccountInfo.tryBorrow mode args.loader.info.data state with
    | mk result during =>
      cases result with
      | error failure => exact ⟨_, rfl⟩
      | ok guard =>
        obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current typed acquired
        dsimp only
        rw [current]
        dsimp only
        cases checked : discriminatorCheck index.discriminator bytes with
        | error failure =>
          have live := AccountInfo.GuardCallback.tryBorrow_live acquired
          exact ⟨.returned (.error failure) (Borrow.release during guard).2,
            by simp only [loadError, Borrow.release_live live]⟩
        | ok returnedUnit =>
          cases returnedUnit
          obtain ⟨outcome, completed, _⟩ := mapLoaded_complete args current
          exact ⟨outcome, by simpa only [checked] using completed⟩

/-- Source-domain family; `load_complete` proves the local relation has an
actual outcome from every admitted input. Raw panic/error branches are retained. -/
def loadFamily (mode : Borrow.Mode) : Family where
  Index := LoadIndex
  State := fun _ => AccountInfo.State
  Args := LoadArgs
  Value := fun i => Except Error (Mapped i.Payload)
  Unwind := fun _ => LoadPanic
  Terminal := fun _ => LoadPanic
  contract := fun i => {
    requires := LoadReady mode
    post := fun state args outcome => load mode i state args = some outcome }

/-- The unchanged optional local evaluator interpreted as a finite relation. -/
def loadRun (mode : Borrow.Mode) : FamilyRun (loadFamily mode) :=
  fun i state args outcome => load mode i state args = some outcome

theorem load_reference (mode : Borrow.Mode) : FamilyReference (loadFamily mode) (loadRun mode) := by
  intro _ _ _ _ _ step
  exact step

/-- A concrete nonempty payload layout for the exact family witness. -/
def loadSample : LoadIndex := ⟨Nat, [10], 2, 1, true⟩

/-- A writable alias and aligned base for the shared and mutable samples. -/
def loadSampleArgs : LoadArgs loadSample :=
  ⟨AccountInfo.sampleProfile, ⟨{ AccountInfo.sampleInfo with isWritable := true }⟩, 8⟩

theorem load_execution (mode : Borrow.Mode) :
    FamilyHasExecution (loadFamily mode) (loadRun mode) loadSample := by
  refine ⟨AccountInfo.sampleState, loadSampleArgs,
    .returned (.ok ⟨⟨0, 1⟩⟩)
      (Borrow.transfer (AccountInfo.tryBorrow mode AccountInfo.sampleInfo.data
        AccountInfo.sampleState).2 ⟨0, 0⟩ (.bytesRange 1 2)).2,
    (by cases mode <;> trivial), ?_⟩
  cases mode <;> rfl

end Solanalib.Specs.Core.AnchorAccount
