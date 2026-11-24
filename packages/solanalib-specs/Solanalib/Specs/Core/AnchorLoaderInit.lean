/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoading

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoaderInit

/-- The declared Anchor error for a nonzero initialization discriminator. -/
def alreadySet : AnchorAccount.Error :=
  .anchor ⟨"AccountDiscriminatorAlreadySet", 3000,
    "The account discriminator was already set on this account", none, none⟩

/-- The source `iter().any` only observes the discriminator prefix. -/
def hasDiscriminator (discriminator bytes : _root_.Solanalib.Runtime.Bytes) : Bool :=
  (bytes.take discriminator.length).any (fun byte => byte != 0)

/-- `load_init` checks writability, acquires the exclusive guard, then slices
the discriminator without the preceding length test of the checked loader. A short
prefix therefore panics. It requires zeros, maps the payload, and does not write
the discriminator; the later `AccountsExit::exit` performs that write. -/
def run (index : AnchorAccount.LoadIndex) (before : AccountInfo.State)
    (args : AnchorAccount.LoadArgs index) : Option (AnchorAccount.LoadOutcome index) :=
  if args.loader.info.isWritable = false then
    some (.returned (.error (AnchorAccount.error .notMutable)) before)
  else
    let (borrowed, during) := AccountInfo.tryBorrow .exclusive args.loader.info.data before
    match borrowed with
    | .error failure => some (.returned (.error (AnchorAccount.programError failure)) during)
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => none
      | .ok (_, .data bytes) =>
        if bytes.length < index.discriminator.length then
          AnchorAccount.loadPanic index args.profile during guard .sliceBounds
        else if hasDiscriminator index.discriminator bytes then
          AnchorAccount.loadError index during guard alreadySet
        else AnchorAccount.mapLoaded index args during guard bytes

/-- Only a reached data acquisition needs the selected current-data input.
Short buffers, misalignment and an already-set discriminator stay admitted. -/
def Ready {index : AnchorAccount.LoadIndex} (before : AccountInfo.State)
    (args : AnchorAccount.LoadArgs index) : Prop :=
  if args.loader.info.isWritable = false then True
  else AccountInfo.DataBorrow.Ready .exclusive before args.loader.info.data

/-- Every represented input has an actual finite local result. The proof
establishes the current read and the real guard release or transfer. -/
theorem complete {index : AnchorAccount.LoadIndex} {before : AccountInfo.State}
    {args : AnchorAccount.LoadArgs index} (ready : Ready before args) :
    ∃ outcome, run index before args = some outcome := by
  unfold run
  split
  · exact ⟨_, rfl⟩
  next writable =>
    have typed : AccountInfo.DataBorrow.Ready .exclusive before args.loader.info.data := by
      simpa only [Ready, ite_eq_right writable] using ready
    cases acquired : AccountInfo.tryBorrow .exclusive args.loader.info.data before with
    | mk borrowed during =>
      cases borrowed with
      | error failure => exact ⟨_, rfl⟩
      | ok guard =>
        obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current typed acquired
        have live := AccountInfo.GuardCallback.tryBorrow_live acquired
        dsimp only
        rw [current]
        dsimp only
        split
        · unfold AnchorAccount.loadPanic
          split
          · exact ⟨_, rfl⟩
          · exact ⟨_, by rw [Borrow.release_live live]⟩
        · split
          · exact ⟨.returned (.error alreadySet) (Borrow.release during guard).2,
              by simp only [AnchorAccount.loadError, Borrow.release_live live]⟩
          · obtain ⟨outcome, mapped, _⟩ := AnchorAccount.mapLoaded_complete args current
            exact ⟨outcome, mapped⟩

/-- This facet records value errors and guard effects. The companion owned
family supplies the actual error-resource allocation sequence. -/
def family : Family where
  Index := AnchorAccount.LoadIndex
  State := fun _ => AccountInfo.State
  Args := AnchorAccount.LoadArgs
  Value := fun index => Except AnchorAccount.Error (AnchorAccount.Mapped index.Payload)
  Unwind := fun _ => AnchorAccount.LoadPanic
  Terminal := fun _ => AnchorAccount.LoadPanic
  contract := fun index => {
    requires := Ready
    post := fun before args outcome => run index before args = some outcome }

/-- The exact checked evaluator is the reference finite-outcome relation. -/
def reference : FamilyRun family := fun index before args outcome =>
  run index before args = some outcome

theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ step
  exact step

/-- A nonempty zero-copy payload with an initially zero discriminator. -/
def sample : AnchorAccount.LoadIndex := ⟨Nat, [10], 2, 1, true⟩

def sampleState : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [0, 20, 30], AccountInfo.sampleProfile.policy⟩], []⟩

def sampleArgs : AnchorAccount.LoadArgs sample :=
  ⟨AccountInfo.sampleProfile, ⟨{ AccountInfo.sampleInfo with isWritable := true }⟩, 8⟩

theorem has_execution : FamilyHasExecution family reference sample := by
  refine ⟨sampleState, sampleArgs, .returned (.ok ⟨⟨0, 1⟩⟩)
    (Borrow.transfer (AccountInfo.tryBorrow .exclusive AccountInfo.sampleInfo.data
      sampleState).2 ⟨0, 0⟩ (.bytesRange 1 2)).2, trivial, rfl⟩

end Solanalib.Specs.Core.AnchorLoaderInit
