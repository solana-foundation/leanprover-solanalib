/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaInstructionView.Request
import Solanalib.Specs.Core.CpiRequestCheckedSliceFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaInstructionView.CheckedSlice

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.CpiRequest.Checked
open Solanalib.Specs.SolanaInstructionView

theorem seed_conversion_keeps_empty_and_long_bytes :
    (cpi.Seed.from_slice_model () []).1 = [] ∧
    (cpi.Seed.from_slice_model () (List.replicate 33 7)).1 = List.replicate 33 7 :=
  ⟨rfl, rfl⟩

theorem signer_keeps_empty_seeds_and_order :
    (cpi.Signer.from_slice_model () [[], [7], [], [7]]).1 = [[], [7], [], [7]] := rfl

/-- The syscall is deliberately unavailable: validation failures must not call it. -/
def noInvocation : Syscall Nat Nat Nat := fun _ _ _ => False

/-- Ordinary signed execution includes allocation, exact prefix invocation and drop. -/
theorem signed_executes_nonempty_prefix :
    cpi.invoke_signed_with_slice_run sampleSliceTypes (0 : Nat) sampleSigned
      (.returned (.ok ()) (112 : Nat)) := sample_signed_execution

/-- An oversized request fails before allocation effects and cannot invoke CPI. -/
def oversized : SignedCall sampleSliceTypes where
  request := ⟨{ sampleInstruction with
    metas := List.replicate 129 (Instruction.accountMeta .zero false false) }, [], []⟩
  invoke := noInvocation

set_option maxRecDepth 2048 in
/-- The maximum count check occurs before the missing-account check and allocation. -/
theorem maximum_count_precedes_allocation
    (outcome : Outcome Nat (Except Error Unit) Nat Nat) :
    cpi.invoke_signed_with_slice_run sampleSliceTypes (4 : Nat) oversized outcome ↔
      outcome = .returned (.error .InvalidArgument) 4 := by
  change sliceV1 (fun _ : Nat => samplePool) sampleStorage noInvocation 4
    oversized.request outcome ↔ _
  exact sliceV1_too_many _ _ _ _ _ (by simp [oversized]) _

/-- The ordinary missing-account path still owns the already allocated box. -/
def missing : SignedCall sampleSliceTypes where
  request := ⟨sampleInstruction, [⟨1⟩], []⟩
  invoke := noInvocation

/-- The insufficient-account error keeps allocation effects and then drops the box. -/
theorem allocation_precedes_missing_accounts
    (outcome : Outcome Nat (Except Error Unit) Nat Nat) :
    cpi.invoke_signed_with_slice_run sampleSliceTypes (4 : Nat) missing outcome ↔
      outcome = .returned (.error .NotEnoughAccountKeys) 114 := by
  change sliceV1 (fun _ : Nat => samplePool) sampleStorage noInvocation 4
    ⟨sampleInstruction, [⟨1⟩], []⟩ outcome ↔ _
  simp [sliceV1, sampleInstruction, Instruction.make, Callback.bind, sampleStorage,
    Owned.scope, innerV1, Owned.cleanup]

/-- Account zero is held through an actual successful exclusive acquisition. -/
def exclusivePool : AccountView.State := (AccountView.acquire samplePool ⟨0⟩ .exclusive).2

/-- Both borrow observations refer to the actual acquired guard. -/
theorem exclusive_guard_is_live :
    AccountView.acquire samplePool ⟨0⟩ .exclusive = (.ok ⟨0, 0⟩, exclusivePool) ∧
    AccountView.isBorrowed exclusivePool ⟨0⟩ = true ∧
    AccountView.isBorrowedMut exclusivePool ⟨0⟩ = true := ⟨rfl, rfl, rfl⟩

/-- Same v1 box dependency with the exclusively borrowed source account. -/
def exclusiveTypes : SliceTypes where
  toTypes := ⟨Nat, fun _ => exclusivePool, Nat, Nat⟩
  Resource := Nat
  storage := sampleStorage

/-- A readonly meta still checks for a mutable borrow in v1. -/
def readonlyBorrowed : SignedCall exclusiveTypes where
  request := ⟨Instruction.make .zero [Instruction.accountMeta (.ofNat 0) false false] [],
    [⟨0⟩], []⟩
  invoke := noInvocation

/-- Unlike v2, a readonly v1 account under a mutable borrow fails before CPI. -/
theorem readonly_exclusive_borrow_rejected
    (outcome : Outcome Nat (Except Error Unit) Nat Nat) :
    cpi.invoke_signed_with_slice_run exclusiveTypes (0 : Nat) readonlyBorrowed outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 110 := by
  change sliceV1 (fun _ : Nat => exclusivePool) sampleStorage noInvocation 0
    readonlyBorrowed.request outcome ↔ _
  simp only [sliceV1, readonlyBorrowed, Instruction.make, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  change Callback.bind sampleStorage.allocate (fun resource state result =>
    Owned.scope sampleStorage.doubleUnwind [fun current => sampleStorage.drop current resource]
      (fun current (_ : Unit) final => final = .returned (.error .AccountBorrowFailed) current)
      state () result) 0 1 outcome ↔ _
  simp [Callback.bind, sampleStorage, Owned.scope, Owned.cleanup]

/-- A mismatched key has priority over the exclusive borrow of this account. -/
theorem address_mismatch_precedes_borrow :
    checkV1 exclusivePool (Instruction.accountMeta (.ofNat 9) false true) ⟨0⟩ =
      .error .InvalidArgument := rfl

/-- An earlier borrow failure wins over a later address mismatch. -/
theorem first_account_failure_precedes_later_mismatch :
    prepareV1 exclusivePool
      [Instruction.accountMeta (.ofNat 0) false true,
        Instruction.accountMeta (.ofNat 9) false false] [⟨0⟩, ⟨1⟩] =
      .error .AccountBorrowFailed := rfl

/-- Signed calls preserve duplicate positions and nested seed groups in the
initialized prefix, while ignoring the trailing borrowed reference. -/
def duplicateProbe : SignedCall sampleSliceTypes where
  request := ⟨Instruction.make .zero
    [Instruction.accountMeta (.ofNat 1) true false,
      Instruction.accountMeta (.ofNat 1) false true] [1, 0, 7],
    [⟨1⟩, ⟨1⟩, ⟨9⟩], [[], [[], [1]], [[2, 3]]]⟩
  invoke := fun (before : Nat) request outcome =>
    request.accounts = [capture samplePool ⟨1⟩, capture samplePool ⟨1⟩] ∧
    request.signers = [[], [[], [1]], [[2, 3]]] ∧
    request.instruction.metas.map (fun item => (item.signerByte, item.writableByte)) =
      [(1, 0), (0, 1)] ∧ request.instruction.data = [1, 0, 7] ∧
    outcome = .returned () (before + 2)

/-- The actual signed path passes the exact prefix, flags, data and signer tree. -/
theorem signed_duplicate_prefix_and_seeds :
    cpi.invoke_signed_with_slice_run sampleSliceTypes (0 : Nat) duplicateProbe
      (.returned (.ok ()) (112 : Nat)) := by
  change Callback.bind sampleStorage.allocate _ 0 2 _
  refine ⟨.returned 2 10, rfl, .returned (.ok ()) (12 : Nat), ?_, .returned () (112 : Nat), rfl,
    rfl⟩
  exact ⟨.returned () (12 : Nat), ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- An unsigned invocation records empty seeds and unwinds after changing state. -/
def unsignedProbe : UnsignedCall sampleSliceTypes where
  instruction := sampleInstruction
  accounts := [⟨1⟩, ⟨2⟩]
  invoke := fun (before : Nat) request outcome =>
    request.signers = [] ∧ outcome = .unwound (17 : Nat) (before + 3)

/-- Unwind cleanup starts after the actual effects of the invocation. -/
theorem unsigned_unwind_drops_box_from_actual_state :
    cpi.invoke_with_slice_run sampleSliceTypes (0 : Nat) unsignedProbe
      (.unwound (17 : Nat) (113 : Nat)) := by
  change Callback.bind sampleStorage.allocate _ 0 2 _
  refine ⟨.returned 2 10, rfl, .unwound (17 : Nat) (13 : Nat), ?_, .returned () (113 : Nat), rfl,
    rfl⟩
  exact ⟨.unwound (17 : Nat) (13 : Nat), ⟨rfl, rfl⟩, rfl⟩

/-- Terminal invocation uses an impossible drop, proving that drop is skipped. -/
def terminalTypes : SliceTypes where
  toTypes := sampleTypes
  Resource := Nat
  storage := { sampleStorage with drop := fun _ _ _ => False }

/-- A terminal opaque invocation has no normal or unwinding continuation. -/
def terminalProbe : SignedCall terminalTypes where
  request := sampleSigned.request
  invoke := fun _ _ outcome => outcome = .terminated (23 : Nat)

/-- A terminal result does not acquire a fictitious post-state or execute cleanup. -/
theorem terminal_skips_box_drop :
    cpi.invoke_signed_with_slice_run terminalTypes (0 : Nat) terminalProbe
      (.terminated (23 : Nat)) := by
  change Callback.bind sampleStorage.allocate _ 0 2 _
  refine ⟨.returned 2 10, rfl, .terminated (23 : Nat), ?_, rfl⟩
  exact ⟨.terminated (23 : Nat), rfl, rfl⟩

/-- Drop can itself unwind; the terminal policy uses its actual state and both reasons. -/
def doubleTypes : SliceTypes where
  toTypes := sampleTypes
  Resource := Nat
  storage := { sampleStorage with
    drop := fun (before : Nat) _ outcome => outcome = .unwound (5 : Nat) (before + 100)
    doubleUnwind := fun (state first second terminal : Nat) => terminal = state + first + second }

/-- The body unwinds before the retained box destructor is run. -/
def doubleProbe : SignedCall doubleTypes where
  request := sampleSigned.request
  invoke := fun (before : Nat) _ outcome => outcome = .unwound (17 : Nat) (before + 3)

/-- The second unwind terminates with the dependency policy, retaining its actual inputs. -/
theorem double_unwind_uses_post_drop_state :
    cpi.invoke_signed_with_slice_run doubleTypes (0 : Nat) doubleProbe
      (.terminated (135 : Nat)) := by
  change Callback.bind sampleStorage.allocate _ 0 2 _
  refine ⟨.returned 2 10, rfl, .unwound (17 : Nat) (13 : Nat), ?_, .unwound (5 : Nat) (113 : Nat),
    rfl, (135 : Nat), rfl, rfl⟩
  exact ⟨.unwound (17 : Nat) (13 : Nat), rfl, rfl⟩

/-- An allocation dependency may exit before it creates the owned box token. -/
def allocationFailureTypes (terminal : Bool) : SliceTypes where
  toTypes := sampleTypes
  Resource := Nat
  storage := {
    allocate := fun (before : Nat) _ outcome => outcome =
      if terminal then .terminated (41 : Nat) else .unwound (31 : Nat) (before + 9)
    drop := fun _ _ _ => False
    doubleUnwind := fun _ _ _ _ => False }

/-- A nonempty request whose allocation never reaches account validation. -/
def allocationFailureCall (terminal : Bool) : SignedCall (allocationFailureTypes terminal) where
  request := sampleSigned.request
  invoke := noInvocation

/-- Allocation unwind keeps its own state and cannot destroy a nonexistent token. -/
theorem allocation_unwind_precedes_body_and_cleanup :
    cpi.invoke_signed_with_slice_run (allocationFailureTypes false) (4 : Nat)
      (allocationFailureCall false) (.unwound (31 : Nat) (13 : Nat)) :=
  ⟨.unwound (31 : Nat) (13 : Nat), rfl, rfl⟩

/-- Allocation terminal exit also skips validation and cleanup. -/
theorem allocation_terminal_precedes_body_and_cleanup :
    cpi.invoke_signed_with_slice_run (allocationFailureTypes true) (4 : Nat)
      (allocationFailureCall true) (.terminated (41 : Nat)) :=
  ⟨.terminated (41 : Nat), rfl, rfl⟩

/-- A first destructor unwind needs no double-unwind terminal policy. -/
def dropUnwindTypes : SliceTypes where
  toTypes := sampleTypes
  Resource := Nat
  storage := { sampleStorage with
    drop := fun (before : Nat) _ outcome => outcome = .unwound (5 : Nat) (before + 100)
    doubleUnwind := fun _ _ _ _ => False }

/-- The invocation returns normally before the retained box drop unwinds. -/
def dropUnwindCall : SignedCall dropUnwindTypes where
  request := sampleSigned.request
  invoke := sampleProvider

/-- The first drop unwind replaces a pending normal return with its actual state. -/
theorem first_drop_unwind_survives_without_second_unwind_policy :
    cpi.invoke_signed_with_slice_run dropUnwindTypes (0 : Nat) dropUnwindCall
      (.unwound (5 : Nat) (112 : Nat)) := by
  change Callback.bind sampleStorage.allocate _ 0 2 _
  refine ⟨.returned 2 10, rfl, .returned (.ok ()) (12 : Nat), ?_,
    .unwound (5 : Nat) (112 : Nat), rfl, rfl⟩
  exact ⟨.returned () (12 : Nat), rfl, rfl⟩

/-- A source header whose nonzero flag bytes all produce true Boolean getters. -/
def noncanonicalHeader : RawHeader := ⟨2, 17, 9, 165⟩

/-- V1 observes Boolean getters, each of which compares the source byte with zero. -/
def booleanGetterPool : AccountView.State :=
  ⟨[⟨{ AccountView.Account.empty with metadata := ⟨.zero,
    noncanonicalHeader.isSigner != 0, noncanonicalHeader.isWritable != 0,
    noncanonicalHeader.executable != 0⟩ }, Borrow.Policy.accountView⟩], []⟩

/-- V1 normalizes Boolean fields and does not copy the source padding byte. -/
theorem v1_normalizes_nonzero_getters_and_does_not_copy_padding :
    capture booleanGetterPool ⟨0⟩ = (⟨⟨0⟩, 0, 0, 1, 1, 1, none⟩ : Descriptor) := rfl

end SolanalibTest.Specs.SolanaInstructionView.CheckedSlice

namespace SolanalibTest.Specs.SolanaInstructionView.CheckedArray

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.CpiRequest.Checked
open Solanalib.Specs.SolanaInstructionView

/-- Nonempty byte-array input with an embedded zero. -/
def byteArray : Instruction.ArrayValue UInt8 := ⟨3, [9, 0, 7], rfl⟩
/-- Seed-array input with empty and repeated entries. -/
def seedArray : Instruction.ArrayValue Instruction.Seed := ⟨4, [[], [7], [], [7]], rfl⟩

theorem seed_slice_and_array_keep_values :
    (cpi.Seed.from_slice_model () [9, 0, 7]).1 = [9, 0, 7] ∧
    (cpi.Seed.from_array_model () byteArray).1 = [9, 0, 7] ∧
    (cpi.Seed.from_array_model () ⟨0, [], rfl⟩).1 = [] := ⟨rfl, rfl, rfl⟩

theorem signer_array_keeps_empty_seeds_and_order :
    (cpi.Signer.from_array_model () seedArray).1 = [[], [7], [], [7]] := rfl

theorem readonly_signer_flags_are_asymmetric :
    (InstructionAccount.readonly_signer_model () .zero).1 =
      (⟨.zero, 1, 0⟩ : _root_.Solanalib.Runtime.CpiMeta) := rfl

/-- A retained reference follows the observation supplied at the point of use;
the copied signer and writable flags do not change with that observation. -/
theorem borrowed_meta_observes_current_key
    (firstKey nextKey : _root_.Solanalib.Runtime.Pubkey) :
    let descriptor : Instruction.RefMeta Nat := ⟨4, true, false⟩
    descriptor.observe (fun _ => firstKey) =
        (⟨firstKey, 1, 0⟩ : _root_.Solanalib.Runtime.CpiMeta) ∧
    descriptor.observe (fun _ => nextKey) =
        (⟨nextKey, 1, 0⟩ : _root_.Solanalib.Runtime.CpiMeta) := ⟨rfl, rfl⟩

/-- The sample reaches normal CPI completion after preparing exactly two accounts. -/
theorem checked_array_executes_nonempty_prefix :
    cpi.invoke_signed_run sampleArrayTypes (0 : Nat) sampleArray
      (.returned (.ok ()) (2 : Nat)) := sample_array_execution

/-- A mathematical array outside the source const bound. Only its first two
positions are visited; binding this to a Rust instantiation is not justified. -/
def largeArray : ArrayCall sampleArrayTypes where
  instruction := sampleInstruction
  accounts := ⟨65, [⟨1⟩, ⟨2⟩] ++ List.replicate 63 ⟨7⟩, by decide⟩
  signers := sampleArray.signers
  invoke := sampleProvider

/-- The actual checked model still initializes the two-account prefix and
retains the result of the provider; the source const assertion adds no runtime error. -/
theorem array_above_source_bound_executes :
    cpi.invoke_signed_run sampleArrayTypes (0 : Nat) largeArray
      (.returned (.ok ()) (2 : Nat)) := by
  change directV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool)
    largeArray.invoke 0 ⟨largeArray.instruction, largeArray.accounts.values, largeArray.signers⟩ _
  apply (directV2_iff _ _ _ _ _ _).mpr
  change invokePrepared sampleProvider sampleInstruction sampleArray.signers
    sampleDescriptors (0 : Nat) (.returned (.ok ()) (2 : Nat))
  exact invokePrepared_returned _ _ _ _ _ _ rfl

/-- Neither conversion nor invocation has a finite outcome in this interpretation. -/
def unavailableTypes : ArrayTypes where
  toHeaderTypes := sampleHeaderTypes
  Account := Unit
  asRef := fun _ _ _ => False

/-- The complete count check has to stop before looking at any account value. -/
def missing : ArrayCall unavailableTypes where
  instruction := sampleInstruction
  accounts := ⟨1, [()], rfl⟩
  signers := []
  invoke := fun _ _ _ => False

/-- Missing accounts are reported with the entry state, without invoking AsRef. -/
theorem missing_count_precedes_every_callback
    (outcome : Outcome Nat (Except Error Unit) Nat Nat) :
    cpi.invoke_signed_run unavailableTypes (7 : Nat) missing outcome ↔
      outcome = .returned (.error .NotEnoughAccountKeys) 7 := Iff.rfl

/-- One acquired exclusive guard is used to distinguish the revisions. -/
def exclusivePool : AccountView.State := (AccountView.acquire samplePool ⟨0⟩ .exclusive).2

/-- Concrete evidence that the tested borrow is live. -/
theorem exclusive_guard_is_live :
    AccountView.acquire samplePool ⟨0⟩ .exclusive = (.ok ⟨0, 0⟩, exclusivePool) ∧
    AccountView.isBorrowedMut exclusivePool ⟨0⟩ = true := ⟨rfl, rfl⟩

/-- Borrowed AccountView identity specialization with this current pool. -/
def exclusiveTypes : ArrayTypes where
  toTypes := ⟨Nat, fun _ => exclusivePool, Nat, Nat⟩
  rawHeader := fun _ => normalizedHeader exclusivePool
  Account := AccountView.Handle
  asRef := identityAsRef

/-- A readonly meta is permitted by the v2 local checks even under a mutable borrow. -/
def readonlyBorrowed : ArrayCall exclusiveTypes where
  instruction := Instruction.make .zero [Instruction.accountMeta (.ofNat 0) false false] []
  accounts := ⟨1, [⟨0⟩], rfl⟩
  signers := []
  invoke := sampleProvider

/-- The v2 readonly path reaches the opaque invocation; v1 rejects this case. -/
theorem readonly_exclusive_borrow_reaches_invocation :
    cpi.invoke_signed_run exclusiveTypes (0 : Nat) readonlyBorrowed
      (.returned (.ok ()) (1 : Nat)) := by
  change directV2 (fun _ : Nat => exclusivePool) (fun _ => normalizedHeader exclusivePool)
    sampleProvider 0
    ⟨readonlyBorrowed.instruction, [⟨0⟩], []⟩ _
  apply (directV2_iff _ _ _ _ _ _).mpr
  change invokePrepared sampleProvider readonlyBorrowed.instruction []
    [captureV2 exclusivePool (normalizedHeader exclusivePool) ⟨0⟩] 0 (.returned (.ok ()) 1)
  exact invokePrepared_returned _ _ _ _ _ _ rfl

/-- Writable metadata fails on the same live mutable borrow. -/
theorem writable_exclusive_borrow_rejected :
    checkDirectV2 exclusivePool (normalizedHeader exclusivePool) (Instruction.accountMeta (.ofNat
      0) false true) ⟨0⟩ =
      .error .AccountBorrowFailed := rfl

/-- Address comparison precedes borrow checking at each position. -/
theorem address_mismatch_precedes_borrow :
    checkDirectV2 exclusivePool (normalizedHeader exclusivePool) (Instruction.accountMeta (.ofNat
      9) false true) ⟨0⟩ =
      .error .InvalidArgument := rfl

/-- A provider checks the actual prepared prefix, metadata and nested seed tree. -/
def duplicateProbe : ArrayCall sampleArrayTypes where
  instruction := Instruction.make .zero
    [Instruction.accountMeta (.ofNat 1) true false,
      Instruction.accountMeta (.ofNat 1) false true] [1, 0, 7]
  accounts := ⟨3, [⟨1⟩, ⟨1⟩, ⟨9⟩], rfl⟩
  signers := [[], [[], [1]], [[2, 3]]]
  invoke := fun (before : Nat) request outcome =>
    request.accounts = [captureV2 samplePool (normalizedHeader samplePool) ⟨1⟩, captureV2
      samplePool (normalizedHeader samplePool) ⟨1⟩] ∧
    request.signers = [[], [[], [1]], [[2, 3]]] ∧
    request.instruction.metas.map (fun item => (item.signerByte, item.writableByte)) =
      [(1, 0), (0, 1)] ∧ request.instruction.data = [1, 0, 7] ∧
    outcome = .returned () (before + 2)

/-- Duplicate positions survive while the trailing source reference is trimmed. -/
theorem array_keeps_duplicate_prefix_and_seed_tree :
    cpi.invoke_signed_run sampleArrayTypes (0 : Nat) duplicateProbe
      (.returned (.ok ()) (2 : Nat)) := by
  change directV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool)
    duplicateProbe.invoke 0
    ⟨duplicateProbe.instruction, [⟨1⟩, ⟨1⟩, ⟨9⟩], duplicateProbe.signers⟩ _
  apply (directV2_iff _ _ _ _ _ _).mpr
  change invokePrepared duplicateProbe.invoke duplicateProbe.instruction duplicateProbe.signers
    [captureV2 samplePool (normalizedHeader samplePool) ⟨1⟩, captureV2 samplePool (normalizedHeader
      samplePool) ⟨1⟩] (0 : Nat) (.returned (.ok ()) (2 : Nat))
  exact invokePrepared_returned _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An effectful AsRef whose successive calls choose three different accounts. -/
def switchingRef : AsRef Nat Unit Nat Nat := fun before _ outcome =>
  outcome = .returned (if before = 0 then ⟨1⟩ else if before = 1 then ⟨2⟩ else ⟨3⟩)
    (before + 1)

/-- Writable validation uses the second reference and captures the third,
without assuming that it equals the reference used for the address comparison. -/
theorem repeated_asref_can_select_distinct_handles :
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) switchingRef
      (Instruction.accountMeta (.ofNat 1) false true) 0 ()
      (.returned (.ok (captureV2 samplePool (normalizedHeader samplePool) ⟨3⟩)) 3) := by
  refine ⟨.returned ⟨1⟩ 1, rfl, ?_⟩
  refine ⟨.returned ⟨2⟩ 2, rfl, ?_⟩
  exact ⟨.returned ⟨3⟩ 3, rfl, rfl⟩

/-- Repeated conversion effects are visible before a local address error. -/
theorem address_error_retains_first_asref_effect
    (outcome : Outcome Nat (Except Error Descriptor) Nat Nat) :
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) switchingRef
      (Instruction.accountMeta (.ofNat 9) false true) 0 () outcome ↔
      outcome = .returned (.error .InvalidArgument) 1 := by
  change Callback.bind switchingRef (fun account state result =>
    if (samplePool.account account).metadata.address ≠ Solanalib.Runtime.Pubkey.ofNat 9 then
      result = .returned (.error .InvalidArgument) state
    else _) 0 () outcome ↔ _
  simp only [Callback.bind, switchingRef]
  have mismatch : (samplePool.account ⟨1⟩).metadata.address ≠ Solanalib.Runtime.Pubkey.ofNat 9 :=
    by decide
  simp [mismatch]

/-- The second AsRef chooses a borrowed account after the first address matched. -/
def borrowRef : AsRef Nat Unit Nat Nat := fun before _ outcome =>
  outcome = .returned (if before = 0 then ⟨1⟩ else ⟨0⟩) (before + 1)

/-- Borrow failure observes the actual second handle and keeps both callback effects. -/
theorem borrow_error_retains_second_asref_effect
    (outcome : Outcome Nat (Except Error Descriptor) Nat Nat) :
    checkV2 (fun _ : Nat => exclusivePool) (fun _ => normalizedHeader exclusivePool) borrowRef
      (Instruction.accountMeta (.ofNat 1) false true) 0 () outcome ↔
      outcome = .returned (.error .AccountBorrowFailed) 2 := by
  change Callback.bind borrowRef _ 0 () outcome ↔ _
  simp only [Callback.bind, borrowRef]
  have key : (exclusivePool.account ⟨1⟩).metadata.address = Solanalib.Runtime.Pubkey.ofNat 1 := rfl
  have borrowed : AccountView.isBorrowed exclusivePool ⟨0⟩ = true := rfl
  simp [key, borrowed, Instruction.accountMeta]

/-- A dependency can stop at any of the three actual conversion call sites. -/
def stoppingRef (phase : Nat) (terminal : Bool) : AsRef Nat Unit Nat Nat :=
  fun before _ outcome => outcome =
    if before = phase then
      if terminal then .terminated 91 else .unwound 77 (before + 10)
    else .returned ⟨1⟩ (before + 1)

/-- The unwind of the first conversion is not filtered or turned into a local SDK error. -/
theorem address_asref_unwind_survives :
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) (stoppingRef 0 false)
      (Instruction.accountMeta (.ofNat 1) false true) 0 () (.unwound 77 10) :=
  ⟨.unwound 77 10, rfl, rfl⟩

/-- The unwind of the second conversion preserves its current state. -/
theorem borrow_asref_unwind_survives :
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) (stoppingRef 1 false)
      (Instruction.accountMeta (.ofNat 1) false true) 0 () (.unwound 77 11) :=
  ⟨.returned ⟨1⟩ 1, rfl, .unwound 77 11, rfl, rfl⟩

/-- The separate conversion during initialization has its own observable unwind. -/
theorem initialization_asref_unwind_survives :
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) (stoppingRef 2 false)
      (Instruction.accountMeta (.ofNat 1) false true) 0 () (.unwound 77 12) :=
  ⟨.returned ⟨1⟩ 1, rfl, .returned ⟨1⟩ 2, rfl, .unwound 77 12, rfl, rfl⟩

/-- All three conversion sites also preserve terminal exits without continuing. -/
theorem every_asref_terminal_site_survives :
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) (stoppingRef 0 true)
        (Instruction.accountMeta (.ofNat 1) false true) 0 () (.terminated 91) ∧
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) (stoppingRef 1 true)
        (Instruction.accountMeta (.ofNat 1) false true) 0 () (.terminated 91) ∧
    checkV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) (stoppingRef 2 true)
        (Instruction.accountMeta (.ofNat 1) false true) 0 () (.terminated 91) :=
  ⟨⟨.terminated 91, rfl, rfl⟩,
    ⟨.returned ⟨1⟩ 1, rfl, .terminated 91, rfl, rfl⟩,
    ⟨.returned ⟨1⟩ 1, rfl, .returned ⟨1⟩ 2, rfl, .terminated 91, rfl, rfl⟩⟩

/-- An account pool whose current lengths follow the callback clock, within
fixed backing storage. These are current values, not entry snapshots. -/
def evolvingPool (clock : Nat) : AccountView.State :=
  ⟨(List.range 10).map (fun index =>
    ⟨{ AccountView.Account.empty with
      metadata := ⟨.ofNat index, false, true, false⟩
      dataLen := clock % 8
      backing := List.replicate 8 0 }, Borrow.Policy.accountView⟩), []⟩

/-- Each actual identity-selecting conversion advances the dependency clock. -/
def tickingRef : AsRef Nat AccountView.Handle Nat Nat := fun before account outcome =>
  outcome = .returned account (before + 1)

/-- Two readonly entries and one unused trailing account. -/
def evolvingMetas : List Solanalib.Runtime.CpiMeta :=
  [Instruction.accountMeta (.ofNat 1) false false,
    Instruction.accountMeta (.ofNat 2) false false]

/-- Earlier copied lengths survive later callback mutations; the extra account
causes no conversion. Readonly entries use exactly two calls each. -/
theorem descriptors_capture_at_each_actual_initialization :
    prepareV2 evolvingPool (fun clock => normalizedHeader (evolvingPool clock)) tickingRef
      evolvingMetas [⟨1⟩, ⟨2⟩, ⟨9⟩] 0
      (.returned (.ok [captureV2 (evolvingPool 2) (normalizedHeader (evolvingPool 2)) ⟨1⟩,
        captureV2 (evolvingPool 4) (normalizedHeader (evolvingPool 4)) ⟨2⟩]) 4) := by
  refine ⟨.returned (.ok (captureV2 (evolvingPool 2) (normalizedHeader (evolvingPool 2)) ⟨1⟩)) 2,
    ?_, ?_⟩
  · exact ⟨.returned ⟨1⟩ 1, rfl, .returned ⟨1⟩ 2, rfl, rfl⟩
  · refine ⟨.returned (.ok [captureV2 (evolvingPool 4) (normalizedHeader (evolvingPool 4)) ⟨2⟩]) 4,
    ?_, rfl⟩
    refine ⟨.returned (.ok (captureV2 (evolvingPool 4) (normalizedHeader (evolvingPool 4)) ⟨2⟩)) 4,
      ?_, ?_⟩
    · exact ⟨.returned ⟨2⟩ 3, rfl, .returned ⟨2⟩ 4, rfl, rfl⟩
    · exact ⟨.returned (.ok []) 4, rfl, rfl⟩

/-- Captured values differ even though both current accounts have length four later. -/
theorem earlier_descriptor_is_not_reloaded_after_later_callbacks :
    (captureV2 (evolvingPool 2) (normalizedHeader (evolvingPool 2)) ⟨1⟩).dataLen = 2 ∧
    (captureV2 (evolvingPool 4) (normalizedHeader (evolvingPool 4)) ⟨2⟩).dataLen = 4 ∧
    ((evolvingPool 4).account ⟨1⟩).dataLen = 4 := ⟨rfl, rfl, rfl⟩

/-- Opaque invocation exits are forwarded only after the checks pass. -/
theorem raw_unwind_and_terminal_preserved :
    invokePrepared (fun (before : Nat) _ (outcome : Outcome Nat Unit Nat Nat) => outcome = .unwound
      (13 : Nat) (before + 6))
        sampleInstruction [] sampleDescriptors 4 (.unwound 13 10) ∧
    invokePrepared (fun (_ : Nat) _ (outcome : Outcome Nat Unit Nat Nat) => outcome = .terminated
      (19 : Nat))
        sampleInstruction [] sampleDescriptors 4 (.terminated 19) :=
  ⟨invokePrepared_unwound _ _ _ _ _ _ _ rfl,
    invokePrepared_terminated _ _ _ _ _ _ rfl⟩

/-- A unit-returning unchecked call cannot fabricate an ordinary post-CPI error. -/
theorem no_sdk_error_after_unchecked_return (invoke : Syscall Nat Nat Nat) :
    ¬ invokePrepared invoke sampleInstruction [] sampleDescriptors 0
      (.returned (.error .InvalidArgument) 7) := invokePrepared_no_error _ _ _ _ _ _ _

/-- All three Boolean getters report true for the nonzero raw bytes below. -/
def rawPool : AccountView.State :=
  ⟨(List.range 10).map (fun index =>
    ⟨{ AccountView.Account.empty with
      metadata := ⟨.ofNat index, true, true, true⟩ }, Borrow.Policy.accountView⟩), []⟩

/-- Noncanonical flags and nonzero padding occur only at the actual final
construction state and final AsRef handle. Earlier calls see other raw bytes. -/
def exactRawHeader (clock : Nat) (account : AccountView.Handle) : RawHeader :=
  if clock = 3 ∧ account.cell = 3 then ⟨2, 17, 9, 165⟩ else ⟨1, 1, 1, 0⟩

/-- Generic AsRef and the raw current header are independent explicit observations. -/
def rawTypes : ArrayTypes where
  toTypes := ⟨Nat, fun _ => rawPool, Nat, Nat⟩
  rawHeader := exactRawHeader
  Account := Unit
  asRef := switchingRef

/-- The exact expected initialized descriptor contains raw bytes, not booleans. -/
def rawDescriptor : Descriptor := ⟨⟨3⟩, 0, 0, 2, 17, 9, some 165⟩

/-- The provider observes the exact prepared descriptor after three conversions;
its second supplied array entry must never be visited. -/
def rawCall : ArrayCall rawTypes where
  instruction := Instruction.make .zero [Instruction.accountMeta (.ofNat 1) false true] []
  accounts := ⟨2, [(), ()], rfl⟩
  signers := []
  invoke := fun (before : Nat) request outcome =>
    request.accounts = [rawDescriptor] ∧ outcome = .returned () (before + 100)

/-- Full checked execution reads raw flags and padding at the actual final
AsRef state and handle, then passes those exact bytes to opaque invocation. -/
theorem full_array_retains_raw_flag_two_and_nonzero_padding :
    cpi.invoke_signed_run rawTypes (0 : Nat) rawCall
      (.returned (.ok ()) (103 : Nat)) := by
  change innerV2 (fun _ : Nat => rawPool) exactRawHeader switchingRef rawCall.invoke 0
    ⟨rawCall.instruction, [(), ()], []⟩ (.returned (.ok ()) (103 : Nat))
  unfold innerV2
  simp only [rawCall, Instruction.make, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  refine ⟨.returned (.ok [rawDescriptor]) (3 : Nat), ?_, ?_⟩
  · refine ⟨.returned (.ok rawDescriptor) (3 : Nat), ?_,
      .returned (.ok []) (3 : Nat), rfl, rfl⟩
    exact ⟨.returned ⟨1⟩ 1, rfl, .returned ⟨2⟩ 2, rfl, .returned ⟨3⟩ 3, rfl, rfl⟩
  · exact ⟨.returned () (103 : Nat), ⟨rfl, rfl⟩, rfl⟩

/-- Boolean agreement is insufficient to identify the raw descriptor bytes. -/
theorem raw_two_is_not_normalized_to_one :
    (rawPool.account ⟨3⟩).metadata.signer = true ∧
    (captureV2 rawPool (exactRawHeader 3) ⟨3⟩).isSigner = 2 ∧
    (captureV2 rawPool (normalizedHeader rawPool) ⟨3⟩).isSigner = 1 ∧
    (captureV2 rawPool (exactRawHeader 3) ⟨3⟩).copiedPadding = some 165 :=
  ⟨rfl, rfl, rfl, rfl⟩

end SolanalibTest.Specs.SolanaInstructionView.CheckedArray
