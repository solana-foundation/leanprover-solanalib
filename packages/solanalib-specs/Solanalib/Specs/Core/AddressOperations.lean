/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressValueOperations
public import Solanalib.Specs.Core.AddressSyscallFamily
public import Solanalib.Specs.Core.AddressSyscallSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Operations

open Solanalib.Contracts.Model Solanalib.Specs.Core Address.Syscall

/-! Shared value and selected-Solana PDA wrapper semantics. The providers are
explicit assumed library/runtime interfaces. No Rust implementation is proved.
Zeroed destinations and `MaybeUninit` destinations are distinct profiles. -/

inductive Error where
  | maxSeedLengthExceeded
  | invalidSeeds
  | illegalOwner
  deriving DecidableEq, Repr

/-- 1.x monolithic solana-program has no status-2 conversion. -/
inductive ErrorProfile where
  | legacyPubkey
  | pubkey
  | address
  deriving DecidableEq, Repr

def ErrorProfile.decode (profile : ErrorProfile) (status : UInt64) : Option Error :=
  if status = 1 then some .invalidSeeds
  else if status = 2 ∧ profile ≠ .legacyPubkey then some .illegalOwner
  else none

def ErrorProfile.panicMessage : ErrorProfile → String
  | .address => "Unsupported AddressError"
  | _ => "Unsupported PubkeyError"

/-- Initial local destination, visible to an interpreted syscall. -/
inductive Initialization where
  | zeroed
  | uninitialized
  deriving DecidableEq, Repr

def Initialization.Output : Initialization → Type
  | .zeroed => Value
  | .uninitialized => Option Value

def Initialization.initial : Initialization → Option Value
  | .zeroed => some .zero
  | .uninitialized => none

def Initialization.observe (mode : Initialization) : mode.Output → Option Value :=
  match mode with
  | .zeroed => some
  | .uninitialized => id

structure CreateRequest where
  inputs : PdaInputs
  seedCount : UInt64
  output : Option Value

structure CreateReply (mode : Initialization) where
  status : UInt64
  output : mode.Output

def createRequest (mode : Initialization) (inputs : PdaInputs) : CreateRequest :=
  ⟨inputs, UInt64.ofNat inputs.seeds.length, mode.initial⟩

/-- The source checks count first, then individual lengths. No sorting,
concatenation, deduplication or removal of empty seeds occurs. -/
def badSeeds (inputs : PdaInputs) : Bool :=
  inputs.seeds.length > 16 || inputs.seeds.any (fun seed => seed.length > 32)

structure CreateIndex (mode : Initialization) extends Types where
  syscall : Callback.Run State CreateRequest (CreateReply mode) Unwind Terminal
  panic : Callback.Run State String Empty Unwind Terminal

/-- Only the reached the normal success of the syscall needs initialized output. The
zeroed profile has a total 32-byte result even after partial or absent writes. -/
def createReady {mode : Initialization} (index : CreateIndex mode)
    (before : index.State) (inputs : PdaInputs) : Prop :=
  match mode with
  | .zeroed => True
  | .uninitialized => badSeeds inputs = false →
      ∀ reply after, index.syscall before (createRequest .uninitialized inputs)
        (.returned reply after) → reply.status = 0 → ∃ value, reply.output = some value

def panicAs {State Result Unwind Terminal : Type}
    (panic : Callback.Run State String Empty Unwind Terminal) (message : String) :
    State → Outcome State Result Unwind Terminal → Prop :=
  fun before => Callback.map (fun impossible : Empty => nomatch impossible) panic before message

def finishCreate {mode : Initialization} (profile : ErrorProfile) (index : CreateIndex mode)
    (reply : CreateReply mode) (after : index.State) :
    Outcome index.State (Except Error Value) index.Unwind index.Terminal → Prop :=
  if reply.status = 0 then fun outcome =>
    ∃ value, mode.observe reply.output = some value ∧ outcome = .returned (.ok value) after
  else match profile.decode reply.status with
    | some error => fun outcome => outcome = .returned (.error error) after
    | none => panicAs index.panic profile.panicMessage after

def createRun {mode : Initialization} (profile : ErrorProfile) (index : CreateIndex mode) :
    Callback.Run index.State PdaInputs (Except Error Value) index.Unwind index.Terminal :=
  fun before inputs outcome =>
    if badSeeds inputs then outcome = .returned (.error .maxSeedLengthExceeded) before
    else Callback.bind index.syscall (finishCreate profile index) before
      (createRequest mode inputs) outcome

def createFamily (mode : Initialization) (profile : ErrorProfile) : Family where
  Index := CreateIndex mode
  State := fun index => index.State
  Args := fun _ => PdaInputs
  Value := fun _ => Except Error Address.Value
  Unwind := fun index => index.Unwind
  Terminal := fun index => index.Terminal
  contract := fun index => {
    requires := createReady index
    post := createRun profile index }

def createReference (mode : Initialization) (profile : ErrorProfile) :
    FamilyRun (createFamily mode profile) := fun index => createRun profile index

theorem createReference_correct (mode : Initialization) (profile : ErrorProfile) :
    FamilyReference (createFamily mode profile) (createReference mode profile) :=
  fun _ _ _ _ _ execution => execution

/-- Each successful callback exit can be represented, including an untouched
zero buffer. The initialization premise is used only for MaybeUninit success. -/
theorem create_success_retained {mode : Initialization} (profile : ErrorProfile)
    (index : CreateIndex mode) (before after : index.State) (inputs : PdaInputs)
    (ready : createReady index before inputs) (valid : badSeeds inputs = false)
    (reply : CreateReply mode)
    (step : index.syscall before (createRequest mode inputs) (.returned reply after))
    (success : reply.status = 0) :
    ∃ value, mode.observe reply.output = some value ∧
      createRun profile index before inputs (.returned (.ok value) after) := by
  have initialized : ∃ value, mode.observe reply.output = some value := by
    cases mode with
    | zeroed => exact ⟨reply.output, rfl⟩
    | uninitialized => exact ready valid reply after step success
  obtain ⟨value, initialized⟩ := initialized
  refine ⟨value, initialized, ?_⟩
  simp only [createRun, valid, Bool.false_eq_true, ↓reduceIte]
  refine ⟨.returned reply after, step, ?_⟩
  simp only [finishCreate, success, ↓reduceIte]
  exact ⟨value, initialized, rfl⟩

theorem create_rejects_before_syscall {mode : Initialization} (profile : ErrorProfile)
    (index : CreateIndex mode) (before : index.State) (inputs : PdaInputs)
    (bad : badSeeds inputs = true)
    (outcome : Outcome index.State (Except Error Value) index.Unwind index.Terminal) :
    createRun profile index before inputs outcome ↔
      outcome = .returned (.error .maxSeedLengthExceeded) before := by
  simp only [createRun, bad, ↓reduceIte]

def sampleOutput : (mode : Initialization) → mode.Output
  | .zeroed => .zero
  | .uninitialized => some .zero

def createSample (mode : Initialization) : CreateIndex mode where
  State := Unit
  Unwind := String
  Terminal := String
  syscall := Callback.ofFunction fun before _ => .returned ⟨0, sampleOutput mode⟩ before
  panic := Callback.ofFunction fun before message => .unwound message before

def sampleInputs : PdaInputs := ⟨[[], [7, 8]], .zero⟩

theorem createSample_execution (mode : Initialization) (profile : ErrorProfile) :
    FamilyHasExecution (createFamily mode profile) (createReference mode profile)
      (createSample mode) := by
  refine ⟨(), sampleInputs, .returned (.ok .zero) (), ?_, ?_⟩
  · cases mode with
    | zeroed => trivial
    | uninitialized =>
      intro _ reply after step _
      cases step
      exact ⟨.zero, rfl⟩
  · change createRun profile (createSample mode) () sampleInputs _
    simp only [createRun, sampleInputs, badSeeds, List.length_cons, List.length_nil,
      List.any_cons, List.any_nil]
    refine ⟨.returned ⟨0, sampleOutput mode⟩ (), rfl, ?_⟩
    simp only [finishCreate, ↓reduceIte]
    exact ⟨.zero, by cases mode <;> rfl, rfl⟩

/-! `Pubkey` PDA search uses a zeroed local array, unlike `Address`. -/

structure ZeroFindReply where
  status : UInt64
  output : Value
  bump : UInt8

structure ZeroFindIndex extends Types where
  syscall : Callback.Run State PdaRequest ZeroFindReply Unwind Terminal
  panic : Callback.Run State SearchPanic Empty Unwind Terminal

def zeroFindRequest (inputs : PdaInputs) : PdaRequest :=
  { pdaRequest inputs with addressOutput := some .zero }

def zeroFindDecode (reply : ZeroFindReply) : Option (Value × UInt8) :=
  if reply.status = 0 then some (reply.output, reply.bump) else none

def zeroFindRun (index : ZeroFindIndex) :
    Callback.Run index.State PdaInputs (Value × UInt8) index.Unwind index.Terminal :=
  fun before inputs => Callback.bind
    (Callback.map zeroFindDecode index.syscall) (finishFind index.panic)
    before (zeroFindRequest inputs)

def zeroFindFamily : Family where
  Index := ZeroFindIndex
  State := fun index => index.State
  Args := fun _ => PdaInputs
  Value := fun _ => Address.Value × UInt8
  Unwind := fun index => index.Unwind
  Terminal := fun index => index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := zeroFindRun index }

def zeroFindReference : FamilyRun zeroFindFamily := zeroFindRun

theorem zeroFindReference_correct : FamilyReference zeroFindFamily zeroFindReference :=
  fun _ _ _ _ _ execution => execution

def zeroFindSample : ZeroFindIndex where
  State := Unit
  Unwind := String
  Terminal := String
  syscall := Callback.ofFunction fun before _ => .returned ⟨0, .zero, 253⟩ before
  panic := Callback.ofFunction fun before _ => .unwound panicMessage before

theorem zeroFindSample_execution :
    FamilyHasExecution zeroFindFamily zeroFindReference zeroFindSample :=
  ⟨(), sampleInputs, .returned (.zero, 253) (), trivial,
    .returned (some (.zero, 253)) (), ⟨.returned ⟨0, .zero, 253⟩ (), rfl, rfl⟩, rfl⟩

/-! Seed derivation calls the hashv library boundary once, after both guards. -/

structure SeedInputs where
  base : Value
  seed : String
  owner : Value

def SeedInputs.bytes (args : SeedInputs) : Solanalib.Runtime.Bytes := args.seed.toUTF8.data.toList

def marker : Solanalib.Runtime.Bytes := Solanalib.Runtime.PDA_MARKER

def seedError (args : SeedInputs) : Option Error :=
  if args.bytes.length > 32 then some .maxSeedLengthExceeded
  else if args.owner.bytes.drop (32 - marker.length) = marker then some .illegalOwner
  else none

def seedSlices (args : SeedInputs) : List Solanalib.Runtime.Bytes :=
  [args.base.bytes, args.bytes, args.owner.bytes]

structure SeedIndex extends Types where
  /-- The actual hashv boundary, including state and abnormal exits. -/
  hashv : Callback.Run State (List Solanalib.Runtime.Bytes) Value Unwind Terminal

def seedRun (index : SeedIndex) :
    Callback.Run index.State SeedInputs (Except Error Value) index.Unwind index.Terminal :=
  fun before args outcome => match seedError args with
    | some error => outcome = .returned (.error error) before
    | none => Callback.map Except.ok index.hashv before (seedSlices args) outcome

def seedFamily : Family where
  Index := SeedIndex
  State := fun index => index.State
  Args := fun _ => SeedInputs
  Value := fun _ => Except Error Address.Value
  Unwind := fun index => index.Unwind
  Terminal := fun index => index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := seedRun index }

def seedReference : FamilyRun seedFamily := seedRun

theorem seedReference_correct : FamilyReference seedFamily seedReference :=
  fun _ _ _ _ _ execution => execution

def seedSample : SeedIndex where
  State := Unit
  Unwind := String
  Terminal := String
  hashv := Callback.ofFunction fun before _ => .returned .zero before

def sampleSeed : SeedInputs := ⟨.zero, "seed", .zero⟩

theorem seedSample_execution : FamilyHasExecution seedFamily seedReference seedSample := by
  refine ⟨(), sampleSeed, .returned (.ok .zero) (), trivial, ?_⟩
  change seedRun seedSample () sampleSeed _
  have clear : seedError sampleSeed = none := by
    simp only [seedError, sampleSeed, SeedInputs.bytes, marker, Solanalib.Runtime.PDA_MARKER,
      Solanalib.Runtime.strBytes, String.toUTF8_eq_toByteArray]
    decide +kernel
  simp only [seedRun, clear]
  exact ⟨.returned .zero (), rfl, rfl⟩

/-- A useful cryptographic projection requires the ordinary
reply law of the hash boundary. It neither excludes runtime failure nor assumes termination. -/
theorem seed_returned_hash (index : SeedIndex) (hash : List Solanalib.Runtime.Bytes → Value)
    (agreement : ∀ before slices value after,
      index.hashv before slices (.returned value after) → value = hash slices)
    (before after : index.State) (args : SeedInputs) (value : Value)
    (execution : seedRun index before args (.returned (.ok value) after)) :
    seedError args = none ∧ value = hash (seedSlices args) := by
  cases valid : seedError args with
  | some error => simp [seedRun, valid] at execution
  | none =>
    simp only [seedRun, valid] at execution
    obtain ⟨actual, step, mapped⟩ := execution
    cases actual with
    | returned result state => cases mapped; exact ⟨rfl, agreement before _ value after step⟩
    | unwound reason state => cases mapped
    | terminated reason => cases mapped

end Solanalib.Specs.Core.Address.Operations
