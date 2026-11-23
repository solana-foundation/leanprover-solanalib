/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Address
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Syscall

universe u v w

/-- Borrowed PDA inputs retain seed order, duplicates and empty byte strings.
The selected wrapper does not apply the seed count/length limits of the runtime. -/
structure PdaInputs where
  seeds : List _root_.Solanalib.Runtime.Bytes
  programId : Value

/-- The explicit 64-bit source slice profile, independent of PDA seed limits. -/
def PdaInputs.Bounded (inputs : PdaInputs) : Prop :=
  inputs.seeds.length < _root_.Solanalib.Runtime.U64_LIMIT ∧
    ∀ seed ∈ inputs.seeds, seed.length < _root_.Solanalib.Runtime.U64_LIMIT

/-- None denotes an address slot that is not established as fully initialized,
including partial initialization. The slot is a real output destination, not a
null pointer. Its physical bytes and storage identity need a separate binding. -/
structure PdaRequest where
  seeds : List _root_.Solanalib.Runtime.Bytes
  seedCount : UInt64
  programId : Value
  addressOutput : Option Value
  bumpOutput : UInt8

/-- Returned register and output observations are distinct. Nonzero status
does not promise an initialized address or an unchanged bump/output slot. -/
structure PdaReply where
  status : UInt64
  addressOutput : Option Value
  bumpOutput : UInt8

/-- The selected Solana branch creates MaybeUninit<Address> and bump 255,
then supplies the exact input slices/count and both output destinations. -/
def pdaRequest (inputs : PdaInputs) : PdaRequest :=
  ⟨inputs.seeds, UInt64.ofNat inputs.seeds.length, inputs.programId, none, 255⟩

/-- Only status zero reads the address/bump outputs. An uninitialized success
is not assigned a fallback key or a fabricated None return. -/
def decodePda (reply : PdaReply) (result : Option (Value × UInt8)) : Prop :=
  if reply.status = 0 then
    ∃ address, reply.addressOutput = some address ∧ result = some (address, reply.bumpOutput)
  else result = none

/-- Admission concerns every actual successful reply at this call. Other
statuses and abnormal exits need no initialized address output. -/
def SuccessInitialized {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (before : State) (inputs : PdaInputs) : Prop :=
  ∀ reply after, syscall before (pdaRequest inputs) (.returned reply after) →
    reply.status = 0 → ∃ address, reply.addressOutput = some address

/-- Initialization on status zero is exactly the condition that lets the
local decoder continue. It imposes no restriction on the returned bump. -/
theorem decodePda_hasResult_iff (reply : PdaReply) :
    (∃ result, decodePda reply result) ↔
      (reply.status = 0 → ∃ address, reply.addressOutput = some address) := by
  constructor
  · rintro ⟨result, decoded⟩ zero
    simp only [decodePda, zero, ↓reduceIte] at decoded
    obtain ⟨address, initialized, _⟩ := decoded
    exact ⟨address, initialized⟩
  · intro initialized
    by_cases zero : reply.status = 0
    · obtain ⟨address, present⟩ := initialized zero
      exact ⟨some (address, reply.bumpOutput), by
        simpa only [decodePda, zero, ↓reduceIte] using ⟨address, present, rfl⟩⟩
    · exact ⟨none, by simp only [decodePda, zero, ↓reduceIte]⟩

/-- Local selected-target try_find wrapper; the actual syscall is the only
primitive provider here. It preserves finite unwind and terminal exits. -/
def tryRun {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal) :
    Callback.Run State PdaInputs (Option (Value × UInt8)) Unwind Terminal :=
  fun before inputs => Callback.bind syscall
    (fun reply after outcome =>
      ∃ result, decodePda reply result ∧ outcome = .returned result after)
    before (pdaRequest inputs)

/-- Independent finite-exit characterization of the try_find wrapper. -/
def tryPost {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (before : State) (inputs : PdaInputs) :
    Outcome State (Option (Value × UInt8)) Unwind Terminal → Prop
  | .returned result after =>
      ∃ reply, syscall before (pdaRequest inputs) (.returned reply after) ∧ decodePda reply result
  | .unwound reason after => syscall before (pdaRequest inputs) (.unwound reason after)
  | .terminated reason => syscall before (pdaRequest inputs) (.terminated reason)

theorem tryRun_post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (before : State) (inputs : PdaInputs)
    (outcome : Outcome State (Option (Value × UInt8)) Unwind Terminal)
    (execution : tryRun syscall before inputs outcome) : tryPost syscall before inputs outcome := by
  obtain ⟨actual, source, next⟩ := execution
  cases actual with
  | returned reply after =>
      obtain ⟨result, decoded, rfl⟩ := next
      exact ⟨reply, source, decoded⟩
  | unwound reason after =>
      subst outcome
      exact source
  | terminated reason =>
      subst outcome
      exact source

theorem tryRun_returned {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (before after : State) (inputs : PdaInputs) (reply : PdaReply)
    (result : Option (Value × UInt8))
    (source : syscall before (pdaRequest inputs) (.returned reply after))
    (decoded : decodePda reply result) :
    tryRun syscall before inputs (.returned result after) :=
  ⟨.returned reply after, source, result, decoded, rfl⟩

/-- Every actual provider exit has a continuation under initialization
admission. Returned values retain the exact reply and state; abnormal exits
retain their reason and state without consulting the decoder. -/
theorem tryRun_retains {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (before : State) (inputs : PdaInputs)
    (ready : SuccessInitialized syscall before inputs)
    (exit : Outcome State PdaReply Unwind Terminal)
    (source : syscall before (pdaRequest inputs) exit) :
    match exit with
    | .returned reply after => ∃ result, decodePda reply result ∧
        tryRun syscall before inputs (.returned result after)
    | .unwound reason after => tryRun syscall before inputs (.unwound reason after)
    | .terminated reason => tryRun syscall before inputs (.terminated reason) := by
  cases exit with
  | returned reply after =>
      obtain ⟨result, decoded⟩ := (decodePda_hasResult_iff reply).2
        (ready reply after source)
      exact ⟨result, decoded, tryRun_returned syscall before after inputs reply result source
        decoded⟩
  | unwound reason after => exact ⟨.unwound reason after, source, rfl⟩
  | terminated reason => exact ⟨.terminated reason, source, rfl⟩

/-- Admission prevents local decoding from removing a finite provider exit.
This equivalence does not assert that the provider terminates. -/
theorem tryRun_hasOutcome_iff {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (before : State) (inputs : PdaInputs)
    (ready : SuccessInitialized syscall before inputs) :
    (∃ outcome, tryRun syscall before inputs outcome) ↔
      ∃ exit, syscall before (pdaRequest inputs) exit := by
  constructor
  · rintro ⟨_, exit, source, _⟩
    exact ⟨exit, source⟩
  · rintro ⟨exit, source⟩
    have retained := tryRun_retains syscall before inputs ready exit source
    cases exit with
    | returned reply after =>
        obtain ⟨result, _, execution⟩ := retained
        exact ⟨.returned result after, execution⟩
    | unwound reason after => exact ⟨.unwound reason after, retained⟩
    | terminated reason => exact ⟨.terminated reason, retained⟩

/-- This fixed panic site follows only an ordinary None return from try_find.
The callback includes panic machinery/cleanup and cannot return normally. -/
def panicMessage : String := "Unable to find a viable program address bump seed"

def finishFind {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal)
    (result : Option (Value × UInt8)) (after : State)
    (outcome : Outcome State (Value × UInt8) Unwind Terminal) : Prop :=
  match result with
  | some value => outcome = .returned value after
  | none => Callback.map (fun impossible : Empty => nomatch impossible)
      panic after .noViableProgramAddress outcome

/-- The selected find wrapper sequences the actual try_find exit, then invokes
its local panic site only for returned None, using the actual state of that syscall. -/
def findRun {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal) :
    Callback.Run State PdaInputs (Value × UInt8) Unwind Terminal :=
  Callback.bind (tryRun syscall) (finishFind panic)

/-- A successful reply continues with its actual address/bump. A nonzero
reply reaches the panic provider in the actual returned state and retains
each of the finite exits of that provider. No panic termination is assumed. -/
theorem findRun_retains {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal)
    (before : State) (inputs : PdaInputs)
    (ready : SuccessInitialized syscall before inputs)
    (exit : Outcome State PdaReply Unwind Terminal)
    (source : syscall before (pdaRequest inputs) exit) :
    match exit with
    | .returned reply after =>
        if reply.status = 0 then ∃ address, reply.addressOutput = some address ∧
          findRun syscall panic before inputs (.returned (address, reply.bumpOutput) after)
        else ∀ panicExit, panic after .noViableProgramAddress panicExit →
          findRun syscall panic before inputs
            (Outcome.map (fun impossible : Empty => nomatch impossible) panicExit)
    | .unwound reason after => findRun syscall panic before inputs (.unwound reason after)
    | .terminated reason => findRun syscall panic before inputs (.terminated reason) := by
  cases exit with
  | returned reply after =>
      by_cases zero : reply.status = 0
      · simp only [zero, ↓reduceIte]
        obtain ⟨address, initialized⟩ := ready reply after source zero
        refine ⟨address, initialized, .returned (some (address, reply.bumpOutput)) after, ?_, rfl⟩
        apply tryRun_returned syscall before after inputs reply _ source
        exact (by simpa only [decodePda, zero, ↓reduceIte] using ⟨address, initialized, rfl⟩)
      · simp only [zero, ↓reduceIte]
        intro panicExit panicked
        refine ⟨.returned none after, ?_, panicExit, panicked, rfl⟩
        apply tryRun_returned syscall before after inputs reply _ source
        simp only [decodePda, zero, ↓reduceIte]
  | unwound reason after =>
      exact ⟨.unwound reason after, ⟨.unwound reason after, source, rfl⟩, rfl⟩
  | terminated reason =>
      exact ⟨.terminated reason, ⟨.terminated reason, source, rfl⟩, rfl⟩

/-- Finite progress additionally requires a finite panic exit only when an
actual nonzero reply reaches that provider. Success and abnormal syscall
exits have no panic-execution premise. -/
theorem findRun_hasOutcome {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal)
    (before : State) (inputs : PdaInputs)
    (ready : SuccessInitialized syscall before inputs)
    (exit : Outcome State PdaReply Unwind Terminal)
    (source : syscall before (pdaRequest inputs) exit)
    (panicProgress : match exit with
      | .returned reply after => reply.status ≠ 0 →
          ∃ panicExit, panic after .noViableProgramAddress panicExit
      | .unwound _ _ => True
      | .terminated _ => True) :
    ∃ outcome, findRun syscall panic before inputs outcome := by
  have retained := findRun_retains syscall panic before inputs ready exit source
  cases exit with
  | returned reply after =>
      by_cases zero : reply.status = 0
      · simp only [zero, ↓reduceIte] at retained
        obtain ⟨address, _, execution⟩ := retained
        exact ⟨.returned (address, reply.bumpOutput) after, execution⟩
      · simp only [zero, ↓reduceIte] at retained
        obtain ⟨panicExit, panicked⟩ := panicProgress zero
        exact ⟨_, retained panicExit panicked⟩
  | unwound reason after => exact ⟨.unwound reason after, retained⟩
  | terminated reason => exact ⟨.terminated reason, retained⟩

/-- The find postcondition composes the independent try_find exit
characterization with the local unwrap_or_else panic site. -/
def findPost {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal) :
    Callback.Run State PdaInputs (Value × UInt8) Unwind Terminal :=
  Callback.bind (tryPost syscall) (finishFind panic)

theorem findRun_post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal)
    (before : State) (inputs : PdaInputs)
    (outcome : Outcome State (Value × UInt8) Unwind Terminal)
    (execution : findRun syscall panic before inputs outcome) :
    findPost syscall panic before inputs outcome := by
  obtain ⟨actual, tried, next⟩ := execution
  exact ⟨actual, tryRun_post syscall before inputs actual tried, next⟩

/-- Optional mathematical correspondence for ordinary syscall replies only.
It imposes no condition on metering failures, unwind or terminal exits. -/
def ReplyAgrees (reply : PdaReply) (answer : Option (Value × UInt8)) : Prop :=
  (reply.status = 0 → ∀ address, reply.addressOutput = some address →
    answer = some (address, reply.bumpOutput)) ∧
  (reply.status ≠ 0 → answer = none)

def NormalPdaAgreement {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal) (crypto : Crypto) : Prop :=
  ∀ before inputs reply after,
    syscall before (pdaRequest inputs) (.returned reply after) →
    ReplyAgrees reply (tryFind ⟨crypto, inputs.seeds, inputs.programId⟩)

/-- The pure PDA facet follows from primitive normal-reply correspondence;
the theorem neither supplies nor excludes any non-returning syscall exit. -/
theorem tryRun_returned_projection {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal) (crypto : Crypto)
    (agreement : NormalPdaAgreement syscall crypto) (before after : State)
    (inputs : PdaInputs) (result : Option (Value × UInt8))
    (execution : tryRun syscall before inputs (.returned result after)) :
    result = tryFind ⟨crypto, inputs.seeds, inputs.programId⟩ := by
  obtain ⟨reply, source, decoded⟩ := tryRun_post syscall before inputs _ execution
  have agrees := agreement before inputs reply after source
  by_cases zero : reply.status = 0
  · simp only [decodePda, zero, ↓reduceIte] at decoded
    obtain ⟨address, initialized, rfl⟩ := decoded
    exact (agrees.1 zero address initialized).symm
  · simp only [decodePda, zero, ↓reduceIte] at decoded
    exact decoded.trans (agrees.2 zero).symm

theorem finishFind_returned {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal)
    (result : Option (Value × UInt8)) (middle after : State) (value : Value × UInt8)
    (execution : finishFind panic result middle (.returned value after)) :
    result = some value ∧ middle = after := by
  cases result with
  | some result =>
      cases execution
      exact ⟨rfl, rfl⟩
  | none =>
      obtain ⟨actual, _, mapped⟩ := execution
      cases actual with
      | returned impossible _ => exact nomatch impossible
      | unwound _ _ => cases mapped
      | terminated _ => cases mapped

theorem findRun_returned_projection {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal)
    (panic : Callback.Run State SearchPanic Empty Unwind Terminal)
    (crypto : Crypto) (agreement : NormalPdaAgreement syscall crypto)
    (before after : State) (inputs : PdaInputs) (value : Value × UInt8)
    (execution : findRun syscall panic before inputs (.returned value after)) :
    tryFind ⟨crypto, inputs.seeds, inputs.programId⟩ = some value := by
  obtain ⟨actual, tried, next⟩ := execution
  cases actual with
  | returned result middle =>
      obtain ⟨sameValue, _⟩ := finishFind_returned panic result middle after value next
      exact (tryRun_returned_projection syscall crypto agreement before middle inputs result
        tried).symm.trans sameValue
  | unwound _ _ => cases next
  | terminated _ => cases next

/-- Address passes null. The separate initialized-byte constructor makes the
distinction from the Curve SDK scratch-output API explicit and testable. -/
inductive CurveOutput where
  | nullPointer
  | initializedByte (value : UInt8)
  deriving DecidableEq, Repr

structure CurveRequest where
  curve : UInt64
  point : Value
  output : CurveOutput

def curveRequest (address : Value) : CurveRequest := ⟨0, address, .nullPointer⟩

/-- Concrete Address::is_on_curve uses its known AsRef implementation, then
the Ed25519 syscall with a null third argument, and tests only status zero. -/
def curveRun {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State CurveRequest UInt64 Unwind Terminal) :
    Callback.Run State Value Bool Unwind Terminal :=
  fun before address => Callback.map (fun status => status == 0)
    syscall before (curveRequest address)

def curvePost {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State CurveRequest UInt64 Unwind Terminal)
    (before : State) (address : Value) : Outcome State Bool Unwind Terminal → Prop
  | .returned value after =>
      ∃ status, syscall before (curveRequest address) (.returned status after) ∧ value = (status ==
        0)
  | .unwound reason after => syscall before (curveRequest address) (.unwound reason after)
  | .terminated reason => syscall before (curveRequest address) (.terminated reason)

theorem curveRun_post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State CurveRequest UInt64 Unwind Terminal)
    (before : State) (address : Value) (outcome : Outcome State Bool Unwind Terminal)
    (execution : curveRun syscall before address outcome) : curvePost syscall before address
      outcome := by
  obtain ⟨actual, source, rfl⟩ := execution
  cases actual with
  | returned status after => exact ⟨status, source, rfl⟩
  | unwound _ _ => exact source
  | terminated _ => exact source

/-- Pure curve agreement concerns the return register only. Null-output
admission, state effects and abnormal exits remain separate syscall facts. -/
def NormalCurveAgreement {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State CurveRequest UInt64 Unwind Terminal) (crypto : Crypto) : Prop :=
  ∀ before address status after,
    syscall before (curveRequest address) (.returned status after) →
    (status == 0) = isOnCurve crypto address

theorem curveRun_returned_projection {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (syscall : Callback.Run State CurveRequest UInt64 Unwind Terminal) (crypto : Crypto)
    (agreement : NormalCurveAgreement syscall crypto) (before after : State)
    (address : Value) (value : Bool)
    (execution : curveRun syscall before address (.returned value after)) :
    value = isOnCurve crypto address := by
  obtain ⟨status, source, result⟩ := curveRun_post syscall before address _ execution
  exact result.trans (agreement before address status after source)

end Solanalib.Specs.Core.Address.Syscall
