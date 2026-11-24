/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Hash
public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family
public import Solanalib.Runtime.Syscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Hash.Syscall

universe u v w

/-- The two cfg alternatives selecting the same syscall branch in hasher 3.1.0.
The host SHA2 and host panic branches are outside this selected-target model. -/
inductive Target where
  /-- The source target_os is solana. -/
  | solanaOS
  /-- The source target_arch is bpf. -/
  | bpfArch
  deriving DecidableEq, Repr

/-- The forwarded slice count fits its u64 cast. Runtime slice-count limits are
separate; the wrapper neither concatenates nor bounds the slice count itself. -/
def Bounded (slices : List Solanalib.Runtime.Bytes) : Prop :=
  slices.length < Solanalib.Runtime.U64_LIMIT

/-- Exact ordered slice arguments and initial MaybeUninit output observation.
None includes incomplete initialization; it is not a null output pointer. -/
structure Request where
  /-- The source slices, retaining boundaries and order. -/
  slices : List Solanalib.Runtime.Bytes
  /-- The source slice count after its u64 cast. -/
  count : UInt64
  /-- The initialization of the destination before the call. -/
  output : Option Hash.Value

/-- The returned status and output observation are distinct. Provider effects,
including any partially written memory, remain in the supplied callback state. -/
structure Reply where
  /-- The returned word, which this source wrapper ignores. -/
  status : UInt64
  /-- A complete initialized array, or an incomplete destination. -/
  output : Option Hash.Value

/-- The actual wrapper starts with an uninitialized 32-byte destination. -/
def request (slices : List Solanalib.Runtime.Bytes) : Request :=
  ⟨slices, UInt64.ofNat slices.length, none⟩

/-- The mathematical request for the canonical runtime model preserves every
slice boundary, duplicate and empty slice. It does not establish VM translation. -/
def Request.canonical (request : Request) : Solanalib.Runtime.SysReq := .hash .sha256 request.slices

/-- With the source width premise, the forwarded count is the actual count. -/
theorem request_count (slices : List Solanalib.Runtime.Bytes) (bounded : Bounded slices) :
    (request slices).count.toNat = slices.length := by
  change slices.length % 2^64 = slices.length
  exact Nat.mod_eq_of_lt bounded

/-- The primitive law needed before assume_init. The source ignores status,
so this quantifies every normal return, including nonzero status. A provider
with even one uninitialized normal exit cannot satisfy this premise. -/
def EveryReturnInitialized {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal)
    (before : State) (slices : List Solanalib.Runtime.Bytes) : Prop :=
  ∀ reply after, provider before (request slices) (.returned reply after) →
    ∃ hash, reply.output = some hash

/-- Once initialized, assume_init reads exactly the written hash. It does not
turn a nonzero status into a source Result error or synthesize missing bytes. -/
def run {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal) :
    Callback.Run State (List Solanalib.Runtime.Bytes) Hash.Value Unwind Terminal :=
  fun before slices => Callback.bind provider
    (fun reply after outcome =>
      ∃ hash, reply.output = some hash ∧ outcome = .returned hash after)
    before (request slices)

/-- Independent finite-exit characterization of the selected wrapper. Unwind
and terminal exits are the exact exits of the provider, without invented final state. -/
def post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal)
    (before : State) (slices : List Solanalib.Runtime.Bytes) :
    Outcome State Hash.Value Unwind Terminal → Prop
  | .returned hash after =>
      ∃ reply, provider before (request slices) (.returned reply after) ∧ reply.output = some hash
  | .unwound reason after => provider before (request slices) (.unwound reason after)
  | .terminated reason => provider before (request slices) (.terminated reason)

theorem run_iff_post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal) (before : State)
    (slices : List Solanalib.Runtime.Bytes) (outcome : Outcome State Hash.Value Unwind Terminal) :
    run provider before slices outcome ↔ post provider before slices outcome := by
  constructor
  · rintro ⟨actual, source, forwarded⟩
    cases actual with
    | returned reply after =>
      obtain ⟨hash, written, rfl⟩ := forwarded
      exact ⟨reply, source, written⟩
    | unwound reason after => subst outcome; exact source
    | terminated reason => subst outcome; exact source
  · intro step
    cases outcome with
    | returned hash after =>
      obtain ⟨reply, source, written⟩ := step
      exact ⟨.returned reply after, source, hash, written, rfl⟩
    | unwound reason after => exact ⟨.unwound reason after, step, rfl⟩
    | terminated reason => exact ⟨.terminated reason, step, rfl⟩

/-- Every normal provider exit is represented under the initialization law;
the precondition does not justify retaining only a convenient provider branch. -/
theorem initialized_return_has_run {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal)
    {before after : State} {slices : List Solanalib.Runtime.Bytes} {reply : Reply}
    (initialized : EveryReturnInitialized provider before slices)
    (source : provider before (request slices) (.returned reply after)) :
    ∃ hash, reply.output = some hash ∧ run provider before slices (.returned hash after) := by
  obtain ⟨hash, written⟩ := initialized reply after source
  exact ⟨hash, written,
    (run_iff_post provider before slices (.returned hash after)).mpr ⟨reply, source, written⟩⟩

/-- The mathematical primitive and its provider correspondence remain explicit.
This is only a normal-output law, not a runtime admission or termination law. -/
def NormalHashAgreement {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal)
    (primitives : Solanalib.Runtime.CryptoPrimitives) : Prop :=
  ∀ before slices reply after, provider before (request slices) (.returned reply after) →
    ∀ hash, reply.output = some hash → hash.bytes = primitives.sha256 slices.flatten

theorem returned_hash_projection {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (provider : Callback.Run State Request Reply Unwind Terminal)
    (primitives : Solanalib.Runtime.CryptoPrimitives) (agreement : NormalHashAgreement provider
      primitives)
    (before after : State) (slices : List Solanalib.Runtime.Bytes) (hash : Hash.Value)
    (execution : run provider before slices (.returned hash after)) :
    hash.bytes = primitives.sha256 slices.flatten := by
  obtain ⟨reply, source, written⟩ := (run_iff_post provider before slices _).mp execution
  exact agreement before slices reply after source hash written

/-- The canonical value-level hash reply uses the same concatenation. Actual
provider interpretation, output width/access, metering and failure stay separate. -/
theorem canonical_hash_reply (primitives : Solanalib.Runtime.CryptoPrimitives)
    (limit : Nat) (slices : List Solanalib.Runtime.Bytes) (bounded : slices.length ≤ limit) :
    Solanalib.Runtime.hashReply limit (fun inputs => primitives.sha256 inputs.flatten) slices =
      .ok ⟨0, [primitives.sha256 slices.flatten]⟩ :=
  Solanalib.Runtime.hashReply_ok _ _ _ bounded

/-- A selected target and explicit stateful syscall provider. Pointer placement,
slice legality and the chosen cfg must be bound to a source profile separately. -/
structure Index where
  /-- The ambient state of the provider, including its observable effects. -/
  State : Type
  /-- Reasons attached to finite unwinding exits. -/
  Unwind : Type
  /-- Reasons attached to terminal exits. -/
  Terminal : Type
  /-- A cfg alternative that selects the syscall branch. -/
  target : Target
  /-- The supplied complete finite-exit syscall relation. -/
  provider : Callback.Run State Request Reply Unwind Terminal

/-- Full selected-wrapper family with mandatory all-return initialization.
Exact count-word equality is the separate `request_count` result. -/
def family : Family where
  Index := Index
  State := Index.State
  Args := fun _ => List Solanalib.Runtime.Bytes
  Value := fun _ => Hash.Value
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun before slices => EveryReturnInitialized index.provider before slices
    post := post index.provider
  }

/-- Execute the common callback sequence at the supplied family index. -/
def reference : FamilyRun family := fun index => run index.provider

theorem reference_correct : FamilyReference family reference := by
  intro index before slices outcome _ execution
  exact (run_iff_post index.provider before slices outcome).mp execution

/-- An inhabited provider for closed consistency evidence, not a SHA-256
implementation or a promise that the runtime succeeds. -/
def sample : Index where
  State := Unit
  Unwind := Empty
  Terminal := Empty
  target := .solanaOS
  provider := Callback.ofFunction fun state _ => .returned ⟨0, some Hash.zero⟩ state

theorem sample_hasExecution : FamilyHasExecution family reference sample := by
  refine ⟨(), [[1, 2], [], [3]], .returned Hash.zero (), ?_, ?_⟩
  · intro reply after execution
    cases execution
    exact ⟨Hash.zero, rfl⟩
  · exact ⟨.returned ⟨0, some Hash.zero⟩ (), rfl, Hash.zero, rfl, rfl⟩

end Solanalib.Specs.Core.Hash.Syscall
