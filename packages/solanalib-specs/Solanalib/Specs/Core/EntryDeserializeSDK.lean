/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserialize
public import Solanalib.Specs.Core.AccountInfoSdk
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.EntryDeserialize.SDK

/-- One returned AccountInfo and the unique serialized header that supplies its references.
The `unused` field of the shared value vocabulary carries the real rent epoch at SDK 2.3.0. -/
structure Info where
  value : AccountInfo.Value
  headerOffset : Nat
  deriving DecidableEq, Repr

/-- Allocation sites in their actual source order. A duplicate performs no allocation. -/
inductive Allocation where
  | vector (requestedCapacity : Nat)
  | lamports (headerOffset : Nat)
  | data (headerOffset : Nat)
  deriving DecidableEq, Repr

/-- The input at the instant an allocation dependency is called. In particular the data
allocation observes the original-length write, whereas the lamports allocation precedes it. -/
structure AllocationRequest where
  site : Allocation
  input : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

/-- The Global allocator has no legal unwinding exit. An explicit provider may return,
terminate, or have no finite outcome. It frames input bytes and existing account resources;
the request exposes the current input observation of the source without permitting arbitrary writes.
-/
structure Index where
  Aux : Type
  Terminal : Type
  allocate : Aux → AllocationRequest → Option (Outcome Aux Unit Empty Terminal)

/-- A single shared world. Existing account cells, owners and vectors remain represented.
Rc counts and vector slots record owned aliases; handles alone never assert a permission. -/
structure State (Aux : Type) where
  bytes : Solanalib.Runtime.Bytes
  accounts : AccountInfoSdk.State
  rcStrong : List Nat
  vectors : List (List Info)
  allocator : Aux
  deriving DecidableEq, Repr

structure Result where
  views : Views
  vector : Nat
  deriving DecidableEq, Repr

/-- Cells, serialized buffers and Rc multiplicities use the same finite index space. -/
def Coherent {Aux : Type} (state : State Aux) : Prop :=
  state.accounts.buffers.length = state.accounts.borrow.cells.length ∧
    state.rcStrong.length = state.accounts.borrow.cells.length

/-- Pointer and lifetime safety are separately supplied by the execution representation.
These premises ensure the mathematical parse and the shared cell-to-buffer interpretation. -/
def Admitted {Aux : Type} (state : State Aux) : Prop :=
  Coherent state ∧ ∃ parsed, parse state.bytes = some parsed ∧ parsed.slots.length * 48 < 2^63

/-- Lift a successful allocator reply into the same account world. A terminal has no
invented post-state or cleanup; no finite allocator outcome gives no finite call outcome. -/
def allocateThen (index : Index) (before : State index.Aux) (site : Allocation)
    (next : State index.Aux → Option (Outcome (State index.Aux) Result Empty index.Terminal)) :
    Option (Outcome (State index.Aux) Result Empty index.Terminal) := do
  let outcome ← index.allocate before.allocator ⟨site, before.bytes⟩
  match outcome with
  | .returned () after => next { before with allocator := after }
  | .terminated reason => pure (.terminated reason)
  | .unwound impossible _ => nomatch impossible

/-- Create one fresh, unborrowed Rc/RefCell payload and its aligned buffer/count slots. -/
def insertCell {Aux : Type} (before : State Aux) (content : AccountInfo.Content)
    (buffer : Option AccountInfoSdk.Buffer) : Borrow.Handle × State Aux :=
  let (handle, borrow) := before.accounts.borrow.insert (.refCell 64) content
  (handle, { before with
    accounts := { before.accounts with borrow := borrow, buffers := before.accounts.buffers ++
      [buffer] }
    rcStrong := before.rcStrong ++ [1] })

/-- The two Rc clones of the source preserve all pointed identities. Fresh Rc counts cannot
overflow on the admitted domain: each count is bounded by the number of input slots,
whose 48-byte AccountInfo vector must fit below isize::MAX on the reviewed 64-bit layout. -/
def cloneInfo {Aux : Type} (before : State Aux) (info : Info) : State Aux :=
  let counts := before.rcStrong.set info.value.lamports.cell
    (before.rcStrong.getD info.value.lamports.cell 0 + 1)
  { before with
    rcStrong := counts.set info.value.data.cell (counts.getD info.value.data.cell 0 + 1) }

def push {Aux : Type} (before : State Aux) (vector : Nat) (infos : List Info) : State Aux :=
  { before with vectors := before.vectors.set vector infos }

/-- Source account processing, including the write between the two Rc allocations.
Only a nonduplicate introduces cells or owner storage; duplicates copy the preceding
Info verbatim, including its borrow cells and serialized header location. -/
def process (index : Index) (views : Views) (vector : Nat) :
    List Slot → List Info → State index.Aux →
      Option (Outcome (State index.Aux) Result Empty index.Terminal)
  | [], _, before => some (.returned ⟨views, vector⟩ before)
  | slot :: rest, infos, before =>
    match slot.duplicate with
    | some earlier => do
      let info ← infos[earlier]?
      let after := push (cloneInfo before info) vector (infos ++ [info])
      process index views vector rest (infos ++ [info]) after
    | none =>
      allocateThen index before (.lamports slot.account.offset) fun allocatedLamports =>
        let (lamports, withLamports) := insertCell allocatedLamports
          (.lamports slot.account.lamports) none
        let recorded := { withLamports with
          bytes := overwrite withLamports.bytes (slot.account.offset + 4)
            (Solanalib.Runtime.leBytes 4 slot.account.data.length) }
        allocateThen index recorded (.data slot.account.offset) fun allocatedData =>
          let (data, withData) := insertCell allocatedData (.data slot.account.data)
            (some ⟨slot.account.data.length, slot.account.data.length, slot.account.spare⟩)
          let ownerRef : AccountInfo.OwnerRef := ⟨withData.accounts.owners.length⟩
          let info : Info := ⟨⟨slot.account.key, lamports, data, slot.account.owner,
            slot.account.rentEpoch, slot.account.signer != 0, slot.account.writable != 0,
            slot.account.executable != 0, ownerRef⟩, slot.account.offset⟩
          let owned := { withData with accounts :=
            { withData.accounts with owners := withData.accounts.owners ++ [slot.account.owner] } }
          process index views vector rest (infos ++ [info]) (push owned vector (infos ++ [info]))

/-- The vector reserves capacity once before any account read. Its zero-capacity
construction allocates no heap. Every push fits, so there is no growth allocation. -/
def execute (index : Index) (before : State index.Aux) :
    Option (Outcome (State index.Aux) Result Empty index.Terminal) := do
  let parsed ← parse before.bytes
  let vector := before.vectors.length
  let next := fun allocated => process index parsed.views vector parsed.slots []
    { allocated with vectors := allocated.vectors ++ [[]] }
  if parsed.slots.isEmpty then next before
  else allocateThen index before (.vector parsed.slots.length) next

def family : Family where
  Index := Index
  State := fun index => State index.Aux
  Args := fun _ => Unit
  Value := fun _ => Result
  Unwind := fun _ => Empty
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun before _ => Admitted before
    post := fun before _ outcome => execute index before = some outcome }

def run : FamilyRun family := fun index before _ outcome => execute index before = some outcome

theorem reference : FamilyReference family run := by
  intro _ _ _ _ _ step
  exact step

/-- A closed allocator interpretation that records successful requests in order. This
is a mathematical provider witness, not a proof of GlobalAlloc or a successful Rust allocation. -/
def traceIndex : Index where
  Aux := List AllocationRequest
  Terminal := Allocation
  allocate := fun before request => some (.returned () (before ++ [request]))

def emptyState (bytes : Solanalib.Runtime.Bytes) : State (List AllocationRequest) :=
  ⟨bytes, ⟨⟨[], []⟩, [], []⟩, [], [], []⟩

def sample : Index := traceIndex

theorem hasExecution : FamilyHasExecution family run sample := by
  refine ⟨emptyState emptyBytes, (), .returned ⟨⟨16, .zero, 16, []⟩, 0⟩
    { emptyState emptyBytes with vectors := [[]] }, ?_, ?_⟩
  · exact ⟨⟨rfl, rfl⟩, ⟨_, parse_empty, by decide⟩⟩
  · change execute traceIndex (emptyState emptyBytes) = _
    simp [execute, emptyState, parse_empty, process, Parsed.views, Parsed.instructionOffset]
    rfl

theorem satisfiable : FamilySatisfiable family sample := hasExecution.satisfiable

/-- The cell insertion preserves the table correspondence used by later SDK resizes. -/
theorem insertCell_coherent {Aux : Type} (before : State Aux) (content : AccountInfo.Content)
    (buffer : Option AccountInfoSdk.Buffer) (coherent : Coherent before) :
    Coherent (insertCell before content buffer).2 := by
  rcases coherent with ⟨buffers, counts⟩
  simp [Coherent, insertCell, Borrow.State.insert, buffers, counts]

/-- A newly installed data cell has exactly the original length and spare bytes supplied
by the entrypoint, at the same handle consumed by AccountInfo::realloc. -/
theorem insertCell_buffer {Aux : Type} (before : State Aux) (content : AccountInfo.Content)
    (buffer : AccountInfoSdk.Buffer) (coherent : Coherent before) :
    (insertCell before content (some buffer)).2.accounts.buffer
      (insertCell before content (some buffer)).1 = some buffer := by
  simp [insertCell, Borrow.State.insert, AccountInfoSdk.State.buffer, ← coherent.1]

/-- The returned cell starts with one owned Rc, independently of earlier resources. -/
theorem insertCell_count {Aux : Type} (before : State Aux) (content : AccountInfo.Content)
    (buffer : Option AccountInfoSdk.Buffer) (coherent : Coherent before) :
    (insertCell before content buffer).2.rcStrong[(insertCell before content buffer).1.cell]? =
      some 1 := by
  simp [insertCell, Borrow.State.insert, ← coherent.2]

end Solanalib.Specs.Core.EntryDeserialize.SDK
