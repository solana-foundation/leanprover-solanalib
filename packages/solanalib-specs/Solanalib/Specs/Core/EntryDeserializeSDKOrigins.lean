/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserializeSDKShape

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Solanalib.Specs.Core.EntryDeserialize.SDK

/-- One unique source header supplies two independent RefCells, in allocation order. -/
def originCells (account : Account) : List (Borrow.Cell AccountInfo.Content) :=
  [⟨.lamports account.lamports, .refCell 64⟩, ⟨.data account.data, .refCell 64⟩]

def originBuffers (account : Account) : List (Option AccountInfoSdk.Buffer) :=
  [none, some ⟨account.data.length, account.data.length, account.spare⟩]

def originInfo (account : Account) (index : Nat) : Info :=
  ⟨⟨account.key, ⟨2 * index⟩, ⟨2 * index + 1⟩, account.owner, account.rentEpoch,
    account.signer != 0, account.writable != 0, account.executable != 0, ⟨index⟩⟩,
    account.offset⟩

def HasOrigin (origins : List Account) (info : Info) : Prop :=
  ∃ index account, origins[index]? = some account ∧ info = originInfo account index

theorem originCells_length (origins : List Account) :
    (origins.flatMap originCells).length = 2 * origins.length := by
  induction origins with
  | nil => rfl
  | cons account rest induction => simp [originCells, induction]; omega

theorem hasOrigin_append (origins : List Account) (account : Account) (info : Info)
    (found : HasOrigin origins info) : HasOrigin (origins ++ [account]) info := by
  obtain ⟨index, source, lookup, equal⟩ := found
  refine ⟨index, source, ?_, equal⟩
  rw [List.getElem?_append_left ((List.getElem_of_getElem? lookup).choose)]
  exact lookup

theorem hasOrigin_last (origins : List Account) (account : Account) :
    HasOrigin (origins ++ [account]) (originInfo account origins.length) := by
  exact ⟨origins.length, account, by simp, rfl⟩

/-- The complete fresh SDK object graph, independently of physical addresses. Every Info
names the same two cells and owner index as its unique source header; duplicates introduce
neither a new cell nor a new owner. All cells start unborrowed, with their full resize reserve. -/
structure Origins {Aux : Type} (vector length used : Nat) (origins : List Account)
    (infos : List Info) (state : State Aux) : Prop where
  cells : state.accounts.borrow.cells = origins.flatMap originCells
  buffers : state.accounts.buffers = origins.flatMap originBuffers
  owners : state.accounts.owners = origins.map Account.owner
  guards : state.accounts.borrow.slots = []
  counts : state.rcStrong.length = 2 * origins.length
  number : origins.length ≤ used
  bounds : ∀ account ∈ origins,
    account.offset + 88 + account.data.length + account.spare.length ≤ length
  infoOrigins : ∀ info ∈ infos, HasOrigin origins info
  present : vector < state.vectors.length
  stored : state.vectors.getD vector [] = infos

/-- The state after the two successful allocations for one unique account. The private state of the
allocator is the second reply; the input write still occurs between the actual requests
in `process`, and is not moved across that effect by this projection. -/
def created {Aux : Type} (before : State Aux) (account : Account) (allocator : Aux) :
    Info × State Aux :=
  let (lamports, withLamports) := insertCell { before with allocator := allocator }
    (.lamports account.lamports) none
  let recorded := { withLamports with
    bytes := overwrite withLamports.bytes (account.offset + 4)
      (Solanalib.Runtime.leBytes 4 account.data.length) }
  let (data, withData) := insertCell recorded (.data account.data)
    (some ⟨account.data.length, account.data.length, account.spare⟩)
  let ownerRef : AccountInfo.OwnerRef := ⟨withData.accounts.owners.length⟩
  let info : Info := ⟨⟨account.key, lamports, data, account.owner, account.rentEpoch,
    account.signer != 0, account.writable != 0, account.executable != 0, ownerRef⟩,
    account.offset⟩
  (info, { withData with accounts :=
    { withData.accounts with owners := withData.accounts.owners ++ [account.owner] } })

theorem created_info {Aux : Type} {vector length used : Nat} {origins : List Account}
    {infos : List Info} {before : State Aux} (graph : Origins vector length used origins infos
      before)
    (account : Account) (allocator : Aux) :
    (created before account allocator).1 = originInfo account origins.length := by
  have cellCount : before.accounts.borrow.cells.length = 2 * origins.length := by
    rw [graph.cells, originCells_length]
  simp [created, insertCell, Borrow.State.insert, originInfo, cellCount, graph.owners]

theorem Origins.clone {Aux : Type} {vector length used : Nat} {origins : List Account}
    {infos : List Info} {before : State Aux} (graph : Origins vector length used origins infos
      before)
    (info : Info) (member : info ∈ infos) :
    Origins vector length (used + 1) origins (infos ++ [info])
      (push (cloneInfo before info) vector (infos ++ [info])) := by
  refine ⟨graph.cells, graph.buffers, graph.owners, graph.guards, ?_,
    by have := graph.number; omega,
    graph.bounds, ?_, ?_, ?_⟩
  · simpa [cloneInfo, push] using graph.counts
  · intro value found
    simp only [List.mem_append, List.mem_singleton] at found
    rcases found with found | rfl
    · exact graph.infoOrigins value found
    · exact graph.infoOrigins _ member
  · simpa [cloneInfo, push] using graph.present
  · exact push_infos _ _ _ (by simpa [cloneInfo] using graph.present)

theorem Origins.create {Aux : Type} {vector length used : Nat} {origins : List Account}
    {infos : List Info} {before : State Aux} (graph : Origins vector length used origins infos
      before)
    (account : Account) (allocator : Aux)
    (bounds : account.offset + 88 + account.data.length + account.spare.length ≤ length) :
    Origins vector length (used + 1) (origins ++ [account])
      (infos ++ [(created before account allocator).1])
      (push (created before account allocator).2 vector
        (infos ++ [(created before account allocator).1])) := by
  constructor
  · simp [created, insertCell, Borrow.State.insert, push, graph.cells, originCells,
      List.flatMap_append, List.append_assoc]
  · simp [created, insertCell, push, graph.buffers, originBuffers,
      List.flatMap_append, List.append_assoc]
  · simp [created, insertCell, push, graph.owners]
  · simpa [created, insertCell, Borrow.State.insert, push] using graph.guards
  · simp [created, insertCell, push, graph.counts]; omega
  · simp only [List.length_append, List.length_singleton]
    have := graph.number
    omega
  · intro source member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact graph.bounds source member
    · exact bounds
  · intro info member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact hasOrigin_append origins account info (graph.infoOrigins info member)
    · rw [created_info graph]
      exact hasOrigin_last origins account
  · simpa [created, insertCell, push] using graph.present
  · exact push_infos _ _ _ (by simpa [created, insertCell] using graph.present)

theorem process_origins (index : Index) (views : Views) (vector length : Nat) (slots : List Slot)
    (origins : List Account) (infos : List Info) (used : Nat) (before after : State index.Aux)
    (result : Result) (graph : Origins vector length used origins infos before)
    (bounds : ∀ slot ∈ slots,
      slot.account.offset + 88 + slot.account.data.length + slot.account.spare.length ≤ length)
    (returned : process index views vector slots infos before = some (.returned result after)) :
    ∃ sources, Origins vector length (used + slots.length) sources
      (after.vectors.getD vector []) after := by
  induction slots generalizing origins infos used before with
  | nil =>
    have same : before = after := (Outcome.returned.inj (Option.some.inj returned)).2
    subst after
    refine ⟨origins, ?_⟩
    rw [graph.stored]
    simpa using graph
  | cons slot rest induction =>
    have header := bounds slot (by simp)
    have tail : ∀ other ∈ rest,
        other.account.offset + 88 + other.account.data.length + other.account.spare.length ≤ length
          :=
      fun other member => bounds other (by simp [member])
    cases duplicate : slot.duplicate with
    | some earlier =>
      simp only [process, duplicate] at returned
      cases found : infos[earlier]? with
      | none => simp [found] at returned
      | some info =>
        simp only [found] at returned
        have next := induction origins (infos ++ [info]) (used + 1) _
          (graph.clone info (List.mem_of_getElem? found)) tail returned
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
    | none =>
      simp only [process, duplicate] at returned
      obtain ⟨_, _, returned⟩ := allocateThen_returned index _ _ _ _ _ returned
      obtain ⟨allocatedData, _, returned⟩ := allocateThen_returned index _ _ _ _ _ returned
      change process index views vector rest
        (infos ++ [(created before slot.account allocatedData).1])
        (push (created before slot.account allocatedData).2 vector
          (infos ++ [(created before slot.account allocatedData).1])) = _ at returned
      have next := induction (origins ++ [slot.account]) _ (used + 1) _
        (graph.create slot.account allocatedData header) tail returned
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

theorem execute_origins (index : Index) (before after : State index.Aux) (result : Result)
    (parsed : Parsed) (parsedBytes : parse before.bytes = some parsed)
    (accounts : before.accounts = ⟨⟨[], []⟩, [], []⟩)
    (vectors : before.vectors = []) (counts : before.rcStrong = [])
    (bounds : ∀ slot ∈ parsed.slots,
      slot.account.offset + 88 + slot.account.data.length + slot.account.spare.length ≤
        before.bytes.length)
    (returned : execute index before = some (.returned result after)) :
    ∃ origins, Origins 0 before.bytes.length parsed.slots.length origins
      (after.vectors.getD 0 []) after := by
  have finish (allocator : index.Aux)
      (processed : process index parsed.views 0 parsed.slots []
        { before with vectors := [[]], allocator := allocator } = some (.returned result after)) :
      ∃ origins, Origins 0 before.bytes.length parsed.slots.length origins
        (after.vectors.getD 0 []) after := by
    have initial : Origins 0 before.bytes.length 0 [] []
        { before with vectors := [[]], allocator := allocator } := by
      constructor <;> simp [accounts, counts]
    simpa using process_origins index parsed.views 0 before.bytes.length parsed.slots [] [] 0
      _ _ _ initial bounds processed
  unfold execute at returned
  simp [parsedBytes, vectors] at returned
  split at returned
  · exact finish before.allocator returned
  · obtain ⟨allocator, _, processed⟩ := allocateThen_returned index _ _ _ _ _ returned
    apply finish allocator
    simpa [vectors] using processed

end Solanalib.Specs.Core.EntryDeserialize.SDK
