/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedGuardComposition
public import Solanalib.Specs.Core.TokenRequestAllocatedGuardObservations
public import Solanalib.Specs.Core.TokenRequestAllocatedPdaAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedCollectAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedLiteralAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Admission

open AllocatedGuard AllocatedControl

/-- The graph of an actual infallible empty-vector primitive. This exposes its
real state transition to admission without changing the source operation. -/
def emptyCall {Extra Resource Unwind Terminal : Type}
    (empty : World Extra → Resource × World Extra) :
    Callback.Run (World Extra) Unit Resource Unwind Terminal :=
  Callback.ofFunction fun before _ => .returned (empty before).1 (empty before).2

/-- The allocation-free metadata write viewed as its actual finite transition. -/
def writeMetaCall (types : Types) :
    Callback.Run (World types.Extra) (types.MetaResource × Nat × Solanalib.Runtime.CpiMeta) Unit
      types.Unwind types.Terminal :=
  fun before input outcome => ∃ after,
    types.writeMeta before input.1 input.2.1 input.2.2 after ∧ outcome = .returned () after

/-- Exactly the ordinary provider operations used by fee=None preparation.
The catalogue omits unused vector methods. Rc calls keep their Empty unwind
type; the actual CPI is outside the source-local data-guard scopes. -/
inductive Primitive (types : Types) : {Args Value Unwind : Type} →
    Callback.Run (World types.Extra) Args Value Unwind types.Terminal → Prop
  /-- Create the empty instruction-byte owner. -/
  | bytesEmpty : Primitive types (emptyCall (Unwind := types.Unwind) (Terminal := types.Terminal)
    types.bytes.empty)
  /-- Allocate instruction-byte storage with capacity. -/
  | bytesCapacity : Primitive types (types.bytes.withCapacity)
  /-- Append one encoded instruction byte. -/
  | bytesPush : Primitive types (types.bytes.push)
  /-- Append encoded instruction bytes. -/
  | bytesExtend : Primitive types (types.bytes.extend)
  /-- Destroy the instruction-byte owner. -/
  | bytesDrop : Primitive types (types.bytes.drop)
  /-- Allocate instruction metadata storage. -/
  | metasCapacity : Primitive types (types.metas.withCapacity)
  /-- Construct the initial instruction metadata. -/
  | metasList : Primitive types (types.metas.fromList)
  /-- Append a resolved account metadata entry. -/
  | metasPush : Primitive types (types.metas.push)
  /-- Append the current Execute metadata suffix. -/
  | metasExtend : Primitive types (types.metas.extend)
  /-- Destroy an instruction metadata owner. -/
  | metasDrop : Primitive types (types.metas.drop)
  /-- Append a cloned AccountInfo owner. -/
  | infosPush : Primitive types (types.infos.push)
  /-- Clone and append the current Execute account suffix. -/
  | infosExtend : Primitive types (types.infos.extend)
  /-- Destroy an AccountInfo vector and its elements. -/
  | infosDrop : Primitive types (types.infos.drop)
  /-- Create the TLV duplicate-discriminator accumulator. -/
  | discriminatorsEmpty : Primitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.discriminators.empty)
  /-- Record a parsed TLV discriminator. -/
  | discriminatorsPush : Primitive types (types.discriminators.push)
  /-- Destroy the discriminator accumulator. -/
  | discriminatorsDrop : Primitive types (types.discriminators.drop)
  /-- Allocate the repeated-zero Mint padding temporary. -/
  | paddingList : Primitive types (types.paddingBytes.fromList)
  /-- Destroy the padding temporary before the next account read. -/
  | paddingDrop : Primitive types (types.paddingBytes.drop)
  /-- Allocate an owned literal seed buffer. -/
  | literalBytes : Primitive types (types.seedOps.bytes.fromList)
  /-- Create the owned seed accumulator. -/
  | seedsEmpty : Primitive types (emptyCall (Unwind := types.Unwind) (Terminal := types.Terminal)
    types.seedOps.seeds.empty)
  /-- Append an unpacked seed and transfer its literal owner. -/
  | seedsPush : Primitive types (types.seedOps.seeds.push)
  /-- Destroy owned seeds and their literal buffers. -/
  | seedsDrop : Primitive types (types.seedOps.seeds.drop)
  /-- Create the borrowed seed-view accumulator. -/
  | refsEmpty : Primitive types (emptyCall (Unwind := types.Unwind) (Terminal := types.Terminal)
    types.seedOps.refs.empty)
  /-- Append a captured borrowed seed view. -/
  | refsPush : Primitive types (types.seedOps.refs.push)
  /-- Destroy the view accumulator while retaining its referents. -/
  | refsDrop : Primitive types (types.seedOps.refs.drop)
  /-- Run the selected AccountInfo literal constructor command. -/
  | literalWork : Primitive types (types.infoLiteral.work)
  /-- Transfer the completed literal elements into their vector. -/
  | literalFinish : Primitive types (types.infoLiteral.finish)
  /-- Retire literal-construction storage after cleanup. -/
  | literalRetire : Primitive types (types.infoLiteral.retire)
  /-- Clone one actual AccountInfo Rc field. -/
  | rcClone : Primitive types (types.rc.cloneRc)
  /-- Destroy one actual AccountInfo Rc field. -/
  | rcDrop : Primitive types (types.rc.dropRc)
  /-- Call the raw PDA syscall while source references are retained. -/
  | pda : Primitive types (types.pdaSyscall)
  /-- Run the actual panic dependency at a selected source failure. -/
  | raise : Primitive types (types.raise)
  /-- Clear the selected authority metadata signer flag. -/
  | writeMeta : Primitive types (writeMetaCall types)

/-- These operations run while the collected Ref vector is separately owned.
Its destructor is excluded because it consumes that vector. -/
inductive ResolverPrimitive (types : Types) :
    {Args Value : Type} →
      Callback.Run (World types.Extra) Args Value types.Unwind types.Terminal → Prop
  /-- Allocate an owned literal seed buffer. -/
  | literalBytes : ResolverPrimitive types (types.seedOps.bytes.fromList)
  /-- Create the owned seed accumulator. -/
  | seedsEmpty : ResolverPrimitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.seedOps.seeds.empty)
  /-- Append an unpacked seed and transfer its literal owner. -/
  | seedsPush : ResolverPrimitive types (types.seedOps.seeds.push)
  /-- Destroy owned seeds and their literal buffers. -/
  | seedsDrop : ResolverPrimitive types (types.seedOps.seeds.drop)
  /-- Create the borrowed seed-view accumulator. -/
  | refsEmpty : ResolverPrimitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.seedOps.refs.empty)
  /-- Append a captured borrowed seed view. -/
  | refsPush : ResolverPrimitive types (types.seedOps.refs.push)
  /-- Destroy the view accumulator while retaining its referents. -/
  | refsDrop : ResolverPrimitive types (types.seedOps.refs.drop)
  /-- Call the raw PDA syscall while source references are retained. -/
  | pda : ResolverPrimitive types (types.pdaSyscall)
  /-- Run the actual panic dependency at a selected source failure. -/
  | raise : ResolverPrimitive types (types.raise)

/-- Presence of the selected typed data cell, with no scalar or length bound. -/
def DataReady (state : AccountInfo.State) (cell : Borrow.Handle) : Prop :=
  ∃ bytes policy, state.lookupCell cell = some ⟨.data bytes, policy⟩

/-- The state returned by a primitive retains protocol validity and the typed data
cells needed for subsequent checked acquisitions. Values and lengths of
unborrowed data may change; live shared data has the separate guard frame. -/
def DataFrame (before after : AccountInfo.State) : Prop :=
  after.Valid ∧ ∀ cell, DataReady before cell → DataReady after cell

/-- Only ordinary returns must support a subsequent typed acquisition.
Unwind and terminal paths introduce no new borrow. -/
def DataOutcome {Extra Value Unwind Terminal : Type} (before : World Extra) :
    Outcome (World Extra) Value Unwind Terminal → Prop
  | .returned _ after => DataFrame before.1 after.1
  | .unwound _ _ | .terminated _ => True

/-- Pointwise input admission does not wait for a later borrow or full helper
result: a type-destroying primitive exit is rejected at that primitive. -/
def DataPreserves {Extra Args Value Unwind Terminal : Type}
    (call : Callback.Run (World Extra) Args Value Unwind Terminal) : Prop :=
  ∀ before args, before.1.Valid → ∀ outcome, call before args outcome → DataOutcome before outcome

/-- Existing input frames imply this smaller no-bounds obligation. -/
theorem DataPreserves.of_input {Extra Args Value Unwind Terminal : Type} {wordBits : Nat}
    {call : Callback.Run (World Extra) Args Value Unwind Terminal}
    (law : InputPreserves wordBits call) : DataPreserves call := by
  intro before args valid outcome called
  have frame := law before args valid outcome called
  cases outcome with
  | terminated _ | unwound _ _ => trivial
  | returned _ after =>
    refine ⟨frame.valid, ?_⟩
    rintro cell ⟨bytes, policy, present⟩
    obtain ⟨⟨nextValue, nextPolicy⟩, found, _, kind⟩ := frame.cells cell ⟨.data bytes, policy⟩
      present
    cases nextValue with
    | lamports balance => exact False.elim kind
    | data nextBytes => exact ⟨nextBytes, nextPolicy, found⟩

/-- An actual admitted return leaves the next selected checked acquisition
available. This uses neither a complete helper exit nor an initial width law. -/
theorem DataPreserves.borrow_after {types : Types} {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (law : DataPreserves call) {before after : World types.Extra} {args : Args}
    {value : Value} {info : AccountInfo.Value} (valid : before.1.Valid)
    (typed : DataReady before.1 info.data) (called : call before args (.returned value after)) :
    ∃ result final, borrow types.raise true info after (.returned result final) := by
  have next := (law before args valid _ called).2 info.data typed
  cases acquired : AccountInfo.tryBorrow .shared info.data after.1 with
  | mk result during =>
    cases result with
    | error failure =>
      refine ⟨.error .AccountBorrowFailed, (during, after.2), ?_⟩
      simp only [borrow, fromStep, Onchain.borrowData, acquired, ↓reduceIte]
    | ok guard =>
      obtain ⟨bytes, current⟩ := AccountInfo.GuardCallback.data_current next acquired
      refine ⟨.ok ⟨guard, bytes.length⟩, (during, after.2), ?_⟩
      simp only [borrow, fromStep, Onchain.borrowData, acquired, current]

/-- Only the provider operations actually used in collection are admitted.
Each internal exit is constrained before another iterator read or callback;
no complete Trace or Token result appears in these primitive premises. -/
structure CollectionReady (types : Types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal) : Prop where
  /-- Preserve outer live data guards through internal work, finish and failed-collection
  retirement. -/
  frames : CollectionFrames protocol
  /-- Retain selected typed inputs before the next callback acquisition. -/
  internalData : ∀ index acquired,
    DataPreserves (fun state (_ : Unit) => protocol.internal index acquired state)
  /-- Retain typed inputs after successful collection for a later extra entry. -/
  finishData : DataPreserves protocol.finish
  /-- Guard-store updates leave the auxiliary iterator observation unchanged. -/
  inputOnAux : CurrentOnAux types.infos.current
  /-- Internal finite exits retain the current source iterator vector. -/
  internalInput : ∀ index acquired,
    Retains types.infos.current (fun state (_ : Unit) => protocol.internal index acquired state)
  /-- Each actual finite cleanup site passes the local order check before
  any complete collection trace or destructor result is assumed. -/
  cleanup : ∀ resource length entry,
    AllocatedCollect.CleanupReady protocol (infoIterator types resource length)
      (AllocatedCollect.borrowElement types.raise) entry

/-- Provider admission is independent of completed SDK behavior. It protects
actual data leases, later typed borrows and the separately owned collected-Ref
ledger. It assumes neither primitive termination nor constructor success, and
does not replace source/resource representation obligations. -/
structure Admitted (types : Types) (deps : Dependencies types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal) : Prop where
  /-- Each selected primitive preserves held guards and next-borrow inputs. -/
  primitive : ∀ {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal},
    Primitive types call → Preserves call ∧ DataPreserves call
  /-- The Ref-vector destructor may retire its own elements while retaining outer guards. -/
  guardDrop : PreservesExcept (ownedGuards types.guards) types.guards.drop
  /-- A normal Ref-vector drop retains typed inputs for subsequent source borrows. -/
  guardDropData : DataPreserves types.guards.drop
  /-- Seed-resolution primitives retain the separately owned Ref-vector ledger. -/
  resolver : ∀ {Args Value : Type}
    {call : Callback.Run (World types.Extra) Args Value types.Unwind types.Terminal},
    ResolverPrimitive types call → Retains types.guards.current call
  /-- Actual collector exits follow this same selected protocol. -/
  conforms : deps.collect.Conforms protocol
  /-- Successful protocol transfer exposes the actual ordered Ref-vector contents. -/
  collected : AllocatedCollect.ResourceLaws protocol types.guards
  /-- Use this protocol for all iterator, guard, input and cleanup-site continuations. -/
  collection : CollectionReady types protocol
  /-- Status zero must initialize the address at an actual source syscall
  request, before the local decoder reads that output. -/
  pdaReady : PdaAdmission.Ready types
  /-- The two source literals retain actual work/evaluation/completion and
  cleanup exits at their local count and permutation checks. -/
  literalReady : LiteralAdmission.Ready types

/-- Every actual primitive exit has its immediate held-data read and checked
release continuation. On unwind the read is skipped and the actual unwind
state is released; termination is forwarded without a fabricated state. -/
theorem Admitted.read_cleanup {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {Args Value : Type}
    {call : Callback.Run (World types.Extra) Args Value types.Unwind types.Terminal}
    (selected : Primitive types call) {before : World types.Extra} {args : Args}
    {reference : DataRef} {bytes : Bytes} (valid : before.1.Valid)
    (read : reference.read before = some bytes)
    {pending : Outcome (World types.Extra) Value types.Unwind types.Terminal}
    (called : call before args pending) :
    ∃ observed final,
      bind (perform fun state => call state args) (fun _ => inspect reference.read) before observed
        ∧
      AccountInfo.GuardCallback.releaseOutcome reference.guard observed = some final ∧
      scope types.doubleUnwind [reference.drop]
        (bind (perform fun state => call state args) (fun _ => inspect reference.read)) before
          final :=
  perform_read_scope_retains types.doubleUnwind (ready.primitive selected).1 valid read called

/-- Selected data typing makes the next checked borrow available after each
actual primitive return. No width or unrelated AccountInfo field is needed. -/
theorem Admitted.borrow_after {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {Args Value : Type}
    {call : Callback.Run (World types.Extra) Args Value types.Unwind types.Terminal}
    (selected : Primitive types call) {before after : World types.Extra} {args : Args}
    {value : Value} {info : AccountInfo.Value} (valid : before.1.Valid)
    (typed : DataReady before.1 info.data) (called : call before args (.returned value after)) :
    ∃ result final, borrow types.raise true info after (.returned result final) :=
  (ready.primitive selected).2.borrow_after valid typed called

/-- Successful destruction of the collected inner references precedes the
next extra-entry iteration. Its actual return preserves the typed source
input needed by that next checked borrow. -/
theorem Admitted.borrow_after_guard_drop {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {before after : World types.Extra}
    {resource : types.GuardResource} {info : AccountInfo.Value} (valid : before.1.Valid)
    (typed : DataReady before.1 info.data)
    (called : types.guards.drop before resource (.returned () after)) :
    ∃ result final, borrow types.raise true info after (.returned result final) :=
  ready.guardDropData.borrow_after valid typed called

/-- The inner Ref-vector drop may release its actual elements. Every finite
exit still admits the enclosing source the checked cleanup of Ref when that Ref
was not an owned vector element. -/
theorem Admitted.guard_drop_cleanup {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {before : World types.Extra}
    {resource : types.GuardResource} {entries : List AllocatedCollect.Element}
    {reference : DataRef} {bytes : Bytes} (valid : before.1.Valid)
    (read : reference.read before = some bytes)
    (current : types.guards.current before resource = some entries)
    (outside : reference.guard ∉ entries.map (fun entry => entry.2.guard))
    {pending : Outcome (World types.Extra) Unit types.Unwind types.Terminal}
    (called : types.guards.drop before resource pending) :
    ∃ final,
      AccountInfo.GuardCallback.releaseOutcome reference.guard pending = some final ∧
      Owned.cleanup types.doubleUnwind [reference.drop] pending final := by
  obtain ⟨slot, _, live, _⟩ := read_live read
  have frame := guardDrop_outer ready.guardDrop valid live current outside called
  obtain ⟨final, released⟩ := frame.release_exists live
  exact ⟨final, released, (data_cleanup_iff types.doubleUnwind reference pending final).mpr
    released⟩

/-- Each normal internal collector exit keeps the captured iterator element
and admits the actual source key-before-borrow callback on that element. -/
theorem CollectionReady.internal_continue {types : Types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal} (ready : CollectionReady types protocol)
    {before after : World types.Extra} {resource : types.InfoResource}
    {length index step : Nat} {acquired : List AllocatedCollect.Element}
    {info : AccountInfo.Value} (valid : before.1.Valid)
    (typed : DataReady before.1 info.data)
    (read : (infoIterator types resource length).elementAt before index = some info)
    (called : protocol.internal step acquired before (.returned () after)) :
    (infoIterator types resource length).elementAt after index = some info ∧
      ∃ result final, AllocatedCollect.borrowElement types.raise after info
        (.returned result final) := by
  refine ⟨collection_internal_iterator (ready.internalInput step acquired) read called, ?_⟩
  obtain ⟨result, final, borrowed⟩ :=
    (ready.internalData step acquired).borrow_after valid typed (args := ()) called
  cases result with
  | ok reference =>
    exact ⟨.ok (info.key, reference), final,
      AllocatedCollect.borrowElement_ok _ _ _ _ _ borrowed⟩
  | error failure =>
    exact ⟨.error failure, final, AllocatedCollect.borrowElement_error _ _ _ _ _ borrowed⟩

/-- A successful source acquisition cannot erase the next captured iterator
element through its account guard-store update. -/
theorem CollectionReady.borrow_iterator {types : Types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal} (ready : CollectionReady types protocol)
    {before after : World types.Extra} {resource : types.InfoResource}
    {length index : Nat} {info argument : AccountInfo.Value} {element : AllocatedCollect.Element}
    (read : (infoIterator types resource length).elementAt before index = some info)
    (called : AllocatedCollect.borrowElement types.raise before argument
      (.returned (.ok element) after)) :
    (infoIterator types resource length).elementAt after index = some info :=
  collection_borrow_iterator ready.inputOnAux read called

/-- After a successful collection transfer, the later source borrow can use
the current typed account input. This consumes only the actual
return of that primitive and does not assert that collection or the resolver terminates. -/
theorem CollectionReady.finish_borrow {types : Types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal} (ready : CollectionReady types protocol)
    {before after : World types.Extra} {acquired : List AllocatedCollect.Element}
    {resource : types.GuardResource} {info : AccountInfo.Value} (valid : before.1.Valid)
    (typed : DataReady before.1 info.data)
    (called : protocol.finish before acquired (.returned resource after)) :
    ∃ result final, borrow types.raise true info after (.returned result final) :=
  ready.finishData.borrow_after valid typed called

/-- Every actual cleanup exit extends the same admitted collector prefix.
The order check cannot discard that exit; the supplied retirement and
double-unwind policy still determine whether such a downstream exit exists. -/
theorem CollectionReady.cleanup_continue {types : Types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal} (ready : CollectionReady types protocol)
    {resource : types.InfoResource} {length : Nat} {entry after : World types.Extra}
    {acquired : List AllocatedCollect.Element} {calls : List Nat}
    {pending final : Outcome (World types.Extra) (Except Error types.GuardResource)
      types.Unwind types.Terminal}
    (site : AllocatedCollect.CleanupSite protocol (infoIterator types resource length)
      (AllocatedCollect.borrowElement types.raise) entry acquired after pending calls)
    (cleaned : Owned.cleanup protocol.double (protocol.partialDrops after acquired) pending final) :
    AllocatedCollect.Trace protocol (infoIterator types resource length)
      (AllocatedCollect.borrowElement types.raise) 0 [] entry calls final :=
  site.extend (ready.cleanup resource length entry) cleaned

/-- The admitted protocol follows each actual collection trace. Every finite
collection exit preserves the held data of the caller for its local read/release
continuation, including error and unwind cleanup. -/
theorem Admitted.collection_cleanup {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {resource : types.InfoResource}
    {before : World types.Extra} {reference : DataRef} {bytes : Bytes}
    (valid : before.1.Valid) (read : reference.read before = some bytes)
    {pending : Outcome (World types.Extra) (Except Error types.GuardResource)
      types.Unwind types.Terminal}
    (called : collectRefs types deps resource before pending) :
    ∃ final,
      AccountInfo.GuardCallback.releaseOutcome reference.guard pending = some final ∧
      scope types.doubleUnwind [reference.drop]
        (collectRefs types deps resource) before final := by
  obtain ⟨slot, _, live, _⟩ := read_live read
  exact data_scope_retains types.doubleUnwind
    (collectRefs_frames ready.conforms ready.collection.frames (ready.primitive .raise).1 resource
      before () valid reference.guard slot live (by simp)) live called

/-- An actual resolver return preserves both the current Ref vector and every
live data read, so the next source observation is available before vector drop. -/
theorem Admitted.resolver_read {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {Args Value : Type}
    {call : Callback.Run (World types.Extra) Args Value types.Unwind types.Terminal}
    (ordinary : Primitive types call) (selected : ResolverPrimitive types call)
    {before after : World types.Extra} {args : Args} {value : Value}
    {resource : types.GuardResource} {values : Hook.Observations}
    (valid : before.1.Valid) (read : guardObservations types resource before = some values)
    (called : call before args (.returned value after)) :
    guardObservations types resource after = some values :=
  guardObservations_returned (ready.primitive ordinary).1 (ready.resolver selected) valid read
    called

/-- An actual resolver unwind retains the same owned Ref vector until its
source cleanup starts, together with the exact current bytes of every element. -/
theorem Admitted.resolver_unwind {types : Types} {deps : Dependencies types}
    {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal}
    (ready : Admitted types deps protocol) {Args Value : Type}
    {call : Callback.Run (World types.Extra) Args Value types.Unwind types.Terminal}
    (ordinary : Primitive types call) (selected : ResolverPrimitive types call)
    {before after : World types.Extra} {args : Args} {reason : types.Unwind}
    {resource : types.GuardResource} {values : Hook.Observations}
    (valid : before.1.Valid) (read : guardObservations types resource before = some values)
    (called : call before args (.unwound reason after)) :
    guardObservations types resource after = some values :=
  guardObservations_unwound (ready.primitive ordinary).1 (ready.resolver selected) valid read called

end Solanalib.Specs.Core.Token.OnchainAllocated.Admission
