/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TransferHookResolutionRun
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.TransferHookResolution.Sample

open Token (Error Bytes)
open Token.AllocatedControl

/-- A finite interpretation used for closed witnesses. Ordinary vector slots,
actual shared guards and Rc multiplicities are separate observations. -/
structure Extra where
  bytes : Owned.VectorState UInt8 := []
  metas : Owned.VectorState Solanalib.Runtime.CpiMeta := []
  infos : Owned.VectorState AccountInfo.Value := []
  guards : Owned.VectorState GuardElement := []
  discriminators : Owned.VectorState Bytes := []
  seeds : Owned.VectorState (Token.AllocatedSeeds.Seed Nat) := []
  seedRefs : Owned.VectorState Unit := []
  rcOwners : List Nat := []
  rcEvents : List AccountInfoRc.Event := []
  pdaCalls : List (List Bytes × Solanalib.Runtime.Pubkey) := []
  deriving DecidableEq, Repr

abbrev State := World Extra

/-- Focus only the bytes ledger, preserving every other observation. -/
def bytesFocus : Owned.Focus State (Owned.VectorState UInt8) where
  get := fun state => state.2.bytes
  set := fun state values => (state.1, { state.2 with bytes := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus only the metas ledger, preserving every other observation. -/
def metasFocus : Owned.Focus State (Owned.VectorState Solanalib.Runtime.CpiMeta) where
  get := fun state => state.2.metas
  set := fun state values => (state.1, { state.2 with metas := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus only the infos ledger, preserving every other observation. -/
def infosFocus : Owned.Focus State (Owned.VectorState AccountInfo.Value) where
  get := fun state => state.2.infos
  set := fun state values => (state.1, { state.2 with infos := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus only the guards ledger, preserving every other observation. -/
def guardsFocus : Owned.Focus State (Owned.VectorState GuardElement) where
  get := fun state => state.2.guards
  set := fun state values => (state.1, { state.2 with guards := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus only the discriminators ledger, preserving every other observation. -/
def discriminatorsFocus : Owned.Focus State (Owned.VectorState Bytes) where
  get := fun state => state.2.discriminators
  set := fun state values => (state.1, { state.2 with discriminators := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus only the seeds ledger, preserving every other observation. -/
def seedsFocus : Owned.Focus State (Owned.VectorState (Token.AllocatedSeeds.Seed Nat)) where
  get := fun state => state.2.seeds
  set := fun state values => (state.1, { state.2 with seeds := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus only the seedRefs ledger, preserving every other observation. -/
def seedRefsFocus : Owned.Focus State (Owned.VectorState Unit) where
  get := fun state => state.2.seedRefs
  set := fun state values => (state.1, { state.2 with seedRefs := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def bytesOps : Owned.VectorOps State UInt8 Nat Nat Nat :=
  Owned.vectorReference.focus bytesFocus

def metasOps : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Nat Nat :=
  Owned.vectorReference.focus metasFocus

def infoValuesOps : Owned.VectorOps State AccountInfo.Value Nat Nat Nat :=
  Owned.vectorReference.focus infosFocus

def guardValuesOps : Owned.VectorOps State GuardElement Nat Nat Nat :=
  Owned.vectorReference.focus guardsFocus

/-- This finite sample deliberately admits only empty borrowed-seed storage.
It supports fixed keys, key-data resolution, errors before the first seed-view
push and empty-seed PDA calls. General retained seed views remain part of the
full family and are not claimed to execute under this restricted sample. -/
def emptyOnlyOps {Element : Type} (part : Owned.Focus State (Owned.VectorState Unit)) :
    Owned.VectorOps State Element Nat Nat Nat :=
  let units : Owned.VectorOps State Unit Nat Nat Nat := Owned.vectorReference.focus part
  { current := fun state resource => (units.current state resource).map (fun _ => [])
    empty := units.empty
    withCapacity := units.withCapacity
    fromList := fun state values outcome => values = [] ∧ units.withCapacity state 0 outcome
    push := fun _ _ _ => False
    extend := fun state (resource, values) outcome =>
      values = [] ∧ units.Live state resource ∧ outcome = .returned () state
    drop := units.drop }

/-- Actual owner availability and selected signed-width overflow bound. -/
def rcReady (clone : Bool) (state : State) (cell : Borrow.Handle) : Prop :=
  cell.cell < state.2.rcOwners.length ∧ 0 < state.2.rcOwners[cell.cell]! ∧
    (if clone then state.2.rcOwners[cell.cell]! < 2^64 - 1 else True)

/-- A successful Rc call changes exactly one multiplicity and records the
selected field/alias; it does not copy, replace or release the borrow cell. -/
def rcAfter (clone : Bool) (state : State) (field : AccountInfoRc.Field)
    (cell : Borrow.Handle) : State :=
  let count := state.2.rcOwners[cell.cell]!
  let updated := if clone then count + 1 else count - 1
  let event := if clone then AccountInfoRc.Event.clone field cell else .drop field cell
  (state.1, { state.2 with
    rcOwners := state.2.rcOwners.set cell.cell updated
    rcEvents := state.2.rcEvents ++ [event] })

def rcOps : AccountInfoRc.Ops State Nat where
  cloneRc := fun state (field, cell) outcome =>
    rcReady true state cell ∧ outcome = .returned () (rcAfter true state field cell)
  dropRc := fun state (field, cell) outcome =>
    rcReady false state cell ∧ outcome = .returned () (rcAfter false state field cell)

def cloneInfos : List AccountInfo.Value → Callback.Run State Unit Unit Nat Nat
  | [] => fun state _ outcome => outcome = .returned () state
  | info :: rest =>
    Callback.bind
      (fun state (_ : Unit) => AccountInfoRc.lift (AccountInfoRc.cloneCall rcOps) state info)
      (fun _ state outcome => cloneInfos rest state () outcome)

def dropInfos : List AccountInfo.Value → Callback.Run State Unit Unit Nat Nat
  | [] => fun state _ outcome => outcome = .returned () state
  | info :: rest =>
    Callback.bind
      (fun state (_ : Unit) => AccountInfoRc.lift (AccountInfoRc.dropCall rcOps) state info)
      (fun _ state outcome => dropInfos rest state () outcome)

/-- The sample slice extension clones every supplied owner before appending;
its destructor destroys every stored occurrence before retiring the slot.
This particular nonfailing schedule is not asserted of all std allocators. -/
def infosOps : Owned.VectorOps State AccountInfo.Value Nat Nat Nat := { infoValuesOps with
  extend := fun before (resource, values) outcome =>
    Callback.bind (cloneInfos values)
      (fun _ state result => infoValuesOps.extend state (resource, values) result) before () outcome
  drop := fun before resource outcome =>
    ∃ values, infoValuesOps.current before resource = some values ∧
      Callback.bind (dropInfos values)
        (fun _ state result => infoValuesOps.drop state resource result) before () outcome }

/-- A concrete no-failure constructor schedule. The array trace supplies the
source expressions and proves prefix ownership on every allowed exit. -/
def literalOps : LiteralOps State Nat Nat Nat where
  work := fun before (count, values) outcome =>
    if values.length < count then outcome = .returned .evaluate before
    else values.length = count ∧ outcome = .returned .finish before
  finish := infosOps.fromList
  cleanupOrder := fun _ values => List.finRange values.length
  retire := fun before _ outcome => outcome = .returned () before

/-- Unlike the seed sample, the collection sample supports every finite list
of actual shared Refs. Its own storage retirement never releases a Ref twice. -/
def collectionOps : CollectionOps Extra Nat Nat Nat where
  current := guardValuesOps.current
  internal := fun _ _ _ _ => False
  finish := guardValuesOps.fromList
  partialOrder := fun _ acquired => acquired
  retire := fun resource _ before outcome => match resource with
    | none => outcome = .returned () before
    | some identity => guardValuesOps.drop before identity outcome

/-- Scripted PDA replies retain exactly the actual call inputs and full
initialized output. They do not claim real curve/hash implementation behavior. -/
def pdaAfter (before : State) (request : Address.Syscall.PdaRequest) : State :=
  (before.1, { before.2 with
    pdaCalls := before.2.pdaCalls ++ [(request.seeds, request.programId)] })

def panicCode : Panic → Nat
  | .podSliceBounds requested capacity => 1000 + 100 * requested + capacity
  | .noViableProgramAddress => 102

def types (reply : Address.Operations.ZeroFindReply) : Types where
  Extra := Extra
  ByteResource := Nat
  MetaResource := Nat
  InfoResource := Nat
  GuardResource := Nat
  DiscResource := Nat
  SeedResource := Nat
  SeedRefResource := Nat
  Unwind := Nat
  Terminal := Nat
  bytes := bytesOps
  metas := metasOps
  infos := infosOps
  literal := literalOps
  collection := collectionOps
  discriminators := Owned.vectorReference.focus discriminatorsFocus
  seedOps := {
    bytes := bytesOps
    seeds := Owned.vectorReference.focus seedsFocus
    refs := emptyOnlyOps seedRefsFocus }
  rc := rcOps
  pdaSyscall := Callback.ofFunction fun before request => .returned reply (pdaAfter before request)
  raise := Callback.ofFunction fun before reason => .unwound (panicCode reason) before
  doubleUnwind := fun _ original later terminal => terminal = original + later

/-- All ordinary byte-vector laws hold at every scripted reply. -/
theorem bytes_laws (reply : Address.Operations.ZeroFindReply) : (types reply).bytes.Laws :=
  Owned.VectorOps.focus_laws Owned.vectorReference_laws bytesFocus

/-- All ordinary metadata-vector laws hold at every scripted reply. -/
theorem metas_laws (reply : Address.Operations.ZeroFindReply) : (types reply).metas.Laws :=
  Owned.VectorOps.focus_laws Owned.vectorReference_laws metasFocus

end Solanalib.Specs.Core.TransferHookResolution.Sample
