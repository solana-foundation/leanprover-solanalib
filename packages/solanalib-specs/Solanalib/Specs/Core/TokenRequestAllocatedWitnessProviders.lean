/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedTypes
public import Solanalib.Specs.Core.TokenRequestOnchainContract
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocusFacts
public import Solanalib.Specs.Core.OwnedArray

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

/-- Cleanup observations used by controls that distinguish partial-array
element drops, instruction-field drops and remaining argument drops. -/
inductive CleanupEvent where
  /-- An AccountInfo field drop records the current instruction-vector liveness. -/
  | accountDrop (field : AccountInfoRc.Field) (cell : Borrow.Handle)
      (instructionBytesLive instructionMetasLive : Bool)
  /-- The temporary-storage retirement operation of the literal provider has returned. -/
  | literalRetire
  /-- The retained instruction metadata allocation has been retired. -/
  | metadataDrop
  /-- The retained instruction byte allocation has been retired. -/
  | byteDrop
  deriving DecidableEq, Repr

/-- Owned-vector and Rc state for finite witnesses. In the positive sample,
one owner of each cell belongs outside the call, allowing the four moved
arguments and all temporary aliases to retire while the account cells stay live. -/
structure Extra where
  /-- Current instruction and padding byte-vector allocations. -/
  bytes : Owned.VectorState UInt8 := []
  /-- Current instruction account-metadata allocations. -/
  metas : Owned.VectorState Solanalib.Runtime.CpiMeta := []
  /-- Current vectors of owned account-info entries. -/
  infos : Owned.VectorState AccountInfo.Value := []
  /-- Empty-only collection slots for the unused hook-guard path. -/
  guards : Owned.VectorState Unit := []
  /-- Current owned extension-discriminator sequences. -/
  discriminators : Owned.VectorState Bytes := []
  /-- Empty-only seed-vector slots, unused by the bare-mint sample. -/
  seeds : Owned.VectorState Unit := []
  /-- Empty-only seed-reference slots, unused by the bare-mint sample. -/
  seedRefs : Owned.VectorState Unit := []
  /-- Every actual selected Rc operation in execution order. -/
  rcEvents : List AccountInfoRc.Event := []
  /-- Optional observations made by the distinguishing cleanup controls. -/
  cleanupEvents : List CleanupEvent := []
  /-- Aggregate strong owners of represented lamports cells, including outside owners. -/
  lamportsOwners : Nat := 5
  /-- Aggregate strong owners of represented data cells, including outside owners. -/
  dataOwners : Nat := 5
  /-- An observable state effect of the explicit CPI callback of the sample. -/
  invocations : Nat := 0
  deriving DecidableEq, Repr

/-- Actual account borrows paired with owned-vector ledgers and Rc state. -/
abbrev State := World Extra

/-- A lawful focus on the byte ledger, preserving the rest of the world. -/
def bytesFocus : Owned.Focus State (Owned.VectorState UInt8) where
  get := fun state => state.2.bytes
  set := fun state values => (state.1, { state.2 with bytes := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful focus on the metadata ledger, preserving all other resources. -/
def metasFocus : Owned.Focus State (Owned.VectorState Solanalib.Runtime.CpiMeta) where
  get := fun state => state.2.metas
  set := fun state values => (state.1, { state.2 with metas := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful focus on current account-info vector contents. -/
def infosFocus : Owned.Focus State (Owned.VectorState AccountInfo.Value) where
  get := fun state => state.2.infos
  set := fun state values => (state.1, { state.2 with infos := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful focus on the empty-only guard collection ledger of the sample. -/
def guardsFocus : Owned.Focus State (Owned.VectorState Unit) where
  get := fun state => state.2.guards
  set := fun state values => (state.1, { state.2 with guards := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful focus on owned extension-discriminator vectors. -/
def discriminatorsFocus : Owned.Focus State (Owned.VectorState Bytes) where
  get := fun state => state.2.discriminators
  set := fun state values => (state.1, { state.2 with discriminators := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful focus on the empty-only seed-vector ledger of the sample. -/
def seedsFocus : Owned.Focus State (Owned.VectorState Unit) where
  get := fun state => state.2.seeds
  set := fun state values => (state.1, { state.2 with seeds := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful focus on the empty-only seed-reference ledger of the sample. -/
def seedRefsFocus : Owned.Focus State (Owned.VectorState Unit) where
  get := fun state => state.2.seedRefs
  set := fun state values => (state.1, { state.2 with seedRefs := values })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Shared vector semantics instantiated on the actual byte ledger. -/
def bytesOps : Owned.VectorOps State UInt8 Nat Nat Nat :=
  Owned.vectorReference.focus bytesFocus

/-- Shared vector semantics instantiated on the actual metadata ledger. -/
def metasOps : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Nat Nat :=
  Owned.vectorReference.focus metasFocus

/-- Account-info value storage; the ownership-aware provider adds Rc calls
to slice extension and current-element destruction. -/
def infoValuesOps : Owned.VectorOps State AccountInfo.Value Nat Nat Nat :=
  Owned.vectorReference.focus infosFocus

/-- An explicit partial vector provider for branches unused by this sample.
Only empty sequences have finite construction/update executions. Every
resource still has an actual live ledger slot and is retired by drop. This
avoids storing arbitrary State-dependent views recursively inside State;
it supplies no execution for nonempty guard or seed collections. -/
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

/-- Select the represented strong-owner count for an AccountInfo Rc field. -/
def ownerCount (extra : Extra) : AccountInfoRc.Field → Nat
  | .lamports => extra.lamportsOwners
  | .data => extra.dataOwners

/-- The two concrete account cells represented by this finite Rc sample. -/
def expectedCell : AccountInfoRc.Field → Borrow.Handle
  | .lamports => ⟨0⟩
  | .data => ⟨1⟩

/-- The concrete finite sample interprets only represented live Rc owners.
This domain and its counter updates are mathematical witness choices, not
an Rc overflow, allocator or Rust body correctness assertion. -/
def rcReady (clone : Bool) (state : State) (field : AccountInfoRc.Field)
    (cell : Borrow.Handle) : Prop :=
  cell = expectedCell field ∧ 0 < ownerCount state.2 field ∧
    (if clone then ownerCount state.2 field < 2^64 - 1 else True)

/-- Update the selected owner count and append the actual Rc event, leaving
all account bytes, leases and vector contents unchanged. -/
def rcAfter (clone : Bool) (state : State) (field : AccountInfoRc.Field)
    (cell : Borrow.Handle) : State :=
  let count := ownerCount state.2 field
  let updated := if clone then count + 1 else count - 1
  let event := if clone then AccountInfoRc.Event.clone field cell else .drop field cell
  let extra := { state.2 with rcEvents := state.2.rcEvents ++ [event] }
  (state.1, match field with
    | .lamports => { extra with lamportsOwners := updated }
    | .data => { extra with dataOwners := updated })

/-- Finite Rc clone/drop interpretations on represented live owners; each
accepted call performs its explicit counter and trace mutation. -/
def rcOps : AccountInfoRc.Ops State Nat where
  cloneRc := fun state (field, cell) outcome =>
    rcReady true state field cell ∧ outcome = .returned () (rcAfter true state field cell)
  dropRc := fun state (field, cell) outcome =>
    rcReady false state field cell ∧ outcome = .returned () (rcAfter false state field cell)

/-- Element cloning executes both selected Rc operations for every entry in
order. The value of the clone retains the same cells, as cloneCall specifies. -/
def cloneInfos : List AccountInfo.Value → Callback.Run State Unit Unit Nat Nat
  | [] => fun state _ outcome => outcome = .returned () state
  | info :: rest =>
    Callback.bind
      (fun state (_ : Unit) => AccountInfoRc.lift (AccountInfoRc.cloneCall rcOps) state info)
      (fun _ state outcome => cloneInfos rest state () outcome)

/-- The destructor traverses the actual current element sequence in order. -/
def dropInfos : List AccountInfo.Value → Callback.Run State Unit Unit Nat Nat
  | [] => fun state _ outcome => outcome = .returned () state
  | info :: rest =>
    Callback.bind
      (fun state (_ : Unit) => AccountInfoRc.lift (AccountInfoRc.dropCall rcOps) state info)
      (fun _ state outcome => dropInfos rest state () outcome)

/-- Already cloned array elements move into fromList without extra cloning.
Extend clones its supplied slice; drop destroys every current element before
retiring the actual vector slot. The byte and metadata ledgers are untouched. -/
def infosOps : Owned.VectorOps State AccountInfo.Value Nat Nat Nat := { infoValuesOps with
  extend := fun before (resource, values) outcome =>
    Callback.bind (cloneInfos values)
      (fun _ state result => infoValuesOps.extend state (resource, values) result) before () outcome
  drop := fun before resource outcome =>
    ∃ values, infoValuesOps.current before resource = some values ∧
      Callback.bind (dropInfos values)
        (fun _ state result => infoValuesOps.drop state resource result) before () outcome }

/-- One explicit literal-construction schedule evaluates every indexed
expression before transferring its owned result to the vector. The array
engine owns prefix cleanup on unwind; storage retirement is empty in this
sample because no separate temporary allocation is represented. -/
def infoLiteral : Owned.Array.Provider State AccountInfo.Value Nat Nat Nat where
  work := fun before (count, values) outcome =>
    if values.length < count then outcome = .returned .evaluate before
    else values.length = count ∧ outcome = .returned .finish before
  finish := infosOps.fromList
  cleanupOrder := fun _ values => List.finRange values.length
  drop := AccountInfoRc.lift (AccountInfoRc.dropCall rcOps)
  retire := fun before _ outcome => outcome = .returned () before
  double := fun _ original later terminal => terminal = original + later

/-- Distinct mathematical unwind reasons for the source panic dependency. -/
def panicCode : Onchain.Panic → Nat
  | .borrowFailed => 100
  | .multisigSignerRange => 101
  | .noViableProgramAddress => 102

/-- The unused collection providers are deliberately partial, and the unused
PDA syscall has no finite exit. The witness
below exercises ordinary initialized-mint preparation, every constructor
allocation and clone, the real CPI parameter, and all resulting cleanup.
The 64-bit width and enum reservation 128 are explicit sample parameters,
not measured Rust layout or allocator assertions. -/
def sampleTypes : Types where
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
  wordBits := 64
  tokenEnumSize := 128
  bytes := bytesOps
  metas := metasOps
  infos := infosOps
  infoLiteral := infoLiteral
  guards := emptyOnlyOps guardsFocus
  discriminators := Owned.vectorReference.focus discriminatorsFocus
  paddingBytes := bytesOps
  seedOps := {
    bytes := bytesOps
    seeds := emptyOnlyOps seedsFocus
    refs := emptyOnlyOps seedRefsFocus }
  rc := rcOps
  pdaSyscall := fun _ _ _ => False
  ownerAt := fun _ _ => .zero
  raise := fun state reason outcome => outcome = .unwound (panicCode reason) state
  doubleUnwind := fun _ original later terminal => terminal = original + later
  writeMeta := fun before resource index item after =>
    ∃ values, metasOps.current before resource = some values ∧
      after = metasFocus.set before (before.2.metas.set resource (some (values.set index item)))

/-- An initialized bare mint, empty vector ledgers and four moved argument
owners in addition to one owner retained outside this call. -/
def initialState : State := (Onchain.witnessState, {})

/-- Byte and metadata operations inherit all primitive vector laws from the
shared ledger; this does not assert a machine representation or allocator. -/
theorem sample_bytes_laws : sampleTypes.bytes.Laws :=
  Owned.VectorOps.focus_laws Owned.vectorReference_laws bytesFocus

theorem sample_metas_laws : sampleTypes.metas.Laws :=
  Owned.VectorOps.focus_laws Owned.vectorReference_laws metasFocus

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
