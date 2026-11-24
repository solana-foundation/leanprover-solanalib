/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Admission

open AllocatedGuard AllocatedControl

/-- The actual primitive catalogue with a computational call-site tag. The
tag determines its owned mutation footprint; the existing proposition-valued
catalogue continues to provide held-guard and input-typing admission. -/
inductive ResourcePrimitive (types : Types) : {Args Value Unwind : Type} →
    Callback.Run (World types.Extra) Args Value Unwind types.Terminal → Type
  | bytesEmpty : ResourcePrimitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.bytes.empty)
  | bytesCapacity : ResourcePrimitive types types.bytes.withCapacity
  | bytesPush : ResourcePrimitive types types.bytes.push
  | bytesExtend : ResourcePrimitive types types.bytes.extend
  | bytesDrop : ResourcePrimitive types types.bytes.drop
  | metasCapacity : ResourcePrimitive types types.metas.withCapacity
  | metasList : ResourcePrimitive types types.metas.fromList
  | metasPush : ResourcePrimitive types types.metas.push
  | metasExtend : ResourcePrimitive types types.metas.extend
  | metasDrop : ResourcePrimitive types types.metas.drop
  | infosPush : ResourcePrimitive types types.infos.push
  | infosExtend : ResourcePrimitive types types.infos.extend
  | infosDrop : ResourcePrimitive types types.infos.drop
  | discriminatorsEmpty : ResourcePrimitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.discriminators.empty)
  | discriminatorsPush : ResourcePrimitive types types.discriminators.push
  | discriminatorsDrop : ResourcePrimitive types types.discriminators.drop
  | paddingList : ResourcePrimitive types types.paddingBytes.fromList
  | paddingDrop : ResourcePrimitive types types.paddingBytes.drop
  | literalBytes : ResourcePrimitive types types.seedOps.bytes.fromList
  | seedsEmpty : ResourcePrimitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.seedOps.seeds.empty)
  | seedsPush : ResourcePrimitive types types.seedOps.seeds.push
  | seedsDrop : ResourcePrimitive types types.seedOps.seeds.drop
  | refsEmpty : ResourcePrimitive types (emptyCall (Unwind := types.Unwind) (Terminal :=
    types.Terminal) types.seedOps.refs.empty)
  | refsPush : ResourcePrimitive types types.seedOps.refs.push
  | refsDrop : ResourcePrimitive types types.seedOps.refs.drop
  | literalWork : ResourcePrimitive types types.infoLiteral.work
  | literalFinish : ResourcePrimitive types types.infoLiteral.finish
  | literalRetire : ResourcePrimitive types types.infoLiteral.retire
  | rcClone : ResourcePrimitive types types.rc.cloneRc
  | rcDrop : ResourcePrimitive types types.rc.dropRc
  | pda : ResourcePrimitive types types.pdaSyscall
  | raise : ResourcePrimitive types types.raise
  | writeMeta : ResourcePrimitive types (writeMetaCall types)

/-- Every resource tag names one of the existing actual source primitives. -/
theorem ResourcePrimitive.ordinary {types : Types} {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) : Primitive types call := by
  cases selected <;> constructor

/-- Logical owners whose current vectors are read or retained by the selected
ordinary preparation. The three byte roles share the identity type of the source;
the projections may denote different primitive constructor interpretations. -/
inductive ResourceRef (types : Types) where
  | bytes (resource : types.ByteResource)
  | padding (resource : types.ByteResource)
  | literal (resource : types.ByteResource)
  | metas (resource : types.MetaResource)
  | infos (resource : types.InfoResource)
  | seeds (resource : types.SeedResource)
  | refs (resource : types.SeedRefResource)

/-- A retained current observation, separate from source permission or a Rust
representation. Its contents are observed again in each actual callback state. -/
inductive Retained (types : Types) where
  | bytes (resource : types.ByteResource) (values : Bytes)
  | padding (resource : types.ByteResource) (values : Bytes)
  | literal (resource : types.ByteResource) (values : Bytes)
  | metas (resource : types.MetaResource) (values : List Solanalib.Runtime.CpiMeta)
  | infos (resource : types.InfoResource) (values : List AccountInfo.Value)
  | seeds (resource : types.SeedResource) (values : List (AllocatedSeeds.Seed types.ByteResource))
  | refs (resource : types.SeedRefResource)
      (values : List (AllocatedSeeds.BytesView (World types.Extra)))

def Retained.resource {types : Types} : Retained types → ResourceRef types
  | .bytes resource _ => .bytes resource
  | .padding resource _ => .padding resource
  | .literal resource _ => .literal resource
  | .metas resource _ => .metas resource
  | .infos resource _ => .infos resource
  | .seeds resource _ => .seeds resource
  | .refs resource _ => .refs resource

def Retained.Holds {types : Types} (state : World types.Extra) : Retained types → Prop
  | .bytes resource values => types.bytes.current state resource = some values
  | .padding resource values => types.paddingBytes.current state resource = some values
  | .literal resource values => types.seedOps.bytes.current state resource = some values
  | .metas resource values => types.metas.current state resource = some values
  | .infos resource values => types.infos.current state resource = some values
  | .seeds resource values => types.seedOps.seeds.current state resource = some values
  | .refs resource values => types.seedOps.refs.current state resource = some values

/-- Byte-owner identity is shared across instruction packing, zero padding
and seed literal construction. A provider may not bypass retention by choosing
another observation role for the same owned byte resource. -/
def ResourceRef.byteTarget {types : Types} (target : types.ByteResource) :
    ResourceRef types → Prop
  | .bytes resource | .padding resource | .literal resource => resource = target
  | _ => False

/-- A new byte identity is fresh for every byte-constructor role. Other
resource classes already have distinct typed ownership identities. -/
def ResourceRef.Fresh {types : Types} (before : World types.Extra) : ResourceRef types → Prop
  | .bytes resource | .padding resource | .literal resource =>
      types.bytes.current before resource = none ∧
      types.paddingBytes.current before resource = none ∧
      types.seedOps.bytes.current before resource = none
  | .metas resource => types.metas.current before resource = none
  | .infos resource => types.infos.current before resource = none
  | .seeds resource => types.seedOps.seeds.current before resource = none
  | .refs resource => types.seedOps.refs.current before resource = none

/-- The mutation target of the source, or an owner consumed by that actual exit.
Normal seed pushes retain the moved literal; an unwinding push may destroy it.
A seed-vector destructor may consume only literals in its current elements. -/
def Touches {types : Types} {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) (before : World types.Extra) (args : Args)
    (outcome : Outcome (World types.Extra) Value Unwind types.Terminal)
    (resource : ResourceRef types) : Prop :=
  match selected with
  | .bytesPush | .bytesExtend => resource.byteTarget args.1
  | .bytesDrop | .paddingDrop => resource.byteTarget args
  | .metasPush | .metasExtend => resource = .metas args.1
  | .metasDrop => resource = .metas args
  | .infosPush | .infosExtend => resource = .infos args.1
  | .infosDrop => resource = .infos args
  | .seedsPush =>
      resource = .seeds args.1 ∨
        match outcome, args.2 with
        | .unwound _ _, .literal literal => resource.byteTarget literal
        | _, _ => False
  | .seedsDrop =>
      resource = .seeds args ∨ ∃ values literal,
        types.seedOps.seeds.current before args = some values ∧
        AllocatedSeeds.Seed.literal literal ∈ values ∧ resource.byteTarget literal
  | .refsPush => resource = .refs args.1
  | .refsDrop => resource = .refs args
  | .writeMeta => resource = .metas args.1
  | _ => False

def ResourceOutcome {types : Types} {Value Unwind : Type} (retained : Retained types) :
    Outcome (World types.Extra) Value Unwind types.Terminal → Prop
  | .returned _ after | .unwound _ after => retained.Holds after
  | .terminated _ => True

/-- Pointwise retention is checked at each actual provider exit, including
when a destructive return would otherwise prevent every later SDK result. -/
def RetainsResources {types : Types} {Args Value Unwind : Type}
    (call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal) : Prop :=
  ∀ before args retained, retained.Holds before → ∀ outcome,
    call before args outcome → ResourceOutcome retained outcome

def PrimitiveResources {types : Types} {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) : Prop :=
  ∀ before args retained, retained.Holds before → ∀ outcome,
    call before args outcome → ¬ Touches selected before args outcome retained.resource →
      ResourceOutcome retained outcome

/-- Only the actual normal returns of a constructor create an owner. Abnormal
exits create none and are still subject to the independent retention frame. -/
def Constructs {types : Types} {Args Element Resource : Type}
    (current : World types.Extra → Resource → Option (List Element))
    (call : Callback.Run (World types.Extra) Args Resource types.Unwind types.Terminal)
    (contents : Args → List Element) (identity : Resource → ResourceRef types) : Prop :=
  ∀ before args resource after, call before args (.returned resource after) →
    current after resource = some (contents args) ∧ (identity resource).Fresh before

/-- Successful writes use the actual pre-call sequence. A failed write may
leave partial contents, but its owner stays current for source cleanup. -/
structure PushReady {State Element Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps State Element Resource Unwind Terminal) : Prop where
  returned : ∀ before resource value values after,
    ops.current before resource = some values →
    ops.push before (resource, value) (.returned () after) →
      ops.current after resource = some (values ++ [value])
  unwound : ∀ before resource value reason after,
    ops.Live before resource → ops.push before (resource, value) (.unwound reason after) →
      ops.Live after resource

structure ExtendReady {State Element Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps State Element Resource Unwind Terminal) : Prop where
  returned : ∀ before resource extra values after,
    ops.current before resource = some values →
    ops.extend before (resource, extra) (.returned () after) →
      ops.current after resource = some (values ++ extra)
  unwound : ∀ before resource extra reason after,
    ops.Live before resource → ops.extend before (resource, extra) (.unwound reason after) →
      ops.Live after resource

/-- Existing mathematical reference laws can discharge a selected capability;
the admission gate below never asks an arbitrary provider for unused methods. -/
theorem PushReady.of_laws {State Element Resource Unwind Terminal : Type}
    {ops : Owned.VectorOps State Element Resource Unwind Terminal} (laws : ops.Laws) :
    PushReady ops := ⟨laws.push_current, laws.push_unwind_live⟩

theorem ExtendReady.of_laws {State Element Resource Unwind Terminal : Type}
    {ops : Owned.VectorOps State Element Resource Unwind Terminal} (laws : ops.Laws) :
    ExtendReady ops := ⟨laws.extend_current, laws.extend_unwind_live⟩

/-- Constructors whose returned current vectors are subsequently read. In
particular, this does not require unused seed capacity/list constructors,
AccountInfo Vec::new, or the unread discriminator contents of the validator. -/
structure ConstructorsReady (types : Types) : Prop where
  bytesEmpty : Constructs types.bytes.current (emptyCall types.bytes.empty)
    (fun _ => []) ResourceRef.bytes
  bytesCapacity : Constructs types.bytes.current types.bytes.withCapacity
    (fun _ => []) ResourceRef.bytes
  metasCapacity : Constructs types.metas.current types.metas.withCapacity
    (fun _ => []) ResourceRef.metas
  metasList : Constructs types.metas.current types.metas.fromList id ResourceRef.metas
  infosFinish : Constructs types.infos.current types.infoLiteral.finish id ResourceRef.infos
  paddingList : Constructs types.paddingBytes.current types.paddingBytes.fromList id
    ResourceRef.padding
  literalList : Constructs types.seedOps.bytes.current types.seedOps.bytes.fromList id
    ResourceRef.literal
  seedsEmpty : Constructs types.seedOps.seeds.current (emptyCall types.seedOps.seeds.empty)
    (fun _ => []) ResourceRef.seeds
  refsEmpty : Constructs types.seedOps.refs.current (emptyCall types.seedOps.refs.empty)
    (fun _ => []) ResourceRef.refs

/-- Current-shape obligations only for source methods preceding local reads
or transferring an owner to cleanup. Destruction has only a frame on other
owners: the source never reads the current contents of a dropped vector. -/
structure MutationsReady (types : Types) : Prop where
  bytesPush : PushReady types.bytes
  bytesExtend : ExtendReady types.bytes
  metasPush : PushReady types.metas
  metasExtend : ExtendReady types.metas
  infosPush : PushReady types.infos
  infosExtend : ExtendReady types.infos
  seedsPush : PushReady types.seedOps.seeds
  refsPush : PushReady types.seedOps.refs
  writeMeta : ∀ before resource index item values after,
    types.metas.current before resource = some values → index < values.length →
    types.writeMeta before resource index item after →
      types.metas.current after resource = some (values.set index item)

/-- the ordinary operations of Collection retain its borrowed input vector and
all other SDK locals before another iterator read or closure call is possible. -/
structure CollectionResources (types : Types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal) : Prop where
  internal : ∀ index acquired,
    RetainsResources (fun state (_ : Unit) => protocol.internal index acquired state)
  finish : RetainsResources protocol.finish
  retire : ∀ acquired,
    RetainsResources (fun state (_ : Unit) => protocol.retire none acquired state)

/-- The caller still owns these three vectors while the opaque invocation
runs. This is an external frame at that signature, allowing all account-state
effects and every exit kind; it is not a callee body or success theorem. -/
def InvocationResources (types : Types) (deps : Dependencies types) : Prop :=
  ∀ (prepared : Prepared types) before signers request,
    prepared.observe types before signers = some request → ∀ outcome,
    deps.invoke before request outcome →
    ∀ retained, retained.Holds before →
      (retained.resource = .metas prepared.instruction.metas ∨
        retained.resource = .bytes prepared.instruction.data ∨
        retained.resource = .infos prepared.infos) → ResourceOutcome retained outcome

/-- Ordinary resource admission is independent of full SDK executions. It
supplies live constructors, actual update shapes and scoped retention at each
primitive boundary, with no provider termination or whole-body premise. -/
structure ResourceReady (types : Types) (deps : Dependencies types)
    (protocol : AllocatedCollect.Protocol types.Extra types.GuardResource
      types.Unwind types.Terminal) : Prop where
  constructors : ConstructorsReady types
  mutations : MutationsReady types
  onAux : ∀ (retained : Retained types) accounts next extra,
    retained.Holds (accounts, extra) → retained.Holds (next, extra)
  primitive : ∀ {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call), PrimitiveResources selected
  guardDrop : RetainsResources types.guards.drop
  collection : CollectionResources types protocol
  invocation : InvocationResources types deps

/-- Primitive retention composes through the exact callback states. -/
theorem RetainsResources.bind {types : Types} {Args Value Next Unwind : Type}
    {first : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    {next : Value → World types.Extra → Outcome (World types.Extra) Next Unwind types.Terminal →
      Prop}
    (firstLaw : RetainsResources first)
    (nextLaw : ∀ value, RetainsResources (fun state (_ : Unit) => next value state)) :
    RetainsResources (Callback.bind first next) := by
  rintro before args retained current outcome ⟨produced, called, continued⟩
  have kept := firstLaw before args retained current produced called
  cases produced with
  | returned value after => exact nextLaw value after () retained kept outcome continued
  | unwound _ _ => cases continued; exact kept
  | terminated _ => cases continued; trivial

theorem RetainsResources.arguments {types : Types} {Args Selected Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (law : RetainsResources call) (select : Selected → Args) :
    RetainsResources (fun before args => call before (select args)) := by
  intro before args
  exact law before (select args)

theorem RetainsResources.map {types : Types} {Args Value Next Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (law : RetainsResources call) (f : Value → Next) :
    RetainsResources (Callback.map f call) := by
  rintro before args retained current _ ⟨produced, called, rfl⟩
  have kept := law before args retained current produced called
  cases produced <;> exact kept

theorem RetainsResources.empty {types : Types} {Args Value Unwind : Type} :
    RetainsResources (fun (_ : World types.Extra) (_ : Args)
      (_ : Outcome (World types.Extra) Value Unwind types.Terminal) => False) := by
  intro _ _ _ _ _ impossible
  exact False.elim impossible

/-- Each actual constructor exit has the source-local current-read
continuation. Returns read the exact constructed sequence; exceptional exits
propagate before ownership is obtained, with no fabricated provider execution. -/
theorem Constructs.read_after_exit {types : Types} {Args Element Resource : Type}
    {current : World types.Extra → Resource → Option (List Element)}
    {call : Callback.Run (World types.Extra) Args Resource types.Unwind types.Terminal}
    {contents : Args → List Element} {identity : Resource → ResourceRef types}
    (law : Constructs current call contents identity)
    {before : World types.Extra} {args : Args}
    {pending : Outcome (World types.Extra) Resource types.Unwind types.Terminal}
    (called : call before args pending) :
    bind (perform fun state => call state args)
      (fun resource => inspect fun state => current state resource) before
      (Outcome.map (fun _ => Except.ok (contents args)) pending) := by
  refine ⟨Outcome.map Except.ok pending, ⟨pending, called, rfl⟩, ?_⟩
  cases pending with
  | returned resource after => exact ⟨contents args, (law before args resource after called).1, rfl⟩
  | unwound _ _ | terminated _ => rfl

/-- A finite push cannot be lost at the following current read. On unwind
the read is skipped and the live target is handed to cleanup in that state. -/
theorem PushReady.read_after_exit {State Element Resource Unwind Terminal : Type}
    {ops : Owned.VectorOps State Element Resource Unwind Terminal} (law : PushReady ops)
    {before : State} {resource : Resource} {value : Element} {values : List Element}
    {pending : Outcome State Unit Unwind Terminal}
    (current : ops.current before resource = some values)
    (called : ops.push before (resource, value) pending) :
    bind (perform fun state => ops.push state (resource, value))
      (fun _ => inspect fun state => ops.current state resource) before
      (Outcome.map (fun _ => Except.ok (values ++ [value])) pending) ∧
    (match pending with
      | .returned _ after | .unwound _ after => ops.Live after resource
      | .terminated _ => True) := by
  constructor
  · refine ⟨Outcome.map Except.ok pending, ⟨pending, called, rfl⟩, ?_⟩
    cases pending with
    | returned done after =>
      cases done
      exact ⟨values ++ [value], law.returned before resource value values after current called, rfl⟩
    | unwound _ _ | terminated _ => rfl
  · cases pending with
    | returned done after =>
      cases done
      exact ⟨values ++ [value], law.returned before resource value values after current called⟩
    | unwound reason after =>
      exact law.unwound before resource value reason after ⟨values, current⟩ called
    | terminated _ => trivial

/-- Bulk extension has the same local guarantee while retaining its single
source call and actual partial state on unwind. -/
theorem ExtendReady.read_after_exit {State Element Resource Unwind Terminal : Type}
    {ops : Owned.VectorOps State Element Resource Unwind Terminal} (law : ExtendReady ops)
    {before : State} {resource : Resource} {extra values : List Element}
    {pending : Outcome State Unit Unwind Terminal}
    (current : ops.current before resource = some values)
    (called : ops.extend before (resource, extra) pending) :
    bind (perform fun state => ops.extend state (resource, extra))
      (fun _ => inspect fun state => ops.current state resource) before
      (Outcome.map (fun _ => Except.ok (values ++ extra)) pending) ∧
    (match pending with
      | .returned _ after | .unwound _ after => ops.Live after resource
      | .terminated _ => True) := by
  constructor
  · refine ⟨Outcome.map Except.ok pending, ⟨pending, called, rfl⟩, ?_⟩
    cases pending with
    | returned done after =>
      cases done
      exact ⟨values ++ extra, law.returned before resource extra values after current called, rfl⟩
    | unwound _ _ | terminated _ => rfl
  · cases pending with
    | returned done after =>
      cases done
      exact ⟨values ++ extra, law.returned before resource extra values after current called⟩
    | unwound reason after =>
      exact law.unwound before resource extra reason after ⟨values, current⟩ called
    | terminated _ => trivial

variable {types : Types} {deps : Dependencies types}
  {protocol : AllocatedCollect.Protocol types.Extra types.GuardResource types.Unwind types.Terminal}

/-- A surviving return exposes the exact retained current sequence before
any later source Option read is performed. -/
theorem ResourceReady.current_after
    (ready : ResourceReady types deps protocol) {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) {before after : World types.Extra}
    {args : Args} {value : Value} {retained : Retained types}
    (current : retained.Holds before) (called : call before args (.returned value after))
    (outside : ¬ Touches selected before args (.returned value after) retained.resource) :
    retained.Holds after :=
  ready.primitive selected before args retained current _ called outside

/-- A surviving unwind retains another live owner at the actual cleanup
state. It imposes no finite-exit assumption on the destructor of that owner. -/
theorem ResourceReady.current_unwound
    (ready : ResourceReady types deps protocol) {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) {before after : World types.Extra}
    {args : Args} {reason : Unwind} {retained : Retained types}
    (current : retained.Holds before) (called : call before args (.unwound reason after))
    (outside : ¬ Touches selected before args (.unwound reason after) retained.resource) :
    retained.Holds after :=
  ready.primitive selected before args retained current _ called outside

/-- A successful literal allocation immediately supplies the source width
read and its owned literal borrow. The bound is the actual 32-byte payload bound of the address
configuration, not an assumption about allocator termination. -/
theorem ResourceReady.literal_reads
    (ready : ResourceReady types deps protocol) {before after : World types.Extra}
    {values : Bytes} {resource : types.ByteResource} (bounded : values.length ≤ 30)
    (called : types.seedOps.bytes.fromList before values (.returned resource after))
    (args : AllocatedSeeds.Args (World types.Extra))
    (instruction : AllocatedSeeds.BytesView (World types.Extra)) :
    AllocatedSeeds.widthAt types.seedOps.bytes after (.literal resource) = some (2 + values.length)
      ∧
    AllocatedSeeds.seedView types.seedOps args instruction (.literal resource) after ()
      (.returned (.ok (some ⟨values.length, fun state => types.seedOps.bytes.current state
        resource⟩)) after) ∧
    types.seedOps.bytes.Live after resource := by
  have current := (ready.constructors.literalList before values resource after called).1
  refine ⟨?_, ⟨values, current, rfl⟩, values, current⟩
  simp [AllocatedSeeds.widthAt, current, bounded]

private theorem unpackOne_literal_origin {before after : World types.Extra}
    {input : Bytes} {resource : types.ByteResource}
    (called : AllocatedSeeds.unpackOne types.seedOps.bytes input before ()
      (.returned (.ok (.literal resource)) after)) :
    ∃ tag length payload, input = tag :: length :: payload ∧
      types.seedOps.bytes.fromList before (payload.take length.toNat) (.returned resource after) :=
        by
  cases input with
  | nil => cases called
  | cons tag rest =>
    simp only [AllocatedSeeds.unpackOne] at called
    split at called
    · cases called
    · split at called
      · cases rest with
        | nil => cases called
        | cons length payload =>
          dsimp only at called
          split at called
          · cases called
          · obtain ⟨produced, allocated, mapped⟩ := called
            cases produced with
            | returned actual during =>
              cases mapped
              exact ⟨tag, length, payload, rfl, allocated⟩
            | unwound _ _ | terminated _ => cases mapped
      · split at called
        · split at called <;> cases called
        · split at called
          · split at called <;> cases called
          · split at called
            · split at called <;> cases called
            · cases called

/-- The actual Seed::unpack result from a suffix of the 32-byte address
configuration always reaches widthAt. The literal bound follows from the
source input and exact allocation contents, rather than being assumed of the
returned vector or a completed unpacking loop. -/
theorem ResourceReady.unpack_width
    (ready : ResourceReady types deps protocol) {before after : World types.Extra}
    {input : Bytes} {seed : AllocatedSeeds.Seed types.ByteResource}
    (bounded : input.length ≤ 32)
    (called : AllocatedSeeds.unpackOne types.seedOps.bytes input before ()
      (.returned (.ok seed) after)) :
    ∃ width, AllocatedSeeds.widthAt types.seedOps.bytes after seed = some width ∧
      (seed ≠ .uninitialized → 0 < width) := by
  cases seed with
  | uninitialized => exact ⟨0, rfl, fun different => False.elim (different rfl)⟩
  | instructionData _ _ => exact ⟨3, rfl, fun _ => by decide⟩
  | accountKey _ => exact ⟨2, rfl, fun _ => by decide⟩
  | accountData _ _ _ => exact ⟨4, rfl, fun _ => by decide⟩
  | literal resource =>
    obtain ⟨tag, length, payload, input, allocated⟩ := unpackOne_literal_origin called
    subst input
    have payloadBound : payload.length ≤ 30 := by simpa using bounded
    have lengthBound : (payload.take length.toNat).length ≤ 30 := by
      simp only [List.length_take]
      omega
    have current := (ready.constructors.literalList before _ resource after allocated).1
    refine ⟨2 + (payload.take length.toNat).length, ?_, fun _ => by omega⟩
    simp [AllocatedSeeds.widthAt, current]
    omega

/-- The return of the repeated-zero constructor cannot disappear at the padding
comparison: both the borrowed Mint data and exact temporary vector are current. -/
theorem ResourceReady.padding_reads
    (ready : ResourceReady types deps protocol) (admitted : Admitted types deps protocol)
    {before after : World types.Extra} {reference : DataRef} {bytes : Bytes}
    {resource : types.ByteResource} (valid : before.1.Valid)
    (read : reference.read before = some bytes)
    (called : types.paddingBytes.fromList before (List.replicate AllocatedTlv.mintPaddingLength 0)
      (.returned resource after)) :
    reference.read after = some bytes ∧
    types.paddingBytes.current after resource = some (List.replicate AllocatedTlv.mintPaddingLength
      0) ∧
    types.paddingBytes.Live after resource := by
  have current := (ready.constructors.paddingList before _ resource after called).1
  exact ⟨(admitted.primitive .paddingList).1.read_returned valid read called,
    current, _, current⟩

/-- Fresh padding is a distinct owner from retained instruction data. Its
actual destructor may return, unwind or terminate; none of those exits can
erase the other byte vector through an aliased temporary identity. -/
theorem ResourceReady.padding_cleanup_retains_data
    (ready : ResourceReady types deps protocol) {before during : World types.Extra}
    {instructionData temporary : types.ByteResource} {instructionBytes : Bytes}
    (current : types.bytes.current before instructionData = some instructionBytes)
    (allocated : types.paddingBytes.fromList before (List.replicate AllocatedTlv.mintPaddingLength
      0)
      (.returned temporary during))
    {pending : Outcome (World types.Extra) Unit types.Unwind types.Terminal}
    (dropped : types.paddingBytes.drop during temporary pending) :
    Callback.bind types.paddingBytes.fromList
      (fun resource state outcome => types.paddingBytes.drop state resource outcome)
      before (List.replicate AllocatedTlv.mintPaddingLength 0) pending ∧
    ResourceOutcome (.bytes instructionData instructionBytes) pending := by
  have constructed := ready.constructors.paddingList before _ temporary during allocated
  have different : instructionData ≠ temporary := by
    intro same
    subst temporary
    have fresh : types.bytes.current before instructionData = none := constructed.2.1
    rw [current] at fresh
    cases fresh
  have kept := ready.current_after .paddingList (retained := .bytes instructionData
    instructionBytes)
    current allocated (by simp [Touches])
  exact ⟨⟨.returned temporary during, allocated, dropped⟩,
    ready.primitive .paddingDrop during temporary (.bytes instructionData instructionBytes) kept
      pending dropped different⟩

/-- The new Execute metadata literal cannot alias the still-owned transfer
metadata vector. Its first actual push therefore retains the current sequence of the transfer,
including on unwind before outer cleanup. -/
theorem ResourceReady.execute_meta_push_retains_transfer
    (ready : ResourceReady types deps protocol) {before during : World types.Extra}
    {transferMetas executeMetas : types.MetaResource} {transferValues executeValues : List
      Solanalib.Runtime.CpiMeta}
    {item : Solanalib.Runtime.CpiMeta}
    (current : types.metas.current before transferMetas = some transferValues)
    (allocated : types.metas.fromList before executeValues (.returned executeMetas during))
    {pending : Outcome (World types.Extra) Unit types.Unwind types.Terminal}
    (pushed : types.metas.push during (executeMetas, item) pending) :
    ResourceOutcome (.metas transferMetas transferValues) pending := by
  have constructed := ready.constructors.metasList before executeValues executeMetas during
    allocated
  have different : transferMetas ≠ executeMetas := by
    intro same
    subst executeMetas
    have fresh : types.metas.current before transferMetas = none := constructed.2
    rw [current] at fresh
    cases fresh
  have kept := ready.current_after .metasList (retained := .metas transferMetas transferValues)
    current allocated (by simp [Touches])
  apply ready.primitive .metasPush during (executeMetas, item) (.metas transferMetas transferValues)
    kept pending pushed
  simpa [Touches, Retained.resource] using different

/-- The actual finite transition of the field-write callback has the exact fourth-slot continuation
of the source; no completed clearAuthoritySigner is assumed. -/
theorem ResourceReady.authority_write
    (ready : ResourceReady types deps protocol) {before after : World types.Extra}
    {resource : types.MetaResource} {values : List Solanalib.Runtime.CpiMeta} {item :
      Solanalib.Runtime.CpiMeta}
    (current : types.metas.current before resource = some values)
    (slot : values[3]? = some item)
    (wrote : types.writeMeta before resource 3 { item with signerByte := 0 } after) :
    clearAuthoritySigner types resource before (.returned (.ok ()) after) := by
  have bound : 3 < values.length := by
    by_cases inside : 3 < values.length
    · exact inside
    · have missing := List.getElem?_eq_none (Nat.le_of_not_lt inside) (l := values)
      rw [missing] at slot
      cases slot
  exact ⟨values, item, after, current, slot,
    wrote, ready.mutations.writeMeta before resource 3 _ values after current bound wrote, rfl⟩

/-- A retained AccountInfo vector supplies the captured length of the iterator
and next actual indexed element after an ordinary provider return. -/
theorem ResourceReady.info_iterator_after
    (ready : ResourceReady types deps protocol) {Args Value Unwind : Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) {before after : World types.Extra}
    {args : Args} {value : Value} {resource : types.InfoResource}
    {values : List AccountInfo.Value} {index : Nat}
    (current : types.infos.current before resource = some values)
    (inside : index < values.length) (called : call before args (.returned value after))
    (outside : ¬ Touches selected before args (.returned value after) (.infos resource)) :
    (infoIterator types resource values.length).elementAt after index = some values[index] := by
  have kept := ready.current_after selected (retained := .infos resource values) current called
    outside
  simp [infoIterator, Retained.Holds] at kept ⊢
  simp [kept, List.getElem?_eq_getElem inside]

/-- Borrowed-seed iteration keeps its original length and indexed seed
across every actual reference-vector push. The reference vector may change. -/
theorem ResourceReady.seed_index_after_push
    (ready : ResourceReady types deps protocol) {before after : World types.Extra}
    {seeds : types.SeedResource} {references : types.SeedRefResource}
    {values : List (AllocatedSeeds.Seed types.ByteResource)} {index : Nat}
    {view : AllocatedSeeds.BytesView (World types.Extra)}
    (current : types.seedOps.seeds.current before seeds = some values)
    (inside : index < values.length)
    (called : types.seedOps.refs.push before (references, view) (.returned () after)) :
    ∃ actual, types.seedOps.seeds.current after seeds = some actual ∧
      actual.length = values.length ∧ actual[index]? = some values[index] := by
  have kept := ready.current_after .refsPush (retained := .seeds seeds values) current called
    (by simp [Touches, Retained.resource])
  exact ⟨values, kept, rfl, List.getElem?_eq_getElem inside⟩

/-- Both fixed-prefix checks in copyExtras are discharged before the actual returned transition of
either extension is composed. The first extension
cannot erase the Execute AccountInfo vector needed by the second read. -/
theorem ResourceReady.copy_extras_returns
    (ready : ResourceReady types deps protocol) (transfer execute : Prepared types)
    {before during after : World types.Extra} {metas : List Solanalib.Runtime.CpiMeta}
    {infos : List AccountInfo.Value}
    (metasCurrent : types.metas.current before execute.instruction.metas = some metas)
    (metasLength : 5 ≤ metas.length)
    (infosCurrent : types.infos.current before execute.infos = some infos)
    (infosLength : 5 ≤ infos.length)
    (metasExtended : types.metas.extend before (transfer.instruction.metas, metas.drop 5)
      (.returned () during))
    (infosExtended : types.infos.extend during (transfer.infos, infos.drop 5)
      (.returned () after)) :
    copyExtras types transfer execute before (.returned (.ok ()) after) := by
  have kept := ready.current_after .metasExtend (retained := .infos execute.infos infos)
    infosCurrent metasExtended (by simp [Touches, Retained.resource])
  refine ⟨.returned (.ok (metas.drop 5)) before, ?_, ?_⟩
  · exact ⟨metas.drop 5, by simp [metasCurrent, metasLength], rfl⟩
  refine ⟨.returned (.ok ()) during, ?_, ?_⟩
  · exact ⟨.returned () during, metasExtended, rfl⟩
  refine ⟨.returned (.ok (infos.drop 5)) during, ?_, ?_⟩
  · exact ⟨infos.drop 5, by simp [show types.infos.current during execute.infos = some infos from
    kept,
      infosLength], rfl⟩
  exact ⟨.returned () after, infosExtended, rfl⟩

/-- The three final current projections remain available after a primitive
that touches none of those owners. This supplies the actual pre-invoke read. -/
theorem ResourceReady.prepared_observe_after
    (ready : ResourceReady types deps protocol) (prepared : Prepared types) {Args Value Unwind :
      Type}
    {call : Callback.Run (World types.Extra) Args Value Unwind types.Terminal}
    (selected : ResourcePrimitive types call) {before after : World types.Extra}
    {args : Args} {value : Value} {signers : List (List Bytes)}
    {request : CpiRequest.Request AccountInfo.Value}
    (observed : prepared.observe types before signers = some request)
    (called : call before args (.returned value after))
    (metasOutside : ¬ Touches selected before args (.returned value after)
      (.metas prepared.instruction.metas))
    (bytesOutside : ¬ Touches selected before args (.returned value after)
      (.bytes prepared.instruction.data))
    (infosOutside : ¬ Touches selected before args (.returned value after) (.infos prepared.infos))
      :
    prepared.observe types after signers = some request := by
  cases hm : types.metas.current before prepared.instruction.metas with
  | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm] at observed
  | some metas =>
    cases hb : types.bytes.current before prepared.instruction.data with
    | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm, hb] at observed
    | some bytes =>
      cases hi : types.infos.current before prepared.infos with
      | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm, hb, hi] at observed
      | some infos =>
        have km := ready.current_after selected (retained := .metas prepared.instruction.metas
          metas)
          hm called metasOutside
        have kb := ready.current_after selected (retained := .bytes prepared.instruction.data bytes)
          hb called bytesOutside
        have ki := ready.current_after selected (retained := .infos prepared.infos infos)
          hi called infosOutside
        simpa [Prepared.observe, Instruction.OwnedValue.observe,
          show types.metas.current after prepared.instruction.metas = some metas from km,
          show types.bytes.current after prepared.instruction.data = some bytes from kb,
          show types.infos.current after prepared.infos = some infos from ki] using
          (show some (⟨Instruction.make prepared.instruction.programId metas bytes,
            infos, signers⟩ : CpiRequest.Request AccountInfo.Value) = some request by
            simpa [Prepared.observe, Instruction.OwnedValue.observe, hm, hb, hi] using observed)

/-- The actual opaque invocation exit leaves each source cleanup token
represented. No execution of those later opaque destructors is postulated. -/
theorem ResourceReady.invocation_cleanup_current
    (ready : ResourceReady types deps protocol) (prepared : Prepared types)
    {before after : World types.Extra} {signers : List (List Bytes)}
    {request : CpiRequest.Request AccountInfo.Value} {result : Except Error Unit}
    (observed : prepared.observe types before signers = some request)
    (called : deps.invoke before request (.returned result after)) :
    types.metas.Live after prepared.instruction.metas ∧
    types.bytes.Live after prepared.instruction.data ∧ types.infos.Live after prepared.infos := by
  cases hm : types.metas.current before prepared.instruction.metas with
  | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm] at observed
  | some metas =>
    cases hb : types.bytes.current before prepared.instruction.data with
    | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm, hb] at observed
    | some bytes =>
      cases hi : types.infos.current before prepared.infos with
      | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm, hb, hi] at observed
      | some infos =>
        exact ⟨⟨metas, ready.invocation prepared before signers request observed _ called
            (.metas prepared.instruction.metas metas) hm (Or.inl rfl)⟩,
          ⟨bytes, ready.invocation prepared before signers request observed _ called
            (.bytes prepared.instruction.data bytes) hb (Or.inr (Or.inl rfl))⟩,
          ⟨infos, ready.invocation prepared before signers request observed _ called
            (.infos prepared.infos infos) hi (Or.inr (Or.inr rfl))⟩⟩

/-- Unwinding CPI exposes the same live local cleanup tokens at its actual
unwind state; account values may have changed inside the opaque invocation. -/
theorem ResourceReady.invocation_unwind_current
    (ready : ResourceReady types deps protocol) (prepared : Prepared types)
    {before after : World types.Extra} {signers : List (List Bytes)}
    {request : CpiRequest.Request AccountInfo.Value} {reason : types.Unwind}
    (observed : prepared.observe types before signers = some request)
    (called : deps.invoke before request (.unwound reason after)) :
    types.metas.Live after prepared.instruction.metas ∧
    types.bytes.Live after prepared.instruction.data ∧ types.infos.Live after prepared.infos := by
  cases hm : types.metas.current before prepared.instruction.metas with
  | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm] at observed
  | some metas =>
    cases hb : types.bytes.current before prepared.instruction.data with
    | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm, hb] at observed
    | some bytes =>
      cases hi : types.infos.current before prepared.infos with
      | none => simp [Prepared.observe, Instruction.OwnedValue.observe, hm, hb, hi] at observed
      | some infos =>
        exact ⟨⟨metas, ready.invocation prepared before signers request observed _ called
            (.metas prepared.instruction.metas metas) hm (Or.inl rfl)⟩,
          ⟨bytes, ready.invocation prepared before signers request observed _ called
            (.bytes prepared.instruction.data bytes) hb (Or.inr (Or.inl rfl))⟩,
          ⟨infos, ready.invocation prepared before signers request observed _ called
            (.infos prepared.infos infos) hi (Or.inr (Or.inr rfl))⟩⟩

/-- Exactly the borrowed view forms produced by the source seed match. It
does not admit arbitrary state-sensitive functions stored in a test vector. -/
inductive SourceSeedView (types : Types) (args : AllocatedSeeds.Args (World types.Extra))
    (instruction : AllocatedSeeds.BytesView (World types.Extra)) :
    AllocatedSeeds.BytesView (World types.Extra) → Prop
  | literal (resource : types.ByteResource) (length : Nat) :
      SourceSeedView types args instruction
        ⟨length, fun state => types.seedOps.bytes.current state resource⟩
  | instruction (offset length : Nat) :
      SourceSeedView types args instruction (instruction.slice offset length)
  | accountKey (index : Nat) :
      SourceSeedView types args instruction
        ⟨32, fun state => (AllocatedSeeds.accountKeyAt args index state).map (·.bytes)⟩
  | accountData (index parentLength offset length : Nat) :
      SourceSeedView types args instruction
        ((⟨parentLength, AllocatedSeeds.accountDataAt args index⟩ :
          AllocatedSeeds.BytesView (World types.Extra)).slice offset length)

/-- Every successful source view construction has one of these exact forms. -/
theorem seedView_source (args : AllocatedSeeds.Args (World types.Extra))
    (instruction : AllocatedSeeds.BytesView (World types.Extra))
    {before after : World types.Extra} {seed : AllocatedSeeds.Seed types.ByteResource}
    {view : AllocatedSeeds.BytesView (World types.Extra)}
    (called : AllocatedSeeds.seedView types.seedOps args instruction seed before ()
      (.returned (.ok (some view)) after)) : SourceSeedView types args instruction view := by
  cases seed with
  | uninitialized => cases called
  | literal resource =>
    obtain ⟨bytes, _, equal⟩ := called
    cases equal
    exact .literal resource bytes.length
  | instructionData offset length =>
    obtain ⟨bytes, _, result⟩ := called
    split at result
    · cases result
    · cases result; exact .instruction offset.toNat length.toNat
  | accountKey index =>
    obtain ⟨accounts, _, result⟩ := called
    cases selected : accounts[index.toNat]? with
    | none => rw [selected] at result; cases result
    | some account => rw [selected] at result; cases result; exact .accountKey index.toNat
  | accountData index offset length =>
    obtain ⟨accounts, _, result⟩ := called
    cases selected : accounts[index.toNat]? with
    | none => rw [selected] at result; cases result
    | some account =>
      rcases account with ⟨key, data⟩
      cases data with
      | none => rw [selected] at result; cases result
      | some bytes =>
        by_cases short : bytes.length < offset.toNat + length.toNat
        · simp [selected, short] at result
        · simp only [selected, short, ↓reduceIte] at result
          cases result
          exact .accountData index.toNat bytes.length offset.toNat length.toNat

private theorem view_length_of_read {State : Type} (view : AllocatedSeeds.BytesView State)
    (before : State) {bytes : Bytes} (read : view.observe before = some bytes) :
    bytes.length = view.length := by
  cases current : view.read before with
  | none => simp [AllocatedSeeds.BytesView.observe, current] at read
  | some values =>
    simp only [AllocatedSeeds.BytesView.observe, current] at read
    change (if values.length = view.length then some values else none) = some bytes at read
    split at read
    · cases read; assumption
    · cases read

private theorem view_slice_read {State : Type} (view : AllocatedSeeds.BytesView State)
    (before : State) {bytes : Bytes} (read : view.observe before = some bytes)
    (offset length : Nat) (bounded : offset + length ≤ view.length) :
    (view.slice offset length).observe before = some (Solanalib.Runtime.slice bytes offset length)
      := by
  have size := view_length_of_read view before read
  have sliceSize := Solanalib.Runtime.length_slice_of_le (show offset + length ≤ bytes.length by
    omega)
  have current : (view.slice offset length).read before = some (Solanalib.Runtime.slice bytes
    offset length) := by
    simp [AllocatedSeeds.BytesView.slice, read, bounded]
  simp [AllocatedSeeds.BytesView.observe, current, sliceSize]
  rfl

/-- A successfully constructed source seed view is immediately readable.
Together with seedView_source, this supplies the initial invariant used by
the later per-push retention theorem, rather than assuming an arbitrary view. -/
theorem seedView_readable (args : AllocatedSeeds.Args (World types.Extra))
    (instruction : AllocatedSeeds.BytesView (World types.Extra))
    {before after : World types.Extra} {seed : AllocatedSeeds.Seed types.ByteResource}
    {view : AllocatedSeeds.BytesView (World types.Extra)}
    (called : AllocatedSeeds.seedView types.seedOps args instruction seed before ()
      (.returned (.ok (some view)) after)) : ∃ bytes, view.observe after = some bytes := by
  cases seed with
  | uninitialized => cases called
  | literal resource =>
    obtain ⟨bytes, current, equal⟩ := called
    cases equal
    exact ⟨bytes, by simp [AllocatedSeeds.BytesView.observe, current]⟩
  | instructionData offset length =>
    obtain ⟨bytes, current, result⟩ := called
    split at result
    · cases result
    · cases result
      exact ⟨Solanalib.Runtime.slice bytes offset.toNat length.toNat,
        view_slice_read instruction before current offset.toNat length.toNat (by omega)⟩
  | accountKey index =>
    obtain ⟨accounts, current, result⟩ := called
    cases selected : accounts[index.toNat]? with
    | none => rw [selected] at result; cases result
    | some account =>
      rw [selected] at result
      cases result
      exact ⟨account.1.bytes, by simp [AllocatedSeeds.BytesView.observe,
        AllocatedSeeds.accountKeyAt, current, selected, Solanalib.Runtime.Pubkey.length_eq]⟩
  | accountData index offset length =>
    obtain ⟨accounts, current, result⟩ := called
    cases selected : accounts[index.toNat]? with
    | none => rw [selected] at result; cases result
    | some account =>
      rcases account with ⟨key, data⟩
      cases data with
      | none => rw [selected] at result; cases result
      | some bytes =>
        by_cases short : bytes.length < offset.toNat + length.toNat
        · simp [selected, short] at result
        · simp only [selected, short, ↓reduceIte] at result
          cases result
          refine ⟨Solanalib.Runtime.slice bytes offset.toNat length.toNat, ?_⟩
          apply view_slice_read _ before ?_ offset.toNat length.toNat (by dsimp; omega)
          simp [AllocatedSeeds.BytesView.observe, AllocatedSeeds.accountDataAt, current, selected]

private theorem view_observe_kept {State : Type}
    (view : AllocatedSeeds.BytesView State) (before after : State)
    (keeps : ∀ bytes, view.read before = some bytes → view.read after = some bytes)
    {bytes : Bytes} (observed : view.observe before = some bytes) :
    view.observe after = some bytes := by
  cases read : view.read before with
  | none => simp [AllocatedSeeds.BytesView.observe, read] at observed
  | some current =>
    have next := keeps current read
    simpa only [AllocatedSeeds.BytesView.observe, read, next] using observed

private theorem view_slice_kept {State : Type}
    (view : AllocatedSeeds.BytesView State) (before after : State) (offset length : Nat)
    (keeps : ∀ bytes, view.observe before = some bytes → view.observe after = some bytes)
    {bytes : Bytes} (observed : (view.slice offset length).observe before = some bytes) :
    (view.slice offset length).observe after = some bytes := by
  apply view_observe_kept _ before after ?_ observed
  intro current read
  cases parent : view.observe before with
  | none => simp [AllocatedSeeds.BytesView.slice, parent] at read
  | some values =>
    have next := keeps values parent
    simpa only [AllocatedSeeds.BytesView.slice, parent, next] using read

/-- Each generated view follows a retained literal, instruction slice, or
collected account observation. Retaining those footprints preserves its read
without freezing unrelated provider state. -/
theorem SourceSeedView.observe_kept
    {args : AllocatedSeeds.Args (World types.Extra)}
    {instruction view : AllocatedSeeds.BytesView (World types.Extra)}
    (source : SourceSeedView types args instruction view) {before after : World types.Extra}
    (literals : ∀ resource bytes, types.seedOps.bytes.current before resource = some bytes →
      types.seedOps.bytes.current after resource = some bytes)
    (instructionKept : ∀ bytes, instruction.observe before = some bytes →
      instruction.observe after = some bytes)
    (accountsKept : ∀ accounts, args.accountsAt before = some accounts →
      args.accountsAt after = some accounts)
    {bytes : Bytes} (observed : view.observe before = some bytes) :
    view.observe after = some bytes := by
  cases source with
  | literal resource length => exact view_observe_kept _ before after (literals resource) observed
  | instruction offset length =>
    exact view_slice_kept _ before after offset length instructionKept observed
  | accountKey index =>
    apply view_observe_kept _ before after ?_ observed
    intro current read
    cases accounts : args.accountsAt before with
    | none => simp [AllocatedSeeds.accountKeyAt, accounts] at read
    | some values =>
      have next := accountsKept values accounts
      simpa only [AllocatedSeeds.accountKeyAt, accounts, next] using read
  | accountData index parentLength offset length =>
    apply view_slice_kept _ before after offset length ?_ observed
    intro current read
    apply view_observe_kept _ before after ?_ read
    intro original selected
    cases accounts : args.accountsAt before with
    | none => simp [AllocatedSeeds.accountDataAt, accounts] at selected
    | some values =>
      have next := accountsKept values accounts
      simpa only [AllocatedSeeds.accountDataAt, accounts, next] using selected

private theorem view_list_kept {State : Type} (before after : State)
    (views : List (AllocatedSeeds.BytesView State))
    (keeps : ∀ view ∈ views, ∀ bytes, view.observe before = some bytes →
      view.observe after = some bytes)
    (values : List Bytes) (read : AllocatedSeeds.readViews before views = some values) :
    AllocatedSeeds.readViews after views = some values := by
  induction views generalizing values with
  | nil => exact read
  | cons view rest induction =>
    unfold AllocatedSeeds.readViews at read ⊢
    cases first : view.observe before with
    | none => rw [List.mapM_cons, first] at read; cases read
    | some bytes =>
      have next := keeps view (by simp) bytes first
      rw [List.mapM_cons, first] at read
      change (rest.mapM (fun (item : AllocatedSeeds.BytesView State) => item.observe before)).bind
        (fun tail => some (bytes :: tail)) = some values at read
      cases tailRead : rest.mapM (fun (item : AllocatedSeeds.BytesView State) => item.observe
        before) with
      | none => rw [tailRead] at read; cases read
      | some tail =>
        have nextTail := induction (fun item member => keeps item (by simp [member])) tail tailRead
        unfold AllocatedSeeds.readViews at nextTail
        rw [tailRead] at read
        cases read
        rw [List.mapM_cons, next]
        change (rest.mapM (fun (item : AllocatedSeeds.BytesView State) => item.observe after)).bind
          (fun tail => some (bytes :: tail)) = _
        rw [nextTail]
        rfl

/-- A reference-vector push updates that vector while preserving the bytes
of every source-generated view already stored in it. This combines ordinary
resource retention with actual held-data retention on the same primitive. -/
theorem ResourceReady.refs_push_views
    (ready : ResourceReady types deps protocol) (admitted : Admitted types deps protocol)
    (args : AllocatedSeeds.Args (World types.Extra))
    (instruction : AllocatedSeeds.BytesView (World types.Extra))
    (instructionData : types.ByteResource) (guards : types.GuardResource)
    (instructionSource : instruction.read = fun state => types.bytes.current state instructionData)
    (accountsSource : args.accountsAt = guardObservations types guards)
    {before after : World types.Extra} {references : types.SeedRefResource}
    {views : List (AllocatedSeeds.BytesView (World types.Extra))} {values : List Bytes}
    {view : AllocatedSeeds.BytesView (World types.Extra)} {bytes : Bytes}
    (valid : before.1.Valid) (current : types.seedOps.refs.current before references = some views)
    (sources : ∀ item ∈ views, SourceSeedView types args instruction item)
    (source : SourceSeedView types args instruction view)
    (read : AllocatedSeeds.readViews before views = some values)
    (viewRead : view.observe before = some bytes)
    (called : types.seedOps.refs.push before (references, view) (.returned () after)) :
    types.seedOps.refs.current after references = some (views ++ [view]) ∧
    AllocatedSeeds.readViews after (views ++ [view]) = some (values ++ [bytes]) := by
  have literals : ∀ resource values, types.seedOps.bytes.current before resource = some values →
      types.seedOps.bytes.current after resource = some values := by
    intro resource values observed
    exact ready.current_after .refsPush (retained := .literal resource values) observed called
      (by simp [Touches, Retained.resource])
  have instructionKept : ∀ values, instruction.observe before = some values →
      instruction.observe after = some values := by
    intro values observed
    apply view_observe_kept instruction before after ?_ observed
    intro contents selected
    rw [instructionSource] at selected ⊢
    exact ready.current_after .refsPush (retained := .bytes instructionData contents) selected
      called
      (by simp [Touches, Retained.resource])
  have accountsKept : ∀ accounts, args.accountsAt before = some accounts →
      args.accountsAt after = some accounts := by
    intro accounts observed
    rw [accountsSource] at observed ⊢
    exact admitted.resolver_read .refsPush .refsPush valid observed called
  have kept := view_list_kept before after views
    (fun item member contents observed => (sources item member).observe_kept
      literals instructionKept accountsKept observed) values read
  have next := source.observe_kept literals instructionKept accountsKept viewRead
  refine ⟨ready.mutations.refsPush.returned before references view views after current called, ?_⟩
  simp only [AllocatedSeeds.readViews, List.mapM_append] at kept ⊢
  rw [kept]
  simp [next]

/-- Once the local current observations are available, each actual PDA
provider exit reaches the unchanged source search relation in that same state.
This forward statement does not assume a completed search result. -/
theorem searchPda_of_actual_exit
    (find : AllocatedSeeds.FindPda (World types.Extra) types.Unwind types.Terminal)
    (programAt : World types.Extra → Option Solanalib.Runtime.Pubkey)
    {before : World types.Extra} {references : types.SeedRefResource}
    {views : List (AllocatedSeeds.BytesView (World types.Extra))} {values : List Bytes}
    {program : Solanalib.Runtime.Pubkey}
    (current : types.seedOps.refs.current before references = some views)
    (read : AllocatedSeeds.readViews before views = some values)
    (selected : programAt before = some program)
    {pending : Outcome (World types.Extra) (Solanalib.Runtime.Pubkey × UInt8) types.Unwind
      types.Terminal}
    (called : find before ⟨values, program⟩ pending) :
    AllocatedSeeds.searchPda types.seedOps find programAt references before ()
      (Outcome.map (fun value => Except.ok value.1) pending) :=
  ⟨views, values, program, current, read, selected, pending, called, rfl⟩

end Solanalib.Specs.Core.Token.OnchainAllocated.Admission
