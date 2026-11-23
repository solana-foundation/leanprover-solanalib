/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedResourceAdmission
public import Solanalib.Specs.Core.TokenRequestAllocatedWitnessAdmission

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.OnchainAllocated.Witness

open Admission

private theorem emptyOnly_empty_current {Element : Type}
    (part : Owned.Focus State (Owned.VectorState Unit)) (before : State) :
    (emptyOnlyOps (Element := Element) part).current
      ((emptyOnlyOps (Element := Element) part).empty before).2
      ((emptyOnlyOps (Element := Element) part).empty before).1 = some [] := by
  have current := (Owned.VectorOps.focus_laws
    (Owned.vectorReference_laws (Element := Unit) (Unwind := Nat) (Terminal := Nat))
      part).empty_current before
  exact congrArg (Option.map (fun (_ : List Unit) => ([] : List Element))) current

private theorem emptyOnly_empty_fresh {Element : Type}
    (part : Owned.Focus State (Owned.VectorState Unit)) (before : State) :
    (emptyOnlyOps (Element := Element) part).current before
      ((emptyOnlyOps (Element := Element) part).empty before).1 = none := by
  have current := (Owned.VectorOps.focus_laws
    (Owned.vectorReference_laws (Element := Unit) (Unwind := Nat) (Terminal := Nat))
      part).empty_fresh before
  exact congrArg (Option.map (fun (_ : List Unit) => ([] : List Element))) current

/-- The unchanged sample supplies only the constructors used by the source.
All three byte-constructor roles use the same finite ledger and fresh identity. -/
theorem sample_resource_constructors : ConstructorsReady sampleTypes := by
  have infosL := Owned.VectorOps.focus_laws
    (Owned.vectorReference_laws (Element := AccountInfo.Value) (Unwind := Nat) (Terminal := Nat))
      infosFocus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro before args resource after called
    cases called
    exact ⟨sample_bytes_laws.empty_current before,
      sample_bytes_laws.empty_fresh before, sample_bytes_laws.empty_fresh before,
      sample_bytes_laws.empty_fresh before⟩
  · intro before capacity resource after called
    have fresh := sample_bytes_laws.capacity_fresh before capacity resource after called
    exact ⟨sample_bytes_laws.capacity_current before capacity resource after called, fresh, fresh,
      fresh⟩
  · intro before capacity resource after called
    exact ⟨sample_metas_laws.capacity_current before capacity resource after called,
      sample_metas_laws.capacity_fresh before capacity resource after called⟩
  · intro before values resource after called
    exact ⟨sample_metas_laws.list_current before values resource after called,
      sample_metas_laws.list_fresh before values resource after called⟩
  · intro before values resource after called
    exact ⟨infosL.list_current before values resource after called,
      infosL.list_fresh before values resource after called⟩
  · intro before values resource after called
    have fresh := sample_bytes_laws.list_fresh before values resource after called
    exact ⟨sample_bytes_laws.list_current before values resource after called, fresh, fresh, fresh⟩
  · intro before values resource after called
    have fresh := sample_bytes_laws.list_fresh before values resource after called
    exact ⟨sample_bytes_laws.list_current before values resource after called, fresh, fresh, fresh⟩
  · intro before args resource after called
    cases called
    exact ⟨emptyOnly_empty_current seedsFocus before, emptyOnly_empty_fresh seedsFocus before⟩
  · intro before args resource after called
    cases called
    exact ⟨emptyOnly_empty_current seedRefsFocus before, emptyOnly_empty_fresh seedRefsFocus before⟩

private theorem vector_allocate_keeps {Element : Type} {before : Owned.VectorState Element}
    {resource : Nat} {values : List Element} (current : before.current resource = some values)
    (extra : List Element) : (before.allocate extra).2.current resource = some values := by
  have bounded := Owned.VectorState.current_bound current
  simpa [Owned.VectorState.allocate, Owned.VectorState.current,
    List.getElem?_append_left bounded] using current

private theorem vector_allocate_map_keeps {Element Value : Type}
    {before : Owned.VectorState Element} {resource : Nat} {values : Value}
    (f : List Element → Value) (current : (before.current resource).map f = some values)
    (extra : List Element) : ((before.allocate extra).2.current resource).map f = some values := by
  cases found : before.current resource with
  | none => simp [found] at current
  | some original =>
    rw [vector_allocate_keeps found extra]
    simpa [found] using current

private theorem bytes_allocate_keeps (before : State) (values : Bytes)
    (retained : Retained sampleTypes) (current : retained.Holds before) :
    retained.Holds (bytesFocus.set before (before.2.bytes.allocate values).2) := by
  cases retained with
  | bytes _ _ | padding _ _ | literal _ _ => exact vector_allocate_keeps current values
  | metas _ _ | infos _ _ | seeds _ _ | refs _ _ => exact current

private theorem metas_allocate_keeps (before : State) (values : List Solanalib.Runtime.CpiMeta)
    (retained : Retained sampleTypes) (current : retained.Holds before) :
    retained.Holds (metasFocus.set before (before.2.metas.allocate values).2) := by
  cases retained with
  | metas _ _ => exact vector_allocate_keeps current values
  | bytes _ _ | padding _ _ | literal _ _ | infos _ _ | seeds _ _ | refs _ _ => exact current

private theorem infos_allocate_keeps (before : State) (values : List AccountInfo.Value)
    (retained : Retained sampleTypes) (current : retained.Holds before) :
    retained.Holds (infosFocus.set before (before.2.infos.allocate values).2) := by
  cases retained with
  | infos _ _ => exact vector_allocate_keeps current values
  | bytes _ _ | padding _ _ | literal _ _ | metas _ _ | seeds _ _ | refs _ _ => exact current

private theorem seeds_allocate_keeps (before : State) (values : List Unit)
    (retained : Retained sampleTypes) (current : retained.Holds before) :
    retained.Holds (seedsFocus.set before (before.2.seeds.allocate values).2) := by
  cases retained with
  | seeds _ _ => exact vector_allocate_map_keeps (fun _ => []) current values
  | bytes _ _ | padding _ _ | literal _ _ | metas _ _ | infos _ _ | refs _ _ => exact current

private theorem refs_allocate_keeps (before : State) (values : List Unit)
    (retained : Retained sampleTypes) (current : retained.Holds before) :
    retained.Holds (seedRefsFocus.set before (before.2.seedRefs.allocate values).2) := by
  cases retained with
  | refs _ _ => exact vector_allocate_map_keeps (fun _ => []) current values
  | bytes _ _ | padding _ _ | literal _ _ | metas _ _ | infos _ _ | seeds _ _ => exact current

private theorem bytes_set_keeps (before : State) (target : Nat) (values : Option Bytes)
    (retained : Retained sampleTypes) (current : retained.Holds before)
    (outside : ¬ retained.resource.byteTarget target) :
    retained.Holds (bytesFocus.set before (before.2.bytes.set target values)) := by
  cases retained with
  | bytes resource values | padding resource values | literal resource values =>
    exact (Owned.VectorState.current_set_other _ target resource _ outside).trans current
  | metas _ _ | infos _ _ | seeds _ _ | refs _ _ => exact current

private theorem metas_set_keeps (before : State) (target : Nat)
    (values : Option (List Solanalib.Runtime.CpiMeta))
    (retained : Retained sampleTypes) (current : retained.Holds before)
    (outside : retained.resource ≠ .metas target) :
    retained.Holds (metasFocus.set before (before.2.metas.set target values)) := by
  cases retained with
  | metas resource values =>
    exact (Owned.VectorState.current_set_other _ target resource _
      (fun same => outside (congrArg ResourceRef.metas same))).trans current
  | bytes _ _ | padding _ _ | literal _ _ | infos _ _ | seeds _ _ | refs _ _ => exact current

private theorem infos_set_keeps (before : State) (target : Nat)
    (values : Option (List AccountInfo.Value))
    (retained : Retained sampleTypes) (current : retained.Holds before)
    (outside : retained.resource ≠ .infos target) :
    retained.Holds (infosFocus.set before (before.2.infos.set target values)) := by
  cases retained with
  | infos resource values =>
    exact (Owned.VectorState.current_set_other _ target resource _
      (fun same => outside (congrArg ResourceRef.infos same))).trans current
  | bytes _ _ | padding _ _ | literal _ _ | metas _ _ | seeds _ _ | refs _ _ => exact current

private theorem seeds_set_keeps (before : State) (target : Nat) (values : Option (List Unit))
    (retained : Retained sampleTypes) (current : retained.Holds before)
    (outside : retained.resource ≠ .seeds target) :
    retained.Holds (seedsFocus.set before (before.2.seeds.set target values)) := by
  cases retained with
  | seeds resource items =>
    change (Owned.VectorState.current (before.2.seeds.set target values) resource).map _ = some
      items
    rw [Owned.VectorState.current_set_other _ target resource _
      (fun same => outside (congrArg ResourceRef.seeds same))]
    exact current
  | bytes _ _ | padding _ _ | literal _ _ | metas _ _ | infos _ _ | refs _ _ => exact current

private theorem refs_set_keeps (before : State) (target : Nat) (values : Option (List Unit))
    (retained : Retained sampleTypes) (current : retained.Holds before)
    (outside : retained.resource ≠ .refs target) :
    retained.Holds (seedRefsFocus.set before (before.2.seedRefs.set target values)) := by
  cases retained with
  | refs resource items =>
    change (Owned.VectorState.current (before.2.seedRefs.set target values) resource).map _ = some
      items
    rw [Owned.VectorState.current_set_other _ target resource _
      (fun same => outside (congrArg ResourceRef.refs same))]
    exact current
  | bytes _ _ | padding _ _ | literal _ _ | metas _ _ | infos _ _ | seeds _ _ => exact current

/-- Real Rc counter and event changes preserve the current vector ledgers. -/
theorem rc_resources : RetainsResources (types := sampleTypes) rcOps.cloneRc ∧
    RetainsResources (types := sampleTypes) rcOps.dropRc := by
  constructor
  all_goals
    rintro before ⟨field, cell⟩ retained current _ ⟨_, rfl⟩
    cases retained <;> cases field <;> exact current

private theorem resources_rcLift {Args Value Unwind : Type}
    {call : Callback.Run State Args Value Empty Nat}
    (law : RetainsResources (types := sampleTypes) call) :
    RetainsResources (types := sampleTypes) (AccountInfoRc.lift (Unwind := Unwind) call) := by
  rintro before args retained current _ ⟨produced, called, rfl⟩
  have kept := law before args retained current produced called
  cases produced with
  | returned _ _ | terminated _ => exact kept
  | unwound impossible _ => exact nomatch impossible

private theorem cloneCall_resources :
    RetainsResources (types := sampleTypes) (AccountInfoRc.cloneCall rcOps) := by
  intro before info retained current outcome called
  exact ((rc_resources.1.arguments (fun (_ : Unit) => (.lamports, info.lamports))).bind
    (fun _ => (rc_resources.1.arguments (fun (_ : Unit) => (.data, info.data))).map
      (fun _ => AccountInfo.clone info))) before () retained current outcome called

private theorem dropCall_resources :
    RetainsResources (types := sampleTypes) (AccountInfoRc.dropCall rcOps) := by
  intro before info retained current outcome called
  exact ((rc_resources.2.arguments (fun (_ : Unit) => (.lamports, info.lamports))).bind
    (fun _ => rc_resources.2.arguments (fun (_ : Unit) => (.data, info.data))))
    before () retained current outcome called

/-- The element effects of the sample retain every other source-local vector. -/
theorem cloneInfos_resources (values : List AccountInfo.Value) :
    RetainsResources (types := sampleTypes) (cloneInfos values) := by
  induction values with
  | nil =>
    intro before args retained current outcome called
    cases called
    exact current
  | cons value rest induction =>
    exact ((resources_rcLift cloneCall_resources).arguments (fun (_ : Unit) => value)).bind
      (fun _ => induction)

theorem dropInfos_resources (values : List AccountInfo.Value) :
    RetainsResources (types := sampleTypes) (dropInfos values) := by
  induction values with
  | nil =>
    intro before args retained current outcome called
    cases called
    exact current
  | cons value rest induction =>
    exact ((resources_rcLift dropCall_resources).arguments (fun (_ : Unit) => value)).bind
      (fun _ => induction)

/-- Current AccountInfo sequences survive actual element-clone effects
before extension updates the selected vector. -/
theorem infos_extend_ready : ExtendReady infosOps := by
  have storage := ExtendReady.of_laws (Owned.VectorOps.focus_laws
    (Owned.vectorReference_laws (Element := AccountInfo.Value) (Unwind := Nat) (Terminal := Nat))
      infosFocus)
  constructor
  · rintro before resource extra values after current ⟨produced, cloned, continued⟩
    have kept := cloneInfos_resources extra before () (.infos resource values) current produced
      cloned
    cases produced with
    | returned _ during => exact storage.returned during resource extra values after kept continued
    | unwound _ _ | terminated _ => cases continued
  · rintro before resource extra reason after ⟨values, current⟩ ⟨produced, cloned, continued⟩
    have kept := cloneInfos_resources extra before () (.infos resource values) current produced
      cloned
    cases produced with
    | returned _ during =>
      exact storage.unwound during resource extra reason after ⟨values, kept⟩ continued
    | unwound _ _ => cases continued; exact ⟨values, kept⟩
    | terminated _ => cases continued

/-- The selected mutation methods, including the actual metadata write,
have their precise current-sequence guarantees in the unchanged sample. -/
theorem sample_resource_mutations : MutationsReady sampleTypes := by
  have infosL := Owned.VectorOps.focus_laws
    (Owned.vectorReference_laws (Element := AccountInfo.Value) (Unwind := Nat) (Terminal := Nat))
      infosFocus
  refine ⟨PushReady.of_laws sample_bytes_laws, ExtendReady.of_laws sample_bytes_laws,
    PushReady.of_laws sample_metas_laws, ExtendReady.of_laws sample_metas_laws,
    ⟨infosL.push_current, infosL.push_unwind_live⟩,
    infos_extend_ready, ?_, ?_, ?_⟩
  · constructor <;> intro _ _ _ _ _ _ impossible <;> exact False.elim impossible
  · constructor <;> intro _ _ _ _ _ _ impossible <;> exact False.elim impossible
  · rintro before resource index item values after current _ ⟨actual, observed, rfl⟩
    have same : actual = values := Option.some.inj (observed.symm.trans current)
    subst actual
    exact Owned.VectorState.current_set before.2.metas resource _
      (Owned.VectorState.current_bound current)

private theorem focused_allocate_resources {Element Args : Type}
    (part : Owned.Focus State (Owned.VectorState Element)) (contents : Args → List Element)
    (keeps : ∀ before values (retained : Retained sampleTypes), retained.Holds before →
      retained.Holds (part.set before ((part.get before).allocate values).2)) :
    RetainsResources (types := sampleTypes) (Unwind := Nat)
      (part.lift (returnsOf fun state args => state.allocate (contents args))) := by
  rintro before args retained current _ ⟨produced, allocated, rfl⟩
  cases produced with
  | returned resource inner =>
    change (part.get before).allocate (contents args) = (resource, inner) at allocated
    have same : inner = ((part.get before).allocate (contents args)).2 :=
      (congrArg Prod.snd allocated).symm
    subst inner
    exact keeps before (contents args) retained current
  | unwound _ _ => exact False.elim allocated
  | terminated _ => trivial

private theorem all_resources_primitive {Args Value Unwind : Type}
    {call : Callback.Run State Args Value Unwind Nat}
    {selected : ResourcePrimitive sampleTypes call}
    (law : RetainsResources (types := sampleTypes) call) : PrimitiveResources selected := by
  intro before args retained current outcome called _
  exact law before args retained current outcome called

/-- Every actual ordinary primitive is checked before its following local
read. Allocations preserve existing slots, mutations frame distinct identities,
and Rc/array bookkeeping may change the counters and events of the sample. -/
theorem sample_resource_primitives {Args Value Unwind : Type}
    {call : Callback.Run State Args Value Unwind Nat}
    (selected : ResourcePrimitive sampleTypes call) : PrimitiveResources selected := by
  apply ResourcePrimitive.rec
    (motive := fun {A V U} (operation : Callback.Run State A V U Nat)
      (tag : ResourcePrimitive sampleTypes operation) => PrimitiveResources tag) (t := selected)
  case bytesEmpty =>
    rintro before args retained current outcome called _
    cases called
    exact bytes_allocate_keeps before [] retained current
  case bytesCapacity =>
    exact all_resources_primitive (focused_allocate_resources bytesFocus (fun (_ : Nat) => [])
      bytes_allocate_keeps)
  case bytesPush | bytesExtend | bytesDrop | paddingDrop =>
    rintro before args retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩ outside
    exact bytes_set_keeps before _ _ retained current outside
  case metasCapacity =>
    exact all_resources_primitive (focused_allocate_resources metasFocus (fun (_ : Nat) => [])
      metas_allocate_keeps)
  case metasList =>
    exact all_resources_primitive (focused_allocate_resources metasFocus id metas_allocate_keeps)
  case metasPush | metasExtend | metasDrop =>
    rintro before args retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩ outside
    exact metas_set_keeps before _ _ retained current outside
  case infosPush =>
    rintro before args retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩ outside
    exact infos_set_keeps before _ _ retained current outside
  case infosExtend =>
    rintro before ⟨resource, values⟩ retained current outcome ⟨produced, cloned, continued⟩ outside
    have kept := cloneInfos_resources values before () retained current produced cloned
    cases produced with
    | returned _ during =>
      obtain ⟨_, ⟨actual, _, rfl⟩, rfl⟩ := continued
      exact infos_set_keeps during resource _ retained kept outside
    | unwound _ _ => cases continued; exact kept
    | terminated _ => cases continued; trivial
  case infosDrop =>
    rintro before resource retained current outcome ⟨values, _, produced, dropped, continued⟩
      outside
    have kept := dropInfos_resources values before () retained current produced dropped
    cases produced with
    | returned _ during =>
      obtain ⟨_, ⟨actual, _, rfl⟩, rfl⟩ := continued
      exact infos_set_keeps during resource _ retained kept outside
    | unwound _ _ => cases continued; exact kept
    | terminated _ => cases continued; trivial
  case discriminatorsEmpty =>
    rintro before args retained current outcome called _
    cases called
    cases retained <;> exact current
  case discriminatorsPush | discriminatorsDrop =>
    rintro before args retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩ _
    cases retained <;> exact current
  case paddingList | literalBytes =>
    exact all_resources_primitive (focused_allocate_resources bytesFocus id bytes_allocate_keeps)
  case seedsEmpty =>
    rintro before args retained current outcome called _
    cases called
    exact seeds_allocate_keeps before [] retained current
  case seedsPush | refsPush | pda =>
    intro _ _ _ _ _ impossible
    exact False.elim impossible
  case seedsDrop =>
    rintro before resource retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩ outside
    exact seeds_set_keeps before resource _ retained current (fun same => outside (Or.inl same))
  case refsEmpty =>
    rintro before args retained current outcome called _
    cases called
    exact refs_allocate_keeps before [] retained current
  case refsDrop =>
    rintro before resource retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩ outside
    exact refs_set_keeps before resource _ retained current outside
  case literalWork =>
    intro before input retained current outcome called _
    change (if input.2.length < input.1 then _ else _) at called
    split at called
    · cases called; exact current
    · cases called.2; exact current
  case literalFinish =>
    exact all_resources_primitive (focused_allocate_resources infosFocus id infos_allocate_keeps)
  case literalRetire =>
    intro before input retained current outcome called _
    cases called
    exact current
  case rcClone => exact all_resources_primitive rc_resources.1
  case rcDrop => exact all_resources_primitive rc_resources.2
  case raise =>
    intro before input retained current outcome called _
    cases called
    exact current
  case writeMeta =>
    rintro before ⟨resource, index, item⟩ retained current _ ⟨after, ⟨values, _, rfl⟩, rfl⟩ outside
    exact metas_set_keeps before resource _ retained current outside

/-- The guard-vector destructor of the sample touches only its separate ledger. -/
theorem sample_guard_drop_resources : RetainsResources (types := sampleTypes)
  sampleTypes.guards.drop := by
  rintro before resource retained current _ ⟨_, ⟨values, _, rfl⟩, rfl⟩
  cases retained <;> exact current

/-- The exact sample remains admissible without an assumed populated guard
collection. Its explicit invocation frame is supplied at the opaque signature. -/
theorem sample_resources (deps : Dependencies sampleTypes)
    (invocation : InvocationResources sampleTypes deps) :
    ResourceReady sampleTypes deps sampleGuardProtocol := by
  refine ⟨sample_resource_constructors, sample_resource_mutations, ?_, sample_resource_primitives,
    sample_guard_drop_resources, ?_, invocation⟩
  · intro retained accounts next extra current
    cases retained <;> exact current
  · refine ⟨fun _ _ => RetainsResources.empty, RetainsResources.empty, ?_⟩
    intro acquired before args retained current outcome called
    cases called
    exact current

end Solanalib.Specs.Core.Token.OnchainAllocated.Witness
