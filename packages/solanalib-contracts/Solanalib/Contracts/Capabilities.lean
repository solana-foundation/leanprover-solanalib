/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Contracts.Family
public import Solanalib.Contracts.Versioning

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Contracts.Model.Capabilities

/-- The scope assigned to a model by the source registry. A supporting or
observation model is not upgraded by collecting it into a capability bundle. -/
inductive Kind where
  /-- The registered function model is complete under its stated premises. -/
  | full
  /-- The registered model has explicit remaining model requirements. -/
  | partialModel
  /-- A value or state projection omits parts of the primary source model. -/
  | observation
  /-- A reusable protocol or mathematical dependency supports source models. -/
  | supporting
  deriving DecidableEq, Repr

/-- The exact Rust identity of one registered source function, taken from the
source registry. `item` and `implementation` are the readable descriptions
of the called item and its resolved implementation. A binding to the Rust implementation
must compare both with its selected source call. The registry
records names, not generic instantiations; this is not implementation evidence. -/
structure RustIdentity where
  /-- The Cargo package of the pinned source of the API, such as `example-codec`. -/
  crateName : String
  /-- The exact version of that package, such as `2.6.0`. -/
  crateVersion : String
  /-- The source item through which the function is called: the function
  itself, or the trait method of a trait implementation, such as
  `core::convert::AsRef::as_ref`. -/
  item : String
  /-- The generic implementation that the item resolves to, as registered,
  such as `<example_codec::Buffer as core::convert::AsRef<[u8]>>::as_ref`. -/
  implementation : String
  deriving DecidableEq, Repr

/-- Embed a nongeneric contract without changing its state, admission or
outcomes. Generic source functions use their original `Family` instead. -/
def single {State Args Value Unwind Terminal : Type}
    (contract : Solanalib.Contracts.Model State Args Value Unwind Terminal) : Family where
  Index := PUnit.{2}
  State := fun _ => State
  Args := fun _ => Args
  Value := fun _ => Value
  Unwind := fun _ => Unwind
  Terminal := fun _ => Terminal
  contract := fun _ => contract

/-- A typed collection of exact model families. Model identities, roles and
Rust identities come from the existing source registry; they are not
implementation evidence.
Native model states remain explicit. An execution adapter must supply a common
world and representation when it combines calls on shared storage. -/
structure Catalog where
  /-- The finite source-model member type of a generated library catalog. -/
  Key : Type
  /-- The exact family, retaining every type, provider and profile index. -/
  family : Key → Family
  /-- The stable model identity in the source registry. -/
  modelId : Key → String
  /-- The registered scope of each member. -/
  kind : Key → Kind
  /-- Every Rust identity registered for the source APIs of the member, in registry
  order. A model with several APIs or Rust names lists them all; a supporting
  or observation model without a registered source function lists none. -/
  identities : Key → List RustIdentity
  /-- Whether the source registry associates this member with a Rust call.
  Selection retains this flag, so mathematical observations cannot acquire
  call identities merely because their source versions were reviewed. -/
  sourceCallRegistered : Key → Bool := fun key => !(identities key).isEmpty
  /-- Reviewed source/version/build alternatives for each model. These supply
  the source identities of `forBuild`, without changing the family of a model. -/
  applicability : Key → List Versioning.Profile := fun _ => []
  /-- Source-less helpers inherit applicability through these named consumers.
  They never acquire the Rust call identities of those consumers. -/
  applicabilityConsumers : Key → List String := fun _ => []

/-- A requested subset can select whole functions or individual generic
instantiations. It does not silently require unrelated library capabilities. -/
abbrev Selection (catalog : Catalog) :=
  (key : catalog.Key) → (catalog.family key).Index → Prop

/-- One fixed interpretation of every operation and generic instantiation.
Subset composition keeps this assignment fixed, including shared callbacks. -/
abbrev Operations (catalog : Catalog) :=
  (key : catalog.Key) → FamilyRun (catalog.family key)

/-- Ordinary propositional library assumptions for the requested subset.
This is partial correctness of explicit outcome relations, not termination,
provider-exit retention or correctness of a Rust implementation. -/
structure Spec (catalog : Catalog) (needs : Selection catalog)
    (operations : Operations catalog) : Prop where
  /-- Each requested operation satisfies its exact selected model contract. -/
  holds : ∀ key index, needs key index →
    ((catalog.family key).contract index).Holds (operations key index)

namespace Selection

/-- Request every member at every generic instantiation. -/
def all (catalog : Catalog) : Selection catalog := fun _ _ => True

/-- Request no operation. -/
def none (catalog : Catalog) : Selection catalog := fun _ _ => False

/-- Request one function at every generic instantiation. -/
def member (catalog : Catalog) (wanted : catalog.Key) : Selection catalog :=
  fun key _ => key = wanted

/-- Request exactly one typed function instantiation. -/
def one (catalog : Catalog) (wanted : catalog.Key)
    (instantiation : (catalog.family wanted).Index) : Selection catalog :=
  fun key index => (⟨key, index⟩ : (key : catalog.Key) × (catalog.family key).Index) =
    ⟨wanted, instantiation⟩

/-- Combine requirements without changing their operation interpretation. -/
def union {catalog : Catalog} (left right : Selection catalog) : Selection catalog :=
  fun key index => left key index ∨ right key index

/-- Every operation requested on the left is requested on the right. -/
def Subset {catalog : Catalog} (left right : Selection catalog) : Prop :=
  ∀ key index, left key index → right key index

end Selection

namespace Spec

/-- A caller may forget capabilities while retaining the same exact models
and operation interpretation. -/
theorem restrict {catalog : Catalog} {large small : Selection catalog}
    {operations : Operations catalog} (spec : Spec catalog large operations)
    (subset : small.Subset large) : Spec catalog small operations :=
  ⟨fun key index requested => spec.holds key index (subset key index requested)⟩

/-- Two subsets compose only for the same catalog and operation assignment.
There is no choice of a different implementation on an overlapping member. -/
theorem union {catalog : Catalog} {left right : Selection catalog}
    {operations : Operations catalog} (first : Spec catalog left operations)
    (second : Spec catalog right operations) :
    Spec catalog (left.union right) operations :=
  ⟨fun key index requested => requested.elim
    (first.holds key index) (second.holds key index)⟩

/-- A combined specification contains exactly its two requested subsets. -/
theorem union_iff {catalog : Catalog} {left right : Selection catalog}
    {operations : Operations catalog} :
    Spec catalog (left.union right) operations ↔
      Spec catalog left operations ∧ Spec catalog right operations := by
  constructor
  · intro spec
    exact ⟨spec.restrict (fun _ _ => Or.inl), spec.restrict (fun _ _ => Or.inr)⟩
  · rintro ⟨first, second⟩
    exact first.union second

/-- The empty requested subset has no hidden contract assumptions. -/
theorem none (catalog : Catalog) (operations : Operations catalog) :
    Spec catalog (Selection.none catalog) operations :=
  ⟨fun _ _ impossible => False.elim impossible⟩

end Spec

namespace Catalog

/-- Select a reviewed compilation while retaining the exact mathematical
families and their indices. Only matching source identities become callable.
Unsupported or unresolved profiles yield no source identity, and source-less
helpers remain mathematical capabilities. `build` must describe the actual
compilation; profile conditions and Rust correctness remain explicit obligations. -/
def forBuild (catalog : Catalog) (build : Versioning.Build) : Catalog :=
  { catalog with
    identities := fun key =>
      if catalog.sourceCallRegistered key then
        (catalog.applicability key).filterMap fun profile =>
          if profile.matches build then
            (profile.identityPackage build).map fun package =>
              ⟨package.package, package.version, profile.item, profile.implementation⟩
          else none
      else [] }

/-- Version selection changes no contract, generic index, precondition or
outcome relation. Existing mathematical reference witnesses remain reusable. -/
theorem forBuild_spec_iff (catalog : Catalog) (build : Versioning.Build)
    (needs : Selection catalog) (operations : Operations catalog) :
    Spec (catalog.forBuild build) needs operations ↔ Spec catalog needs operations :=
  ⟨fun spec => ⟨spec.holds⟩, fun spec => ⟨spec.holds⟩⟩

/-- Combine distinct library catalogs by tagging their member identities.
Each member keeps its own Rust identities. This does not identify their native
states or assert disjoint ownership; shared-state interpretation belongs to
the execution binding of the caller. -/
def sum (left right : Catalog) : Catalog where
  Key := Sum left.Key right.Key
  family := fun key => match key with
    | .inl member => left.family member
    | .inr member => right.family member
  modelId := fun key => match key with
    | .inl member => left.modelId member
    | .inr member => right.modelId member
  kind := fun key => match key with
    | .inl member => left.kind member
    | .inr member => right.kind member
  identities := fun key => match key with
    | .inl member => left.identities member
    | .inr member => right.identities member
  sourceCallRegistered := fun key => match key with
    | .inl member => left.sourceCallRegistered member
    | .inr member => right.sourceCallRegistered member
  applicability := fun key => match key with
    | .inl member => left.applicability member
    | .inr member => right.applicability member
  applicabilityConsumers := fun key => match key with
    | .inl member => left.applicabilityConsumers member
    | .inr member => right.applicabilityConsumers member

end Catalog

/-- Combine the fixed interpretations for a tagged union of catalogs. -/
def sumOperations {left right : Catalog} (first : Operations left)
    (second : Operations right) : Operations (left.sum right) :=
  fun key => match key with
    | .inl member => first member
    | .inr member => second member

/-- Select a subset from each tagged catalog. -/
def sumSelection {left right : Catalog} (first : Selection left)
    (second : Selection right) : Selection (left.sum right) :=
  fun key => match key with
    | .inl member => first member
    | .inr member => second member

/-- Library subsets compose without adding assumptions on other members. -/
theorem sumSpec {left right : Catalog} {first : Selection left}
    {second : Selection right} {leftOps : Operations left} {rightOps : Operations right}
    (leftSpec : Spec left first leftOps) (rightSpec : Spec right second rightOps) :
    Spec (left.sum right) (sumSelection first second) (sumOperations leftOps rightOps) := by
  constructor
  intro key index requested
  cases key with
  | inl member => exact leftSpec.holds member index requested
  | inr member => exact rightSpec.holds member index requested

end Solanalib.Contracts.Model.Capabilities
