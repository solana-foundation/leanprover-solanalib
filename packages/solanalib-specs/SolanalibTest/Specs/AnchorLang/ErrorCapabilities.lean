/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.error
public import Solanalib.Specs.AnchorLang.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.ErrorCapabilities

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorErrorOwned
open Solanalib.Specs.AnchorLang.error.Error

/-- The unrelated String constructor of this provider reuses a live identity.
The actual Box operation and both current observations are unchanged. -/
def boxingOps : Ops Reference.State Reference.StringId Reference.BoxId Reference.Failure :=
  { Reference.ops with
    copyLiteral := Callback.ofFunction fun before _ => .returned ⟨0⟩ before }

def boxingTypes : Types :=
  ⟨Reference.State, Reference.StringId, Reference.BoxId, Reference.Failure, boxingOps⟩

private theorem boxing_laws : boxingOps.BoxingLaws :=
  ⟨Reference.ops_laws.box.current, Reference.ops_laws.box.fresh, Reference.ops_laws.box_strings⟩

private theorem boxing_run : fromAnchor boxingOps sampleAnchorState sampleAnchor
    (.returned sampleError sampleBoxState) := by
  apply (fromAnchor_returned_iff _ _ _ _ _).mpr
  rfl

/-- The unused copy operation fails its real freshness law at a live String. -/
theorem boxing_provider_fails_unused_copy_law : ¬ boxingOps.Laws := by
  intro laws
  have absent := laws.copy.fresh sampleAnchorState "unused" ⟨0⟩ sampleAnchorState rfl
  cases absent

/-- Exact versioned boxing admits that provider and performs a real allocation. -/
theorem boxing_family_execution : FamilyHasExecution
    from_anchor_error_contract from_anchor_error_run boxingTypes :=
  ⟨sampleAnchorState, sampleAnchor, .returned sampleError sampleBoxState,
    ⟨boxing_laws, sampleAnchor_ready⟩, boxing_run⟩

/-- The retained current/fresh and String-frame facts derive the actual post,
including a ready returned error, despite the unrelated constructor defect. -/
theorem boxing_post_without_copy_law : ¬ boxingOps.Laws ∧
    (from_anchor_error_contract.contract boxingTypes).post sampleAnchorState sampleAnchor
      (.returned sampleError sampleBoxState) :=
  ⟨boxing_provider_fails_unused_copy_law,
    from_anchor_error_reference boxingTypes _ _ _ ⟨boxing_laws, sampleAnchor_ready⟩ boxing_run⟩

/-- Returning the same Box without a store exposes separate current/fresh
failures depending on whether that Box was initially live. -/
def unchangedBoxOps : Ops Reference.State Reference.StringId Reference.BoxId Reference.Failure :=
  { Reference.ops with
    newBox := Callback.ofFunction fun before _ => .returned ⟨0⟩ before }

def unchangedBoxTypes : Types :=
  ⟨Reference.State, Reference.StringId, Reference.BoxId, Reference.Failure, unchangedBoxOps⟩

/-- A reused live Box has a raw returned execution but violates the promised
freshness postcondition. Initial owned fields remain initialized. -/
theorem reused_box_breaks_fresh_post :
    fromAnchor unchangedBoxOps sampleBoxState sampleAnchor (.returned sampleError sampleBoxState) ∧
    ¬ (from_anchor_error_contract.contract unchangedBoxTypes).post sampleBoxState sampleAnchor
      (.returned sampleError sampleBoxState) := by
  refine ⟨(fromAnchor_returned_iff _ _ _ _ _).mpr rfl, ?_⟩
  intro post
  have absent := post.2.1
  cases absent

/-- A missing returned Box has a raw execution but cannot satisfy the actual
current-payload postcondition, even though its identity was absent initially. -/
theorem missing_box_breaks_current_post :
    fromAnchor unchangedBoxOps sampleAnchorState sampleAnchor
      (.returned sampleError sampleAnchorState) ∧
    ¬ (from_anchor_error_contract.contract unchangedBoxTypes).post sampleAnchorState sampleAnchor
      (.returned sampleError sampleAnchorState) := by
  refine ⟨(fromAnchor_returned_iff _ _ _ _ _).mpr rfl, ?_⟩
  intro post
  have present := post.2.2.1
  cases present

/-- This Box allocation stores the payload but erases its String resources. -/
def erasingBoxOps : Ops Reference.State Reference.StringId Reference.BoxId Reference.Failure :=
  { Reference.ops with
    newBox := Callback.ofFunction fun before payload =>
      let allocated := Reference.boxResult before payload
      .returned allocated.1 { allocated.2 with strings := [] } }

def erasingBoxTypes : Types :=
  ⟨Reference.State, Reference.StringId, Reference.BoxId, Reference.Failure, erasingBoxOps⟩

def erasedState : Reference.State := { sampleBoxState with strings := [] }

/-- Current Box metadata alone does not establish returned readiness. The raw
allocation is retained, and the missing moved String refutes the real post. -/
theorem erased_strings_break_ready_post :
    fromAnchor erasingBoxOps sampleAnchorState sampleAnchor (.returned sampleError erasedState) ∧
    ¬ (from_anchor_error_contract.contract erasingBoxTypes).post sampleAnchorState sampleAnchor
      (.returned sampleError erasedState) := by
  refine ⟨(fromAnchor_returned_iff _ _ _ _ _).mpr rfl, ?_⟩
  intro post
  obtain ⟨payload, present, _, live⟩ := post.2.2.2
  have same : payload = .anchor sampleAnchor := Option.some.inj present.symm
  subst payload
  obtain ⟨contents, current⟩ := live ⟨0⟩ (by
    exact List.mem_cons.mpr (Or.inl rfl))
  cases current

/-- Replacement needs neither Box allocation nor Box retirement. The unused freeBox of this provider
returns without retiring its current Box. -/
def comparisonOps : Ops Reference.State Reference.StringId Reference.BoxId Nat :=
  { Reference.natOps with
    newBox := Callback.ofFunction fun before _ => .returned ⟨0⟩ before
    freeBox := Callback.ofFunction fun before _ => .returned () before }

def comparisonTypes : Types :=
  ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat, comparisonOps⟩

private theorem comparison_laws : comparisonOps.ComparisonLaws :=
  ⟨Reference.natOps_laws.stringDrop.other, Reference.natOps_laws.drop_boxes,
    Reference.natOps_laws.store.current, Reference.natOps_laws.store_strings⟩

/-- The excluded retirement law fails at an actual finite primitive return. -/
theorem comparison_provider_fails_unused_retirement : ¬ comparisonOps.Laws := by
  intro laws
  have absent := laws.boxFree.current sampleBoxState ⟨0⟩ sampleBoxState rfl
  cases absent

def pubkeysAfter : Reference.State :=
  { sampleBoxState with
    boxes := sampleBoxState.boxes.set 0
      (some ((Payload.anchor sampleAnchor).withPubkeys sampleKey sampleKey))
    events := sampleBoxState.events ++ [.write ⟨0⟩] }

private theorem pubkeys_run : withPubkeys comparisonOps sampleBoxState
    (sampleError, sampleKey, sampleKey) (.returned sampleError pubkeysAfter) :=
  ⟨.anchor sampleAnchor, rfl, .returned () sampleBoxState, rfl,
    .anchor sampleAnchor, rfl, pubkeysAfter, rfl, rfl⟩

/-- The exact versioned comparison family accepts its four comparison laws and reached local-store
capability. -/
theorem pubkeys_family_execution : FamilyHasExecution
    with_pubkeys_contract with_pubkeys_run comparisonTypes :=
  ⟨sampleBoxState, (sampleError, sampleKey, sampleKey), .returned sampleError pubkeysAfter,
    ⟨comparison_laws, sampleBox_ready,
      ComparisonStoreReady.of_available comparisonOps comparison_laws.drop_boxes
        Reference.natOps_laws.store.available _ _ _⟩, pubkeys_run⟩

theorem pubkeys_post_without_retirement_law : ¬ comparisonOps.Laws ∧
    (with_pubkeys_contract.contract comparisonTypes).post sampleBoxState
      (sampleError, sampleKey, sampleKey) (.returned sampleError pubkeysAfter) :=
  ⟨comparison_provider_fails_unused_retirement,
    with_pubkeys_reference comparisonTypes _ _ _ ⟨comparison_laws, sampleBox_ready,
      ComparisonStoreReady.of_available comparisonOps comparison_laws.drop_boxes
        Reference.natOps_laws.store.available _ _ _⟩ pubkeys_run⟩

def valuesTypes : ValuesTypes where
  base := comparisonTypes
  Left := String
  Right := String
  Unwind := Nat
  callbacks := sampleValuesCallbacks

private theorem values_run : withValues comparisonOps sampleValuesCallbacks
    sampleValuesState sampleValuesArgs (.returned sampleError sampleValuesAfter) := by
  obtain ⟨payload, present, guarded⟩ := sampleValues_run
  refine ⟨payload, present, ?_⟩
  apply protectReturnPlace_of_protect
  apply (protect_returned_iff _ _ _ _ _ _ _).mpr
  exact (protect_returned_iff _ _ _ _ _ _ _).mp
    ((protectReturnPlace_returned_iff _ _ _ _ _ _ _ _).mp guarded)

private theorem values_admissible :
    sampleValuesCallbacks.Admissible comparisonOps sampleValuesArgs sampleValuesState where
  left := (sampleValuesCallbacks_admissible sampleValuesArgs sampleValuesState).left
  right := (sampleValuesCallbacks_admissible sampleValuesArgs sampleValuesState).right
  dropLeft := (sampleValuesCallbacks_admissible sampleValuesArgs sampleValuesState).dropLeft
  dropRight := (sampleValuesCallbacks_admissible sampleValuesArgs sampleValuesState).dropRight

/-- The actual ToString allocations, assignment and operand drops satisfy the
versioned family even when an unrelated Box destructor has no retirement law. -/
theorem values_family_execution : FamilyHasExecution
    with_values_contract with_values_run valuesTypes :=
  ⟨sampleValuesState, sampleValuesArgs, .returned sampleError sampleValuesAfter,
    ⟨comparison_laws, sampleValues_ready, ValuesCallbacks.CallReady.of_admissible
      sampleValues_ready values_admissible
        comparison_laws.drop_boxes Reference.natOps_laws.store.available⟩, values_run⟩

theorem values_post_without_retirement_law : ¬ comparisonOps.Laws ∧
    (with_values_contract.contract valuesTypes).post sampleValuesState sampleValuesArgs
      (.returned sampleError sampleValuesAfter) :=
  ⟨comparison_provider_fails_unused_retirement,
    with_values_reference valuesTypes _ _ _
      ⟨comparison_laws, sampleValues_ready, ValuesCallbacks.CallReady.of_admissible
        sampleValues_ready values_admissible
        comparison_laws.drop_boxes Reference.natOps_laws.store.available⟩ values_run⟩

namespace ReturnedFrames

def payload : Payload Reference.StringId := .program ⟨.invalidArgument, none, none⟩
def changedPayload : Payload Reference.StringId := .program ⟨.invalidAccountData, none, none⟩
def initial : Reference.State := ⟨[], [some payload], 2, []⟩
def args : ValuesArgs Reference.BoxId String String := ⟨sampleError, "12", "34"⟩
def changed : Reference.State := ⟨[], [some changedPayload], 2, [.write ⟨0⟩]⟩
def retired : Reference.State := ⟨[], [none], 2, [.write ⟨0⟩, .freeBox ⟨0⟩]⟩

/-- The same provider can allocate normally or update the current Box and
unwind. The latter effect violates the broader source ownership frame. -/
def callbacks : ValuesCallbacks Reference.State Reference.StringId String String Nat Nat :=
  { sampleValuesCallbacks with
    left := fun before value outcome => sampleValuesCallbacks.left before value outcome ∨
      ∃ after, Reference.natOps.writeBox before sampleError.resource changedPayload = some after ∧
        outcome = .unwound 7 after }

def types : ValuesTypes where
  base := ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat, Reference.natOps⟩
  Left := String
  Right := String
  Unwind := Nat
  callbacks := callbacks

private theorem laws : Reference.natOps.ComparisonLaws :=
  ⟨Reference.natOps_laws.stringDrop.other, Reference.natOps_laws.drop_boxes,
    Reference.natOps_laws.store.current, Reference.natOps_laws.store_strings⟩

private theorem payload_ready : payload.Ready Reference.natOps initial :=
  ⟨by decide, fun _ member => nomatch member⟩

private theorem ready : Ready Reference.natOps initial sampleError :=
  ⟨payload, rfl, payload_ready⟩

private theorem admissible : callbacks.ReturnedAdmissible Reference.natOps args initial where
  left := by
    intro value resource after present live run
    rcases run with run | ⟨_, _, impossible⟩
    · exact (sampleValuesCallbacks_admissible args initial).left
        value (.returned resource after) present live run
    · cases impossible
  right := by
    intro value retained afterLeft resource after present live first run
    rcases first with first | ⟨_, _, impossible⟩
    · exact (sampleValuesCallbacks_admissible args initial).right
        value retained afterLeft (.returned resource after) present live first run
    · cases impossible
  dropLeft := by
    intro before value after _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _
  dropRight := by
    intro before value after _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _

private theorem call_ready : callbacks.CallReady Reference.natOps args initial where
  returned := admissible
  left_unwind := by
    intro reason after run
    rcases run with run | ⟨actual, stored, equal⟩
    · exact False.elim (lift_no_unwind Reference.natOps.copyLiteral _ _ _ _ run)
    · cases equal
      exact ⟨changedPayload, Reference.natOps_laws.store.current _ _ _ _ stored,
        List.nodup_nil, fun _ member => nomatch member⟩
  right_unwind := by
    intro _ _ _ _ _ run
    exact False.elim (lift_no_unwind Reference.natOps.formatLiteral _ _ _ _ run)
  dropLeft := by
    intro pending _ _ _ _ current run
    cases run
    cases pending <;> first | exact current | trivial
  dropRight := by
    intro pending _ _ _ _ current run
    cases run
    cases pending <;> first | exact current | trivial
  assignment := by
    intro _ _ _ _ _ _
    exact ComparisonStoreReady.of_available Reference.natOps Reference.natOps_laws.drop_boxes
      Reference.natOps_laws.store.available _ _ _

private theorem changed_box_drop :
    dropErrorLift (Unwind := Nat) Reference.natOps sampleError changed (.returned () retired) :=
  ⟨.returned () retired,
    ⟨changedPayload, rfl, .returned () changed, rfl,
      .returned () retired, ⟨changedPayload, rfl, rfl⟩, rfl⟩, rfl⟩

private theorem unwind_run :
    withValues Reference.natOps callbacks initial args (.unwound 7 retired) :=
  ⟨payload, rfl, Or.inl ⟨.unwound 7 changed,
    ⟨.unwound 7 changed, ⟨.unwound 7 changed, Or.inr ⟨changed, rfl, rfl⟩, rfl⟩,
      .returned () changed, rfl, .returned () changed, rfl, rfl⟩,
    .returned () retired, changed_box_drop, rfl⟩⟩

def leftResult := Reference.stringResult false initial args.left
def rightResult := Reference.stringResult true leftResult.2 args.right
def normalAfter : Reference.State :=
  { rightResult.2 with
    boxes := [some (payload.withValues leftResult.1 rightResult.1)]
    events := rightResult.2.events ++ [.write ⟨0⟩] }

private theorem normal_run :
    withValues Reference.natOps callbacks initial args (.returned sampleError normalAfter) := by
  refine ⟨payload, rfl, ?_⟩
  apply protectReturnPlace_of_protect
  apply (protect_returned_iff _ _ _ _ _ _ _).mpr
  apply (scope_returned_iff _ _ _ _ _ _ _).mpr
  refine ⟨normalAfter, ?_, .cons _ _ _ _ _ rfl (.cons _ _ _ _ _ rfl (.nil _))⟩
  refine ⟨.returned leftResult.1 leftResult.2, ?_,
    .returned rightResult.1 rightResult.2, ?_, ?_⟩
  · exact Or.inl ⟨.returned leftResult.1 leftResult.2,
      ⟨.returned leftResult.1 leftResult.2, rfl, rfl⟩, rfl⟩
  · apply (protect_returned_iff _ _ _ _ _ _ _).mpr
    exact ⟨.returned rightResult.1 rightResult.2,
      ⟨.returned rightResult.1 rightResult.2, rfl, rfl⟩, rfl⟩
  · exact ⟨.returned sampleError normalAfter,
      ⟨payload, rfl, .returned () rightResult.2, rfl,
        payload, rfl, normalAfter, rfl, rfl⟩, rfl⟩

/-- The new condition admits a real normal execution, with both allocated
Strings retained by the unchanged Ready postcondition. -/
theorem returned_family_execution : FamilyHasExecution with_values_contract with_values_run types :=
  ⟨initial, args, .returned sampleError normalAfter, ⟨laws, ready, call_ready⟩, normal_run⟩

/-- That same admitted provider also has the unframed conversion unwind.
The actual modified Box is retired by the source-ordered receiver cleanup. -/
theorem unframed_unwind_family_execution : FamilyHasExecution with_values_contract with_values_run
  types :=
  ⟨initial, args, .unwound (7 : Nat) retired, ⟨laws, ready, call_ready⟩, unwind_run⟩

/-- A frame on the unwind of the conversion would reject this provider even though
both its actual normal Ready post and complete unwind post hold. -/
theorem unwind_conversion_frame_not_required :
    ¬ callbacks.Admissible Reference.natOps args initial ∧
    (with_values_contract.contract types).post initial args (.returned sampleError normalAfter) ∧
    (with_values_contract.contract types).post initial args (.unwound (7 : Nat) retired) := by
  refine ⟨?_, with_values_reference types _ _ _ ⟨laws, ready, call_ready⟩ normal_run,
    with_values_reference types _ _ _ ⟨laws, ready, call_ready⟩ unwind_run⟩
  intro frames
  have frame := frames.left payload (.unwound 7 changed) rfl payload_ready
    (Or.inr ⟨changed, rfl, rfl⟩)
  have impossible := frame.1
  cases impossible

/-- This conversion unwinds without a String result. Its first operand drop
then performs a real current-Box update and returns before receiver cleanup. -/
def dropCallbacks : ValuesCallbacks Reference.State Reference.StringId String String Nat Nat :=
  { sampleValuesCallbacks with
    left := fun before _ outcome => outcome = .unwound 9 before
    dropLeft := fun before _ outcome => ∃ after,
      Reference.natOps.writeBox before sampleError.resource changedPayload = some after ∧
      outcome = .returned () after }

def dropTypes : ValuesTypes := { types with callbacks := dropCallbacks }

private theorem no_normal_body {result : Error Reference.BoxId} {after : Reference.State} :
    ¬ valuesBody Reference.natOps dropCallbacks args initial () (.returned result after) := by
  rintro ⟨first, called, rest⟩
  cases called
  cases rest

private theorem drop_admissible :
    dropCallbacks.ReturnedAdmissible Reference.natOps args initial where
  left := by
    intro _ _ _ _ _ impossible
    cases impossible
  right := by
    intro _ _ _ _ _ _ _ impossible
    cases impossible
  dropLeft := by
    rintro _ _ _ ⟨_, _, body, _⟩
    exact False.elim (no_normal_body body)
  dropRight := by
    rintro _ _ _ ⟨_, _, body, _⟩
    exact False.elim (no_normal_body body)

private theorem drop_call_ready : dropCallbacks.CallReady Reference.natOps args initial where
  returned := drop_admissible
  left_unwind := by
    intro reason after run
    cases run
    exact ready
  right_unwind := by
    intro _ _ _ _ first _
    cases first
  dropLeft := by
    intro pending before outcome _ _ _ run
    obtain ⟨after, stored, equal⟩ := run
    cases equal
    have live : Ready Reference.natOps after sampleError :=
      ⟨changedPayload, Reference.natOps_laws.store.current _ _ _ _ stored,
        List.nodup_nil, fun _ member => nomatch member⟩
    cases pending <;> first | exact live | trivial
  dropRight := by
    intro pending _ _ _ _ current run
    cases run
    cases pending <;> first | exact current | trivial
  assignment := by
    intro _ _ _ _ first _
    cases first

private theorem drop_unwind_run :
    withValues Reference.natOps dropCallbacks initial args (.unwound 9 retired) :=
  ⟨payload, rfl, Or.inl ⟨.unwound 9 changed,
    ⟨.unwound 9 initial, ⟨.unwound 9 initial, rfl, rfl⟩,
      .returned () changed, ⟨changed, rfl, rfl⟩, .returned () changed, rfl, rfl⟩,
    .returned () retired, changed_box_drop, rfl⟩⟩

/-- Returned destructor calls reached from an unwinding body remain actual
model effects; they satisfy the reached cleanup resource obligation. -/
theorem unwind_body_drop_family_execution : FamilyHasExecution
    with_values_contract with_values_run dropTypes :=
  ⟨initial, args, .unwound (9 : Nat) retired, ⟨laws, ready, drop_call_ready⟩, drop_unwind_run⟩

theorem unwind_body_drop_frame_not_required :
    ¬ dropCallbacks.Admissible Reference.natOps args initial ∧
    dropCallbacks.dropLeft initial args.left (.returned () changed) ∧
    (with_values_contract.contract dropTypes).post initial args (.unwound (9 : Nat) retired) := by
  refine ⟨?_, ⟨changed, rfl, rfl⟩,
    with_values_reference dropTypes _ _ _ ⟨laws, ready, drop_call_ready⟩ drop_unwind_run⟩
  intro frames
  have entry : valuesDropEntry Reference.natOps dropCallbacks args [] initial initial :=
    ⟨.unwound 9 initial, .unwound 9 initial, ⟨.unwound 9 initial, rfl, rfl⟩, rfl, rfl⟩
  have frame := frames.dropLeft initial payload (.returned () changed)
    entry rfl payload_ready ⟨changed, rfl, rfl⟩
  have impossible := frame.1
  cases impossible

end ReturnedFrames

end SolanalibTest.Specs.AnchorLang.ErrorCapabilities

namespace SolanalibTest.Specs.AnchorLang.ErrorCapabilities.EqualityProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.AnchorLang.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.error_Error_eq,
      {
        package := "anchor-lang",
        version := "0.32.0",
        source := registry,
        dependencies := [⟨"solana-program-error", "2.2.0", registry⟩] },
      [("core::cmp::PartialEq::eq", "<anchor_lang::error::Error as \
        core::cmp::PartialEq>::eq")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.AnchorLang.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"anchor-lang", build.version, item, implementation⟩))

def members : List Key := [.error_Error_eq]

theorem every_member_has_a_literal_case :
    members.length = 1 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3"].all (fun version => fixtures.all (fun (key, build,
      expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.32.4", "0.32.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.31.99", "0.33.0", "1.0.2", "0.32.4-rc.1"].all (fun version => fixtures.all (fun (key,
      build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- An interval must not conceal a missing reference or a changed item range. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      !(Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).isEmpty &&
      (Solanalib.Specs.AnchorLang.Capabilities.catalog.applicability key).all (fun profile =>
        decide (profile.releases = ["0.32.0", "0.32.1", "0.32.2", "0.32.3"] ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

/-- Each required edge is checked independently. Duplicate compatible
candidates remain ambiguous actual dependency facts. -/
theorem dependency_facts_cannot_be_missing_wrong_or_ambiguous :
    fixtures.all (fun (key, build, _) => build.dependencies.all (fun required =>
      identitiesMatch key { build with dependencies := (build.dependencies.filter
        (fun dependency => dependency.package != required.package)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with version := "99.0.0" } else dependency)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with source :=
            ⟨"git", "https://example.invalid/dependency", "01234567890123456789012345678901\
              23456789"⟩ }
          else dependency)) } [] &&
      identitiesMatch key { build with dependencies := build.dependencies ++ [required] } [])) =
        true := by
  decide +kernel

/-- Provider references and compatible fixtures preserve the actual
identity of the caller; the provider version is not substituted for the defining crate. -/
theorem dependency_references_and_compatible_versions :
    ([("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.9.99", "2.9.99+fixture"])] : List
      (String × List String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, expected) => versions.all (fun version =>
        identitiesMatch key { build with dependencies := (build.dependencies.map
          (fun dependency => if dependency.package == package then
            { dependency with version := version } else dependency)) } expected))) = true := by
  decide +kernel

/-- In particular, the unit BorshIoError of ProgramError 3 cannot replace the
selected owned String carrier. Other rows enforce their declared bounds. -/
theorem dependency_bounds_retain_the_selected_domains :
    ([("solana-program-error", ["2.1.0", "3.0.0", "2.2.2-rc.1"])] : List (String × List
      String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, _) => if (build.dependency package).isSome then
        versions.all (fun version => identitiesMatch key
          { build with dependencies := (build.dependencies.map (fun dependency =>
            if dependency.package == package then { dependency with version := version }
            else dependency)) } []) else true)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorLang.ErrorCapabilities.EqualityProfiles
